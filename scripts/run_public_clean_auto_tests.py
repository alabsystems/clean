#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Run the public clean-auto library tests in validated process shards.

AY's production memory limiter observes whole-process RSS.  A single libtest
process running the complete clean-auto inventory can therefore retain enough
allocator state across otherwise independent tests to trip that limiter.  This
helper keeps Cargo's normal test environment and package working directory, but
starts a fresh process for every bounded, disjoint namespace shard.
"""

from __future__ import annotations

import os
import re
import signal
import subprocess
import sys
from dataclasses import dataclass, field


MAX_TESTS_PER_SHARD = 100
TEST_THREADS = 1
INITIAL_LIST_TIMEOUT_SECONDS = 1800
SELECTOR_LIST_TIMEOUT_SECONDS = 60
SHARD_TIMEOUT_SECONDS = 900
CARGO_TEST = ["cargo", "test", "--locked", "--lib", "-p", "clean-auto"]


@dataclass
class Node:
    members: list[str] = field(default_factory=list)
    terminals: list[str] = field(default_factory=list)
    children: dict[str, "Node"] = field(default_factory=dict)


@dataclass(frozen=True)
class Shard:
    mode: str
    selector: str
    expected: tuple[str, ...]


@dataclass(frozen=True)
class CommandResult:
    returncode: int
    stdout: str
    stderr: str


class CommandRegistry:
    """Track Cargo's process group so signals and timeouts reap descendants."""

    def __init__(self) -> None:
        self._process: subprocess.Popen[str] | None = None

    def cancel(self) -> None:
        process = self._process
        if process is None or process.poll() is not None:
            return
        self._signal_group(process, signal.SIGTERM)
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self._signal_group(process, signal.SIGKILL)
            process.wait()

    @staticmethod
    def _signal_group(process: subprocess.Popen[str], sig: int) -> None:
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            pass

    def run(
        self,
        command: list[str],
        *,
        timeout: int,
        stderr_to_stdout: bool = False,
    ) -> CommandResult:
        if self._process is not None:
            raise RuntimeError("attempted to overlap serial test commands")
        environment = os.environ.copy()
        environment["CARGO_TERM_COLOR"] = "never"
        process = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT if stderr_to_stdout else subprocess.PIPE,
            text=True,
            errors="replace",
            start_new_session=True,
            env=environment,
        )
        self._process = process
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            self._signal_group(process, signal.SIGTERM)
            try:
                stdout, stderr = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                self._signal_group(process, signal.SIGKILL)
                stdout, stderr = process.communicate()
            raise RuntimeError(
                f"command exceeded its {timeout}-second deadline: "
                f"{command!r}\n{stdout}{stderr or ''}"
            )
        finally:
            self._process = None
        return CommandResult(process.returncode, stdout, stderr or "")


def parse_inventory(output: str, context: str) -> list[str]:
    """Parse stable libtest terse-list output and reject anything unexpected."""

    names: list[str] = []
    summary_seen = False
    for raw_line in output.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if re.fullmatch(r"[0-9]+ tests?, [0-9]+ benchmarks?", line):
            if summary_seen:
                raise RuntimeError(f"{context}: duplicate libtest list summary")
            summary_seen = True
            continue
        if summary_seen or not line.endswith(": test"):
            raise RuntimeError(
                f"{context}: unexpected libtest list line: {raw_line!r}"
            )
        names.append(line[:-6])
    if not names:
        raise RuntimeError(f"{context}: test inventory is empty")
    if len(names) != len(set(names)):
        raise RuntimeError(f"{context}: test inventory contains duplicate names")
    return names


def build_trie(names: list[str]) -> Node:
    root = Node()
    for name in sorted(names):
        node = root
        node.members.append(name)
        for component in name.split("::"):
            node = node.children.setdefault(component, Node())
            node.members.append(name)
        node.terminals.append(name)
    return root


def partition_inventory(names: list[str], max_tests: int) -> list[Shard]:
    """Partition an inventory into exact tests or validated module filters."""

    if max_tests <= 0:
        raise ValueError("max_tests must be positive")
    root = build_trie(names)
    name_set = set(names)
    shards: list[Shard] = []

    def visit(node: Node, prefix: list[str]) -> None:
        if prefix and len(node.members) <= max_tests and not node.terminals:
            selector = "::".join(prefix) + "::"
            # libtest filters by substring, not necessarily by prefix.  Only
            # use a compact module filter when it selects exactly this node.
            selected = {name for name in names if selector in name}
            if selected == set(node.members):
                shards.append(
                    Shard("filter", selector, tuple(sorted(node.members)))
                )
                return
        for terminal in node.terminals:
            shards.append(Shard("exact", terminal, (terminal,)))
        for component in sorted(node.children):
            visit(node.children[component], [*prefix, component])

    visit(root, [])
    covered = [name for shard in shards for name in shard.expected]
    if len(covered) != len(set(covered)):
        raise RuntimeError("shard partition contains duplicate test names")
    if set(covered) != name_set:
        missing = sorted(name_set - set(covered))
        extra = sorted(set(covered) - name_set)
        raise RuntimeError(
            "shard partition does not equal inventory; "
            f"missing={missing[:3]!r} extra={extra[:3]!r}"
        )
    if any(len(shard.expected) > max_tests for shard in shards):
        raise RuntimeError("shard partition exceeds configured test cap")
    return shards


def cargo_command(shard: Shard | None, *harness_args: str) -> list[str]:
    command = [*CARGO_TEST, "--"]
    if shard is not None:
        command.append(shard.selector)
        if shard.mode == "exact":
            command.append("--exact")
    command.extend(harness_args)
    return command


def list_tests(
    registry: CommandRegistry,
    shard: Shard | None,
    context: str,
    timeout: int,
) -> list[str]:
    result = registry.run(
        cargo_command(shard, "--list", "--format", "terse"),
        timeout=timeout,
    )
    if result.returncode != 0:
        detail = result.stderr or result.stdout
        raise RuntimeError(
            f"{context}: Cargo/libtest listing exited {result.returncode}\n{detail}"
        )
    return parse_inventory(result.stdout, context)


def run_shard(
    registry: CommandRegistry,
    shard: Shard,
    index: int,
    total: int,
) -> None:
    selected = list_tests(
        registry,
        shard,
        f"shard {shard.selector!r}",
        SELECTOR_LIST_TIMEOUT_SECONDS,
    )
    if len(selected) != len(shard.expected) or set(selected) != set(shard.expected):
        raise RuntimeError(
            f"shard {shard.selector!r} selected {len(selected)} tests instead "
            f"of its exact expected set of {len(shard.expected)}"
        )
    print(
        f"== running clean-auto shard {index}/{total} {shard.selector!r} "
        f"({len(shard.expected)} tests)",
        flush=True,
    )
    result = registry.run(
        cargo_command(shard, f"--test-threads={TEST_THREADS}"),
        timeout=SHARD_TIMEOUT_SECONDS,
        stderr_to_stdout=True,
    )
    sys.stdout.write(result.stdout)
    if result.stdout and not result.stdout.endswith("\n"):
        sys.stdout.write("\n")
    sys.stdout.flush()
    if result.returncode != 0:
        raise RuntimeError(
            f"shard {shard.selector!r} exited {result.returncode}"
        )


def main() -> int:
    if len(sys.argv) != 1:
        print(
            "error: this committed release helper takes no arguments",
            file=sys.stderr,
        )
        return 2
    registry = CommandRegistry()

    def handle_signal(signum: int, _frame: object) -> None:
        registry.cancel()
        raise SystemExit(128 + signum)

    for sig in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, handle_signal)

    try:
        inventory = list_tests(
            registry,
            None,
            "full clean-auto inventory",
            INITIAL_LIST_TIMEOUT_SECONDS,
        )
        shards = partition_inventory(inventory, MAX_TESTS_PER_SHARD)
        print(
            f"== clean-auto plan: {len(inventory)} tests in {len(shards)} "
            f"validated serial shards (max "
            f"{max(len(shard.expected) for shard in shards)})",
            flush=True,
        )
        for index, shard in enumerate(shards, 1):
            run_shard(registry, shard, index, len(shards))
    except (OSError, RuntimeError, ValueError) as error:
        registry.cancel()
        print(f"error: {error}", file=sys.stderr)
        return 1

    covered = sum(len(shard.expected) for shard in shards)
    if covered != len(inventory):
        print(
            f"error: clean-auto shards covered {covered} of {len(inventory)} tests",
            file=sys.stderr,
        )
        return 1
    print(
        f"== clean-auto shard coverage complete: {covered} of "
        f"{len(inventory)} tests"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
