#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Run one libtest inventory in validated, bounded process shards."""

from __future__ import annotations

import argparse
import os
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path


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
class ShardResult:
    shard: Shard
    output: str
    error: str | None = None


@dataclass(frozen=True)
class CommandResult:
    returncode: int
    stdout: str
    stderr: str


class CommandRegistry:
    """Track child process groups so failure and signals reap descendants."""

    def __init__(self) -> None:
        self._lock = threading.RLock()
        self._stopping = threading.Event()
        self._processes: set[subprocess.Popen[str]] = set()

    def cancel(self) -> None:
        self._stopping.set()
        with self._lock:
            processes = list(self._processes)
        for process in processes:
            self._signal_group(process, signal.SIGTERM)
        deadline = time.monotonic() + 5
        while any(process.poll() is None for process in processes):
            if time.monotonic() >= deadline:
                break
            time.sleep(0.05)
        with self._lock:
            processes = list(self._processes)
        for process in processes:
            self._signal_group(process, signal.SIGKILL)

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
        with self._lock:
            if self._stopping.is_set():
                raise RuntimeError("shard execution was cancelled")
            process = subprocess.Popen(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT if stderr_to_stdout else subprocess.PIPE,
                text=True,
                errors="replace",
                start_new_session=True,
            )
            self._processes.add(process)
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
                f"command exceeded its {timeout}-second shard deadline: "
                f"{command!r}\n{stdout}{stderr or ''}"
            )
        finally:
            with self._lock:
                self._processes.discard(process)
        return CommandResult(process.returncode, stdout, stderr or "")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--label", required=True)
    parser.add_argument(
        "--partition",
        required=True,
        choices=("namespace", "character"),
        help="prefix trie used to construct validated libtest filters",
    )
    parser.add_argument("--max-tests", required=True, type=int)
    parser.add_argument("--jobs", required=True, type=int)
    parser.add_argument("--test-threads", required=True, type=int)
    args = parser.parse_args()
    for name in ("max_tests", "jobs", "test_threads"):
        if getattr(args, name) <= 0:
            parser.error(f"--{name.replace('_', '-')} must be positive")
    return args


def parse_inventory(output: str, context: str) -> list[str]:
    names: list[str] = []
    for raw_line in output.splitlines():
        if not raw_line.endswith(": test"):
            raise RuntimeError(f"{context}: unexpected libtest list line: {raw_line!r}")
        names.append(raw_line[:-6])
    if not names:
        raise RuntimeError(f"{context}: test inventory is empty")
    if len(names) != len(set(names)):
        raise RuntimeError(f"{context}: test inventory contains duplicate names")
    return names


def list_tests(
    registry: CommandRegistry, command: list[str], context: str
) -> list[str]:
    result = registry.run(command, timeout=60)
    if result.returncode != 0:
        detail = result.stderr or result.stdout
        raise RuntimeError(
            f"{context}: libtest listing exited {result.returncode}\n{detail}"
        )
    return parse_inventory(result.stdout, context)


def build_trie(names: list[str], partition: str) -> Node:
    root = Node()
    for name in sorted(names):
        node = root
        node.members.append(name)
        tokens = list(name) if partition == "character" else name.split("::")
        for token in tokens:
            node = node.children.setdefault(token, Node())
            node.members.append(name)
        node.terminals.append(name)
    return root


def make_selector(prefix: list[str], partition: str) -> str:
    if partition == "character":
        return "".join(prefix)
    return "::".join(prefix) + "::"


def partition_inventory(
    names: list[str], partition: str, max_tests: int
) -> list[Shard]:
    root = build_trie(names, partition)
    name_set = set(names)
    shards: list[Shard] = []

    def visit(node: Node, prefix: list[str]) -> None:
        if prefix and len(node.members) <= max_tests and not node.terminals:
            selector = make_selector(prefix, partition)
            selected = {name for name in names if selector in name}
            if selected == set(node.members):
                shards.append(
                    Shard("filter", selector, tuple(sorted(node.members)))
                )
                return
        for terminal in node.terminals:
            shards.append(Shard("exact", terminal, (terminal,)))
        for token in sorted(node.children):
            visit(node.children[token], [*prefix, token])

    visit(root, [])
    covered = [name for shard in shards for name in shard.expected]
    if len(covered) != len(set(covered)):
        raise RuntimeError("shard partition contains duplicate test names")
    if set(covered) != name_set:
        missing = sorted(name_set - set(covered))
        extra = sorted(set(covered) - name_set)
        raise RuntimeError(
            f"shard partition does not equal inventory; missing={missing[:3]!r} "
            f"extra={extra[:3]!r}"
        )
    if any(len(shard.expected) > max_tests for shard in shards):
        raise RuntimeError("shard partition exceeds configured test cap")
    return shards


def selector_command(binary: Path, shard: Shard) -> list[str]:
    command = [str(binary), shard.selector]
    if shard.mode == "exact":
        command.append("--exact")
    return command


def run_shard(
    registry: CommandRegistry,
    binary: Path,
    label: str,
    index: int,
    total_shards: int,
    test_threads: int,
    shard: Shard,
) -> ShardResult:
    header = (
        f"== running {label} shard {index}/{total_shards} "
        f"{shard.selector!r} ({len(shard.expected)} tests, "
        f"{test_threads} worker(s))\n"
    )
    try:
        selected = list_tests(
            registry,
            selector_command(binary, shard) + ["--list", "--format", "terse"],
            f"{label} shard {shard.selector!r}",
        )
        if len(selected) != len(shard.expected) or set(selected) != set(
            shard.expected
        ):
            return ShardResult(
                shard,
                header,
                f"selector chose {len(selected)} tests instead of the exact "
                f"expected set of {len(shard.expected)}",
            )
        result = registry.run(
            selector_command(binary, shard)
            + [f"--test-threads={test_threads}"],
            timeout=3600,
            stderr_to_stdout=True,
        )
    except (OSError, RuntimeError) as error:
        return ShardResult(shard, header, str(error))
    output = header + result.stdout
    if result.returncode != 0:
        return ShardResult(
            shard,
            output,
            f"test process exited {result.returncode}",
        )
    return ShardResult(shard, output)


def cancel_pending(
    registry: CommandRegistry,
    executor: ThreadPoolExecutor,
    futures: list[Future[ShardResult]],
) -> None:
    registry.cancel()
    for future in futures:
        future.cancel()
    executor.shutdown(wait=True, cancel_futures=True)


def main() -> int:
    args = parse_args()
    binary = args.binary.resolve()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise SystemExit(f"error: test binary is not executable: {binary}")

    registry = CommandRegistry()

    def handle_signal(signum: int, _frame: object) -> None:
        registry.cancel()
        raise SystemExit(128 + signum)

    for sig in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, handle_signal)

    try:
        inventory = list_tests(
            registry,
            [str(binary), "--list", "--format", "terse"],
            f"{args.label} full inventory",
        )
        shards = partition_inventory(inventory, args.partition, args.max_tests)
    except (OSError, RuntimeError) as error:
        raise SystemExit(f"error: {error}") from error

    print(
        f"== {args.label} plan: {len(inventory)} tests in {len(shards)} "
        f"validated shards (max {max(len(s.expected) for s in shards)}, "
        f"{args.jobs} process job(s), {args.test_threads} worker(s) each)"
    )

    executor = ThreadPoolExecutor(max_workers=args.jobs)
    futures = [
        executor.submit(
            run_shard,
            registry,
            binary,
            args.label,
            index,
            len(shards),
            args.test_threads,
            shard,
        )
        for index, shard in enumerate(shards, 1)
    ]
    for future in as_completed(futures):
        try:
            result = future.result()
        except Exception as error:  # Defensive: workers normally return errors.
            print(f"error: shard worker failed: {error}", file=sys.stderr)
            cancel_pending(registry, executor, futures)
            return 1
        sys.stdout.write(result.output)
        if result.output and not result.output.endswith("\n"):
            sys.stdout.write("\n")
        sys.stdout.flush()
        if result.error is not None:
            print(
                f"error: {args.label} shard {result.shard.selector!r}: "
                f"{result.error}",
                file=sys.stderr,
            )
            cancel_pending(registry, executor, futures)
            return 1
    executor.shutdown(wait=True)

    covered = sum(len(shard.expected) for shard in shards)
    if covered != len(inventory):
        print(
            f"error: {args.label} shards covered {covered} of "
            f"{len(inventory)} tests",
            file=sys.stderr,
        )
        return 1
    print(
        f"== {args.label} shard coverage complete: {covered} of "
        f"{len(inventory)} tests"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
