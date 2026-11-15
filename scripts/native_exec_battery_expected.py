#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""native_exec_battery_expected.py -- mint the native execution battery's
expected outputs from pinned Lean.

The battery itself is the Rust integration test
crates/clean/tests/native_exec_battery.rs (the `compile-runtime` scorecard
row's gate, and the `native-exec-battery` leg of scripts/local_gate.sh). It
compares `clean run` with the COMMITTED bytes under
tests/fixtures/native_exec_battery/expected/, so running it needs no Lean
install. This tool is how those bytes are made, and the only way:

  LEAN_BACKTRACE=0 lean -Dlinter.all=false --run <program> <args>  < <stdin>

run in a fresh scratch working directory per program.

  * LEAN_BACKTRACE=0: a panic's backtrace carries load addresses, which are
    not reproducible bytes (measured: `a[5]!` printed a 2.6 KB backtrace).
  * -Dlinter.all=false: `lean --run` prints linter warnings on STDOUT, ahead of
    the program's own output (measured: an unused `let` put a warning there).

A program pinned Lean REJECTS, or for which it prints a compile message, is
refused here rather than recorded: the battery's programs must be Lean.

`--fixture DIR` mints another fixture of the same shape (`DIR/programs/*.lean`
into `DIR/expected/`) by the same command; the advice-replay checker's
(tests/fixtures/advice_replay_checker, unit X1 of the self-proof execution
plan) is minted this way.

Usage:
  scripts/native_exec_battery_expected.py [--lean PATH] [--fixture DIR] [--only NAME ...]
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
FIXTURE = REPO_ROOT / "tests" / "fixtures" / "native_exec_battery"
DEFAULT_LEAN = (
    Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.30.0-rc2" / "bin" / "lean"
)
COMPILE_MESSAGE = re.compile(rb"\.lean:\d+:\d+: (error|warning|info)")


def program_args(programs: Path, name: str) -> list[str]:
    path = programs / f"{name}.args"
    return [line for line in path.read_text().splitlines() if line] if path.exists() else []


def program_stdin(programs: Path, name: str) -> bytes:
    path = programs / f"{name}.stdin"
    return path.read_bytes() if path.exists() else b""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--lean", default=str(DEFAULT_LEAN))
    parser.add_argument("--fixture", default=str(FIXTURE),
                        help="fixture directory holding programs/ and expected/")
    parser.add_argument("--only", nargs="+", default=None)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()

    lean = Path(args.lean)
    if not os.access(lean, os.X_OK):
        print(f"[native-exec-expected] FAIL: no executable lean at {lean}", file=sys.stderr)
        return 1
    programs = Path(args.fixture).resolve() / "programs"
    expected = Path(args.fixture).resolve() / "expected"
    names = sorted(p.stem for p in programs.glob("*.lean"))
    if not names:
        print(f"[native-exec-expected] FAIL: no programs under {programs}", file=sys.stderr)
        return 1
    if args.only:
        unknown = sorted(set(args.only) - set(names))
        if unknown:
            print(f"[native-exec-expected] FAIL: unknown program(s) {unknown}", file=sys.stderr)
            return 1
        names = [n for n in names if n in args.only]

    version = subprocess.run([str(lean), "--version"], capture_output=True, text=True).stdout
    expected.mkdir(parents=True, exist_ok=True)
    (expected / "LEAN_VERSION").write_text(version)
    env = dict(os.environ, LEAN_BACKTRACE="0")
    for name in names:
        with tempfile.TemporaryDirectory(prefix="native-exec-expected-") as cwd:
            try:
                proc = subprocess.run(
                    [str(lean), "-Dlinter.all=false", "--run", str(programs / f"{name}.lean"),
                     *program_args(programs, name)],
                    input=program_stdin(programs, name), capture_output=True, timeout=args.timeout,
                    cwd=cwd, env=env,
                )
            except subprocess.TimeoutExpired:
                print(f"[native-exec-expected] FAIL: lean timed out on {name}", file=sys.stderr)
                return 1
        if COMPILE_MESSAGE.search(proc.stdout):
            print(f"[native-exec-expected] FAIL: lean printed a compile message on stdout for"
                  f" {name}; fix the program, never the expected bytes", file=sys.stderr)
            return 1
        (expected / f"{name}.stdout").write_bytes(proc.stdout)
        (expected / f"{name}.stderr").write_bytes(proc.stderr)
        (expected / f"{name}.rc").write_text(f"{proc.returncode}\n")
        print(f"  lean {name}: rc={proc.returncode} stdout={len(proc.stdout)}B"
              f" stderr={len(proc.stderr)}B")
    print(f"[native-exec-expected] minted by {version.strip()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
