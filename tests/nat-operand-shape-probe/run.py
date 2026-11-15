#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Nat operand-shape probe — which Nat ops Lean's kernel grinds on, and where.

Each probe puts a large literal at one operand position of one `Nat` operation,
leaves the other operand SYMBOLIC, and forces whnf with a recursor whose major
premise is the op application. That is the shape the foreign-kernel cross-check
actually hit; see README.md for the two weaker designs that measured nothing.

Verdicts:
  STUCK-fast  the kernel declined in milliseconds. SAFE.
  GRIND       the kernel walked the literal and blew a limit (or timed out).
  OK          it reduced and the statement held.

The probe statements are deliberately not all true: what is under test is
whether the kernel grinds TRYING, not whether the proposition holds.

Usage:
    python3 tests/nat-operand-shape-probe/run.py
    python3 tests/nat-operand-shape-probe/run.py --filter sub

Exit code is non-zero when any measured verdict differs from the `probe-expect`
pinned in its header, so a change in Lean's reduction behaviour cannot land
silently.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROBES = HERE / "probes"
TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"

EXPECT_RE = re.compile(r"^--@\s*probe-expect:\s*(\S+)", re.MULTILINE)
GRIND_RE = re.compile(r"maximum recursion depth|maximum number of heartbeats|deep recursion")


def lean_cmd() -> list[str]:
    return ["lean", f"+{TOOLCHAIN}"]


def toolchain_ok() -> tuple[bool, str]:
    """Identify the compiler, or refuse.

    FAIL CLOSED. A sibling corpus in the Trust tree silently reported a full
    table of verdicts produced by a compiler that never ran, because its
    toolchain symlink was dangling and nothing checked. A probe result is a
    measurement or it is nothing.
    """
    try:
        p = subprocess.run(lean_cmd() + ["--version"], capture_output=True, text=True, timeout=60)
    except Exception as exc:  # noqa: BLE001
        return False, f"could not run lean: {exc}"
    if p.returncode != 0 or not p.stdout.strip():
        return False, (p.stderr or p.stdout).strip()[:200] or "lean produced no version output"
    return True, p.stdout.strip().splitlines()[0]


def run_probe(path: Path, timeout: int) -> tuple[str, int]:
    t0 = time.time()
    try:
        p = subprocess.run(lean_cmd() + [str(path)], capture_output=True, text=True, timeout=timeout)
        rc, out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        rc, out = 124, ""
    ms = int((time.time() - t0) * 1000)
    if rc == 124:
        return "GRIND", ms
    if rc == 0:
        return "OK", ms
    return ("GRIND" if GRIND_RE.search(out) else "STUCK-fast"), ms


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--filter", default=None)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--output", default=str(HERE / "matrix.json"))
    args = ap.parse_args()

    ok, ident = toolchain_ok()
    if not ok:
        print(
            f"REFUSING to run: no usable lean ({' '.join(lean_cmd())}).\n  {ident}\n"
            "  Every probe would be recorded by a compiler that never ran.",
            file=sys.stderr,
        )
        return 2
    print(f"toolchain: {ident}")

    files = sorted(PROBES.glob("*.lean"))
    if args.filter:
        files = [f for f in files if args.filter in f.name]
    if not files:
        print("REFUSING: the filter selected zero probes.", file=sys.stderr)
        return 2

    rows, deviations = [], []
    for f in files:
        text = f.read_text(encoding="utf-8")
        m = EXPECT_RE.search(text)
        expect = m.group(1) if m else None
        verdict, ms = run_probe(f, args.timeout)
        rows.append({"probe": f.stem, "expect": expect, "verdict": verdict, "ms": ms})
        if expect is None:
            deviations.append(f"{f.name}: no probe-expect header")
        elif expect != verdict:
            deviations.append(f"{f.name}: expected {expect}, got {verdict} ({ms} ms)")
        print(f"  {'!' if expect != verdict else ' '} {f.stem:<28} {verdict:<11} {ms:>6} ms")

    Path(args.output).write_text(json.dumps(rows, indent=1) + "\n")
    grinds = sum(1 for r in rows if r["verdict"] == "GRIND")
    print(f"\n{len(rows)} probes, {grinds} GRIND, {len(deviations)} deviating")
    for d in deviations:
        print(f"  ! {d}")
    if deviations:
        print(
            "\n  A deviation is not automatically a bug: if Lean's reduction changed\n"
            "  deliberately, update the probe's `probe-expect` in the same commit."
        )
    return 1 if deviations else 0


if __name__ == "__main__":
    sys.exit(main())
