#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Re-derive the pinned Lean verdicts of every `tests/fixtures/mutual_nested`
fixture (gap G23, designs/2026-10-08-mutual-nested-recursion.md).

The verdicts the Clean tests compare against are never typed by hand: this
script runs the pinned `lean` binaries on each fixture — v4.8.0, the version
trust-ir's package pins, and v4.30.0-rc2, the conformance reference of
docs/DECISIONS.md R2 — and writes `tests/fixtures/mutual_nested/verdicts.json`.
`--check` re-derives them and fails when the recorded file disagrees (or a
binary is missing: exit 2).

    python3 scripts/mutual_nested_verdicts.py           # (re)write verdicts.json
    python3 scripts/mutual_nested_verdicts.py --check   # compare, exit 1 on drift
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "tests" / "fixtures" / "mutual_nested"
VERDICTS = FIXTURES / "verdicts.json"
TOOLCHAINS = Path.home() / ".elan/toolchains"
LEANS = {
    "lean_4_8_0": TOOLCHAINS / "leanprover--lean4---v4.8.0/bin/lean",
    "lean_4_30_0_rc2": TOOLCHAINS / "leanprover--lean4---v4.30.0-rc2/bin/lean",
}


def lean_verdict(lean: Path, fixture: Path) -> tuple[str, str]:
    proc = subprocess.run(
        [str(lean), fixture.name],
        cwd=fixture.parent,
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    out = (proc.stdout + proc.stderr).strip()
    errors = [line for line in out.splitlines() if ": error:" in line]
    accepted = proc.returncode == 0 and not errors
    first = errors[0].split(": error:", 1)[1].strip() if errors else ""
    return ("accepted" if accepted else "refused", first)


def derive() -> dict:
    out = {}
    for fixture in sorted(FIXTURES.glob("*.lean")):
        row = {}
        for key, lean in LEANS.items():
            verdict, first = lean_verdict(lean, fixture)
            row[key] = verdict
            row[key + "_first_error"] = first
        out[fixture.name] = row
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for lean in LEANS.values():
        if not lean.is_file():
            print(f"pinned Lean binary not found: {lean}", file=sys.stderr)
            return 2
    derived = {"schema": "clean-mutual-nested-verdicts-v2", "fixtures": derive()}
    if args.check:
        recorded = json.loads(VERDICTS.read_text())
        if recorded != derived:
            print("verdicts.json disagrees with the pinned Lean binary", file=sys.stderr)
            print(json.dumps(derived, indent=1), file=sys.stderr)
            return 1
        print("verdicts.json matches the pinned Lean binary")
        return 0
    VERDICTS.write_text(json.dumps(derived, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps(derived, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
