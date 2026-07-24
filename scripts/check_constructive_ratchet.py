#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Andrew Yates <andrewyates.name@gmail.com>
"""Ratchet check for the clean-Native mathverse shard's constructive-theorem set.

Ensures the set of constructive theorems (foundational-axiom-only transitive deps)
does not silently change. Drift is only accepted when
``data/constructive_ratchet.json`` is staged in the same commit.

Usage:
    python3 scripts/check_constructive_ratchet.py          # --check (default)
    python3 scripts/check_constructive_ratchet.py --update # rewrite ratchet
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_PATH = REPO_ROOT / "data" / "constructive_ratchet.json"
RATCHET_REL = "data/constructive_ratchet.json"
BASELINE_NOTES = (
    "Baseline after wave-9 Branch A demasquerade sweep. "
    "Future count changes must be accompanied by commits that update this file."
)
CARGO_BUILD_JOBS = os.environ.get("CARGO_BUILD_JOBS", "1")
BUILD_LOG_TAIL_LINES = int(os.environ.get("CONSTRUCTIVE_RATCHET_TAIL_LINES", "80"))


def _tail_text(path: Path, max_lines: int) -> str:
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return ""
    return "\n".join(lines[-max_lines:])


def build_native_shard() -> list[str]:
    """Run ``mathverse_shard build-native`` and return sorted constructive names."""
    with tempfile.TemporaryDirectory(prefix="mathverse-ratchet-") as tmp:
        build_log = Path(tmp) / "cargo-build-native.log"
        cmd = [
            "cargo", "run", "--locked", "--release", "--quiet",
            "--message-format=short", "-j", CARGO_BUILD_JOBS,
            "-p", "clean-mathverse", "--bin", "mathverse_shard", "--",
            "build-native", tmp,
        ]
        with build_log.open("w", encoding="utf-8") as log:
            result = subprocess.run(
                cmd,
                cwd=REPO_ROOT,
                check=False,
                stdout=log,
                stderr=subprocess.STDOUT,
                text=True,
            )
        if result.returncode != 0:
            sys.stderr.write(
                f"mathverse_shard build-native failed; log: {build_log}\n"
            )
            sys.stderr.write(
                f"Last {BUILD_LOG_TAIL_LINES} build log lines:\n"
            )
            tail = _tail_text(build_log, BUILD_LOG_TAIL_LINES)
            if tail:
                sys.stderr.write(tail + "\n")
            sys.exit(2)
        sidecar = Path(tmp) / "clean-native.mathverse.json"
        data = json.loads(sidecar.read_text())
    return sorted(d["name"] for d in data["declarations"])


def load_ratchet() -> dict:
    if not RATCHET_PATH.exists():
        sys.stderr.write(f"Ratchet file missing: {RATCHET_PATH}\n")
        sys.exit(2)
    return json.loads(RATCHET_PATH.read_text())


def write_ratchet(names: list[str], notes: str) -> None:
    payload = {
        "last_updated": dt.date.today().isoformat(),
        "count": len(names),
        "names": names,
        "notes": notes,
    }
    RATCHET_PATH.write_text(json.dumps(payload, indent=2) + "\n")


def ratchet_staged_this_commit() -> bool:
    """True if the ratchet file is staged vs HEAD."""
    result = subprocess.run(
        ["git", "diff", "--cached", "--name-only", "HEAD", "--", RATCHET_REL],
        cwd=REPO_ROOT, check=False, capture_output=True, text=True,
    )
    return bool(result.stdout.strip())


def do_check() -> int:
    ratchet = load_ratchet()
    baseline = sorted(ratchet.get("names", []))
    current = build_native_shard()
    if baseline == current:
        sys.stdout.write(
            f"OK: {len(current)} constructive theorems match ratchet.\n")
        return 0

    added = sorted(set(current) - set(baseline))
    removed = sorted(set(baseline) - set(current))
    if len(current) == len(baseline) and added and removed:
        sys.stderr.write(
            f"RATCHET FAIL: swap detected (count unchanged at {len(current)} "
            "but names differ).\n")
        sys.stderr.write(f"  added:   {added}\n")
        sys.stderr.write(f"  removed: {removed}\n")
        return 1

    if ratchet_staged_this_commit():
        sys.stdout.write(
            f"RATCHET UPDATE: {len(baseline)} -> {len(current)} "
            f"(+{len(added)} / -{len(removed)}). "
            "Ratchet file staged; accepting drift.\n")
        return 0

    sys.stderr.write(
        f"RATCHET FAIL: drift from {len(baseline)} -> {len(current)} "
        f"(added {len(added)}, removed {len(removed)}). "
        "Update data/constructive_ratchet.json and stage it in this commit.\n")
    if added:
        sys.stderr.write(f"  added:   {added}\n")
    if removed:
        sys.stderr.write(f"  removed: {removed}\n")
    return 1


def do_update() -> int:
    current = build_native_shard()
    existing_notes = BASELINE_NOTES
    if RATCHET_PATH.exists():
        try:
            existing_notes = json.loads(RATCHET_PATH.read_text()).get(
                "notes", BASELINE_NOTES) or BASELINE_NOTES
        except Exception:
            pass
    write_ratchet(current, existing_notes)
    sys.stdout.write(f"Wrote {RATCHET_REL} with {len(current)} names.\n")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true",
                       help="compare current shard to ratchet (default)")
    group.add_argument("--update", action="store_true",
                       help="rewrite ratchet file from current shard")
    args = parser.parse_args()
    if args.update:
        return do_update()
    return do_check()


if __name__ == "__main__":
    sys.exit(main())
