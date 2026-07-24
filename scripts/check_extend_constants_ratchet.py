#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed ratchet for the extend_constants_* bulk-import bypass (#4).

extend_constants_unchecked / extend_constants_structural register constants in
bulk, bypassing per-declaration kernel type-checking. This scanner enumerates
every source `.extend_constants_*(` call site under crates/ and asserts each is
accounted for in data/unchecked_decl_ratchet.json (production_sites or
test_excluded_sites) and that the production counts do not exceed the recorded
baseline. A NEW, unaccounted bypass fails the gate — forcing a // SOUNDNESS:
comment + an explicit ratchet entry before it can land.

Wired into scripts/local_gate.sh. Pure-stdlib; no cargo build required.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET = REPO_ROOT / "data" / "unchecked_decl_ratchet.json"
CRATES = REPO_ROOT / "crates"

# Dot-call form only: `<recv>.extend_constants_unchecked(` / `..._structural(`.
# This deliberately does NOT match the method definitions (`fn extend_constants_*`
# in env/registration.rs), the trait delegation (`Environment::extend_constants_*`
# in env/trusted_ext.rs, a `::` call), doc comments, or string literals.
CALL_RE = re.compile(r"\.extend_constants_(unchecked|structural)\s*\(")


def is_test_path(rel: Path) -> bool:
    """True for test FILES (whole-file test targets). Inline #[cfg(test)] blocks
    inside otherwise-production files are NOT caught here — those must be listed
    explicitly in test_excluded_sites."""
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
    # `tests.rs`, `*_tests.rs`, `test_*.rs`, `tests_*.rs`
    return bool(re.search(r"(^test_|_tests?\.rs$|^tests?\.rs$|^tests_)", name)) or "test" in name


def load_ratchet() -> dict:
    try:
        data = json.loads(RATCHET.read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {RATCHET}: {exc}")
    block = data.get("extend_constants")
    if not isinstance(block, dict):
        sys.exit(f"FAIL: {RATCHET} missing the 'extend_constants' block (#4).")
    return block


def main() -> int:
    block = load_ratchet()
    prod = {
        (s["file"], s["method"])
        for s in block.get("production_sites", [])
        if "file" in s and "method" in s
    }
    test_excluded = {
        (s["file"], s["method"])
        for s in block.get("test_excluded_sites", [])
        if "file" in s and "method" in s
    }
    base_unchecked = int(block.get("unchecked_production_count", -1))
    base_structural = int(block.get("structural_production_count", -1))

    counts = {"unchecked": 0, "structural": 0}
    unaccounted: list[str] = []

    for path in sorted(CRATES.rglob("*.rs")):
        rel = path.relative_to(REPO_ROOT)
        if is_test_path(rel):
            continue
        try:
            text = path.read_text()
        except OSError as exc:
            sys.exit(f"FAIL: cannot read {rel}: {exc}")
        for lineno, line in enumerate(text.splitlines(), 1):
            m = CALL_RE.search(line)
            if not m:
                continue
            method = f"extend_constants_{m.group(1)}"
            key = (str(rel), method)
            if key in test_excluded:
                continue
            if key in prod:
                counts[m.group(1)] += 1
                continue
            unaccounted.append(f"{rel}:{lineno}  {method}")

    ok = True
    if unaccounted:
        ok = False
        print("FAIL: unaccounted extend_constants_* bulk-bypass call site(s):", file=sys.stderr)
        for u in unaccounted:
            print(f"  {u}", file=sys.stderr)
        print(
            "  -> add a // SOUNDNESS: comment at the call AND an entry under "
            "data/unchecked_decl_ratchet.json -> extend_constants "
            "(production_sites or test_excluded_sites).",
            file=sys.stderr,
        )

    for label, found, base in (
        ("unchecked", counts["unchecked"], base_unchecked),
        ("structural", counts["structural"], base_structural),
    ):
        if found > base:
            ok = False
            print(
                f"FAIL: {label} production bypass count {found} exceeds baseline {base} "
                f"(data/unchecked_decl_ratchet.json). New bypass must be justified + ratcheted.",
                file=sys.stderr,
            )
        elif found < base:
            # Improvement — allowed, but the baseline is now stale.
            print(
                f"NOTE: {label} production bypass count {found} is BELOW baseline {base}; "
                f"lower extend_constants.{label}_production_count in the ratchet.",
            )

    if ok:
        print(
            f"OK: extend_constants bypass ratchet — "
            f"unchecked={counts['unchecked']}/{base_unchecked}, "
            f"structural={counts['structural']}/{base_structural} production sites accounted for."
        )
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
