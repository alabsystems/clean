#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Prelude instance-priority ratchet: hand-registered priority vs Lean's `.olean`.

Clean's hand-rolled prelude registers typeclass instances with a priority it
GUESSES; real Lean serializes the true priority into every `.olean`
(`Lean.Meta.instanceExtension`, one `InstanceEntry` per registration). `.olean`
import is first-registered-wins, so a wrong guess used to survive forever — and
instance priority decides which candidate `synthInstance` reaches first, i.e.
THE SHAPE OF EVERY ELABORATED TERM.

That defect was fixed one-off three times before anyone counted it:

  8d80c9d98  instOfNatNat  guessed 100, Lean serializes 1000
  066a1173f  instLTNat     guessed 100, Lean serializes 1000 (30th of 43 `LT`)
  28e7834a1  B101 hetero bridges seeded pre-import at 50

The `instOfNatNat` mistake is the one to learn from: Lean's source reads
`@[default_instance 100] instance instOfNatNat …` and Clean read that `100` off
`@[default_instance]` — a DIFFERENT TABLE (literal-type defaulting, not
`synthInstance` candidate ordering). The `instance` itself is unannotated, so
its real priority is Lean's default 1000. **Never read a priority off a Lean
SOURCE attribute; read the `u64` in the shipped `.olean`.**

This gate reads the checked-in census
(`data/prelude_instance_priority_census.json`, produced by the measurement test)
and:
  - ENFORCES monotonic decrease of `mismatched`;
  - REFUSES A SHRINKING DENOMINATOR — `colliding` and `prelude_instances` may
    only grow, so the class cannot be "fixed" by deleting hand-registrations
    until nothing is measured;
  - PINS the measured names, so a row cannot quietly stop being checked;
  - FAILS on a NEW mismatched name even at a flat count (one fixed, one added);
  - CHECKS the census is internally consistent (totals match the listed rows).

  scripts/check_prelude_instance_priority_ratchet.py            # FAIL on regression
  scripts/check_prelude_instance_priority_ratchet.py --update   # lock in a ratchet-down

Pure-stdlib; reads only checked-in JSON — it needs no Lean toolchain, which is
why the measurement and the gate are split. Measurement:
`crates/clean-olean/tests/prelude_instance_priority_census.rs`.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CENSUS = REPO_ROOT / "data" / "prelude_instance_priority_census.json"
RATCHET = REPO_ROOT / "data" / "prelude_instance_priority_ratchet.json"


def load(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {path}: {exc}")


def main(argv: list[str]) -> int:
    census = load(CENSUS)
    ratchet = load(RATCHET)
    totals = census.get("totals", {})
    rows = census.get("rows", [])

    required = ("colliding", "mismatched", "prelude_instances")
    missing = [k for k in required if totals.get(k) is None]
    if missing:
        sys.exit(f"FAIL: {CENSUS.name} has no totals.{'/'.join(missing)}")
    colliding = int(totals["colliding"])
    mismatched = int(totals["mismatched"])
    prelude_instances = int(totals["prelude_instances"])

    # Self-consistency: the totals must describe the rows actually listed, and
    # every row's own mismatch flag must follow from its two priorities.
    if colliding != len(rows):
        sys.exit(
            f"FAIL: {CENSUS.name} totals.colliding={colliding} but {len(rows)} rows are listed"
        )
    live_mismatched = sorted(r["name"] for r in rows if r.get("mismatch"))
    if mismatched != len(live_mismatched):
        sys.exit(
            f"FAIL: {CENSUS.name} totals.mismatched={mismatched} but "
            f"{len(live_mismatched)} rows are flagged mismatch"
        )
    for row in rows:
        if bool(row.get("mismatch")) != (row.get("clean_priority") != row.get("lean_priority")):
            sys.exit(
                f"FAIL: {CENSUS.name} row {row.get('name')} flags "
                f"mismatch={row.get('mismatch')} but clean={row.get('clean_priority')} "
                f"lean={row.get('lean_priority')}"
            )
    live_names = sorted(r["name"] for r in rows)

    if "--update" in argv:
        ratchet.update(
            {
                "baseline_mismatched": mismatched,
                "baseline_colliding": colliding,
                "baseline_prelude_instances": prelude_instances,
                "known_colliding": live_names,
                "known_mismatched": live_mismatched,
            }
        )
        RATCHET.write_text(json.dumps(ratchet, indent=2) + "\n")
        print(
            f"UPDATED {RATCHET.name}: mismatched={mismatched} colliding={colliding} "
            f"prelude_instances={prelude_instances}"
        )
        return 0

    base_mismatched = ratchet.get("baseline_mismatched")
    base_colliding = ratchet.get("baseline_colliding")
    base_prelude = ratchet.get("baseline_prelude_instances")
    if base_mismatched is None or base_colliding is None or base_prelude is None:
        sys.exit(f"FAIL: {RATCHET.name} has no baselines")

    ok = True

    # (1) Numerator: flat-or-down.
    if mismatched > base_mismatched:
        print(
            f"FAIL: hand-registered instance priorities disagreeing with the shipped `.olean` "
            f"rose {base_mismatched} -> {mismatched}.\n"
            f"      Priority decides which candidate `synthInstance` reaches first, so a wrong\n"
            f"      value changes the shape of elaborated terms. Do NOT raise the baseline:\n"
            f"      register the priority the `.olean` serializes (NOT the number on a Lean\n"
            f"      SOURCE attribute — `@[default_instance N]` is a different table).",
            file=sys.stderr,
        )
        ok = False

    # (2) DENOMINATOR: never shrinks. Deleting rows is not a fix.
    if colliding < base_colliding:
        print(
            f"FAIL: the measured denominator SHRANK {base_colliding} -> {colliding}.\n"
            f"      Fewer hand-registered instances collide with Lean than before, so this\n"
            f"      census covers less than it did and `mismatched` is no longer comparable.\n"
            f"      If a registration was genuinely retired, lower baseline_colliding in the\n"
            f"      SAME commit and say why.",
            file=sys.stderr,
        )
        ok = False
    if prelude_instances < base_prelude:
        print(
            f"FAIL: the hand-registered instance surface SHRANK "
            f"{base_prelude} -> {prelude_instances}. See baseline_colliding above.",
            file=sys.stderr,
        )
        ok = False

    # (3) Every pinned name is still measured.
    vanished = sorted(set(ratchet.get("known_colliding", [])) - set(live_names))
    if vanished:
        print(
            f"FAIL: pinned instances are no longer measured: {vanished}.\n"
            f"      They must keep appearing in {CENSUS.name} so their priority stays checked.",
            file=sys.stderr,
        )
        ok = False

    # (4) A NEW mismatch fails even at a flat count.
    allowed = set(ratchet.get("known_mismatched", []))
    unexpected = sorted(set(live_mismatched) - allowed)
    if unexpected:
        print(
            f"FAIL: NEW mismatched hand-registrations {unexpected}.\n"
            f"      Read the priority off the shipped `.olean` and register that value.",
            file=sys.stderr,
        )
        ok = False

    if not ok:
        return 1

    if mismatched < base_mismatched:
        print(
            f"PROGRESS: mismatched {base_mismatched} -> {mismatched} of {colliding} measured. "
            f"Run with --update to lock it in."
        )
    elif mismatched == 0:
        print(
            f"PASS: every one of the {colliding} hand-registered instances that Lean also "
            f"registers carries the priority the shipped `.olean` serializes "
            f"(of {prelude_instances} hand-registered instances total)."
        )
    else:
        print(
            f"PASS: instance-priority mismatches flat — {mismatched} of {colliding} measured "
            f"(of {prelude_instances} hand-registered instances total)."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
