#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Prelude/`.olean` collision ratchet: shrink the shadowed-declaration surface.

Clean seeds a hand-rolled prelude and then imports a real Lean environment on
top of it. `.olean` import is FIRST-REGISTERED-WINS (`crates/clean-olean/src/
import/load.rs:43`, enforced at `import/load_register.rs:1309-1331`), so every
name the prelude already owns causes Lean's declaration to be DISCARDED. Where
the two types disagree, the environment silently keeps Clean's spelling while
the user writes Lean's — the measured example being `List.append_nil`, stated by
the prelude over the bare `List.append` and by Lean in `++` notation, which is
why `rw [List.append_nil]` on `l ++ []` matched nothing.

This gate reads the checked-in census (data/prelude_collision_census.json,
produced by `cargo test --offline --release -p clean-olean --test
prelude_collision_census` with CLEAN_PRELUDE_CENSUS_UPDATE=1) and:
  - ENFORCES monotonic decrease of `type_differing` and `bare_spelled`;
  - PINS the known bare-spelled names so the class cannot stop being measured;
  - CHECKS the census is internally consistent (totals match the listed rows).

  scripts/check_prelude_collision_ratchet.py            # FAIL on regression
  scripts/check_prelude_collision_ratchet.py --update   # lock in a ratchet-down

Wired into scripts/local_gate.sh. Pure-stdlib; reads only checked-in JSON — it
needs no Lean toolchain, which is why the measurement and the gate are split.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CENSUS = REPO_ROOT / "data" / "prelude_collision_census.json"
RATCHET = REPO_ROOT / "data" / "prelude_collision_ratchet.json"


def load(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {path}: {exc}")


def main(argv: list[str]) -> int:
    census = load(CENSUS)
    ratchet = load(RATCHET)
    totals = census.get("totals", {})
    rows = census.get("collisions", [])

    type_differing = totals.get("type_differing")
    bare_spelled = totals.get("bare_spelled")
    if type_differing is None or bare_spelled is None:
        sys.exit(f"FAIL: {CENSUS.name} has no totals.type_differing/bare_spelled")

    # Self-consistency: the totals must describe the rows actually listed.
    if type_differing != len(rows):
        sys.exit(
            f"FAIL: {CENSUS.name} totals.type_differing={type_differing} but "
            f"{len(rows)} rows are listed"
        )
    live_bare = sorted(r["name"] for r in rows if r.get("bare_spelled"))
    if bare_spelled != len(live_bare):
        sys.exit(
            f"FAIL: {CENSUS.name} totals.bare_spelled={bare_spelled} but "
            f"{len(live_bare)} rows are flagged bare_spelled"
        )

    # Per-family breakdown (bare_spelled_by_family): validate when present —
    # it must be exactly the derivation of the listed rows (family = head
    # namespace, entries = name + discarded Lean kind). Absent only in
    # pre-breakdown artifacts, which the census test regenerates away.
    breakdown = census.get("bare_spelled_by_family")
    if breakdown is not None:
        bd_names: list[str] = []
        for family, fam in breakdown.items():
            entries = fam.get("entries", [])
            if fam.get("count") != len(entries):
                sys.exit(
                    f"FAIL: {CENSUS.name} family {family!r}: count={fam.get('count')} "
                    f"but {len(entries)} entries listed"
                )
            for entry in entries:
                entry_name = entry.get("name", "")
                if entry_name.split(".", 1)[0] != family:
                    sys.exit(
                        f"FAIL: {CENSUS.name} family {family!r}: entry "
                        f"{entry_name!r} is not in that head namespace"
                    )
                bd_names.append(entry_name)
        if sorted(bd_names) != live_bare:
            sys.exit(
                f"FAIL: {CENSUS.name} bare_spelled_by_family names do not match "
                f"the bare_spelled rows (breakdown {len(bd_names)}, rows "
                f"{len(live_bare)}). Regenerate the census; never hand-edit it."
            )

    if "--update" in argv:
        ratchet.update(
            {
                "baseline_type_differing": type_differing,
                "baseline_bare_spelled": bare_spelled,
                "known_bare_spelled": live_bare,
            }
        )
        RATCHET.write_text(json.dumps(ratchet, indent=2) + "\n")
        print(
            f"UPDATED {RATCHET.name}: type_differing={type_differing} "
            f"bare_spelled={bare_spelled}"
        )
        return 0

    base_td = ratchet.get("baseline_type_differing")
    base_bs = ratchet.get("baseline_bare_spelled")
    if base_td is None or base_bs is None:
        sys.exit(f"FAIL: {RATCHET.name} has no baselines")

    ok = True
    if type_differing > base_td:
        print(
            f"FAIL: prelude/.olean type-differing collisions rose "
            f"{base_td} -> {type_differing}.\n"
            f"      Each one DISCARDS Lean's declaration and keeps Clean's. Do NOT raise\n"
            f"      the baseline to mask this: make the prelude statement agree with Lean's,\n"
            f"      or stop seeding the stub (Environment::try_with_prelude_for_import).",
            file=sys.stderr,
        )
        ok = False
    if bare_spelled > base_bs:
        print(
            f"FAIL: bare-spelled shadowed statements rose {base_bs} -> {bare_spelled}.\n"
            f"      These are stated by Lean through a class projection and by Clean over\n"
            f"      the bare function, so `rw`/`simp` see a statement the user never wrote.",
            file=sys.stderr,
        )
        ok = False

    known = set(ratchet.get("known_bare_spelled", []))
    vanished = sorted(known - set(live_bare))
    if vanished:
        print(
            f"FAIL: known bare-spelled names are no longer measured: {vanished}.\n"
            f"      If they were genuinely fixed, drop them from {RATCHET.name} in the SAME\n"
            f"      commit and lower the baselines (--update).",
            file=sys.stderr,
        )
        ok = False

    if not ok:
        return 1

    if type_differing < base_td or bare_spelled < base_bs:
        print(
            f"PROGRESS: type_differing {base_td} -> {type_differing}, "
            f"bare_spelled {base_bs} -> {bare_spelled}. "
            f"Run with --update to lock it in."
        )
    else:
        print(
            f"PASS: prelude/.olean collisions flat — type_differing={type_differing}, "
            f"bare_spelled={bare_spelled} (of {totals.get('colliding_names', '?')} "
            f"colliding names)."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
