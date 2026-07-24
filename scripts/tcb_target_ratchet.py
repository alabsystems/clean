#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Path-to-3 ratchet: drive the kernel TCB toward the 3 Lean-4-core axioms only.

GOAL (set 2026-06-17): the soundness-certificate trusted base should contain
exactly the three Lean 4 foundational axioms — `propext`, `Quot.sound`,
`Classical.choice` — and NO domain axioms. Every domain axiom retired by the
elimination campaign should be permanently locked in: the count can go DOWN
(toward 0 domain / 3 total) but never back up.

This ratchet reads the live cert golden (data/soundness_tcb.json — itself pinned
to the live cert by `golden_matches_live_axioms`) and:
  - PINS the denominator: the 3 foundational axioms must remain EXACTLY those 3
    (a 4th "foundational" axiom would silently move the goalposts).
  - ENFORCES monotonic decrease: the domain-axiom count must be <= the recorded
    baseline. A new domain axiom (even via a deliberate golden regen) fails the
    gate until the increase is justified + the baseline deliberately raised.
  - SURFACES distance-to-goal: prints the remaining domain axioms to eliminate.

  scripts/tcb_target_ratchet.py            # FAIL on regression / foundational drift
  scripts/tcb_target_ratchet.py --update   # lock in a ratchet-down (after a retirement)

Wired into scripts/local_gate.sh. Pure-stdlib; reads only checked-in JSON.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
GOLDEN = REPO_ROOT / "data" / "soundness_tcb.json"
RATCHET = REPO_ROOT / "data" / "tcb_target_ratchet.json"
LEAN4_CORE_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def load(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {path}: {exc}")


def live_partition(golden: dict) -> tuple[list[str], list[str]]:
    axioms = list(golden.get("axioms", []))
    foundational = sorted(a for a in axioms if a in LEAN4_CORE_AXIOMS)
    domain = sorted(a for a in axioms if a not in LEAN4_CORE_AXIOMS)
    return foundational, domain


def main(argv: list[str]) -> int:
    golden = load(GOLDEN)
    foundational, domain = live_partition(golden)

    if "--update" in argv:
        ratchet = load(RATCHET) if RATCHET.exists() else {}
        ratchet.update(
            {
                "goal": "Kernel TCB = the 3 Lean-4-core axioms only (propext, Quot.sound, "
                "Classical.choice); eliminate ALL domain axioms.",
                "target_total_axioms": 3,
                "target_domain_axioms": 0,
                "foundational_axioms": sorted(LEAN4_CORE_AXIOMS),
                "baseline_total_axioms": int(golden.get("axiom_count", len(foundational) + len(domain))),
                "baseline_domain_axioms": len(domain),
                "remaining_domain_axioms": domain,
                "source": "data/soundness_tcb.json (cert C2 golden, pinned to the live cert)",
                "generated_by": "scripts/tcb_target_ratchet.py --update",
            }
        )
        RATCHET.write_text(json.dumps(ratchet, indent=2) + "\n")
        print(f"path-to-3 ratchet: baseline locked at {len(domain)} domain axioms ({RATCHET.name}).")
        return 0

    ratchet = load(RATCHET)
    baseline = int(ratchet["baseline_domain_axioms"])
    ok = True

    # (1) Pin the denominator: exactly the 3 Lean-4-core axioms, no more no less.
    fc = int(golden.get("foundational_count", -1))
    if set(foundational) != LEAN4_CORE_AXIOMS or fc != 3:
        ok = False
        print(
            f"FAIL: foundational axioms drifted from the 3 Lean-4 core "
            f"({sorted(LEAN4_CORE_AXIOMS)}); live foundational={foundational}, "
            f"foundational_count={fc}. The 3-axiom goal's denominator must stay fixed.",
            file=sys.stderr,
        )

    # (2) Monotonic decrease toward 0 domain axioms.
    n = len(domain)
    if n > baseline:
        ok = False
        added = sorted(set(domain) - set(ratchet.get("remaining_domain_axioms", [])))
        print(
            f"FAIL: domain axioms grew {baseline} -> {n} (target 0). New/unexpected: {added}. "
            f"A new domain axiom moves AWAY from the 3-axiom goal — justify it and, only if "
            f"genuinely required, raise the baseline with scripts/tcb_target_ratchet.py --update.",
            file=sys.stderr,
        )

    target = ", ".join(sorted(LEAN4_CORE_AXIOMS))
    print(f"GOAL: kernel TCB = the 3 Lean-4-core axioms only ({target}).")
    print(f"  current: {golden.get('axiom_count')} total = 3 foundational + {n} domain "
          f"(baseline {baseline}); distance to goal: {n} domain axiom(s) to eliminate.")
    if n:
        for a in domain:
            print(f"    - {a}")
    if ok and n < baseline:
        print(f"  PROGRESS: domain {baseline} -> {n}; run scripts/tcb_target_ratchet.py --update to lock it in.")
    elif ok and n == 0:
        print("  *** GOAL REACHED: TCB is the 3 Lean-4-core axioms. ***")

    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
