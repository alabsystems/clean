#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Self-test for scripts/check_constructive_ratchet.py -- can it say NO?

WHY THIS EXISTS
---------------
`check_constructive_ratchet.py` guards a property nothing else in this repo
guards: the SET OF NAMES of clean-native theorems whose transitive axiom closure
is empty of domain axioms (`ProofQuality::Constructive`). It is not the axiom
census -- `scripts/tcb_target_ratchet.py` pins that, and a constructive theorem
silently DISAPPEARING does not move it by one. It is not
`data/axiom_audit.json`'s `constructive_theorems`, which sums `theorems` over
conjecture rows flagged `constructive: true` (an NN-conjecture population,
measured 265 while this ratchet holds 318 -- different objects, not drift).

Until 2026-08-25 the gate was an ORPHAN: no runner invoked it, and the only
other reader of `data/constructive_ratchet.json` was a pair of unwired audit
scripts that have since been retired. It is now `gate::constructive` in
`scripts/verify_runner.py`. A wired gate still has to be FALSIFIABLE, and the
gate itself cannot self-test: `do_check` shells out to a release
`mathverse_shard build-native`, which is minutes of cargo. So the seam is here,
in the suite `scripts/check_script_selftests.sh` already runs -- the shard build
is monkeypatched, NOT stubbed behind an environment variable, so the gate gains
no bypass surface from being testable.

Seven arms on `do_check`, in `ConstructiveRatchetGateTest`. Arm 6 is the
uncomfortable one and it is deliberate: it pins the gate's staged-file escape
hatch as OBSERVED BEHAVIOUR rather than leaving it as an unread branch.
`git add data/constructive_ratchet.json` makes the gate accept arbitrary drift.
That is fine for `gate::constructive` -- the pinned runner measures a detached
worktree where nothing is ever staged -- and it is exactly why this gate must
not be re-spelled as a pre-push leg without removing the hatch first.

`ConstructiveRatchetUpdateTest` is a SEPARATE class on purpose. The ten arms
above are the falsifiability claim for `do_check`, and that claim is checked by
mutation: gutting `do_check` to `return 0` must turn all TEN of them red.
(Arms 8-10 are lane LOOSE, 2026-08-25: the `Classical.choice` exception set is
part of the baseline, so the gap between this metric's NAME and its PREDICATE
is measured on every run instead of footnoted in a file nothing re-derives.)
Mixing `do_update` arms into the same class would break that count, so the
refresh path is pinned next door instead. What it pins is the 2026-08-25
finding that re-baselining was SILENT: `do_update` carried the previous `notes`
string over verbatim, so the committed file read "Current 84" above a count of
318 -- prose three re-baselines stale, describing a set nobody had reviewed.
"""
from __future__ import annotations

import importlib.util
import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
GATE = REPO_ROOT / "scripts" / "check_constructive_ratchet.py"


def _load_gate():
    spec = importlib.util.spec_from_file_location("_ccr_under_test", GATE)
    if spec is None or spec.loader is None:  # pragma: no cover - env failure
        raise RuntimeError(f"cannot load {GATE}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


BASE = ["Alpha.thm", "Beta.thm", "Gamma.thm"]


class ConstructiveRatchetGateTest(unittest.TestCase):
    """Every arm drives the REAL do_check(); only the shard build is replaced."""

    def setUp(self) -> None:
        self.mod = _load_gate()
        self._tmp = tempfile.TemporaryDirectory(prefix="ccr-selftest-")
        self.tmp = Path(self._tmp.name)
        self.ratchet = self.tmp / "constructive_ratchet.json"
        self.mod.RATCHET_PATH = self.ratchet
        # Nothing is staged in a temp dir, so the escape hatch is CLOSED by
        # default and every arm below measures the gate's real verdict.
        self.mod.ratchet_staged_this_commit = lambda: False

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write_ratchet(self, names: list[str],
                      choice: list[str] | None = None) -> None:
        doc = {"last_updated": "2026-01-01", "count": len(names),
               "classical_choice_dependents": sorted(choice or []),
               "names": names, "notes": "self-test"}
        self.ratchet.write_text(json.dumps(doc, indent=2) + "\n")

    def write_ratchet_without_exception_set(self, names: list[str]) -> None:
        self.ratchet.write_text(
            json.dumps({"last_updated": "2026-01-01", "count": len(names),
                        "names": names, "notes": "self-test"}, indent=2) + "\n"
        )

    def shard(self, names: list[str], choice: list[str] | None = None) -> None:
        self.mod.build_native_shard = lambda: (sorted(names), sorted(choice or []))

    def run_check(self) -> tuple[int, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            rc = self.mod.do_check()
        return rc, out.getvalue() + err.getvalue()

    # 1 ─ the unmutated tree is green, or every arm below proves nothing.
    def test_matching_set_passes(self) -> None:
        self.write_ratchet(BASE)
        self.shard(BASE)
        rc, text = self.run_check()
        self.assertEqual(rc, 0, text)
        self.assertIn("3 foundational-axiom-only theorems match ratchet", text)

    # 2 ─ a theorem APPEARS without the ratchet being updated.
    def test_added_theorem_fails(self) -> None:
        self.write_ratchet(BASE)
        self.shard(BASE + ["Delta.thm"])
        rc, text = self.run_check()
        self.assertEqual(rc, 1, text)
        self.assertIn("RATCHET FAIL", text)
        self.assertIn("Delta.thm", text)

    # 3 ─ the one an axiom-count gate cannot see: a constructive theorem
    #     VANISHES. tcb_target_ratchet does not move; this must.
    def test_removed_theorem_fails(self) -> None:
        self.write_ratchet(BASE)
        self.shard(["Alpha.thm", "Gamma.thm"])
        rc, text = self.run_check()
        self.assertEqual(rc, 1, text)
        self.assertIn("Beta.thm", text)

    # 4 ─ a SWAP: the count is identical, the set is not. A `count >= floor`
    #     ratchet -- which is what the retired prover audits read -- is
    #     byte-identical here. This gate is not.
    def test_swap_at_equal_count_fails(self) -> None:
        self.write_ratchet(BASE)
        self.shard(["Alpha.thm", "Beta.thm", "Omega.thm"])
        rc, text = self.run_check()
        self.assertEqual(rc, 1, text)
        self.assertIn("swap detected", text)

    # 5 ─ a swap is refused EVEN WITH the ratchet staged. The escape hatch must
    #     not launder a same-count substitution.
    def test_swap_refused_even_when_staged(self) -> None:
        self.write_ratchet(BASE)
        self.shard(["Alpha.thm", "Beta.thm", "Omega.thm"])
        self.mod.ratchet_staged_this_commit = lambda: True
        rc, text = self.run_check()
        self.assertEqual(rc, 1, text)
        self.assertIn("swap detected", text)

    # 6 ─ THE HOLE, PINNED. Staging the ratchet accepts arbitrary drift. This
    #     asserts the behaviour so that changing it is a deliberate act with a
    #     red test, not a silent one.
    def test_staged_ratchet_accepts_drift_documented_hole(self) -> None:
        self.write_ratchet(BASE)
        self.shard(BASE + ["Delta.thm", "Epsilon.thm"])
        self.mod.ratchet_staged_this_commit = lambda: True
        rc, text = self.run_check()
        self.assertEqual(rc, 0, text)
        self.assertIn("RATCHET UPDATE", text)

    # 7 ─ a missing artifact is an ERROR (exit 2), never an empty baseline that
    #     silently matches an empty shard.
    def test_missing_ratchet_file_exits_2(self) -> None:
        self.shard(BASE)
        err = io.StringIO()
        with redirect_stderr(err), self.assertRaises(SystemExit) as cm:
            self.mod.do_check()
        self.assertEqual(cm.exception.code, 2)
        self.assertIn("Ratchet file missing", err.getvalue())


    # 8 ─ THE NAMING CAVEAT, MADE FALSIFIABLE (lane LOOSE, 2026-08-25). A
    #     theorem newly reaching `Classical.choice` is RED even though the
    #     accepted NAME SET is unchanged. `ProofQuality::Constructive` means
    #     "no DOMAIN axiom", and `Classical.choice` is foundational here, so
    #     excluded middle is counted "constructive" -- 2 of 396 at HEAD. Lane
    #     CONSTR wrote that down in a static review file; a static file cannot
    #     notice it becoming 40.
    def test_growing_classical_choice_set_fails(self) -> None:
        self.write_ratchet(BASE, choice=["Alpha.thm"])
        self.shard(BASE, choice=["Alpha.thm", "Beta.thm"])
        rc, text = self.run_check()
        self.assertEqual(rc, 1, text)
        self.assertIn("CLASSICAL-CHOICE exception set moved", text)
        self.assertIn("Beta.thm", text)

    # 9 ─ and it is refused EVEN WITH the ratchet staged. Arm 6 pins that
    #     staging launders name drift; it must not launder this. Staging is a
    #     bookkeeping act; moving the exception set is a claim about what the
    #     word means, and it needs --update --notes.
    def test_classical_choice_drift_refused_even_when_staged(self) -> None:
        self.write_ratchet(BASE, choice=[])
        self.shard(BASE, choice=["Alpha.thm"])
        self.mod.ratchet_staged_this_commit = lambda: True
        rc, text = self.run_check()
        self.assertEqual(rc, 1, text)
        self.assertIn("CLASSICAL-CHOICE exception set moved", text)

    # 10 ─ an ABSENT exception set is not an empty one. A baseline written
    #      before this field existed must fail loudly rather than read as
    #      "nothing reaches Classical.choice".
    def test_missing_classical_choice_field_fails(self) -> None:
        self.write_ratchet_without_exception_set(BASE)
        self.shard(BASE, choice=[])
        rc, text = self.run_check()
        self.assertEqual(rc, 1, text)
        self.assertIn("classical_choice_dependents", text)


class ConstructiveRatchetUpdateTest(unittest.TestCase):
    """The REFRESH path: it must not be possible to re-baseline silently."""

    def setUp(self) -> None:
        self.mod = _load_gate()
        self._tmp = tempfile.TemporaryDirectory(prefix="ccr-update-")
        self.tmp = Path(self._tmp.name)
        self.ratchet = self.tmp / "constructive_ratchet.json"
        self.mod.RATCHET_PATH = self.ratchet
        self.ratchet.write_text(
            json.dumps({"last_updated": "2026-01-01", "count": len(BASE),
                        "classical_choice_dependents": [],
                        "names": BASE, "notes": "STALE PROSE, WRONG COUNT"},
                       indent=2) + "\n"
        )
        self.mod.build_native_shard = lambda: (
            sorted(BASE + ["Delta.thm"]), ["Delta.thm"]
        )

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def run_update(self, notes: str) -> tuple[int, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            rc = self.mod.do_update(notes)
        return rc, out.getvalue() + err.getvalue()

    # 1 - no review, no refresh. The baseline must be untouched on refusal.
    def test_update_without_notes_is_refused(self) -> None:
        rc, text = self.run_update("")
        self.assertEqual(rc, 2, text)
        self.assertIn("REFUSED", text)
        self.assertEqual(
            json.loads(self.ratchet.read_text())["notes"],
            "STALE PROSE, WRONG COUNT",
            "a refused update must not rewrite the file",
        )

    # 2 - whitespace is not a review.
    def test_update_with_blank_notes_is_refused(self) -> None:
        rc, text = self.run_update("   \n\t ")
        self.assertEqual(rc, 2, text)
        self.assertIn("REFUSED", text)

    # 3 - the accepted path records the review AND the measured transition.
    def test_update_with_notes_stamps_the_measured_transition(self) -> None:
        rc, text = self.run_update("Delta.thm is Nat.foo promoted from Axiom.")
        self.assertEqual(rc, 0, text)
        written = json.loads(self.ratchet.read_text())
        self.assertEqual(written["count"], 4)
        self.assertEqual(written["names"], sorted(BASE + ["Delta.thm"]))
        self.assertIn("3 -> 4", written["notes"])
        self.assertIn("(+1 / -0)", written["notes"])
        self.assertIn("Delta.thm is Nat.foo promoted from Axiom.",
                      written["notes"])
        # The refresh path must PERSIST the measured exception set, and stamp
        # it into the generated transition line: a refresh is the only way to
        # move it, so it is the one place it must be written down.
        self.assertEqual(written["classical_choice_dependents"], ["Delta.thm"])
        self.assertIn("1 of 4 reach Classical.choice", written["notes"])
        self.assertIn("FOUNDATIONAL-AXIOM-ONLY", written["metric"])

    # 4 - THE REGRESSION THAT MOTIVATED THIS: stale prose must not survive a
    #     refresh. The old do_update carried `notes` over verbatim.
    def test_update_does_not_carry_stale_notes_over(self) -> None:
        self.run_update("reviewed: one promotion")
        self.assertNotIn("STALE PROSE, WRONG COUNT",
                         json.loads(self.ratchet.read_text())["notes"])


if __name__ == "__main__":
    if not GATE.exists():
        print(f"CONSTRUCTIVE_RATCHET_SELFTEST=fail reason=gate-missing ({GATE})",
              file=sys.stderr)
        raise SystemExit(1)
    unittest.main(verbosity=2)
