# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Self-test for the tactic family gates' three-way verdict.

WHY THIS EXISTS
---------------
On 2026-08-28 G-SIMP reported:

    G-SIMP=failed pass=78/127 baseline=REGRESSED
      FAIL: local_simp_attrs.lean: timed out after 1800s
      FAIL: baseline regression - rows recorded passing now fail:
            [... 'p_simp_local_01', ... 'p_simp_local_09']

Seven of those eight "regressions" were rows the run never reached: ONE
declaration in the file diverges, the file hit PER_FILE_TIMEOUT_SECS, and
fourteen measurements died with it. The fix is to hand `clean check` a
per-declaration budget so a runaway is reported `diverged` and the rest of the
file is still measured -- which only works if the gate treats `diverged` as its
own verdict rather than quietly rounding it to `pass` or to `fail`.

That rounding is exactly the kind of thing a gate cannot self-report, so the
partition arithmetic lives in `classify_file_verdicts` and is exercised here
against canned `clean check --json` reports. No binary, no `import Init`, no
network: this suite runs in milliseconds and is picked up automatically by
scripts/check_script_selftests.sh.
"""

import unittest

from scripts.tactic_parity import family_gate

FIXTURE_TEXT = """import Init

theorem canary_env (n : Nat) : n = n := rfl
theorem p_ok (n : Nat) : n + 0 = n := by simp
theorem p_bad (n : Nat) : n = n + 1 := by simp
theorem p_slow (n : Nat) : n + 1 + 1 = n + 2 := by simp
"""

NAMES = ["canary_env", "p_ok", "p_bad", "p_slow"]

DIVERGED_ROW = (
    "p_slow: did not finish at line 6 - spent the whole per-declaration budget "
    "of 50000000 kernel operations (raise it with --decl-budget <n>, or 0 for "
    "unlimited)"
)


def report(**over):
    """A `clean check --json` report with one pass, one fail, one diverged."""
    base = {
        "status": "fail",
        "decl_count": 4,
        "success_count": 2,
        "failed_count": 1,
        "diverged_count": 1,
        "errors": ["p_bad: simp made no progress at line 5"],
        "trust_failures": [],
        "kernel_failures": [],
        "diverged": [DIVERGED_ROW],
        "proof_state_feedback": [],
    }
    base.update(over)
    return base


class ThreeWayVerdictTests(unittest.TestCase):
    def test_diverged_is_neither_pass_nor_fail(self) -> None:
        verdicts, problems = classify(report())
        self.assertEqual(problems, [])
        self.assertEqual(verdicts["canary_env"], "pass")
        self.assertEqual(verdicts["p_ok"], "pass")
        self.assertEqual(verdicts["p_bad"], "fail")
        self.assertEqual(verdicts["p_slow"], "diverged")

    def test_folding_diverged_into_pass_is_caught_by_the_success_count(self) -> None:
        """The mutation this suite exists to catch.

        A gate that ignored the `diverged` list would count `p_slow` among the
        rows with "no attributed failure" and report three passes against the
        binary's `success_count=2`. The arithmetic must refuse that, because it
        is the only thing standing between a runaway declaration and a green
        row it never earned.
        """
        blind = report()
        blind["diverged"] = []  # a reader that drops the list entirely
        verdicts, problems = classify(blind)
        self.assertEqual(verdicts, {})
        self.assertEqual(len(problems), 1)
        self.assertIn("verdict attribution mismatch", problems[0])
        self.assertIn("success_count=2", problems[0])

    def test_a_declaration_cannot_be_both_failed_and_diverged(self) -> None:
        contradictory = report()
        contradictory["errors"] = ["p_slow: something at line 6"]
        contradictory["success_count"] = 3
        verdicts, problems = classify(contradictory)
        self.assertEqual(verdicts, {})
        self.assertEqual(len(problems), 1)
        self.assertIn("BOTH failed and diverged", problems[0])

    def test_an_unattributable_diverged_row_is_not_silently_dropped(self) -> None:
        stray = report()
        stray["diverged"] = ["some_other_decl: did not finish at line 99 - ..."]
        verdicts, problems = classify(stray)
        self.assertEqual(verdicts, {})
        self.assertIn("verdict attribution mismatch", problems[0])

    def test_a_clean_report_with_no_divergence_still_classifies(self) -> None:
        clean = report(
            status="pass",
            success_count=4,
            failed_count=0,
            diverged_count=0,
            errors=[],
            diverged=[],
        )
        verdicts, problems = classify(clean)
        self.assertEqual(problems, [])
        self.assertEqual(set(verdicts.values()), {"pass"})


class AttributeDivergedTests(unittest.TestCase):
    def test_the_name_is_read_off_the_row_prefix(self) -> None:
        names, unattributed = family_gate.attribute_diverged(
            {"diverged": [DIVERGED_ROW]}, NAMES
        )
        self.assertEqual(names, {"p_slow"})
        self.assertEqual(unattributed, [])

    def test_an_unknown_name_is_reported_not_absorbed(self) -> None:
        names, unattributed = family_gate.attribute_diverged(
            {"diverged": ["ghost: did not finish at line 1 - ..."]}, NAMES
        )
        self.assertEqual(names, set())
        self.assertEqual(len(unattributed), 1)

    def test_a_report_without_the_key_is_empty_not_an_error(self) -> None:
        names, unattributed = family_gate.attribute_diverged({}, NAMES)
        self.assertEqual(names, set())
        self.assertEqual(unattributed, [])


class DeclBudgetWiringTests(unittest.TestCase):
    def test_the_budget_leaves_room_above_the_dearest_finishing_declaration(self) -> None:
        """The budget must not be able to turn a passing row into `diverged`.

        1.3e6 is the dearest per-declaration cost measured over these fixtures
        on 2026-08-28 (`CLEAN_CHECK_DECL_BUDGET_TRACE=1`, target/release/clean
        at 9f035774c) -- and it is the module-level import work, not a probe;
        the dearest actual probe was 5.7e5. A budget within an order of
        magnitude of that would start deciding verdicts.
        """
        self.assertGreaterEqual(family_gate.DECL_BUDGET, 10 * 1_300_000)

    def test_the_budget_is_actually_passed_to_the_binary(self) -> None:
        """A constant nothing reads is a comment. Pin the flag spelling."""
        source = (
            family_gate.REPO_ROOT / "scripts" / "tactic_parity" / "family_gate.py"
        ).read_text(encoding="utf-8")
        self.assertIn('f"--decl-budget={DECL_BUDGET}"', source)


def classify(rep):
    return family_gate.classify_file_verdicts(rep, NAMES, FIXTURE_TEXT, "probe.lean")


if __name__ == "__main__":
    unittest.main()
