#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The Trust leg's runner judges each leg by its rows, its failures and where the
refutation is refused, not its exit status alone, and never takes a source from a
partial clone (scripts/patched_kernel_control_trust.py)."""

import subprocess
import tempfile
import unittest
from pathlib import Path

import patched_kernel_control_trust as runner

PINS = [
    {"site": "trust.island.source", "unmodified": "Refused", "mutant": "Refused"},
    {"site": "kernel.add_decl", "unmodified": "Refused", "mutant": "Minted"},
]
CONTROL = [{"stage": stage, "outcome": "Minted", "detail": ""} for stage in runner.CONTROL_STAGES]
LIVENESS = f"{runner.LIVENESS}, but the linked clean-kernel accepts the planted pair"
SITE_WRONG_ACCEPT = f"{runner.WRONG_ACCEPT}kernel.add_decl: resident"
ENTRY_MISS = {"lane": "int", "miss": "Refused(Kernel(TypeCheckFailed { source: TypeMismatch { .. } }))"}
E9_MISS = {"lane": "e9", "miss": "Refused(Kernel(TypeCheckFailed { source: TypeMismatch { .. } }))"}
DEFAULT_MISSES = {"unmodified": [E9_MISS], "mutant": [ENTRY_MISS], "undeclared": [ENTRY_MISS]}
DEFAULT_FAILURES = {"unmodified": [], "mutant": [], "undeclared": [LIVENESS, SITE_WRONG_ACCEPT]}


def leg(name, exit_status, kernel, outcomes, failures=None, control=None, pins=None, misses=None):
    rows = [{"site": pin["site"], "outcome": outcome, "detail": ""} for pin, outcome in zip(PINS, outcomes)]
    return {"leg": name, "exit_status": exit_status, "kernel": kernel,
            "failures": DEFAULT_FAILURES[name] if failures is None else failures,
            "reference_misses": DEFAULT_MISSES[name] if misses is None else misses,
            "pins": PINS if pins is None else pins, "control": CONTROL if control is None else control, "rows": rows}


class JudgeEachLeg(unittest.TestCase):
    def test_legs_that_end_as_their_contract_requires_pass(self):
        self.assertEqual(runner.judge(leg("unmodified", 0, "declared=Unmodified\tlive=false", ["Refused", "Refused"])), [])
        self.assertEqual(runner.judge(leg("mutant", 0, "declared=Mutant\tlive=true", ["Refused", "Minted"])), [])
        self.assertEqual(runner.judge(leg("undeclared", 101, "declared=Unmodified\tlive=true", ["Refused", "Minted"])), [])

    def test_a_zero_exit_with_a_row_off_its_pin_fails(self):
        problems = runner.judge(leg("mutant", 0, "declared=Mutant\tlive=true", ["Refused", "Refused"]))
        self.assertTrue(any("kernel.add_decl" in p for p in problems), problems)

    def test_the_wrong_exit_status_fails(self):
        self.assertTrue(runner.judge(leg("unmodified", 101, "declared=Unmodified\tlive=false", ["Refused", "Refused"])))
        self.assertTrue(runner.judge(leg("undeclared", 0, "declared=Unmodified\tlive=true", ["Refused", "Minted"])))

    def test_an_undeclared_failure_without_wrong_accept_fails(self):
        problems = runner.judge(leg("undeclared", 101, "declared=Unmodified\tlive=true", ["Refused", "Minted"], failures=[]))
        self.assertTrue(any("WRONG ACCEPT" in p for p in problems), problems)

    def test_an_undeclared_leg_needs_every_site_wrong_accept_not_only_liveness(self):
        undeclared = ("undeclared", 101, "declared=Unmodified\tlive=true", ["Refused", "Minted"])
        problems = runner.judge(leg(*undeclared, failures=[LIVENESS]))
        self.assertTrue(any("kernel.add_decl" in p for p in problems), problems)
        self.assertTrue(runner.judge(leg(*undeclared, failures=[SITE_WRONG_ACCEPT])))

    def test_an_undeclared_leg_that_also_fails_otherwise_fails(self):
        extra = [LIVENESS, SITE_WRONG_ACCEPT, "P3 UNEXPECTED REFUSAL: trust.island.source: other"]
        problems = runner.judge(leg("undeclared", 101, "declared=Unmodified\tlive=true", ["Refused", "Minted"], failures=extra))
        self.assertTrue(any("other failures" in p for p in problems), problems)

    def test_an_undeclared_leg_off_the_mutant_pins_fails(self):
        problems = runner.judge(leg("undeclared", 101, "declared=Unmodified\tlive=true", ["Refused", "Refused"]))
        self.assertTrue(any("kernel.add_decl" in p for p in problems), problems)

    def test_a_passing_leg_that_printed_a_failure_fails(self):
        problems = runner.judge(leg("mutant", 0, "declared=Mutant\tlive=true", ["Refused", "Minted"], failures=["P3 VACUOUS: x"]))
        self.assertTrue(any("failures printed" in p for p in problems), problems)

    def test_the_refutation_is_refused_by_its_reference_entry_only_on_the_mutant_binary(self):
        mutant = ("mutant", 0, "declared=Mutant\tlive=true", ["Refused", "Minted"])
        self.assertTrue(runner.judge(leg(*mutant, misses=[])))
        self.assertTrue(runner.judge(leg(*mutant, misses=[ENTRY_MISS, ENTRY_MISS])))
        self.assertTrue(runner.judge(leg(*mutant, misses=[{"lane": "int", "miss": "NoBase"}])))
        self.assertTrue(runner.judge(leg("unmodified", 0, "declared=Unmodified\tlive=false", ["Refused", "Refused"], misses=[ENTRY_MISS])))

    def test_a_kernel_line_naming_another_kernel_fails(self):
        self.assertTrue(runner.judge(leg("mutant", 0, "declared=Mutant\tlive=false", ["Refused", "Minted"])))
        self.assertTrue(runner.judge(leg("mutant", 0, None, ["Refused", "Minted"])))

    def test_missing_rows_or_pins_fail(self):
        self.assertTrue(runner.judge(leg("unmodified", 0, "declared=Unmodified\tlive=false", ["Refused"])))
        self.assertTrue(runner.judge(leg("unmodified", 0, "declared=Unmodified\tlive=false", [], pins=[])))

    def test_a_control_that_did_not_mint_fails(self):
        refused = [dict(c, outcome="Refused") if c["stage"] == "registered" else c for c in CONTROL]
        self.assertTrue(runner.judge(leg("unmodified", 0, "declared=Unmodified\tlive=false", ["Refused", "Refused"], control=refused)))
        self.assertTrue(runner.judge(leg("unmodified", 0, "declared=Unmodified\tlive=false", ["Refused", "Refused"], control=CONTROL[:2])))


class NeverAPartialClone(unittest.TestCase):
    def test_a_promisor_repository_is_not_a_source(self):
        with tempfile.TemporaryDirectory(prefix="p3-trust-leg-selftest-") as tmp:
            repo = Path(tmp)
            git = ["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@example.invalid"]
            subprocess.run(["git", "init", "-q", "--template=", str(repo)], check=True)
            (repo / "f").write_text("x\n")
            subprocess.run([*git, "add", "f"], check=True)
            subprocess.run([*git, "commit", "-q", "-m", "c"], check=True)
            sha = subprocess.run([*git, "rev-parse", "HEAD"], check=True, capture_output=True, text=True).stdout.strip()
            self.assertTrue(runner.has_commit(repo, sha))
            self.assertFalse(runner.has_commit(repo, "0" * 40))
            subprocess.run([*git, "config", "remote.origin.promisor", "true"], check=True)
            self.assertFalse(runner.has_commit(repo, sha))

    def test_a_named_source_is_used_last_recorded_and_held_to_the_same_rules(self):
        with tempfile.TemporaryDirectory(prefix="p3-trust-leg-selftest-") as tmp:
            root = Path(tmp)
            trust, repo = root / "trust", root / "named" / "zz-p3-selftest"
            trust.mkdir()
            git = ["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@example.invalid"]
            subprocess.run(["git", "init", "-q", "--template=", str(repo)], check=True)
            (repo / "f").write_text("x\n")
            subprocess.run([*git, "add", "f"], check=True)
            subprocess.run([*git, "commit", "-q", "-m", "c"], check=True)
            sha = subprocess.run([*git, "rev-parse", "HEAD"], check=True, capture_output=True, text=True).stdout.strip()
            path = "first-party/zz-p3-selftest"
            with self.assertRaises(SystemExit):
                runner.source_for(path, sha, trust)
            named = runner.named_sources([f"{path}={repo}"])
            self.assertEqual(runner.source_for(path, sha, trust, named), (repo.resolve(), True))
            subprocess.run([*git, "config", "remote.origin.promisor", "true"], check=True)
            with self.assertRaises(SystemExit):
                runner.source_for(path, sha, trust, named)
            subprocess.run([*git, "config", "--unset", "remote.origin.promisor"], check=True)
            beside = root / "named" / "trust"
            beside.mkdir()
            self.assertEqual(runner.source_for(path, sha, beside), (repo.resolve(), False))
            self.assertEqual(runner.source_for(path, sha, beside, named), (repo.resolve(), True))
            for bad in ["zz=" + str(repo), path, path + "="]:
                with self.assertRaises(SystemExit):
                    runner.named_sources([bad])


if __name__ == "__main__":
    unittest.main()
