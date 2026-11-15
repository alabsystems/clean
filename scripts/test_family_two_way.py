# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Self-test for the tactic families' two-way half (lean_verdicts.py: the
sealed sidecar; family_two_way.py: the cross).

Every refusal `verdict_problems` owns is shown failing next to a green
control; the classify precedence is pinned on message lines copied from a
pinned-Lean run (v4.30.0-rc2, 2026-10-27); the ratchet, `--strict`,
`--check-artifact` and an end-to-end `run_family` (with `clean` stubbed) are
exercised on a synthetic family in a temp directory. No binary, no Lean.
Three arms in data/gate_demonstrations.json neuter family_two_way.py or
lean_verdicts.py and require a named test here to go red, so this file is one
of family_gate's pinned inputs (R7). The `main`-level and review-round tests
are in scripts/test_family_gate_two_way.py.
"""

import ast
import contextlib
import copy
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.tactic_parity import family_gate

ftw, lv = family_gate.ftw, family_gate.lv  # the one loaded copy of each
ROOT = Path(__file__).resolve().parent.parent
FIXTURE = b"""import Init

theorem canary_t (n : Nat) : n = n := rfl
def h_t (n : Nat) : Nat := n + 1
theorem p_ok (n : Nat) : n + 0 = n := rfl
theorem p_unk (n : Nat) : n + 0 = n := by norm_num
theorem p_rej (a b : Nat) (h : a = b) : b = a := by grind
theorem neg_t (n : Nat) (h : n = 2) : n = 2 := by simp only []
theorem ctl_t (n : Nat) (h : n = 2) : n = 2 := h
"""
ENTRY = {"file": "t.lean", "label": "t", "canary": "canary_t", "helpers": ["h_t"], "required": [],
         "probes": ["p_ok", "p_unk", "p_rej"],
         "negatives": [{"name": "neg_t", "control": "ctl_t", "lean_class": "elab-error",
                        "lean_contains": "made no progress", "source": "test"}],
         "controls": [{"name": "ctl_t", "source": "test"}]}
MANIFEST = {"family": "g_auto", "plan": "test", "plan_family_total": 3, "comparison_basis": "test",
            "files": [ENTRY]}
# Lines copied from the pinned Lean's `--json` output (verify/v.lean).
UNKNOWN = {"severity": "error", "line_rel": 1, "col": 47, "data": "unknown tactic"}
UNSOLVED = {"severity": "error", "line_rel": 1, "col": 43, "data": "unsolved goals\na : Nat\n⊢ a + 0 = a"}
DISTRIB = {"severity": "error", "line_rel": 1, "col": 69,
           "data": "Structure `Lean.Grind.Config` does not have a field named `distrib`"}
SORRY_W = {"severity": "warning", "line_rel": 1, "col": 8, "data": "declaration uses `sorry`"}
NO_PROGRESS = {"severity": "error", "line_rel": 1, "col": 58, "data": "`simp` made no progress"}


def row(verdict, cls, axioms, messages=(), tactics=()):
    return {"verdict": verdict, "class": cls, "axioms": axioms, "messages": list(messages),
            "unknown_tactics": list(tactics), "split_verdict": verdict}


def make_doc(fixture=FIXTURE):
    world, toolchain, _ = lv.oracle_world(ROOT)
    rows = {"canary_t": row("accept", None, ["propext"]), "h_t": row("accept", None, []),
            "p_ok": row("accept", None, []),
            "p_unk": row("reject", "unknown-tactic", ["sorryAx"], [UNKNOWN, UNSOLVED], ["norm_num"]),
            "p_rej": row("reject", "elab-error", ["sorryAx"], [{**UNSOLVED, "data": "`grind` failed"}]),
            "neg_t": row("reject", "elab-error", ["sorryAx"], [NO_PROGRESS]),
            "ctl_t": row("accept", None, [])}
    doc = {"schema_version": lv.SCHEMA, "family": "g_auto", "generated_by": "test",
           "minted_at_utc": "2026-10-27T00:00:00+00:00",
           "lean_world": {"id": world, "toolchain": toolchain, "githash": lv.ORACLE_GITHASHES[world],
                          "version_line": "Lean (version 4.30.0-rc2)"},
           "rule": lv.RULE, "method": lv.METHOD,
           "files": {"t.lean": {"fixture_sha256": lv.sha256_bytes(fixture), "lean_exit": 1, "rows": rows}}}
    doc["seal"] = lv.seal(doc)
    return doc


def resealed(doc):
    doc["seal"] = lv.seal(doc)
    return doc


class Family(unittest.TestCase):
    """A synthetic family `g_auto` in a temp FIXTURE_ROOT."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="ftw-test-"))
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))
        self.fam = self.tmp / "fixtures" / "g_auto"
        self.fam.mkdir(parents=True)
        (self.fam / "t.lean").write_bytes(FIXTURE)
        (self.fam / "MANIFEST.json").write_text(json.dumps(MANIFEST))
        self.write(make_doc())

    def write(self, doc):
        (self.fam / lv.VERDICTS_FILE).write_text(json.dumps(doc, ensure_ascii=False))

    def problems(self, manifest=MANIFEST):
        return lv.verdict_problems("g_auto", manifest, self.fam, ROOT)


class ClassifyTests(unittest.TestCase):
    def test_classify_unknown_tactic_wins_over_the_earlier_unsolved_goals(self):
        for msgs in ([UNKNOWN, UNSOLVED], [UNSOLVED, UNKNOWN]):
            self.assertEqual(lv.classify(msgs, ["sorryAx"]), ("reject", "unknown-tactic"))

    def test_classify_an_error_with_sorry_free_axioms_rejects(self):
        self.assertEqual(lv.classify([DISTRIB], ["propext", "Classical.choice", "Quot.sound"]),
                         ("reject", "elab-error"))

    def test_classify_sorry_axiom_alone_rejects(self):
        """A theorem that USES a failed one: no message at all, sorryAx in its axioms."""
        self.assertEqual(lv.classify([], ["sorryAx"]), ("reject", "depends-on-sorry"))

    def test_classify_the_remaining_classes(self):
        cases = [([SORRY_W], ["sorryAx"], ("reject", "sorry-warning")),
                 ([{**UNKNOWN, "data": "unexpected token '['; expected command"}], [], ("reject", "parse-error")),
                 ([{**UNKNOWN, "data": "Unknown identifier `foo_bar`"}], ["sorryAx"], ("reject", "unknown-identifier")),
                 ([], None, ("reject", "not-declared")),
                 ([{**SORRY_W, "data": "unused variable `h`"}], ["propext"], ("accept", None)),
                 ([], [], ("accept", None))]
        for msgs, ax, want in cases:
            self.assertEqual(lv.classify(msgs, ax), want, msgs)


class VerdictProblemsTests(Family):
    def assertRefused(self, needle, doc=None, manifest=MANIFEST):
        if doc is not None:
            self.write(doc)
        got = self.problems(manifest)[0]
        self.assertTrue(any(needle in p for p in got), f"{needle!r} not in {got}")

    def test_green_control(self):
        self.assertEqual(self.problems(), ([], []))

    def test_missing_malformed_or_foreign_files_are_refused(self):
        (self.fam / lv.VERDICTS_FILE).unlink()
        self.assertRefused("is missing")
        (self.fam / lv.VERDICTS_FILE).write_text("{ not json")
        self.assertRefused("malformed")
        self.assertRefused("has schema", {**make_doc(), "schema_version": "v0"})
        self.assertRefused("minted for family", resealed({**make_doc(), "family": "g_simp"}))
        self.assertRefused("rule", resealed({**make_doc(), "rule": "other"}))

    def test_a_broken_seal_is_refused(self):
        doc = make_doc()
        doc["files"]["t.lean"]["rows"]["p_rej"]["messages"][0]["data"] = "edited"
        self.assertRefused("content seal", doc)

    def test_another_world_or_build_is_not_the_oracle_world(self):
        for key, val in (("id", "v4.33.1"), ("toolchain", "leanprover/lean4:v4.33.1"), ("githash", "0" * 40)):
            doc = make_doc()
            doc["lean_world"][key] = val
            self.assertRefused("not the oracle world", resealed(doc))

    def test_a_fixture_edited_without_a_re_mint_is_refused(self):
        (self.fam / "t.lean").write_bytes(FIXTURE.replace(b"n + 0 = n := rfl", b"n + 0 = n  := rfl"))
        self.assertRefused("edited without a re-mint")

    def test_row_or_file_sets_that_differ_are_refused(self):
        doc = make_doc()
        del doc["files"]["t.lean"]["rows"]["p_ok"]
        self.assertRefused("minted rows differ", resealed(doc))
        doc = make_doc()
        doc["files"]["u.lean"] = doc["files"]["t.lean"]
        self.assertRefused("not the manifest's", resealed(doc))

    def test_a_hand_flipped_verdict_does_not_re_derive_even_resealed(self):
        doc = make_doc()
        doc["files"]["t.lean"]["rows"]["p_rej"].update(verdict="accept", **{"class": None},
                                                       split_verdict="accept")
        self.assertRefused("does not re-derive", resealed(doc))

    def test_split_and_exit_disagreements_are_refused(self):
        doc = make_doc()
        doc["files"]["t.lean"]["rows"]["p_ok"]["split_verdict"] = "reject"
        self.assertRefused("split reading", resealed(doc))
        doc = make_doc()
        doc["files"]["t.lean"]["lean_exit"] = 0
        self.assertRefused("lean_exit", resealed(doc))

    def test_a_rejected_helper_or_control_is_refused(self):
        for name in ("h_t", "ctl_t"):
            doc = make_doc()
            doc["files"]["t.lean"]["rows"][name] = row("reject", "elab-error", ["sorryAx"], [DISTRIB])
            self.assertRefused(f"{name} is not accepted by pinned Lean", resealed(doc))

    def test_a_negative_must_be_rejected_for_its_named_reason_beside_an_accepted_control(self):
        doc = make_doc()
        doc["files"]["t.lean"]["rows"]["neg_t"] = row("accept", None, [])
        self.assertRefused("ACCEPTED by pinned Lean", resealed(doc))
        other = copy.deepcopy(MANIFEST)
        other["files"][0]["negatives"][0]["lean_contains"] = "Type mismatch"
        self.assertRefused("rejected for a different reason", make_doc(), other)
        other = copy.deepcopy(MANIFEST)
        other["files"][0]["negatives"][0]["control"] = "p_rej"
        self.assertRefused("not accepted by pinned Lean", make_doc(), other)

    def test_a_rejected_canary_is_report_only_in_phase_1(self):
        doc = make_doc()
        doc["files"]["t.lean"]["rows"]["canary_t"] = row("reject", "elab-error", ["sorryAx"], [DISTRIB])
        self.write(resealed(doc))
        problems, notes = self.problems()
        self.assertEqual(problems, [])
        self.assertIn("class 73", notes[0])
        with mock.patch.object(lv, "CANARIES_MUST_ACCEPT", True):
            self.assertIn("class 73", self.problems()[0][0])

    def test_oracle_world_must_be_the_toolchain_pin(self):
        root = self.tmp / "root"
        (root / "crates" / "clean-olean").mkdir(parents=True)
        (root / "crates" / "clean-olean" / "lean_worlds.tsv").write_text(
            "# x\nv4.30.0-rc2\toracle\tleanprover/lean4:v4.30.0-rc2\tf\n")
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        self.assertIn("is not ./lean-toolchain", lv.oracle_world(root)[2][0])
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.30.0-rc2\n")
        self.assertEqual(lv.oracle_world(root), ("v4.30.0-rc2", "leanprover/lean4:v4.30.0-rc2", []))


def measured(verdicts):
    """Rows as run_family builds them, crossed with make_doc()."""
    rows = []
    for name in lv.declared_names(ENTRY):
        r = {"name": name, "file": "t.lean", "label": "t", "kind": lv.row_kind(ENTRY, name),
             "verdict": verdicts.get(name, "pass"), "required": False}
        if name == "neg_t":
            r["control"] = "ctl_t"
        rows.append(r)
    ftw.cross(rows, make_doc())
    return rows


# Clean passes the unknown-tactic probe and fails what Lean rejects in-world.
TYPICAL = {"p_rej": "fail", "neg_t": "fail"}


class TotalsTests(unittest.TestCase):
    def test_totals_count_every_kind_and_the_in_world_subset(self):
        rows = measured({"p_rej": "pass", "neg_t": "fail", "ctl_t": "diverged"})
        t = ftw.totals(rows)
        self.assertEqual((t["probes"], t["passed"], t["failed"]), (3, 3, 0))
        self.assertEqual(t["clean_accepts_lean_rejects"], 2)  # p_unk, p_rej
        self.assertEqual(t["clean_accepts_lean_rejects_in_world"], 1)  # p_rej
        self.assertEqual(t["clean_accepts_lean_rejects_by_class"], {"elab-error": 1, "unknown-tactic": 1})
        self.assertEqual((t["agree_reject"], t["clean_diverged_lean_accept"]), (1, 1))
        self.assertEqual((t["negatives_confirmed"], t["negatives_unconfirmed"]), (0, 1))
        names = ftw.two_way_rows(rows)
        self.assertEqual(names["clean_accepts_lean_rejects_in_world"], ["p_rej"])
        self.assertEqual(names["negatives_unconfirmed"], ["neg_t"])


def baseline_v1(passed=(), fail=(), diverged=None):
    """A v1 (probe-lists-only) baseline; `diverged` absent unless given."""
    out = {"family": "g_auto", "pass": list(passed), "fail": list(fail)}
    return out if diverged is None else {**out, "diverged": list(diverged)}


class RatchetTests(unittest.TestCase):
    def test_ratchet_in_world_new_false_accept_fails(self):
        fails, _ = ftw.ratchet(measured({"neg_t": "fail", "p_rej": "pass"}), baseline_v1(fail=["p_rej"]))
        self.assertEqual(len(fails), 1)
        self.assertIn("NEW-FALSE-ACCEPT p_rej", fails[0])

    def test_ratchet_diverged_counts_and_a_missing_diverged_key_is_empty(self):
        fails, _ = ftw.ratchet(measured({"neg_t": "fail", "p_rej": "pass"}), baseline_v1(diverged=["p_rej"]))
        self.assertIn("NEW-FALSE-ACCEPT p_rej", fails[0])
        self.assertEqual(ftw.ratchet(measured(TYPICAL), baseline_v1(fail=["p_rej"]))[0], [])

    def test_ratchet_unknown_tactic_probe_is_exempt(self):
        """The pinned exemption (in place of an artifact arm that could not stay green)."""
        fails, _ = ftw.ratchet(measured(TYPICAL), baseline_v1(fail=["p_unk", "p_rej"]))
        self.assertEqual(fails, [])

    def test_ratchet_a_negative_is_never_exempt(self):
        rows = measured({"p_rej": "fail", "neg_t": "pass"})
        next(r for r in rows if r["name"] == "neg_t")["lean_class"] = "unknown-tactic"
        base = {**baseline_v1(), "row_verdicts": {"neg_t": {"clean": "fail", "lean": "reject"}}}
        self.assertIn("NEW-FALSE-ACCEPT neg_t", ftw.ratchet(rows, base)[0][0])

    def test_ratchet_reports_lean_side_flips_and_new_rows_without_failing(self):
        base = {**baseline_v1(), "row_verdicts": {"p_unk": {"clean": "pass", "lean": "accept"}}}
        fails, reports = ftw.ratchet(measured(TYPICAL), base)
        self.assertEqual(fails, [])
        self.assertTrue(any("Lean-side flip p_unk: accept -> reject" in r for r in reports), reports)
        self.assertTrue(any("does not record" in r for r in reports), reports)

    def test_ratchet_failure_is_not_the_waivable_regression(self):
        fails, _ = ftw.ratchet(measured({"neg_t": "fail", "p_rej": "pass"}), baseline_v1(fail=["p_rej"]))
        regression = "baseline regression -- rows recorded passing now fail: ['p_ok']"
        blockers = family_gate.record_blockers([regression, *fails], regression, True)
        self.assertEqual(blockers, fails)


class StrictTests(unittest.TestCase):
    def test_strict_fails_on_a_false_acceptance(self):
        rows = [r for r in measured({"p_unk": "pass", **TYPICAL}) if r["kind"] != "negative"]
        got = ftw.strict_failure(ftw.totals(rows), rows)
        self.assertEqual(len(got), 1, got)
        self.assertIn("clean_accepts_lean_rejects=1", got[0])

    def test_strict_fails_on_uncrossed_rows_and_unconfirmed_negatives(self):
        rows = measured({"p_unk": "fail", "p_rej": "fail", "neg_t": "pass"})
        rows[0]["two_way"] = None
        got = " | ".join(ftw.strict_failure(ftw.totals(rows), rows))
        self.assertIn("carry no pinned-Lean verdict", got)
        self.assertIn("negative(s) not confirmed", got)

    def test_strict_is_quiet_when_every_row_agrees(self):
        rows = measured({"p_unk": "fail", **TYPICAL})
        self.assertEqual(ftw.strict_failure(ftw.totals(rows), rows), [])


def artifact(rows, fixture=FIXTURE):
    return {"schema_version": ftw.GATE_SCHEMA, "family": "g_auto", "gate_verdict": "measured",
            "lean_mint": {"seal": make_doc()["seal"]},
            "files": [{"file": "t.lean", "fixture_sha256": lv.sha256_bytes(fixture)}], "rows": rows,
            "totals": {"plan_family_total": 3, **ftw.totals(rows)}, "two_way_rows": ftw.two_way_rows(rows)}


class CheckArtifactTests(unittest.TestCase):
    def run_check(self, art, baseline=None, strict=False):
        return ftw.check_artifact("G-AUTO", "g_auto", art, make_doc(), baseline, strict)

    def test_a_consistent_artifact_is_ok(self):
        rc, lines = self.run_check(artifact(measured(TYPICAL)))
        self.assertEqual(rc, 0, lines)
        self.assertIn("G-AUTO=artifact-ok clean_accepts_lean_rejects=1 in_world=0 crossed=7/7", lines[-1])

    def test_a_v1_artifact_is_refused(self):
        rc, lines = self.run_check({"schema_version": "tactic-family-gate-v1"})
        self.assertEqual(rc, 1)
        self.assertIn("artifact-not-v2", lines[-1])

    def test_a_stale_file_is_unknown_not_red_and_not_green(self):
        rc, lines = self.run_check(artifact(measured(TYPICAL), fixture=b"other bytes"))
        self.assertEqual(rc, ftw.EXIT_UNKNOWN, lines)
        self.assertIn("STALE", lines[0])
        self.assertIn("G-AUTO=artifact-unknown files=1", lines[-1])
        self.assertIn("crossed=0/7", lines[-1])

    def test_a_flipped_row_or_retyped_totals_are_refused(self):
        art = artifact(measured(TYPICAL))
        art["rows"][4]["lean_verdict"] = "accept"
        self.assertIn("disagrees with the verdict file", " ".join(self.run_check(art)[1]))
        art = artifact(measured(TYPICAL))
        art["totals"]["clean_accepts_lean_rejects"] = 0
        self.assertIn("do not re-derive", " ".join(self.run_check(art)[1]))

    def test_the_ratchet_and_strict_apply_offline(self):
        art = artifact(measured({"neg_t": "fail", "p_rej": "pass"}))
        rc, lines = self.run_check(art, baseline_v1(fail=["p_rej"]))
        self.assertEqual(rc, 1)
        self.assertIn("NEW-FALSE-ACCEPT p_rej", " ".join(lines))
        rc, lines = self.run_check(artifact(measured(TYPICAL)), strict=True)
        self.assertEqual(rc, 1)
        self.assertIn("strict=on", lines[-1])


class PinnedInputsAndNoLeanTests(unittest.TestCase):
    def test_pinned_inputs_output(self):
        """The modules family_gate.py imports, and the test file its S-arms run."""
        want = ["scripts/tactic_parity/clean_report.py", "scripts/tactic_parity/family_two_way.py",
                "scripts/tactic_parity/lean_verdicts.py", "scripts/test_family_gate_two_way.py",
                "scripts/test_family_two_way.py"]
        proc = subprocess.run([sys.executable, "scripts/tactic_parity/family_gate.py", "--pinned-inputs"],
                              cwd=ROOT, capture_output=True, text=True, timeout=60)
        self.assertEqual((proc.returncode, proc.stdout), (0, "".join(f"{w}\n" for w in want)))
        self.assertEqual(ftw.first_party_inputs(), want)
        self.assertEqual(ftw.arm_test_modules(), want[3:])

    def test_the_gate_never_runs_lean(self):
        """family_gate.py and the modules it imports import no minter and no
        Lean runner, and name no Lean binary; the three modules start no process."""
        for rel, banned in (("scripts/tactic_parity/family_gate.py", set()),
                            ("scripts/tactic_parity/family_two_way.py", {"subprocess", "os"}),
                            ("scripts/tactic_parity/lean_verdicts.py", {"subprocess", "os"}),
                            ("scripts/tactic_parity/clean_report.py", {"subprocess", "os"})):
            tree = ast.parse((ROOT / rel).read_text(encoding="utf-8"))
            mods = {a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names}
            mods |= {n.module for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)}
            self.assertFalse(mods & ({"mint_lean_verdicts", "lean_suite_conformance"} | banned), rel)
            strings = [n.value for n in ast.walk(tree) if isinstance(n, ast.Constant) and isinstance(n.value, str)]
            self.assertFalse([s for s in strings if ".elan" in s or "bin/lean" in s], rel)


class StubCleanFamily(Family):
    """`clean` stubbed and the report/baseline dirs in temp (no tests here)."""

    def setUp(self):
        super().setUp()
        self.clean = dict(TYPICAL)
        self.on_check = self.on_canary = None
        self.bin = self.tmp / "clean"
        self.bin.write_text("#!/bin/sh\nexit 1\n")
        self.bin.chmod(0o755)
        for name, val in (("FIXTURE_ROOT", self.fam.parent), ("REPORT_DIR", self.tmp / "reports"),
                          ("BASELINE_DIR", self.tmp / "baselines")):
            patcher = mock.patch.object(family_gate, name, val)
            patcher.start()
            self.addCleanup(patcher.stop)
        patcher = mock.patch.object(family_gate.subprocess, "run", self.fake_run)
        patcher.start()
        self.addCleanup(patcher.stop)
        (self.tmp / "baselines").mkdir()

    def fake_run(self, argv, **_kw):
        if argv[0] == "git":
            return subprocess.CompletedProcess(argv, 0, "0" * 40 + "\n", "")
        if "--prelude" in argv:
            if self.on_canary:
                self.on_canary()
            return subprocess.CompletedProcess(argv, 1, json.dumps({"status": "fail", "decl_count": 1, "success_count": 0}), "")
        if self.on_check:
            self.on_check()
        names = lv.declared_names(ENTRY)
        failed = [n for n in names if self.clean.get(n, "pass") == "fail"]
        rep = {"status": "fail" if failed else "pass", "decl_count": len(names),
               "success_count": len(names) - len(failed), "failed_count": len(failed), "diverged_count": 0,
               "errors": [f"{n}: did not close the goal" for n in failed], "trust_failures": [],
               "kernel_failures": [], "diverged": [], "proof_state_feedback": []}
        return subprocess.CompletedProcess(argv, 1 if failed else 0, json.dumps(rep), "")

    def baseline(self, doc):
        (self.tmp / "baselines" / "g_auto.json").write_text(json.dumps(doc))

    def run_gate(self, update=False, strict=False, manifest=MANIFEST):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = family_gate.run_family("g_auto", manifest, self.bin, update, make_doc(), strict)
        return rc, out.getvalue()


class RunFamilyEndToEndTests(StubCleanFamily):
    """run_family with `clean` stubbed and the report/baseline dirs in temp."""

    def test_run_family_seeded_acceptance_names_new_false_accept(self):
        """THE seeded acceptance through the measured code path: a stubbed
        Clean newly passes a negative the baseline recorded fail."""
        self.baseline({**baseline_v1(["p_ok", "p_unk"], ["p_rej"]),
                       "row_verdicts": {"neg_t": {"kind": "negative", "clean": "fail", "lean": "reject"}}})
        self.clean["neg_t"] = "pass"
        rc, out = self.run_gate()
        self.assertEqual(rc, 1, out)
        self.assertIn("NEW-FALSE-ACCEPT neg_t", out)
        art = json.loads((self.tmp / "reports" / "g_auto-latest.json").read_text())
        self.assertEqual(art["schema_version"], ftw.GATE_SCHEMA)
        self.assertEqual(art["files"][0]["fixture_sha256"], lv.sha256_bytes(FIXTURE))
        self.assertEqual((art["totals"]["clean_accepts_lean_rejects"],
                          art["totals"]["clean_accepts_lean_rejects_in_world"]), (2, 1))
        self.assertTrue(all("lean_verdict" in r for r in art["rows"]))
        with mock.patch.dict(os.environ, {"CLEAN_FAMILY_BASELINE_ALLOW_REGRESSION": "1"}):
            rc, out = self.run_gate(update=True)
        self.assertEqual(rc, 1)
        self.assertIn("refusing-to-record-baseline", out)

    def test_run_family_strict_returns_1_on_a_false_acceptance(self):
        self.baseline(baseline_v1(["p_ok", "p_unk"], ["p_rej"]))
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)
        self.assertIn("clean_accepts_lean_rejects=1 in_world=0", out)
        art = json.loads((self.tmp / "reports" / "g_auto-latest.json").read_text())
        self.assertEqual(ftw.check_artifact("G-AUTO", "g_auto", art, make_doc(), None, False)[0], 0)
        rc, out = self.run_gate(strict=True)
        self.assertEqual(rc, 1, out)
        self.assertIn("--strict: clean_accepts_lean_rejects=1", out)
        rc, out = self.run_gate(update=True)
        self.assertEqual(rc, 0, out)
        rec = json.loads((self.tmp / "baselines" / "g_auto.json").read_text())
        self.assertEqual(rec["row_verdicts"]["neg_t"], {"kind": "negative", "clean": "fail", "lean": "reject"})
        self.assertEqual(rec["lean_mint_seal"], make_doc()["seal"])

    def test_run_family_refuses_fixture_bytes_that_moved(self):
        (self.fam / "t.lean").write_bytes(FIXTURE + b"\n")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1)
        self.assertIn("edited without a re-mint", out)
        (self.fam / "t.lean").write_bytes(FIXTURE)
        self.on_check = lambda: (self.fam / "t.lean").write_bytes(FIXTURE + b"-- moved\n")
        rc, out = self.run_gate()
        self.assertEqual(rc, 1)
        self.assertIn("changed while Clean measured it", out)


if __name__ == "__main__":
    unittest.main()
