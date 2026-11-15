# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Self-test for family_gate.py's two-way entry points (item 17 review round).

Each case pins a defect two reviewers found by reproduction, and fails on the
code before its fix:

  * `main` itself: --static refuses a stale sidecar through the real entry
    point (no test called `main`, so neutering the sidecar check there stayed
    green) and prints the seal it validated; a second mode is refused, never
    dropped in silence;
  * one validated read: a sidecar swapped while the canaries run is never the
    one a measured run crosses;
  * an in-world false acceptance the baseline does not record (a renamed row,
    a new negative, a deleted baseline) is not recorded by --update-baseline
    unless MANIFEST.json's reviewed `two_way_record_exemptions` names it;
  * --check-artifact covers every minted file and row, and a stale or missing
    file is UNKNOWN (exit 3), never `artifact-ok`;
  * the out-of-world exemption is a Mathlib-tactic allowlist, not the error
    text, and the recorded unknown tactic re-derives from the fixture;
  * a negative's `lean_class` / `lean_contains` cannot be vacuous.

The shared synthetic family and stubbed `clean` are scripts/test_family_two_way.py's.
No binary, no Lean.
"""

import contextlib
import copy
import io
import json
import os
import unittest
from unittest import mock

from scripts import test_family_two_way as base
from scripts.tactic_parity import family_gate

ftw, lv = family_gate.ftw, family_gate.lv


class MainTests(base.StubCleanFamily):
    def main(self, *argv):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            try:
                rc = family_gate.main(["--family", "g_auto", *argv])
            except SystemExit as exc:
                rc = exc.code
        return rc, out.getvalue()

    def test_main_static_reports_the_seal_it_validated(self):
        rc, out = self.main("--static")
        self.assertEqual(rc, 0, out)
        self.assertIn(f"G-AUTO=fixtures-ok probes=3 files=1 lean_verdicts=sealed:"
                      f"{base.make_doc()['seal'][:12]} rows=7", out)

    def test_main_static_refuses_a_stale_sidecar(self):
        (self.fam / "t.lean").write_bytes(base.FIXTURE + b"-- edited, not re-minted\n")
        rc, out = self.main("--static")
        self.assertEqual(rc, 1, out)
        self.assertIn("t.lean: edited without a re-mint", out)
        self.assertIn("G-AUTO=failed reason=lean-verdicts", out)
        self.assertNotIn("fixtures-ok", out)

    def test_main_refuses_a_second_mode_or_a_flag_it_would_drop(self):
        for argv in (["--static", "--check-artifact"], ["--static", "--canary-check"],
                     ["--canary-check", "--check-artifact"], ["--check-artifact", "--update-baseline"],
                     ["--static", "--update-baseline"], ["--canary-check", "--update-baseline"],
                     ["--static", "--strict"], ["--canary-check", "--strict"]):
            rc, out = self.main(*argv)
            self.assertEqual(rc, 2, (argv, out))
            self.assertIn("error:", out)

    def test_a_measured_run_crosses_the_sidecar_main_validated(self):
        """A consistently forged sidecar swapped in while the canaries run (after
        main validated the committed one) is never crossed or recorded."""
        forged = base.make_doc()
        forged["files"]["t.lean"]["rows"]["p_rej"].update(
            verdict="accept", split_verdict="accept", messages=[], axioms=[], **{"class": None})
        self.on_canary = lambda: self.write(base.resealed(forged))
        with mock.patch.dict(os.environ, {"CLEAN_BIN": str(self.bin)}):
            rc, out = self.main()
        self.assertEqual(rc, 0, out)
        art = json.loads((self.tmp / "reports" / "g_auto-latest.json").read_text())
        self.assertEqual(art["lean_mint"]["seal"], base.make_doc()["seal"])
        p_rej = next(r for r in art["rows"] if r["name"] == "p_rej")
        self.assertEqual((p_rej["lean_verdict"], p_rej["two_way"]), ("reject", ftw.AGREE_REJECT))

    def test_check_artifact_through_main_is_unknown_on_a_stale_file(self):
        art = base.artifact(base.measured(base.TYPICAL), fixture=b"older bytes")
        path = self.tmp / "art.json"
        path.write_text(json.dumps(art))
        rc, out = self.main("--check-artifact", str(path))
        self.assertEqual(rc, ftw.EXIT_UNKNOWN, out)
        self.assertIn("G-AUTO=artifact-unknown files=1", out)


class RecordRefusalTests(base.StubCleanFamily):
    def recorded(self):
        path = self.tmp / "baselines" / "g_auto.json"
        return json.loads(path.read_text()) if path.is_file() else None

    def test_an_unrecorded_in_world_false_acceptance_is_not_recorded(self):
        """A v1 baseline records probes only, so a negative Clean newly passes
        is unrecorded: the ratchet cannot see it, and the record refuses it."""
        self.baseline(base.baseline_v1(["p_ok", "p_unk"], ["p_rej"]))
        self.clean["neg_t"] = "pass"
        rc, out = self.run_gate()
        self.assertEqual(rc, 0, out)
        self.assertIn("1 of them in world, Clean accepting what pinned Lean rejects: neg_t", out)
        rc, out = self.run_gate(update=True)
        self.assertEqual(rc, 1, out)
        self.assertIn("two-way record -- neg_t is an in-world row", out)
        self.assertNotIn("row_verdicts", self.recorded())

    def test_a_renamed_or_deleted_baseline_does_not_launder_a_false_acceptance(self):
        self.clean["p_rej"] = "pass"  # no baseline at all
        rc, out = self.run_gate(update=True)
        self.assertEqual(rc, 1, out)
        self.assertIn("two-way record -- p_rej", out)
        self.assertIsNone(self.recorded())

    def test_a_reviewed_exemption_lets_it_be_recorded(self):
        manifest = copy.deepcopy(base.MANIFEST)
        manifest[lv.EXEMPTIONS_KEY] = {"p_rej": "known: Clean's grind closes it; ledger entry pending"}
        self.clean["p_rej"] = "pass"
        rc, out = self.run_gate(update=True, manifest=manifest)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.recorded()["row_verdicts"]["p_rej"],
                         {"kind": "probe", "clean": "pass", "lean": "reject"})


class CheckArtifactCoverageTests(unittest.TestCase):
    def run_check(self, art, doc=None, baseline=None, strict=False):
        return ftw.check_artifact("G-AUTO", "g_auto", art, doc or base.make_doc(), baseline, strict)

    def test_a_minted_file_the_artifact_never_measured_is_unknown(self):
        doc = base.make_doc()
        doc["files"]["u.lean"] = copy.deepcopy(doc["files"]["t.lean"])
        art = base.artifact(base.measured(base.TYPICAL))
        rc, lines = self.run_check(art, doc)
        self.assertEqual(rc, ftw.EXIT_UNKNOWN, lines)
        self.assertIn("  MISSING (UNKNOWN, not crossed): u.lean has minted verdicts the artifact "
                      "never measured", lines)
        self.assertIn("G-AUTO=artifact-unknown files=1", lines[-1])
        rc, lines = self.run_check(art, doc, strict=True)
        self.assertEqual(rc, 1, lines)
        self.assertIn("minted file(s) the artifact never measured: ['u.lean']", " ".join(lines))

    def test_a_row_dropped_from_the_artifact_is_refused(self):
        """Deleting the row the ratchet would fail, totals re-derived, is not ok."""
        rows = [r for r in base.measured({"neg_t": "fail", "p_rej": "pass"}) if r["name"] != "p_rej"]
        rc, lines = self.run_check(base.artifact(rows), baseline=base.baseline_v1(fail=["p_rej"]))
        self.assertEqual(rc, 1, lines)
        self.assertIn("the artifact's rows are not the minted rows (missing=['p_rej']", " ".join(lines))

    def test_a_duplicated_row_or_an_unlisted_file_is_refused(self):
        rows = base.measured(base.TYPICAL)
        rc, lines = self.run_check(base.artifact(rows + [dict(rows[0])]))
        self.assertIn("8 rows for 7 names", " ".join(lines))
        art = base.artifact(rows)
        art["rows"][0]["file"] = "elsewhere.lean"
        rc, lines = self.run_check(art)
        self.assertEqual(rc, 1, lines)
        self.assertIn("rows name file(s) the artifact does not list: ['elsewhere.lean']", " ".join(lines))

    def test_a_malformed_artifact_or_a_foreign_seal(self):
        art = base.artifact(base.measured(base.TYPICAL))
        del art["lean_mint"]
        self.assertIn("artifact-malformed", self.run_check(art)[1][-1])
        art = base.artifact(base.measured(base.TYPICAL))
        art["lean_mint"]["seal"] = "0" * 64
        rc, lines = self.run_check(art)
        self.assertEqual(rc, 0, lines)
        self.assertIn("measured against verdicts sealed 000000000000", lines[0])

    def test_a_file_the_verdicts_do_not_mint_is_stale(self):
        art = base.artifact(base.measured(base.TYPICAL))
        art["files"].append({"file": "gone.lean", "fixture_sha256": None})
        rc, lines = self.run_check(art)
        self.assertEqual(rc, ftw.EXIT_UNKNOWN, lines)
        self.assertIn("  STALE (UNKNOWN, not crossed): gone.lean changed since the artifact was measured",
                      lines)


class InWorldTests(unittest.TestCase):
    def row(self, toks, kind="probe", cls="unknown-tactic"):
        return {"kind": kind, "lean_class": cls, "lean_unknown_tactics": toks}

    def test_only_a_mathlib_tactic_probe_is_out_of_world(self):
        self.assertFalse(ftw.in_world(self.row(["norm_num"])))
        self.assertFalse(ftw.in_world(self.row(["aesop", "linarith"])))
        for toks in (["library_search"], ["norm_nm"], ["norm_num", "clean_only_tac"], [], None):
            self.assertTrue(ftw.in_world(self.row(toks)), toks)
        self.assertTrue(ftw.in_world(self.row(["norm_num"], kind="negative")))
        self.assertTrue(ftw.in_world(self.row(["norm_num"], cls="elab-error")))

    def test_a_non_mathlib_unknown_tactic_probe_is_ratcheted_and_counted(self):
        rows = base.measured({"neg_t": "fail", "p_rej": "fail", "p_unk": "pass"})
        next(r for r in rows if r["name"] == "p_unk")["lean_unknown_tactics"] = ["library_search"]
        fails, _ = ftw.ratchet(rows, base.baseline_v1(fail=["p_unk"]))
        self.assertIn("NEW-FALSE-ACCEPT p_unk", fails[0])
        self.assertEqual(ftw.totals(rows)["clean_accepts_lean_rejects_in_world"], 1)


class UnknownTacticAndManifestTests(base.Family):
    def test_a_hand_edited_unknown_tactic_does_not_re_derive(self):
        """Respelling the recorded token to a Mathlib name would move a row out
        of world; the stored message's position in the fixture says otherwise."""
        doc = base.make_doc()
        doc["files"]["t.lean"]["rows"]["p_unk"]["unknown_tactics"] = ["aesop"]
        self.write(base.resealed(doc))
        got = " ".join(self.problems()[0])
        self.assertIn("p_unk records unknown_tactics ['aesop'], but its stored `unknown tactic` "
                      "errors point at ['norm_num']", got)

    def test_tactic_at_walks_back_to_the_token_lean_points_into(self):
        line = "theorem p (a : Nat) : a = a := by library_search"
        start = line.index("library_search")
        for col in (start, start + 1, start + 5):
            self.assertEqual(lv.tactic_at(line, col), "library_search")
        self.assertIsNone(lv.tactic_at("x := y", 3))

    def test_a_negative_needs_a_reject_class_and_a_nonempty_needle(self):
        for field, val, needle in (("lean_contains", "", "has an empty lean_contains"),
                                   ("lean_contains", "  ", "has an empty lean_contains"),
                                   ("lean_class", "bogus", "names lean_class 'bogus'"),
                                   ("lean_class", None, "names lean_class None")):
            manifest = copy.deepcopy(base.MANIFEST)
            manifest["files"][0]["negatives"][0][field] = val
            got = self.problems(manifest)[0]
            self.assertTrue(any(needle in p for p in got), (field, val, got))

    def test_exemptions_must_name_declared_rows_with_reasons(self):
        manifest = copy.deepcopy(base.MANIFEST)
        manifest[lv.EXEMPTIONS_KEY] = {"no_such_row": "why", "p_rej": " "}
        got = " ".join(self.problems(manifest)[0])
        self.assertIn("names no_such_row, which is no declared row", got)
        self.assertIn("gives p_rej no written reason", got)
        manifest[lv.EXEMPTIONS_KEY] = ["p_rej"]
        self.assertIn("must be an object", " ".join(self.problems(manifest)[0]))
        manifest[lv.EXEMPTIONS_KEY] = {"p_rej": "reviewed"}
        self.assertEqual(self.problems(manifest), ([], []))


if __name__ == "__main__":
    unittest.main()
