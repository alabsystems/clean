#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Fake exports/logs test control orchestration, never real proof replay."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import byte_literal_typing_controls as controls


def fake_export():
    lines = []
    for root in controls.ROOTS:
        if "_input_v1" in root:
            kind = "nat" if "_nat_" in root else "string"
            judgment = "infers" if "_infers_" in root else "typing"
            typ = ("((x_0 : @CleanVerify.KDeclEnv) -> ((x_1 : (@CleanVerify.ListType @CleanVerify.KExpr)) -> "
                   "((x_2 : @CleanVerify.Nat) -> ((access : Access) -> ((byte : Byte) -> "
                   f"(@CleanVerify.ir_byte_literal_{judgment}_v1 x_0 x_1 (@CleanVerify.literal_{kind} x_2) "
                   "(@CleanVerify.ir_byte_literal_type_v1 memory @CleanVerify.IRTy.fatstr_ scalar)))))))")
        else:
            typ = "Type"
        lines += [f"noncomputable def CleanVerify.{root} : {typ} :=", "  unchanged_proof_term", ""]
    lines += [f"#print axioms CleanVerify.{root}" for root in controls.ROOTS]
    return "\n".join(lines) + "\n"


def axiom_log(roots=controls.ROOTS):
    return "\n".join(f"'CleanVerify.{root}' does not depend on any axioms" for root in roots) + "\n"


class TypingControlTests(unittest.TestCase):
    def test_type_only_mutations_preserve_payload_telescope_proof_and_rest(self):
        source = fake_export()
        for kind in ("nat", "string"):
            for mode, judgment in (("subject", "infers"), ("nominal", "typing")):
                with self.subTest(kind=kind, mode=mode):
                    root = f"ir_byte_literal_{kind}_{judgment}_input_v1"
                    before = controls.declaration(source, root)
                    mutant = controls.mutate(source, kind, mode)
                    after = controls.declaration(mutant, root)
                    self.assertEqual(source[:before.start()], mutant[:after.start()])
                    self.assertEqual(source[before.end():], mutant[after.end():])
                    self.assertEqual(before["body"], after["body"])
                    goal = f"(@CleanVerify.ir_byte_literal_{judgment}_v1"
                    self.assertEqual(before["type"].split(goal)[0], after["type"].split(goal)[0])
                    self.assertIn("x_2)", after["type"])
                    self.assertNotEqual(before["type"], after["type"])

    def test_prepare_appends_both_empty_identities_without_touching_export(self):
        with tempfile.TemporaryDirectory() as tmp:
            source, outdir = Path(tmp) / "export.lean", Path(tmp) / "controls"
            source.write_text(fake_export())
            controls.prepare(source, outdir)
            positive = (outdir / "PositiveControls.lean").read_text()
            self.assertEqual(positive, fake_export() + controls.control_appendix())
            self.assertEqual(len(list(outdir.iterdir())), 5)
            self.assertEqual(source.read_text(), fake_export())
            controls.check_positive(positive, axiom_log(controls.ROOTS + controls.CONTROLS), 0)
            with self.assertRaises(ValueError):
                controls.prepare(source, outdir)

    def test_empty_controls_explicitly_apply_the_implicit_constructor_type(self):
        # Lean makes the inductive constructor's type parameter implicit, unlike
        # Clean's internal surface parser. The independent replay caught the
        # missing @; this spelling check guards that concrete regression.
        appendix = controls.control_appendix()
        self.assertEqual(appendix.count("(@CleanVerify.IROption.none CleanVerify.KExpr)"), 2)
        self.assertNotIn("(CleanVerify.IROption.none CleanVerify.KExpr)", appendix)

    def test_missing_duplicate_root_audit_and_changed_layout_are_refused(self):
        source = fake_export()
        root = controls.ROOTS[0]
        mutations = (
            source.replace(f"noncomputable def CleanVerify.{root} ", "noncomputable def Other "),
            source + f"noncomputable def CleanVerify.{root} : Type :=\n  body\n",
            source.replace(f"#print axioms CleanVerify.{root}\n", ""),
            source + f"#print axioms CleanVerify.{root}\n",
            source.replace(" : Type :=\n", " :\n Type :=\n", 1),
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation[-70:]), self.assertRaises(ValueError):
                controls.validate_source(mutation)

    def test_comments_and_strings_cannot_fake_roots_audits_or_admissions(self):
        source = fake_export()
        root = controls.ROOTS[0]
        comment = f"/- nested /- sorry -/ def CleanVerify.{root}\n#print axioms CleanVerify.{root} -/\n"
        controls.check_positive(comment + source + 'def quoted := "sorry"\n', axiom_log(), 0)
        with self.assertRaises(ValueError):
            controls.validate_source(source.replace(f"#print axioms CleanVerify.{root}",
                                                     f"-- #print axioms CleanVerify.{root}"))

    def test_partial_or_changed_empty_controls_are_refused(self):
        positive = fake_export() + controls.control_appendix()
        for broken in (positive.replace(controls.CONTROLS[1], "other_control"),
                       positive.replace("fun tenv G input h => h", "fun tenv G input h => other", 1)):
            with self.assertRaises(ValueError):
                controls.check_positive(broken, axiom_log(controls.ROOTS + controls.CONTROLS), 0)

    def test_positive_log_requires_every_single_empty_closure_and_no_failures(self):
        for broken in ("", axiom_log() + axiom_log(), axiom_log().replace("any axioms", "axioms: [evil]", 1),
                       axiom_log() + "x:1:1: error: Type mismatch\n", axiom_log() + "timeout\n",
                       axiom_log() + "warning: declaration uses 'sorry'\n"):
            with self.subTest(broken=broken[-70:]), self.assertRaises(ValueError):
                controls.check_positive(fake_export(), broken, 0)
        for status in (1, 124):
            with self.assertRaises(ValueError):
                controls.check_positive(fake_export(), axiom_log(), status)

    def test_changed_conclusion_layout_is_not_silently_mutated(self):
        for source in (fake_export().replace("literal_nat x_2", "literal_nat other_payload"),
                       fake_export().replace("@CleanVerify.IRTy.fatstr_", "@CleanVerify.IRTy.other")):
            with self.assertRaises(ValueError):
                controls.mutate(source, "nat", "subject" if "other_payload" in source else "nominal")

    def test_mutant_requires_first_semantic_target_error_exit1_and_no_resource_or_admission(self):
        root = "ir_byte_literal_nat_infers_input_v1"
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "WrongSubject-nat.lean"
            original = Path(tmp) / "export.lean"
            original.write_text(fake_export())
            source.write_text(controls.mutate(fake_export(), "nat", "subject"))
            match = controls.declaration(source.read_text(), root)
            line = source.read_text().count("\n", 0, match.start()) + 1
            log = f"{source}:{line + 1}:2: error: Type mismatch\n  proof\nhas type A\nbut is expected to have type B\n"
            controls.check_mutant(source, log, 1, root, original)
            controls.check_mutant(source, log + f"'CleanVerify.{root}' depends on axioms: [sorryAx]\n", 1, root, original)
            failures = ((log, 0), (log, 124), ("", 1), (log.replace("Type mismatch", "unknown constant"), 1),
                        (f"{source}:1:1: error: bad import\n" + log, 1),
                        ("error: bad import\n" + log, 1),
                        (log.replace(str(source), str(Path(tmp) / "Other.lean")), 1),
                        ("sorry\n" + log, 1), (log + "timeout\n", 1),
                        (f"'CleanVerify.{root}' depends on axioms: [sorryAx]\n" + log, 1),
                        (log + "warning: declaration uses 'sorry'\n", 1),
                        (log + "'CleanVerify.other' depends on axioms: [sorryAx, evil]\n", 1))
            for broken, status in failures:
                with self.subTest(status=status, broken=broken[-70:]), self.assertRaises(ValueError):
                    controls.check_mutant(source, broken, status, root, original)
            source.write_text(source.read_text() + "def authored := sorry\n")
            with self.assertRaises(ValueError):
                controls.check_mutant(source, log, 1, root, original)

    def test_mutant_check_refuses_payload_telescope_proof_and_rest_drift(self):
        with tempfile.TemporaryDirectory() as tmp:
            original, source = Path(tmp) / "export.lean", Path(tmp) / "WrongNominal-nat.lean"
            original.write_text(fake_export())
            root = "ir_byte_literal_nat_typing_input_v1"
            mutant = controls.mutate(fake_export(), "nat", "nominal")
            match = controls.declaration(mutant, root)
            line = mutant.count("\n", 0, match.start()) + 1
            log = f"{source}:{line + 1}:2: error: Type mismatch\n"
            def replace_group(group, old, new):
                value = mutant[match.start(group):match.end(group)].replace(old, new, 1)
                return mutant[:match.start(group)] + value + mutant[match.end(group):]

            for changed in (replace_group("type", "literal_nat x_2", "literal_nat other_payload"),
                            replace_group("type", "(access : Access)", "(access : Other)"),
                            replace_group("body", "unchanged_proof_term", "other_proof"),
                            mutant + "-- unrelated drift\n"):
                source.write_text(changed)
                with self.assertRaises(ValueError):
                    controls.check_mutant(source, log, 1, root, original)

    def test_scanner_preserves_byte_offsets_and_newline_geometry(self):
        text = 'prefix /- nested /- x -/\ny -/ tail\n-- comment\n"a\\\"b\nc"\ncode\n'
        blanked = controls.blank_noncode_lean(text)
        self.assertEqual(len(text), len(blanked))
        self.assertEqual([i for i, c in enumerate(text) if c == "\n"],
                         [i for i, c in enumerate(blanked) if c == "\n"])
        self.assertIn("prefix", blanked)
        self.assertIn("tail", blanked)
        self.assertIn("code", blanked)
        self.assertNotIn("nested", blanked)


if __name__ == "__main__":
    unittest.main()
