"""Regression checks for byte-exact W4 comparison and its process status."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from kcheck_coverage_readers import parse_transcript
from self_proof_checker_replay import Case, compare, prelude_cases, retained_cases

ROOT = Path(__file__).resolve().parents[1]


class CheckerComparisonTest(unittest.TestCase):
    def test_retained_inputs_change_only_the_intended_bytes(self):
        archives, cases = retained_cases(ROOT)
        rows = {case.name: case for case in cases}
        self.assertEqual(set(archives), {"PR-42", "PR-49", "PR-52", "PR-53"})
        self.assertEqual(len(cases), 27)
        self.assertEqual(len(rows), len(cases))
        good = rows["Init/named-slice"]
        for label in ("k-as-iota", "iota-as-k"):
            wrong = rows["Init/" + label]
            self.assertEqual(wrong.source, good.source)
            self.assertNotEqual(wrong.advice, good.advice)
        wrong = rows["Init/type-as-identity-body"]
        self.assertNotEqual(wrong.source, good.source)
        self.assertEqual(wrong.advice, good.advice)
        self.assertEqual(rows["eta/prod_eta_proj"].status, 2)

    def test_canonical_prelude_controls_preserve_other_verdicts(self):
        _, cases = retained_cases(ROOT)
        prelude = {case.name: case for case in cases if case.name.startswith("Prelude/")}
        original = prelude["Prelude/original"]
        honest, summary = parse_transcript(original.stdout.decode())
        self.assertEqual(len(honest), 310)
        self.assertEqual(summary["accepted"], 22)
        corrupt = prelude["Prelude/native-nat-corrupt"]
        self.assertEqual(original.source, corrupt.source)
        self.assertEqual(len(corrupt.advice), len(original.advice))
        self.assertEqual(sum(a != b for a, b in zip(corrupt.advice, original.advice)), 1)
        wrong = prelude["Prelude/native-nat-wrong-body"]
        self.assertEqual(original.advice, wrong.advice)
        self.assertNotEqual(original.source, wrong.source)
        for case in (corrupt, wrong):
            with self.subTest(case=case.name):
                observed, counts = parse_transcript(case.stdout.decode())
                self.assertEqual(len(observed), len(honest))
                self.assertEqual(counts["accepted"], 21)
                changed = [row for before, row in zip(honest, observed) if before != row]
                self.assertEqual([(row["name"], row["class"]) for row in changed],
                                 [("[s3:Nat s11:noConfusion]", "refused")])

    def test_changed_prelude_archive_is_refused_before_comparison(self):
        read_bytes = Path.read_bytes
        base = ROOT / "reports/self-proof-native-paired-beta"
        for name in ("qualification.json", "prelude-prepared.bin", "native-nat-corrupt.txt.gz"):
            def changed(path):
                content = read_bytes(path)
                return content + b"changed" if path == base / name else content

            with self.subTest(name=name), patch.object(Path, "read_bytes", changed):
                with self.assertRaisesRegex(ValueError, "differs from its Prelude qualification"):
                    prelude_cases(ROOT)

    def test_stdout_stderr_and_exit_all_count(self):
        with tempfile.TemporaryDirectory() as name:
            image = Path(name) / "checker"
            image.write_text("#!/bin/sh\necho rows\necho outside >&2\nexit 2\n")
            image.chmod(0o700)
            good = Case("eta", b"input", b"frame", b"rows\n", b"outside\n", 2)
            self.assertTrue(compare(image, good)["matched"])
            for changed in [(b"row\n", b"outside\n", 2), (b"rows\n", b"", 2), (b"rows\n", b"outside\n", 0)]:
                with self.subTest(changed=changed):
                    self.assertFalse(compare(image, Case("eta", b"input", b"frame", *changed))["matched"])


if __name__ == "__main__":
    unittest.main()
