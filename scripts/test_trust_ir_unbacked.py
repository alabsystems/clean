#!/usr/bin/env python3
"""Regression tests for the unbacked trust-ir flip census."""

from __future__ import annotations

import copy
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

import trust_ir_unbacked


def _digest(n: int) -> str:
    return "sha256:" + f"{n:064x}"


def _row(
    index: int,
    name: str,
    *,
    interpreter: str,
    seam: dict | None = None,
) -> dict:
    return {
        "def_path": name,
        "def_index": index,
        "func_id": index,
        "lineage": _digest(index),
        "instr_count": 4,
        "differentials": {
            "interpreter": {
                "verdict": interpreter,
                "samples": 1 if interpreter == "agreed" else 0,
                "detail": (
                    "1 sample(s) agreed"
                    if interpreter == "agreed"
                    else "non-scalar parameter type is non-interpretable "
                    "(coverage-only skip)"
                ),
            },
            "seam": seam,
            "derived_mir": {
                "verdict": "agreed",
                "markers_exact": True,
                "markers_detail": "1 marker line(s) identical",
            },
        },
    }


class TrustIrUnbackedTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.coverage = self.root / "clean_kernel.coverage.json"
        self.log = self.root / "build.log"
        self.dump = self.root / "clean_kernel.trust-ir.txt"

        rows = [
            _row(10, "clean_kernel::backed", interpreter="agreed"),
            _row(11, "clean_kernel::unbacked", interpreter="not-run"),
            _row(
                12,
                "clean_kernel::seam_backed",
                interpreter="not-run",
                seam={"state": "resolved", "verdict": "agreed", "samples": 2},
            ),
        ]
        artifact = {
            "schema": "trust.thir-lower.crate-module.coverage.v2",
            "crate": "clean_kernel",
            "direct_obligation_capability": "structural-parity-only-v1",
            "proof_authority": False,
            "native_verification_requests": False,
            "totals": {
                "bodies": len(rows),
                "lowered": len(rows),
                "symbolic": 0,
                "spliced": len(rows),
                "declarations": 0,
                "initializer_bodies": 0,
                "instr_count": 12,
                "unsupported": 0,
                "calls": {"resolved": 0, "extern_decls": 0, "unresolved": 0},
            },
            "bodies": rows,
        }
        self.coverage.write_text(json.dumps(artifact), encoding="utf-8")
        self.log.write_text(
            "\n".join(
                [
                    self._event(10),
                    self._event(11),
                    self._event(11),
                    self._event(12, ctfe=True),
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        self.dump.write_text(
            """functy.7 = (ptr, (ty.1, ty.2)) -> bool
rustcc fn @clean_kernel::unbacked(functy.7) {
bb0(%0: ptr, %1: (ty.1, ty.2)):
    %2 = load u8, ptr %0
    ret %2
}
""",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temp.cleanup()

    @staticmethod
    def _event(index: int, *, ctfe: bool = False) -> str:
        prefix = "CTFE " if ctfe else ""
        return (
            "INFO rustc_mir_transform::trust_ir_flip trust-ir-flip: "
            f"{prefix}compiled from trust-ir, "
            f"did=DefId(0:{index} ~ clean_kernel[abcd]::f{index}), "
            f"asserts=0, lineage={_digest(index)}, flipped_so_far=1"
        )

    def test_event_multiplicity_matches_the_authoritative_axis(self) -> None:
        data = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), str(self.dump)
        )

        self.assertEqual(data["flip_events"], 3)
        self.assertEqual(data["flip_def_ids"], 2)
        self.assertEqual(data["backed"], 1)
        self.assertEqual(data["unbacked"], 2)
        self.assertEqual(data["unbacked_def_ids"], 1)
        self.assertEqual(data["unbacked_flips"][0]["event_count"], 2)
        self.assertEqual(
            data["unbacked_flips"][0]["signature"],
            "(ptr, (ty.1, ty.2)) -> bool",
        )
        self.assertEqual(
            data["unbacked_flips"][0]["entry_params"],
            [
                {
                    "value_id": 0,
                    "type": "ptr",
                    "scalar_leaf": False,
                    "mentioned_after_entry": True,
                },
                {
                    "value_id": 1,
                    "type": "(ty.1, ty.2)",
                    "scalar_leaf": False,
                    "mentioned_after_entry": False,
                },
            ],
        )
        self.assertEqual(
            trust_ir_unbacked.check(
                data, str(self.coverage), str(self.log), str(self.dump)
            ),
            [],
        )

    def test_ctfe_channel_uses_the_same_backing_join(self) -> None:
        data = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), ctfe=True
        )
        self.assertEqual(data["flip_events"], 1)
        self.assertEqual(data["backed"], 1)
        self.assertEqual(data["unbacked"], 0)
        self.assertEqual(
            trust_ir_unbacked.check(
                data, str(self.coverage), str(self.log), None
            ),
            [],
        )

    def test_malformed_event_is_unparsed_not_foreign_and_check_refuses(self) -> None:
        with self.log.open("a", encoding="utf-8") as handle:
            handle.write("trust-ir-flip: compiled from trust-ir, malformed\n")

        data = trust_ir_unbacked.census(str(self.coverage), str(self.log))
        self.assertEqual(data["flip_events_unparsed"], 1)
        self.assertEqual(data["foreign_flip_events"], 0)
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), None
        )
        self.assertIn(
            "trust_ir_axes invariant flip_events_unparsed=1",
            errors,
        )

    def test_unjoinable_event_is_counted_per_event(self) -> None:
        with self.log.open("a", encoding="utf-8") as handle:
            handle.write(self._event(99) + "\n")
            handle.write(self._event(99) + "\n")

        data = trust_ir_unbacked.census(str(self.coverage), str(self.log))
        self.assertEqual(data["flip_events_unjoinable"], 2)
        self.assertEqual(data["flip_def_ids_unjoinable"], 1)
        self.assertEqual(
            data["backed"] + data["unbacked"] + data["flip_events_unjoinable"],
            data["flip_events"],
        )
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), None
        )
        self.assertIn(
            "trust_ir_axes invariant flip_events_unjoinable=2",
            errors,
        )

    def test_duplicate_coverage_indexes_are_refused_explicitly(self) -> None:
        artifact = json.loads(self.coverage.read_text(encoding="utf-8"))
        artifact["bodies"].append(dict(artifact["bodies"][1]))
        artifact["totals"]["bodies"] += 1
        self.coverage.write_text(json.dumps(artifact), encoding="utf-8")

        data = trust_ir_unbacked.census(str(self.coverage), str(self.log))
        self.assertEqual(data["coverage_def_index_collisions"], [11])
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), None
        )
        self.assertIn("coverage has duplicate def_index rows: 11", errors)

    def test_checked_dump_requires_every_unbacked_body_to_join(self) -> None:
        self.dump.write_text(
            """functy.7 = () -> bool
rustcc fn @clean_kernel::another_body(functy.7) {
bb0():
    ret
}
""",
            encoding="utf-8",
        )

        data = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), str(self.dump)
        )
        self.assertEqual(data["ir_dump_unjoinable"], ["clean_kernel::unbacked"])
        errors = trust_ir_unbacked.check(
            data, str(self.coverage), str(self.log), str(self.dump)
        )
        self.assertIn(
            "unbacked rows absent or unparsable in IR dump: clean_kernel::unbacked",
            errors,
        )

    def test_a_ws43_quoted_dump_joins_by_the_decoded_name(self) -> None:
        # M2 (2026-09-27): trust-ir WS4.3 prints a non-bare name QUOTED. The
        # same dump so printed joins every unbacked row by its NAME, with the
        # same signature and entry parameters; the regex this reader replaced
        # kept the quotes, so the row was reported unjoinable.
        legacy = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), str(self.dump)
        )
        quoted_text = trust_ir_unbacked.tir_symbols.respell_ws43(self.dump.read_text())
        self.assertIn('rustcc fn @"clean_kernel::unbacked"(functy.7) {', quoted_text)
        self.dump.write_text(quoted_text, encoding="utf-8")
        quoted = trust_ir_unbacked.census(
            str(self.coverage), str(self.log), str(self.dump)
        )
        self.assertEqual(quoted["ir_dump_unjoinable"], [])
        self.assertEqual(legacy["ir_dump_unjoinable"], [])
        self.assertEqual(quoted["unbacked_flips"], legacy["unbacked_flips"])
        self.assertTrue(any(row["signature"] and row["entry_params"]
                            for row in quoted["unbacked_flips"]))

    def test_a_dump_no_trust_ir_printer_wrote_is_refused(self) -> None:
        quoted_text = trust_ir_unbacked.tir_symbols.respell_ws43(self.dump.read_text())
        for text, needle in (
            (quoted_text + "rustcc fn @clean_kernel::raw<'_>(functy.7) {\n}\n", "mixes a QUOTED"),
            (quoted_text.replace('"clean_kernel::unbacked"', '"clean_kernel\\qunbacked"'),
             "is not one the trust-ir printer emits"),
        ):
            self.dump.write_text(text, encoding="utf-8")
            with self.assertRaises(trust_ir_unbacked.DumpRefused) as raised:
                trust_ir_unbacked.census(str(self.coverage), str(self.log), str(self.dump))
            self.assertIn(needle, str(raised.exception))

    def test_checked_cli_writes_only_after_validation_succeeds(self) -> None:
        output = self.root / "checked.json"
        command = [
            sys.executable,
            trust_ir_unbacked.__file__,
            "--coverage",
            str(self.coverage),
            "--log",
            str(self.log),
            "--check",
            "--json",
            str(output),
        ]
        completed = subprocess.run(command, check=False, capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertTrue(output.is_file())
        self.assertEqual(json.loads(output.read_text())["schema"], trust_ir_unbacked.SCHEMA)

        with self.log.open("a", encoding="utf-8") as handle:
            handle.write("trust-ir-flip: compiled from trust-ir, malformed\n")
        refused = self.root / "refused.json"
        command[-1] = str(refused)
        completed = subprocess.run(command, check=False, capture_output=True, text=True)
        self.assertEqual(completed.returncode, 1)
        self.assertIn("flip_events_unparsed=1", completed.stderr)
        self.assertFalse(refused.exists())

    def _json_command(self, output: Path, *, checked: bool) -> list[str]:
        command = [
            sys.executable,
            trust_ir_unbacked.__file__,
            "--coverage", str(self.coverage),
            "--log", str(self.log),
            "--ir-dump", str(self.dump),
            "--json", str(output),
        ]
        if checked:
            command.append("--check")
        return command

    def test_separate_json_output_preserves_inputs_in_both_modes(self) -> None:
        before = {path: path.read_bytes() for path in (self.coverage, self.log, self.dump)}
        for checked in (False, True):
            with self.subTest(checked=checked):
                output = self.root / ("checked.json" if checked else "default.json")
                output.write_bytes(b"previous receipt\n")
                result = subprocess.run(self._json_command(output, checked=checked),
                                        cwd=self.root, capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                data = json.loads(output.read_text())
                self.assertEqual(data["schema"], trust_ir_unbacked.SCHEMA)
                self.assertEqual(data["unbacked"], 2)
                self.assertEqual({path: path.read_bytes() for path in before}, before)
                if checked:
                    self.assertIn("CHECK PASS", result.stdout)

    def test_json_input_aliases_refuse_without_changing_any_input(self) -> None:
        inputs = (self.coverage, self.log, self.dump)
        before = {path: path.read_bytes() for path in inputs}
        (self.root / "relative-dir").mkdir()
        for checked in (False, True):
            for target in inputs:
                for kind in ("identical", "relative", "symlink", "hardlink"):
                    with self.subTest(checked=checked, input=target.name, alias=kind):
                        alias = None
                        if kind == "identical":
                            output = target
                        elif kind == "relative":
                            output = Path("relative-dir") / ".." / target.name
                        else:
                            alias = self.root / (kind + "-output.json")
                            if kind == "symlink":
                                alias.symlink_to(target)
                            else:
                                os.link(target, alias)
                            output = alias
                        try:
                            result = subprocess.run(self._json_command(output, checked=checked),
                                                    cwd=self.root, capture_output=True,
                                                    text=True, timeout=10)
                            self.assertEqual({path: path.read_bytes() for path in inputs}, before)
                            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                            self.assertNotIn("Traceback (most recent call last)",
                                             result.stdout + result.stderr)
                            self.assertNotIn("CHECK PASS", result.stdout)
                            if alias is not None:
                                self.assertEqual(alias.read_bytes(), before[target])
                                if kind == "symlink":
                                    self.assertTrue(alias.is_symlink())
                                else:
                                    self.assertTrue(os.path.samefile(alias, target))
                        finally:
                            if alias is not None:
                                alias.unlink(missing_ok=True)
                            for path, contents in before.items():
                                path.write_bytes(contents)

    def test_failed_checked_publication_preserves_previous_receipt(self) -> None:
        output = self.root / "previous.json"
        output.write_bytes(b"previous receipt\n")
        inputs = (self.coverage, self.log, self.dump)
        before = {path: path.read_bytes() for path in (*inputs, output)}
        before_paths = {path.resolve() for path in self.root.rglob("*")}
        real_replace = os.replace
        calls = 0

        def fail_first_replace(source, destination):
            nonlocal calls
            calls += 1
            if calls == 1:
                raise OSError("injected census publication failure")
            return real_replace(source, destination)

        stdout, stderr = io.StringIO(), io.StringIO()
        with mock.patch.object(sys, "argv", self._json_command(output, checked=True)[1:]), \
                mock.patch.object(trust_ir_unbacked.trust_ir_axes.os, "replace", side_effect=fail_first_replace), \
                redirect_stdout(stdout), redirect_stderr(stderr):
            status = trust_ir_unbacked.main()
        self.assertGreaterEqual(calls, 1, "publication must exercise the failing shared atomic writer")
        self.assertNotEqual(status, 0)
        self.assertNotIn("CHECK PASS", stdout.getvalue())
        self.assertNotIn("Traceback (most recent call last)", stdout.getvalue() + stderr.getvalue())
        self.assertEqual({path: path.read_bytes() for path in before}, before)
        self.assertEqual({path.resolve() for path in self.root.rglob("*")}, before_paths)

    def _assert_bad_coverage_preserves_inputs_and_receipt(self, raw: str, *, checked: bool) -> None:
        self.coverage.write_text(raw, encoding="utf-8")
        output = self.root / "refused-input.json"
        output.write_bytes(b"previous receipt\n")
        before = {path: path.read_bytes() for path in (self.coverage, self.log, self.dump, output)}
        before_paths = {path.resolve() for path in self.root.rglob("*")}
        result = subprocess.run(self._json_command(output, checked=checked), cwd=self.root,
                                capture_output=True, text=True, timeout=10)
        self.assertEqual({path: path.read_bytes() for path in before}, before)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("CHECK PASS", result.stdout)
        self.assertNotIn("Traceback (most recent call last)", result.stdout + result.stderr)
        self.assertEqual({path.resolve() for path in self.root.rglob("*")}, before_paths)

    def test_nonfinite_json_refuses_in_both_modes_including_unused_metadata(self) -> None:
        original = json.loads(self.coverage.read_text())
        for checked in (False, True):
            for location in ("metadata", "unbacked-row"):
                for literal in ("NaN", "Infinity", "-Infinity", "1e999", "-1e999"):
                    with self.subTest(checked=checked, location=location, literal=literal):
                        coverage = copy.deepcopy(original)
                        if location == "metadata":
                            coverage["review_metadata"] = {"unused": "HOSTILE_NUMBER"}
                        else:
                            coverage["bodies"][1]["instr_count"] = "HOSTILE_NUMBER"
                        raw = json.dumps(coverage).replace('"HOSTILE_NUMBER"', literal, 1)
                        self._assert_bad_coverage_preserves_inputs_and_receipt(raw, checked=checked)

    def test_duplicate_json_members_refuse_in_both_modes(self) -> None:
        raw = self.coverage.read_text()
        duplicates = (
            '{"review_metadata": 7, "review_metadata": 0, ' + raw.lstrip()[1:],
            raw.replace('"def_index": 11', '"def_index": 999, "def_index": 11', 1),
        )
        self.assertNotEqual(duplicates[1], raw)
        for checked in (False, True):
            for case, duplicate in enumerate(duplicates):
                with self.subTest(checked=checked, duplicate=case):
                    self._assert_bad_coverage_preserves_inputs_and_receipt(duplicate, checked=checked)

    def test_invalid_def_index_refuses_without_coercion_in_both_modes(self) -> None:
        original = json.loads(self.coverage.read_text())
        cases = (False, True, 11.75, 11.0, "11", -1, None, "MISSING")
        for checked in (False, True):
            for value in cases:
                with self.subTest(checked=checked, value=repr(value)):
                    coverage = copy.deepcopy(original)
                    if value == "MISSING":
                        del coverage["bodies"][1]["def_index"]
                    else:
                        coverage["bodies"][1]["def_index"] = value
                    self._assert_bad_coverage_preserves_inputs_and_receipt(
                        json.dumps(coverage), checked=checked)

    def test_malformed_json_syntax_is_a_clean_refusal_in_both_modes(self) -> None:
        for checked in (False, True):
            for raw in ('{"schema":', '{"bodies": [],}', "not JSON"):
                with self.subTest(checked=checked, malformed=raw):
                    self._assert_bad_coverage_preserves_inputs_and_receipt(raw, checked=checked)

    def test_finite_unused_metadata_remains_accepted_in_both_modes(self) -> None:
        coverage = json.loads(self.coverage.read_text())
        coverage["review_metadata"] = {"unused": 1.25}
        self.coverage.write_text(json.dumps(coverage), encoding="utf-8")
        before = {path: path.read_bytes() for path in (self.coverage, self.log, self.dump)}
        for checked in (False, True):
            with self.subTest(checked=checked):
                output = self.root / ("finite-checked.json" if checked else "finite-default.json")
                result = subprocess.run(self._json_command(output, checked=checked), cwd=self.root,
                                        capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                data = json.loads(output.read_text(), parse_constant=lambda value: self.fail(value))
                self.assertEqual(data["schema"], trust_ir_unbacked.SCHEMA)
                self.assertEqual(data["unbacked"], 2)
                self.assertEqual({path: path.read_bytes() for path in before}, before)
                if checked:
                    self.assertIn("CHECK PASS", result.stdout)

    def test_nonfinite_census_result_cannot_replace_previous_receipt(self) -> None:
        data = trust_ir_unbacked.census(str(self.coverage), str(self.log), str(self.dump))
        data["unbacked_flips"][0]["instr_count"] = float("nan")
        for checked in (False, True):
            with self.subTest(checked=checked):
                output = self.root / "serialization-failure.json"
                output.write_bytes(b"previous receipt\n")
                before = {path: path.read_bytes() for path in (self.coverage, self.log, self.dump, output)}
                before_paths = {path.resolve() for path in self.root.rglob("*")}
                stdout, stderr = io.StringIO(), io.StringIO()
                with mock.patch.object(sys, "argv", self._json_command(output, checked=checked)[1:]), \
                        mock.patch.object(trust_ir_unbacked, "census", return_value=copy.deepcopy(data)), \
                        redirect_stdout(stdout), redirect_stderr(stderr):
                    status = trust_ir_unbacked.main()
                self.assertEqual({path: path.read_bytes() for path in before}, before)
                self.assertNotEqual(status, 0)
                self.assertNotIn("CHECK PASS", stdout.getvalue())
                self.assertNotIn("Traceback (most recent call last)", stdout.getvalue() + stderr.getvalue())
                self.assertEqual({path.resolve() for path in self.root.rglob("*")}, before_paths)


if __name__ == "__main__":
    unittest.main()
