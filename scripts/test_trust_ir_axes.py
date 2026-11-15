#!/usr/bin/env python3
"""Trust-IR axis CLI input validation and artifact publication regressions."""

from __future__ import annotations

import copy
import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import trust_ir_axes as axes


SCRIPT = Path(axes.__file__).resolve()
BAD_COUNTS = (False, True, -1, 0.5, float("nan"), float("inf"), float("-inf"))
SET_CHANNELS = ("interpreter_agreed", "seam_agreed", "flip_backed")


class TrustIrAxesValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="trust-ir-axes-tests-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.measured_path = self.root / "measured.json"
        self.baseline_path = self.root / "baseline.json"
        self.compiler_path = self.root / "compiler.json"
        self.bodies_path = self.root / "bodies.json"
        self.coverage_path = self.root / "clean_kernel.coverage.json"
        self.log_path = self.root / "build.log"
        self.output_path = self.root / "output.json"
        self.compiler = {
            "version_stamp": "synthetic compiler identity A (no compiler runs)",
            "trustc_sha256": "a" * 64,
            "driver_sha256": "b" * 64,
        }
        self.new_compiler = dict(self.compiler, driver_sha256="c" * 64)
        self.measured = self.synthetic_measurement(2)
        self.coverage = json.loads(self.coverage_path.read_text(encoding="utf-8"))
        self.baseline = {
            "schema": "clean.trust_ir_build.baseline.v1",
            "measured": {
                key: self.measured["measured"][key]
                for key, direction, _source, _why in axes.AXES
                if direction != "record"
            },
            "compiler": self.compiler,
            "axis_updated": {},
            "updated_utc_date": "2026-11-13",
        }
        self.bodies = {
            "schema": axes.SCHEMA_BODIES,
            "updated_utc_date": "2026-11-13",
            **copy.deepcopy(self.measured["sets"]),
        }
        self.reset_inputs()

    def synthetic_measurement(self, count: int) -> dict:
        rows = []
        lines = []
        for n in range(count):
            index = n + 10
            digest = "sha256:" + f"{n + 1:064x}"
            name = f"clean_kernel::fixture_{n}"
            row = axes._row(index, name, digest, n)
            row["differentials"]["derived_mir"].update(
                verdict="agreed", markers_exact=True,
                markers_detail="1 marker line(s) identical",
            )
            row["differentials"]["interpreter"].update(verdict="agreed", samples=2)
            rows.append(row)
            lines.append(axes._flip_line(index, digest, name))
        return axes._measure_synthetic(rows, lines, self.root)

    @staticmethod
    def write_json(path: Path, value) -> None:
        # Deliberately permits nonfinite values in hostile fixtures. The CLI,
        # rather than this test's writer, must reject those input bytes.
        path.write_text(json.dumps(value) + "\n", encoding="utf-8")

    def reset_inputs(self) -> None:
        self.write_json(self.measured_path, self.measured)
        self.write_json(self.baseline_path, self.baseline)
        self.write_json(self.compiler_path, self.compiler)
        self.write_json(self.bodies_path, self.bodies)

    def cli(self, command: str, *, bodies: bool = False, write: bool = False):
        argv = [sys.executable, str(SCRIPT), command]
        if command == "measure":
            argv += ["--coverage", str(self.coverage_path), "--log", str(self.log_path),
                     "--out", str(self.output_path)]
        else:
            argv += ["--measured", str(self.measured_path),
                     "--baseline", str(self.baseline_path),
                     "--compiler", str(self.compiler_path)]
            if bodies:
                argv += ["--bodies", str(self.bodies_path)]
            if write:
                argv.append("--write")
        return subprocess.run(argv, text=True, capture_output=True, timeout=10)

    def assert_refused(self, result) -> None:
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Traceback (most recent call last)", result.stdout + result.stderr)

    def test_valid_measure_and_check(self) -> None:
        # Finite additive metadata is permitted; strict JSON is not a ban on
        # every floating-point value outside the count domains.
        self.measured["review_metadata"] = {"finite": 1.25}
        self.write_json(self.measured_path, self.measured)
        result = self.cli("check", bodies=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = self.cli("measure")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(self.output_path.read_text())["measured"],
                         self.measured["measured"])

    def test_valid_rebaseline_then_check(self) -> None:
        self.write_json(self.compiler_path, self.new_compiler)
        result = self.cli("rebaseline", bodies=True, write=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        baseline = json.loads(self.baseline_path.read_text())
        self.assertEqual(baseline["compiler"]["driver_sha256"], "c" * 64)
        self.assertEqual(baseline["measured"], self.baseline["measured"])
        self.assertEqual(json.loads(self.bodies_path.read_text())["flip_backed"],
                         self.measured["sets"]["flip_backed"])
        result = self.cli("check", bodies=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_valid_tighten_then_check(self) -> None:
        improved = self.synthetic_measurement(3)
        self.write_json(self.measured_path, improved)
        result = self.cli("tighten", bodies=True, write=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(self.baseline_path.read_text())["measured"]["lowered"], 3)
        result = self.cli("check", bodies=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    @unittest.skipUnless(os.name == "posix", "requires POSIX file creation modes")
    def test_new_sidecar_honors_umask_and_preserves_existing_baseline_mode(self) -> None:
        for mask in (0o022, 0o077):
            with self.subTest(umask=oct(mask)):
                self.reset_inputs()
                self.baseline_path.chmod(0o640)
                self.bodies_path.unlink()
                self.write_json(self.compiler_path, self.new_compiler)
                previous_mask = os.umask(mask)
                try:
                    result = self.cli("rebaseline", bodies=True, write=True)
                finally:
                    os.umask(previous_mask)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(stat.S_IMODE(self.baseline_path.stat().st_mode), 0o640)
                self.assertEqual(stat.S_IMODE(self.bodies_path.stat().st_mode), 0o666 & ~mask)
                baseline = json.loads(self.baseline_path.read_text())
                self.assertEqual(baseline["compiler"]["driver_sha256"], self.new_compiler["driver_sha256"])
                self.assertEqual(baseline["measured"], self.baseline["measured"])
                sidecar = json.loads(self.bodies_path.read_text())
                self.assertEqual(sidecar["schema"], axes.SCHEMA_BODIES)
                for channel in SET_CHANNELS:
                    self.assertEqual(sidecar[channel], self.measured["sets"][channel])
                result = self.cli("check", bodies=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    @unittest.skipUnless(os.name == "posix" and hasattr(os, "geteuid") and os.geteuid() != 0,
                         "requires an ordinary POSIX UID respecting file write permissions")
    def test_read_only_output_refusal_preserves_both_artifacts(self) -> None:
        for target in (self.baseline_path, self.bodies_path):
            with self.subTest(read_only=target.name):
                self.reset_inputs()
                self.write_json(self.compiler_path, self.new_compiler)
                original_mode = stat.S_IMODE(target.stat().st_mode)
                target.chmod(0o444)
                try:
                    before = {path: (path.read_bytes(), stat.S_IMODE(path.stat().st_mode))
                              for path in (self.baseline_path, self.bodies_path)}
                    result = self.cli("rebaseline", bodies=True, write=True)
                    for path, (contents, mode) in before.items():
                        self.assertEqual(path.read_bytes(), contents)
                        self.assertEqual(stat.S_IMODE(path.stat().st_mode), mode)
                    self.assert_refused(result)
                finally:
                    target.chmod(original_mode)

    @unittest.skipUnless(hasattr(os, "pathconf"), "requires filesystem NAME_MAX discovery")
    def test_legal_name_max_baseline_and_sidecar_paths(self) -> None:
        limit = os.pathconf(self.root, "PC_NAME_MAX")
        self.assertGreater(limit, len(".json"))
        self.baseline_path = self.root / ("b" * (limit - len(".json")) + ".json")
        self.bodies_path = self.root / ("s" * (limit - len(".json")) + ".json")
        self.assertEqual(len(os.fsencode(self.baseline_path.name)), limit)
        self.assertEqual(len(os.fsencode(self.bodies_path.name)), limit)
        self.write_json(self.baseline_path, self.baseline)
        self.baseline_path.chmod(0o600)
        self.assertFalse(self.bodies_path.exists())
        self.write_json(self.compiler_path, self.new_compiler)
        result = self.cli("rebaseline", bodies=True, write=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(stat.S_IMODE(self.baseline_path.stat().st_mode), 0o600)
        baseline = json.loads(self.baseline_path.read_text())
        self.assertEqual(baseline["compiler"]["driver_sha256"], self.new_compiler["driver_sha256"])
        self.assertEqual(baseline["measured"], self.baseline["measured"])
        sidecar = json.loads(self.bodies_path.read_text())
        self.assertEqual(sidecar["schema"], axes.SCHEMA_BODIES)
        for channel in SET_CHANNELS:
            self.assertEqual(sidecar[channel], self.measured["sets"][channel])
        result = self.cli("check", bodies=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_missing_baseline_axis_remains_unbaselined(self) -> None:
        baseline = copy.deepcopy(self.baseline)
        del baseline["measured"]["lowered"]
        self.write_json(self.baseline_path, baseline)
        result = self.cli("check")
        self.assert_refused(result)
        self.assertIn("UNBASELINED", result.stdout + result.stderr)

    def test_count_axes_require_exact_nonnegative_integers(self) -> None:
        count_axes = [key for key, direction, _source, _why in axes.AXES
                      if direction != "pin"]
        for key in count_axes:
            for value in BAD_COUNTS:
                with self.subTest(axis=key, value=repr(value)):
                    measured = copy.deepcopy(self.measured)
                    measured["measured"][key] = value
                    self.write_json(self.measured_path, measured)
                    self.assert_refused(self.cli("check"))

    def test_invariants_require_exact_nonnegative_integers(self) -> None:
        for key, _why in axes.FATAL_INVARIANTS:
            for value in BAD_COUNTS:
                with self.subTest(invariant=key, value=repr(value)):
                    measured = copy.deepcopy(self.measured)
                    measured["invariants"][key] = value
                    self.write_json(self.measured_path, measured)
                    self.assert_refused(self.cli("check"))

    def test_boolean_pins_require_actual_booleans(self) -> None:
        for key in ("proof_authority", "native_verification_requests"):
            for value in (0, 1, 0.0, "false", None):
                for command in ("check", "rebaseline"):
                    with self.subTest(pin=key, value=value, command=command):
                        measured = copy.deepcopy(self.measured)
                        measured["measured"][key] = value
                        self.write_json(self.measured_path, measured)
                        self.write_json(self.compiler_path,
                                        self.new_compiler if command == "rebaseline" else self.compiler)
                        self.assert_refused(self.cli(command))

    def test_mutating_commands_refuse_invalid_counts_without_writes(self) -> None:
        for command in ("tighten", "rebaseline"):
            for key, value in (("mismatch", -1), ("mismatch", False),
                               ("lowered", 2.5), ("lowered", float("inf"))):
                with self.subTest(command=command, axis=key, value=repr(value)):
                    self.reset_inputs()
                    measured = copy.deepcopy(self.measured)
                    measured["measured"][key] = value
                    self.write_json(self.measured_path, measured)
                    self.write_json(self.compiler_path,
                                    self.new_compiler if command == "rebaseline" else self.compiler)
                    before = (self.baseline_path.read_bytes(), self.bodies_path.read_bytes())
                    result = self.cli(command, bodies=True, write=True)
                    self.assertEqual((self.baseline_path.read_bytes(), self.bodies_path.read_bytes()), before)
                    self.assert_refused(result)

    def test_missing_measured_count_or_invariant_is_refused(self) -> None:
        for section, key in (("measured", "lowered"), ("measured", "bodies"),
                             ("invariants", axes.FATAL_INVARIANTS[0][0])):
            with self.subTest(section=section, key=key):
                measured = copy.deepcopy(self.measured)
                del measured[section][key]
                self.write_json(self.measured_path, measured)
                self.assert_refused(self.cli("check"))

    def test_malformed_baseline_counts_are_not_comparison_thresholds(self) -> None:
        for value in BAD_COUNTS:
            with self.subTest(value=repr(value)):
                baseline = copy.deepcopy(self.baseline)
                baseline["measured"]["lowered"] = value
                self.write_json(self.baseline_path, baseline)
                self.assert_refused(self.cli("check"))

    def test_json_loader_refuses_duplicate_members_in_every_input(self) -> None:
        for target in (self.measured_path, self.baseline_path, self.compiler_path):
            with self.subTest(input=target.name):
                self.reset_inputs()
                raw = target.read_text()
                target.write_text('{"review_metadata": 7, "review_metadata": 0, ' + raw.lstrip()[1:])
                self.assert_refused(self.cli("check"))
        raw = json.dumps(self.coverage)
        self.coverage_path.write_text('{"review_metadata": 7, "review_metadata": 0, ' + raw[1:])
        self.assert_refused(self.cli("measure"))

    def test_json_loader_refuses_nonfinite_values_even_in_metadata(self) -> None:
        for target in (self.measured_path, self.baseline_path, self.compiler_path):
            for literal in ("NaN", "Infinity", "-Infinity", "1e309"):
                with self.subTest(input=target.name, literal=literal):
                    self.reset_inputs()
                    raw = target.read_text()
                    target.write_text('{"review_metadata": ' + literal + ", " + raw.lstrip()[1:])
                    self.assert_refused(self.cli("check"))
        for literal in ("NaN", "Infinity", "-Infinity", "1e309"):
            with self.subTest(input="coverage", literal=literal):
                raw = json.dumps(self.coverage)
                self.coverage_path.write_text('{"review_metadata": ' + literal + ", " + raw[1:])
                self.assert_refused(self.cli("measure"))

    def test_supported_measured_schemas_are_required(self) -> None:
        for command in ("check", "tighten", "rebaseline"):
            for section, key in ((None, "schema_self"), ("measured", "schema")):
                for value in (None, "unrecognized.schema.v999"):
                    with self.subTest(command=command, section=section, value=value):
                        self.reset_inputs()
                        measured = copy.deepcopy(self.measured)
                        target = measured if section is None else measured[section]
                        if value is None:
                            del target[key]
                        else:
                            target[key] = value
                        self.write_json(self.measured_path, measured)
                        if command == "rebaseline":
                            self.write_json(self.compiler_path, self.new_compiler)
                        self.assert_refused(self.cli(command))

    def test_measure_refuses_unknown_coverage_schema(self) -> None:
        coverage = copy.deepcopy(self.coverage)
        coverage["schema"] = "unrecognized.coverage.v999"
        self.write_json(self.coverage_path, coverage)
        self.assert_refused(self.cli("measure"))

    def test_measure_refuses_duplicate_def_index(self) -> None:
        coverage = copy.deepcopy(self.coverage)
        first, second = coverage["bodies"]
        second["def_index"] = first["def_index"]
        self.write_json(self.coverage_path, coverage)
        self.log_path.write_text(axes._flip_line(first["def_index"], second["lineage"],
                                               second["def_path"]) + "\n")
        self.assert_refused(self.cli("measure"))

    def test_duplicate_def_paths_remain_a_valid_multiset(self) -> None:
        coverage = copy.deepcopy(self.coverage)
        name = coverage["bodies"][0]["def_path"]
        coverage["bodies"][1]["def_path"] = name
        self.write_json(self.coverage_path, coverage)
        self.log_path.write_text("\n".join(
            axes._flip_line(row["def_index"], row["lineage"], row["def_path"])
            for row in coverage["bodies"]
        ) + "\n")
        result = self.cli("measure")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        measured = json.loads(self.output_path.read_text())
        self.assertEqual(measured["sets"]["interpreter_agreed"].count(name), 2)

    def test_measure_does_not_coerce_sample_counts(self) -> None:
        for value in BAD_COUNTS:
            with self.subTest(value=repr(value)):
                coverage = copy.deepcopy(self.coverage)
                coverage["bodies"][0]["differentials"]["interpreter"]["samples"] = value
                self.write_json(self.coverage_path, coverage)
                self.assert_refused(self.cli("measure"))

    def test_invalid_sidecar_sets_leave_both_outputs_unchanged(self) -> None:
        cases = ("missing", None, {}, {key: "not-a-list" for key in SET_CHANNELS},
                 {key: [7] for key in SET_CHANNELS})
        for command in ("tighten", "rebaseline"):
            for value in cases:
                with self.subTest(command=command, sets=value):
                    self.reset_inputs()
                    measured = copy.deepcopy(self.measured)
                    if value == "missing":
                        del measured["sets"]
                    else:
                        measured["sets"] = value
                    self.write_json(self.measured_path, measured)
                    if command == "rebaseline":
                        self.write_json(self.compiler_path, self.new_compiler)
                    before = (self.baseline_path.read_bytes(), self.bodies_path.read_bytes())
                    result = self.cli(command, bodies=True, write=True)
                    self.assertEqual((self.baseline_path.read_bytes(), self.bodies_path.read_bytes()), before)
                    self.assert_refused(result)

    def test_second_replace_failure_rolls_back_first_artifact(self) -> None:
        original = {self.baseline_path: self.baseline_path.read_bytes(),
                    self.bodies_path: self.bodies_path.read_bytes()}
        replacements = {self.baseline_path: "new baseline\n", self.bodies_path: "new sidecar\n"}
        expected = {path.resolve(): text for path, text in replacements.items()}
        real_replace = os.replace
        calls = 0
        first_target = None

        def fail_second(source, destination):
            nonlocal calls, first_target
            calls += 1
            destination = Path(destination)
            if calls == 1:
                first_target = destination
                return real_replace(source, destination)
            if calls == 2:
                self.assertIsNotNone(first_target)
                self.assertEqual(first_target.read_text(), expected[first_target.resolve()])
                raise OSError("injected second artifact publication failure")
            return real_replace(source, destination)

        with mock.patch.object(axes.os, "replace", side_effect=fail_second):
            with self.assertRaises(OSError):
                axes._write_artifacts(replacements)
        self.assertGreaterEqual(calls, 2)
        for path, before in original.items():
            self.assertEqual(path.read_bytes(), before)

    def test_interrupted_rollback_keeps_the_original_preimage(self) -> None:
        original = {self.baseline_path.resolve(): self.baseline_path.read_bytes(),
                    self.bodies_path.resolve(): self.bodies_path.read_bytes()}
        replacements = {self.baseline_path: "new baseline\n", self.bodies_path: "new sidecar\n"}
        expected = {path.resolve(): text.encode("utf-8") for path, text in replacements.items()}
        before_files = {path.resolve() for path in self.root.rglob("*") if path.is_file()}
        real_replace = os.replace
        calls = 0
        first_target = second_target = None

        def interrupt_rollback(source, destination):
            nonlocal calls, first_target, second_target
            calls += 1
            destination = Path(destination).resolve()
            if calls == 1:
                first_target = destination
                return real_replace(source, destination)
            if calls == 2:
                second_target = destination
                self.assertEqual(first_target.read_bytes(), expected[first_target])
                raise OSError("injected second artifact publication failure")
            if calls == 3:
                self.assertEqual(Path(source).read_bytes(), original[destination])
                raise KeyboardInterrupt("injected interruption during rollback")
            return real_replace(source, destination)

        with mock.patch.object(axes.os, "replace", side_effect=interrupt_rollback):
            with self.assertRaises(KeyboardInterrupt):
                axes._write_artifacts(replacements)
        self.assertGreaterEqual(calls, 3)
        recovery_files = {path.resolve() for path in self.root.rglob("*") if path.is_file()} - before_files
        self.assertTrue(any(path.read_bytes() == original[first_target] for path in recovery_files),
                        "interrupted rollback must retain the original baseline preimage")
        self.assertIn(first_target.read_bytes(), (original[first_target], expected[first_target]))
        self.assertEqual(second_target.read_bytes(), original[second_target])

    def test_interrupt_after_first_install_restores_or_retains_its_preimage(self) -> None:
        for interrupt_restore in (False, True):
            with self.subTest(interrupt_restore=interrupt_restore):
                self.reset_inputs()
                original = {self.baseline_path.resolve(): self.baseline_path.read_bytes(),
                            self.bodies_path.resolve(): self.bodies_path.read_bytes()}
                replacements = {self.baseline_path: "new baseline\n", self.bodies_path: "new sidecar\n"}
                before_paths = {path.resolve() for path in self.root.rglob("*")}
                real_replace = os.replace
                calls = 0
                first_target = None

                def interrupt_after_install(source, destination):
                    nonlocal calls, first_target
                    calls += 1
                    destination = Path(destination).resolve()
                    if calls == 1:
                        first_target = destination
                        real_replace(source, destination)
                        self.assertEqual(destination.read_bytes(), b"new baseline\n")
                        raise KeyboardInterrupt("injected interruption after first install took effect")
                    if interrupt_restore and calls == 2:
                        self.assertEqual(destination, first_target)
                        self.assertEqual(Path(source).read_bytes(), original[first_target])
                        raise KeyboardInterrupt("injected interruption while restoring first artifact")
                    return real_replace(source, destination)

                with mock.patch.object(axes.os, "replace", side_effect=interrupt_after_install):
                    with self.assertRaises(KeyboardInterrupt):
                        axes._write_artifacts(replacements)
                self.assertEqual(self.bodies_path.read_bytes(), original[self.bodies_path.resolve()])
                after_paths = {path.resolve() for path in self.root.rglob("*")}
                if interrupt_restore:
                    self.assertGreaterEqual(calls, 2)
                    recovery_files = {path for path in after_paths - before_paths if path.is_file()}
                    self.assertTrue(any(path.read_bytes() == original[first_target] for path in recovery_files),
                                    "post-effect interruption must leave the original baseline recoverable")
                else:
                    for path, before in original.items():
                        self.assertEqual(path.read_bytes(), before)
                    self.assertEqual(after_paths, before_paths, "successful rollback must clean staging files and directories")


if __name__ == "__main__":
    unittest.main()
