#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Isolation controls for the real-input arms; never mutate the checkout."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import check_extend_constants_ratchet as gate


SNAPSHOT = Path("crates/clean-kernel/src/env/snapshot.rs")
LEDGER_SITE = Path("crates/c/src/ledger.rs")


class ScannerIsolationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="extend_isolation_test_")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name).resolve()
        self.root = self.base / "source"
        (self.root / ".git").mkdir(parents=True)
        self.write(SNAPSHOT, "pub fn ordinary() {}\n")
        self.write(LEDGER_SITE, gate.PLANT_JUSTIFIED)
        self.write("crates/c/src/lib.rs", "mod ledger;\n")
        self.write(gate.RATCHET_REL, json.dumps({"extend_constants": {
            "unchecked_production_count": 1,
            "structural_production_count": 0,
            "production_sites": [{"file": str(LEDGER_SITE),
                                  "method": "extend_constants_unchecked",
                                  "occurrences": 1}],
            "test_excluded_sites": [],
        }}))
        self.copy = self.base / "copy"
        self.copy.mkdir()
        self.lock = self.base / "selftest.lock"

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def arms(self, clean=True):
        output = io.StringIO()
        with mock.patch.object(gate, "_git_clean", return_value=clean), \
                contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            result = gate._standing_plant_arms(self.root, self.lock)
        return result, output.getvalue()

    def test_copy_preserves_every_source_and_real_ledger_without_caches(self):
        self.write("crates/c/src/not_tracked.rs", "// module classifier input, no bypass\n")
        self.write("target/cache/artifact.rs", "not a scanner input")
        self.write("data/unrelated.json", "not a scanner input")
        before = gate._scanner_input_state(self.root)
        state = gate._copy_scanner_inputs(self.root, self.copy)
        self.assertEqual(before, state)
        self.assertEqual(before, gate._scanner_input_state(self.root))
        copied = {p.relative_to(self.copy) for p in self.copy.rglob("*") if p.is_file()}
        self.assertEqual(set(before), copied)
        self.assertTrue((self.copy / ".git").is_dir())
        for rel in before:
            self.assertEqual((self.root / rel).read_bytes(), (self.copy / rel).read_bytes())
            self.assertNotEqual((self.root / rel).stat().st_ino, (self.copy / rel).stat().st_ino)
        self.assertEqual(0, gate._quiet_run(self.copy)[0])
        ledger = json.loads((self.copy / gate.RATCHET_REL).read_text())
        ledger["extend_constants"]["production_sites"] = []
        (self.copy / gate.RATCHET_REL).write_text(json.dumps(ledger))
        rc, diagnostic = gate._quiet_run(self.copy)
        self.assertEqual(1, rc)
        self.assertIn(str(LEDGER_SITE), diagnostic)

    def test_copied_graph_keeps_production_edges_into_test_named_files(self):
        self.write("crates/c/src/lib.rs", '#[path = "../tests/live.rs"]\nmod live;\n')
        self.write("crates/c/tests/live.rs", gate.PLANT)
        gate._copy_scanner_inputs(self.root, self.copy)
        for root in (self.root, self.copy):
            rc, diagnostic = gate._quiet_run(root)
            self.assertEqual(1, rc)
            self.assertIn("crates/c/tests/live.rs", diagnostic)

    def test_four_real_scanner_verdicts_preserve_all_live_bytes_and_mtimes(self):
        before = gate._scanner_input_state(self.root)
        result, output = self.arms()
        self.assertEqual((4, 0, 0), result, output)
        self.assertEqual(before, gate._scanner_input_state(self.root))
        self.assertFalse(self.lock.exists())
        self.assertIn("restored baseline is green", output)

    def test_exact_plant_line_handles_missing_final_newline_and_empty_file(self):
        for text in ("pub fn ordinary() {}", "", "pub fn ordinary() {}\r\n"):
            with self.subTest(source=text):
                self.write(SNAPSHOT, text)
                result, output = self.arms()
                self.assertEqual((4, 0, 0), result, output)

    def test_dirty_target_still_skips_without_copying_or_claiming_pass(self):
        before = gate._scanner_input_state(self.root)
        with mock.patch.object(gate, "_copy_scanner_inputs") as copy:
            result, output = self.arms(clean=False)
        self.assertEqual((0, 0, 2), result)
        self.assertIn("[SKIP]", output)
        copy.assert_not_called()
        self.assertEqual(before, gate._scanner_input_state(self.root))
        self.assertFalse(self.lock.exists())

    def test_busy_lock_still_skips_and_never_releases_another_holders_lock(self):
        self.lock.mkdir()
        with mock.patch.object(gate.time, "sleep") as sleep, \
                mock.patch.object(gate, "_copy_scanner_inputs") as copy:
            result, output = self.arms()
        self.assertEqual((0, 0, 2), result)
        self.assertIn("[SKIP]", output)
        self.assertEqual(600, sleep.call_count)
        sleep.assert_called_with(0.1)
        copy.assert_not_called()
        self.assertTrue(self.lock.is_dir())

    def test_clean_precondition_checks_worktree_and_index_and_never_restores(self):
        for statuses, expected, count in (([0, 0], True, 2), ([1], False, 1),
                                          ([0, 1], False, 2), ([128], False, 1)):
            with self.subTest(statuses=statuses), mock.patch.object(
                    gate.subprocess, "run",
                    side_effect=[mock.Mock(returncode=value) for value in statuses]) as run:
                self.assertEqual(expected, gate._git_clean(str(SNAPSHOT)))
                self.assertEqual(count, run.call_count)
                self.assertEqual(["git", "-C", str(gate.REPO_ROOT), "diff", "--quiet",
                                  "--", str(SNAPSHOT)], run.call_args_list[0].args[0])
                if count == 2:
                    self.assertIn("--cached", run.call_args_list[1].args[0])

    def test_red_unmodified_baseline_cannot_certify_the_mutant(self):
        self.write(SNAPSHOT, gate.PLANT)
        with mock.patch.object(gate, "_quiet_run", wraps=gate._quiet_run) as run:
            result, output = self.arms()
        self.assertEqual((0, 1, 0), result, output)
        self.assertEqual(1, run.call_count)

    def test_unrelated_red_is_not_the_expected_mutation_diagnostic(self):
        actual_run = gate._quiet_run
        calls = 0

        def unrelated_red(root):
            nonlocal calls
            calls += 1
            return (1, "FAIL: an unrelated problem") if calls == 3 else actual_run(root)

        with mock.patch.object(gate, "_quiet_run", side_effect=unrelated_red):
            result, output = self.arms()
        self.assertEqual((3, 1, 0), result, output)

    def test_always_green_scanner_cannot_pass_the_standing_plant(self):
        with mock.patch.object(gate, "_quiet_run", return_value=(0, "OK: inert scanner")):
            result, output = self.arms()
        self.assertEqual((3, 1, 0), result, output)

    def test_missing_target_fails_instead_of_skipping(self):
        (self.root / SNAPSHOT).unlink()
        with mock.patch.object(gate, "_copy_scanner_inputs") as copy:
            result, output = self.arms()
        self.assertEqual((0, 2, 0), result, output)
        copy.assert_not_called()
        self.assertFalse(self.lock.exists())

    def test_copy_refuses_live_or_overlapping_destinations(self):
        for destination in (self.root, self.root / "crates", self.base):
            with self.subTest(destination=destination), self.assertRaisesRegex(ValueError, "overlap"):
                gate._copy_scanner_inputs(self.root, destination)

    def test_copy_refuses_nonempty_destination(self):
        (self.copy / "peer.txt").write_text("preserve me")
        with self.assertRaisesRegex(ValueError, "must be empty"):
            gate._copy_scanner_inputs(self.root, self.copy)
        self.assertEqual("preserve me", (self.copy / "peer.txt").read_text())

    def test_source_and_ledger_symlinks_are_refused_without_touching_their_targets(self):
        for rel in (SNAPSHOT, gate.RATCHET_REL):
            with self.subTest(rel=rel):
                path = self.root / rel
                original = path.read_bytes()
                outside = self.base / "external-input"
                outside.write_bytes(original)
                path.unlink()
                path.symlink_to(outside)
                result, output = self.arms()
                self.assertGreater(result[1], 0, output)
                self.assertIn("symlinked scanner input", output)
                self.assertEqual(original, outside.read_bytes())
                path.unlink()
                path.write_bytes(original)

    def test_source_inventory_change_during_capture_refuses_and_preserves_peer_edit(self):
        actual_inputs = gate._scanner_inputs
        calls = 0

        def changing_inventory(root):
            nonlocal calls
            calls += 1
            if calls == 2:
                self.write("crates/new.rs", "// concurrent edit\n")
            return actual_inputs(root)

        with mock.patch.object(gate, "_scanner_inputs", side_effect=changing_inventory):
            with self.assertRaisesRegex(ValueError, "changed while copying"):
                gate._copy_scanner_inputs(self.root, self.copy)
        self.assertEqual("// concurrent edit\n", (self.root / "crates/new.rs").read_text())

    def test_directory_symlink_cannot_silently_change_module_edge_resolution(self):
        self.write("crates/c/tests/actual/live.rs", gate.PLANT)
        self.write("crates/c/src/lib.rs", '#[path = "../alias/live.rs"]\nmod live;\n')
        (self.root / "crates/c/alias").symlink_to("tests/actual", target_is_directory=True)
        rc, diagnostic = gate._quiet_run(self.root)
        self.assertEqual(1, rc)
        self.assertIn("crates/c/tests/actual/live.rs", diagnostic)
        with self.assertRaisesRegex(ValueError, "symlinked scanner input"):
            gate._copy_scanner_inputs(self.root, self.copy)

    def test_nested_repository_marker_cannot_change_classifier_root(self):
        (self.root / "crates/c/.git").mkdir()
        with self.assertRaisesRegex(ValueError, "nested repository marker"):
            gate._copy_scanner_inputs(self.root, self.copy)

    def test_copy_write_failure_is_red_and_leaves_source_unchanged(self):
        before = gate._scanner_input_state(self.root)
        actual_open = Path.open

        def refuse_copy_write(path, *args, **kwargs):
            if args and args[0] == "xb":
                raise PermissionError("injected isolated copy write failure")
            return actual_open(path, *args, **kwargs)

        with mock.patch.object(Path, "open", refuse_copy_write):
            result, output = self.arms()
        self.assertEqual((0, 1, 0), result, output)
        self.assertIn("copy write failure", output)
        self.assertEqual(before, gate._scanner_input_state(self.root))
        self.assertFalse(self.lock.exists())

    def test_input_change_during_read_is_refused_without_restoring_peer_bytes(self):
        actual_read = Path.read_bytes
        path = self.root / SNAPSHOT

        def changing_read(candidate):
            data = actual_read(candidate)
            if candidate == path:
                candidate.write_text("// changed concurrently while reading\n")
            return data

        with mock.patch.object(Path, "read_bytes", changing_read):
            with self.assertRaisesRegex(ValueError, "changed while reading"):
                gate._scanner_input(self.root, SNAPSHOT)
        self.assertEqual("// changed concurrently while reading\n", path.read_text())

    def test_scanner_exception_restores_only_copy_and_cleans_temporary_tree(self):
        before = gate._scanner_input_state(self.root)
        actual_run = gate._quiet_run
        actual_write = Path.write_bytes
        copies = []
        writes = []

        def observe_copy_write(path, data):
            self.assertNotEqual(self.root / SNAPSHOT, path)
            writes.append(data)
            return actual_write(path, data)

        def fail_on_mutant(root):
            copies.append(root)
            if len(copies) == 3:
                raise SystemExit("injected scanner refusal")
            return actual_run(root)

        with mock.patch.object(gate, "_quiet_run", side_effect=fail_on_mutant), \
                mock.patch.object(Path, "write_bytes", observe_copy_write):
            result, output = self.arms()
        self.assertEqual((2, 1, 0), result, output)
        self.assertIn("injected scanner refusal", output)
        self.assertEqual(before, gate._scanner_input_state(self.root))
        self.assertEqual(3, len(writes))
        self.assertEqual((self.root / SNAPSHOT).read_bytes(), writes[-1])
        self.assertTrue(copies)
        self.assertTrue(all(not copy.exists() for copy in copies))
        self.assertFalse(self.lock.exists())

    def test_peer_source_edit_during_arms_is_detected_and_never_overwritten(self):
        actual_run = gate._quiet_run
        calls = 0

        def edit_live_fixture(root):
            nonlocal calls
            calls += 1
            if calls == 2:
                self.write(SNAPSHOT, "// peer change, must survive\n")
            return actual_run(root)

        with mock.patch.object(gate, "_quiet_run", side_effect=edit_live_fixture):
            result, output = self.arms()
        self.assertEqual((4, 1, 0), result, output)
        self.assertIn("REAL INPUT preservation", output)
        self.assertEqual("// peer change, must survive\n", (self.root / SNAPSHOT).read_text())


if __name__ == "__main__":
    unittest.main()
