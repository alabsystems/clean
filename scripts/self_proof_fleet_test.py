#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

import contextlib
import copy
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import self_proof_fleet as fleet
import self_proof_scoreboard as scoreboard
from self_proof_fleet_product import product_plan


class FleetTests(unittest.TestCase):
    def test_c3_snapshot_uses_the_published_run_and_compiler_receipt(self):
        original = fleet.ROOT / fleet.C3
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            folder = (root / fleet.C3).parent
            folder.mkdir(parents=True)
            for name in fleet.C3_FILES:
                (folder / name).write_bytes((original.parent / name).read_bytes())
            result = fleet.c3_snapshot(root)
            self.assertEqual(result["state"], "qualified_snapshot")
            self.assertEqual(result["revision"], "ce717a98ee9070cf0e2a5f13d7ff5f24ca77abe8")
            self.assertEqual(result["receipt_revision"], fleet.C3_RECEIPT_REVISION)
            row = json.loads(original.read_bytes())
            for updates in ({"qualified_source": "0" * 40}, {"changed_inputs": ["CompleteSound.lean"]},
                            {"c3_theorems": 1, "actual_proof_at_own_statement_and_false_controls": 1}):
                with self.subTest(updates=updates):
                    (root / fleet.C3).write_text(json.dumps({**row, **updates}))
                    self.assertEqual(fleet.c3_snapshot(root)["state"], "unverified")
            (root / fleet.C3).write_bytes(original.read_bytes())
            for name in ("executed-binary.json", "canonical.log.gz", "executed-kcheck-labelled.bin.gz",
                         "qualified-inputs.json"):
                with self.subTest(name=name):
                    (folder / name).write_bytes(b"unrelated run")
                    self.assertEqual(fleet.c3_snapshot(root)["state"], "unverified")
                    (folder / name).unlink()
                    self.assertEqual(fleet.c3_snapshot(root)["state"], "unverified")
                    (folder / name).write_bytes((original.parent / name).read_bytes())

    def test_w3_library_receipt_is_a_source_check_with_unchanged_pins(self):
        event, = [row for row in fleet.recorded_events(fleet.ROOT, "W3")
                  if row["unit"] == "W3" and row.get("measurement") == "digest-library"]
        observations = fleet.followup_results(fleet.ROOT, [event])
        qualified = observations["W3-digest-library"]
        self.assertEqual(qualified["checked_revision"], "d1f3c9343410bdf48c8c5192479cdc57cbba45aa")
        self.assertEqual((qualified["commands_passed"], qualified["unchanged_source_inputs"],
                          qualified["unchanged_pin_files"]), (5, 3723, 175))
        self.assertEqual(fleet.displayed_events([event], None, observations), [event])
        for wrong in ({**event, "source_revision": "0" * 40}, {**event, "source_sha256": "0" * 64},
                      {**event, "source": "reports/missing.json"}):
            self.assertEqual(fleet.followup_results(fleet.ROOT, [wrong]), {})
            self.assertEqual(fleet.displayed_events([wrong], None, observations), [])
        with patch("self_proof_fleet_evidence._historical_blob", return_value=b"{}"):
            self.assertEqual(fleet.followup_results(fleet.ROOT, [event]), {})
        self.assertEqual(fleet.displayed_events([event], None, {}), [])

    def test_native_matcher_is_bound_to_the_proof_stream_and_the_changed_frame(self):
        event, = fleet.recorded_events(fleet.ROOT, "PR-67")
        observed = fleet.followup_results(fleet.ROOT, [event])
        reading = observed["PR-67"]
        self.assertIn("9 ordinary declarations in the first 87", fleet.native_matcher_text(reading))
        self.assertEqual(fleet.displayed_events([event], {}, observed), [event])
        for field in ("input_sha256", "source_sha256", "qualification_sha256"):
            wrong = dict(event, **{field: "0" * 64})
            self.assertEqual(fleet.followup_results(fleet.ROOT, [wrong]), {})
            self.assertEqual(fleet.displayed_events([wrong], {}, observed), [])
        damaged = {**reading, "control": {**reading["control"], "changed_frame_records": 2}}
        self.assertEqual(fleet.native_matcher_text(damaged), "")
        with patch("self_proof_native_matcher.verify", side_effect=ValueError("different control")):
            self.assertEqual(fleet.followup_results(fleet.ROOT, [event]), {})

    def test_timeline_is_dated_sourced_and_filterable(self):
        doc = fleet.read_json(fleet.ROOT / fleet.TIMELINE)
        events = fleet.timeline(doc)
        self.assertGreater(len(events), 1)
        prefix = fleet.timeline(doc, "self-admission-prefix")
        self.assertTrue(prefix)
        self.assertTrue(all("self-admission-prefix" in fleet.event_units(row) for row in prefix))
        row_with_obligation = next(row for row in reversed(events) if "obligation" in row)
        for change in ({"source": "../other"}, {"date": "2025-01-01"}, {"kind": "green"},
                       {"obligation": ""}, {"obligation": row_with_obligation["unit"]},
                       {"related_obligations": "W1"}, {"related_obligations": [""]},
                       {"related_obligations": [row_with_obligation["obligation"]]}, {"related_obligations": ["W1", "W1"]}):
            invalid = {"schema": doc["schema"], "events": [events[0], {**row_with_obligation, **change}]}
            with self.assertRaises(ValueError):
                fleet.timeline(invalid)

    def test_execution_receipt_reads_the_git_blob_and_checks_its_digest(self):
        event = {"source_revision": "a" * 40, "source_sha256": hashlib.sha256(b"run").hexdigest(),
                 "source": "reports/run.json#result"}
        key = event["source_revision"] + ":reports/run.json"
        with patch("self_proof_fleet_evidence._historical_blob", return_value=b"run") as git_read:
            self.assertEqual(fleet.execution_receipts(fleet.ROOT, [event]), {key: event["source_sha256"]})
            git_read.assert_called_once_with(fleet.ROOT, event["source_revision"], "reports/run.json")
            self.assertEqual(fleet.execution_receipts(fleet.ROOT, [{**event, "source_sha256": "0" * 64}]), {})
        with patch("self_proof_fleet_evidence._historical_blob", side_effect=OSError()):
            self.assertEqual(fleet.execution_receipts(fleet.ROOT, [event]), {})

    def test_compared_execution_requires_both_historical_artifacts(self):
        revision, replay_revision = "a" * 40, "b" * 40
        primary, replay = "reports/run.json", "reports/replay.json"
        digest = hashlib.sha256(b"run").hexdigest()
        replay_digest = hashlib.sha256(b"replayed").hexdigest()
        single = {"unit": "W1", "kind": "blocker", "source": primary + "#entry",
                  "source_revision": revision, "source_sha256": digest}
        pair = {**single, "replay_source": replay, "replay_sha256": replay_digest}
        separate = {**pair, "replay_revision": replay_revision}

        def read(root, rev, path):
            if (rev, path) == (revision, primary):
                return b"run"
            if rev in (revision, replay_revision) and path == replay:
                return b"replayed"
            raise OSError("absent historical artifact")

        # A receipt-backed history also checks the single run before crediting it.
        self.assertEqual(fleet.displayed_events([single], {}, receipts={}), [])
        with patch("self_proof_fleet_evidence._historical_blob", side_effect=read):
            for good in (pair, separate):
                verified = fleet.execution_receipts(fleet.ROOT, [good])
                self.assertEqual(fleet.displayed_events([good], {}, receipts=verified), [good])
                self.assertEqual(verified[f"{good.get('replay_revision', revision)}:{replay}"], replay_digest)
            for bad in ({**pair, "replay_sha256": "0" * 64}, {**pair, "replay_source": "absent"},
                        {**pair, "replay_revision": "c" * 40}, {**pair, "replay_source": None},
                        {**single, "replay_sha256": replay_digest}, {**single, "replay_source": replay},
                        {**single, "replay_revision": replay_revision}):
                with self.subTest(bad=bad):
                    self.assertEqual(fleet.execution_receipts(fleet.ROOT, [bad]), {})
                    # The independently cited single run must never certify its damaged comparison.
                    verified = fleet.execution_receipts(fleet.ROOT, [single, bad])
                    self.assertEqual(fleet.displayed_events([single, bad], {}, receipts=verified), [single])

    def test_census_progress_checks_partial_rows_without_a_gate_verdict(self):
        full = fleet.read_json(fleet.ROOT / "reports/self-proof-elab/baseline.json")
        partial = {**full, "complete": False, "modules": full["modules"][:3]}
        result = fleet.census_progress(fleet.ROOT, partial)
        self.assertEqual(result["modules_recorded"], 3)
        self.assertEqual(result["modules_expected"], len(full["expected_modules"]))
        self.assertFalse(result["complete"])
        self.assertEqual(sum(result["module_counts"].values()), 3)
        self.assertEqual(result["adopted_main"]["expected_bytes"], 5110)
        for invalid in ({**partial, "complete": True}, {**partial, "expected_modules": partial["expected_modules"][:3]},
                        {**partial, "runner_sha256": "0" * 64}, {**partial, "modules": list(reversed(partial["modules"]))},
                        {**partial, "modules": [{**partial["modules"][0], "status": "other"}]},
                        {**partial, "probes": [{**r, "status": "executed"} for r in partial["probes"]]}):
            with self.assertRaises(ValueError):
                fleet.census_progress(fleet.ROOT, invalid)

    def test_archived_checkpoint_retains_the_raw_json_and_refuses_a_truncated_stream(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "checkpoint.json.gz"
            compressed = gzip.compress(b'{"complete": false}')
            path.write_bytes(compressed)
            self.assertEqual(fleet.read_json(path), {"complete": False})
            path.write_bytes(compressed[:-4])
            with self.assertRaisesRegex(ValueError, "truncated gzip"):
                fleet.read_json(path)

    def test_entry_census_uses_only_imports_and_still_checks_other_transcripts(self):
        full = fleet.read_json(fleet.ROOT / "reports/self-proof-elab/baseline.json")
        rows = full["modules"][:3]
        partial = {**full, "complete": False, "modules": rows}
        row = rows[1]
        graph = {"entry": "Main.lean", "modules": {
            "Main.lean": {"package": "kcheck_labelled", "in_census": False},
            "LibraryRoot.lean": {"package": "kcheck_labelled", "in_census": False},
            row["module"] + ".lean": {"package": row["package"], "in_census": True, "sha256": row["source_sha256"]}}}
        with patch("self_proof_entry_imports.entry_imports", return_value=graph):
            focused = fleet.census_progress(fleet.ROOT, partial, entry_only=True)
            self.assertEqual((focused["modules_recorded"], focused["modules_expected"]), (1, 1))
            self.assertFalse(focused["complete"])
            self.assertEqual(focused["census_modules_expected"], len(full["expected_modules"]))
            self.assertEqual(focused["adopted_main"], fleet.census_progress(fleet.ROOT, partial)["adopted_main"])
            for broken, message in [([{**rows[0], "status": "forged"}, *rows[1:]], "module verdict"),
                                    ([rows[0], {**row, "source_sha256": "0" * 64}, rows[2]], "entry module source")]:
                with self.assertRaisesRegex(ValueError, message):
                    fleet.census_progress(fleet.ROOT, {**partial, "modules": broken}, entry_only=True)

    def test_proof_source_census_includes_the_root_and_retains_its_verdict(self):
        full = fleet.read_json(fleet.ROOT / "reports/self-proof-elab/baseline.json")
        root, dep = full["modules"][:2]
        path = root["module"] + ".lean"
        graph = {"entry": path, "modules": {r["module"] + ".lean": {
            "package": r["package"], "in_census": True, "sha256": r["source_sha256"]} for r in (root, dep)}}
        with patch("self_proof_entry_imports.entry_imports", return_value=graph):
            partial = {**full, "complete": False, "modules": []}
            empty = fleet.census_progress(fleet.ROOT, partial, proof_source_only=True)
            self.assertEqual(empty["proof_source"], {"status": "pending"})
            measured = fleet.census_progress(fleet.ROOT, {**partial, "modules": [root, dep]}, proof_source_only=True)
            self.assertEqual((measured["modules_expected"], measured["modules_recorded"]), (2, 2))
            self.assertEqual(measured["proof_source"], {"status": root["status"], "first_error": root["first_error"]})

    def test_census_groups_direct_and_imported_module_refusals(self):
        full = fleet.read_json(fleet.ROOT / "reports/self-proof-elab/baseline.json")
        partial = {**full, "complete": False, "modules": full["modules"][:6]}
        result = fleet.census_progress(fleet.ROOT, partial)
        self.assertEqual(result["first_refusals"], [{"declaration": "CICL.Expr.mapLevels_comp", "rows": 3,
                                                    "first_module": "cic_l/CICL/Expr"}])
        self.assertEqual(result["unnamed_refusals"], 0)
        self.assertEqual(result["packages"]["cic_l"]["recorded"], 6)
        self.assertEqual(result["packages"]["cic_l"]["refused"], 3)
        self.assertEqual(result["packages"]["kcheck_labelled"]["recorded"], 0)
        self.assertEqual(sum(row["expected"] for row in result["packages"].values()), len(full["expected_modules"]))
        complete = fleet.census_progress(fleet.ROOT, full)
        self.assertEqual(sum(g["rows"] for g in complete["first_refusals"]) + complete["unnamed_refusals"],
                         complete["module_counts"]["refused"])
        self.assertEqual(sum(v["timed_out"] for v in complete["packages"].values()),
                         complete["module_counts"]["timed_out"])

    def test_prefix_cli_forwards_the_bound_and_checker_exit(self):
        import self_proof_prefix
        args = ["fleet", "--measure-prefix", "export.ndjson.gz", "--limit", "0", "--json"]
        with patch.object(sys, "argv", args), patch.object(self_proof_prefix, "main", return_value=2) as main:
            self.assertEqual(fleet.main(), 2)
        main.assert_called_once_with(["export.ndjson.gz", "--limit", "0", "--json"])
        for opts in (["--limit", "1"], ["--measure-prefix", "export", "--timeline"]):
            with patch.object(sys, "argv", ["fleet", *opts]), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as failed:
                fleet.main()
            self.assertEqual(failed.exception.code, 2)

    def test_w0_shadow_runs_the_candidate_against_the_explicit_root(self):
        board = {"z": 2, "a": 1}
        canonical = b'{\n  "a": 1,\n  "z": 2\n}\n'
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "another checkout"
            candidate = Path(tmp) / "candidate clean"
            result = subprocess.CompletedProcess([], 0, canonical, b"")
            with patch.object(fleet.subprocess, "run", return_value=result) as run:
                fleet.verify_w0_shadow(root, candidate, board)
            run.assert_called_once_with(
                [str(candidate.resolve()), "evidence", "status", "--scoreboard", "--json",
                 "--repo-root", str(root.resolve())],
                cwd=root, stdin=subprocess.DEVNULL, capture_output=True, timeout=60,
            )

    def test_w0_shadow_refuses_noncanonical_bytes_and_candidate_failures(self):
        board = {"z": 2, "a": 1}
        canonical = b'{\n  "a": 1,\n  "z": 2\n}\n'
        variants = (canonical[:-1], canonical + b"\n", canonical.replace(b"\n", b"\r\n"),
                    b'{"z": 2, "a": 1}\n')
        for output in variants:
            self.assertEqual(json.loads(output), board)
        results = [subprocess.CompletedProcess([], 0, output, b"") for output in variants]
        results.extend(subprocess.CompletedProcess([], code, canonical, error)
                       for code, error in ((1, b""), (0, b"\n"), (0, b"warning")))
        for result in results:
            with self.subTest(stdout=result.stdout, code=result.returncode, stderr=result.stderr), \
                 patch.object(fleet.subprocess, "run", return_value=result), self.assertRaises(ValueError):
                fleet.verify_w0_shadow(fleet.ROOT, Path("candidate"), board)

    def test_w0_shadow_cli_refuses_independent_views_before_reading_or_running(self):
        for mode in (["--planning", "status"], ["--planning", "design"],
                     ["--presentation", "slides.html"], ["--timeline"],
                     ["--census-progress", "checkpoint.json"], ["--measure-prefix", "export.ndjson"],
                     ["--replay-checker", "checker"]):
            with self.subTest(mode=mode), \
                 patch.object(sys, "argv", ["fleet", "--shadow-w0", "candidate", *mode]), \
                 patch.object(fleet, "snapshot") as snapshot, \
                 patch.object(fleet.subprocess, "run") as run, \
                 contextlib.redirect_stderr(io.StringIO()) as error, self.assertRaises(SystemExit) as failed:
                fleet.main()
            self.assertEqual(failed.exception.code, 2)
            self.assertIn("--shadow-w0 requires an ordinary fleet report", error.getvalue())
            snapshot.assert_not_called()
            run.assert_not_called()

    def test_native_w0_uses_the_pinned_reader_and_preserves_incumbent_warnings(self):
        raw = (fleet.ROOT / "data/self_proof_scoreboard.json").read_bytes()
        board = json.loads(raw)
        self.assertEqual(raw, scoreboard.serialize(board).encode("utf-8"))
        build = (Path("candidate clean"), Path("build receipt.json"), "a" * 64)
        forged = copy.deepcopy(board)
        forged["headline"]["decided_by_compiled_kcheck"]["real_declarations_decided"] += 1
        missing = "data/self_proof_scoreboard.json does not exist"
        differs = "the record differs from a re-derivation; run scripts/self_proof_scoreboard.py --write"
        records = {
            "canonical": (raw, None),
            "crlf": (raw.replace(b"\n", b"\r\n"), None),
            "missing": (None, missing),
            "missing_lf": (raw[:-1], differs),
            "forged": (scoreboard.serialize(forged).encode("utf-8"), differs),
            "unreadable": (None, missing),
        }
        with tempfile.TemporaryDirectory() as tmp:
            for name, (content, warning) in records.items():
                with self.subTest(record=name):
                    root = Path(tmp) / name
                    record = root / "data/self_proof_scoreboard.json"
                    record.parent.mkdir(parents=True)
                    if name == "unreadable":
                        record.mkdir()
                    elif content is not None:
                        record.write_bytes(content)
                    expected = (board, warning)
                    with patch.object(scoreboard, "derive", return_value=board) as incumbent:
                        self.assertEqual(fleet.read_w0(root), expected)
                    incumbent.assert_called_once_with(root)
                    with patch.object(scoreboard, "derive", side_effect=AssertionError("Python derive used")), \
                         patch("self_proof_fleet_w0.run_pinned_w0_json", return_value=raw) as native:
                        self.assertEqual(fleet.read_w0(root, native_w0=build), expected)
                    native.assert_called_once_with(build, git_root=fleet.ROOT, data_root=root)

    def test_native_w0_reads_and_compares_a_saved_board_without_importing_legacy_module(self):
        script = """\
import json
from pathlib import Path
import sys
from unittest.mock import patch

class BlockLegacyScoreboard:
    def find_spec(self, fullname, path=None, target=None):
        if fullname.rpartition(".")[2] == "self_proof_scoreboard":
            raise AssertionError(f"native W0 imported {fullname}")

scripts, fixture, root = map(Path, sys.argv[1:])
sys.path.insert(0, str(scripts))
sys.meta_path.insert(0, BlockLegacyScoreboard())
import self_proof_fleet as fleet

raw = fixture.read_bytes()
build = ("candidate", "receipt", "a" * 64)
with patch("self_proof_fleet_w0.run_pinned_w0_json", return_value=raw) as native:
    board, canonical = fleet.read_w0(root, native_w0=build)
    record = root / "data/self_proof_scoreboard.json"
    record.write_bytes(raw[:-1])
    changed_board, changed = fleet.read_w0(root, native_w0=build)
assert board == changed_board == json.loads(raw)
assert native.call_count == 2
native.assert_called_with(build, git_root=fleet.ROOT, data_root=root)
assert "self_proof_scoreboard" not in sys.modules
print(json.dumps([canonical, changed]))
"""
        fixture = fleet.ROOT / "data/self_proof_scoreboard.json"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            saved = root / "data/self_proof_scoreboard.json"
            saved.parent.mkdir()
            saved.write_bytes(fixture.read_bytes())
            result = subprocess.run(
                [sys.executable, "-I", "-B", "-c", script, str(fleet.ROOT / "scripts"), str(fixture), str(root)],
                capture_output=True, text=True, timeout=30,
            )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, "")
        self.assertEqual(
            json.loads(result.stdout),
            [None, "the record differs from a re-derivation; run scripts/self_proof_scoreboard.py --write"],
        )

    def test_native_w0_refuses_bad_payloads_and_never_falls_back_to_python(self):
        raw = (fleet.ROOT / "data/self_proof_scoreboard.json").read_bytes()
        board = json.loads(raw)
        invalid = [b"not JSON", b"\xff", b"{}\n", b"[]\n", b"NaN\n", raw[:-1], raw + b"\n",
                   raw.replace(b"\n", b"\r\n"), json.dumps(board).encode("utf-8") + b"\n"]
        for change in (lambda b: b.update(schema="other"),
                       lambda b: b["headline"]["decided_by_compiled_kcheck"].update(real_declarations_decided=False),
                       lambda b: b["route"].pop("lean_kernel_rule_families")):
            malformed = copy.deepcopy(board)
            change(malformed)
            invalid.append(scoreboard.serialize(malformed).encode("utf-8"))
        build = (Path("candidate"), Path("receipt"), "a" * 64)
        with patch.object(scoreboard, "derive", side_effect=AssertionError("Python fallback used")):
            for payload in invalid:
                with self.subTest(payload=payload[:80]), \
                     patch("self_proof_fleet_w0.run_pinned_w0_json", return_value=payload), self.assertRaises(ValueError):
                    fleet.read_w0(fleet.ROOT, native_w0=build)
            for error in (ValueError("candidate refused"), OSError("candidate unavailable"),
                          subprocess.TimeoutExpired("candidate", 60)):
                with self.subTest(error=type(error).__name__), \
                     patch("self_proof_fleet_w0.run_pinned_w0_json", side_effect=error), self.assertRaises(type(error)):
                    fleet.read_w0(fleet.ROOT, native_w0=build)

    def test_native_w0_cli_forwards_the_build_and_refuses_independent_or_shadow_modes(self):
        build = ("candidate", "receipt.json", "a" * 64)
        options = ["--native-w0", *build]
        output = io.StringIO()
        with patch.object(sys, "argv", ["fleet", *options, "--json"]), \
             patch.object(fleet, "snapshot", return_value={"units": []}) as snapshot, \
             contextlib.redirect_stdout(output):
            self.assertEqual(fleet.main(), 0)
        snapshot.assert_called_once_with(report_dir=None, shadow_w0=None, native_w0=build)
        self.assertEqual(json.loads(output.getvalue()), {"units": []})
        for mode in (["--planning", "status"], ["--planning", "preview"], ["--planning", "publish"],
                     ["--timeline"],
                     ["--census-progress", "checkpoint.json"], ["--measure-prefix", "export.ndjson"],
                     ["--replay-checker", "checker"], ["--shadow-w0", "candidate"]):
            with self.subTest(mode=mode), patch.object(sys, "argv", ["fleet", *options, *mode]), \
                 patch.object(fleet, "snapshot") as snapshot, \
                 patch.object(fleet, "planning_view") as planning, \
                 patch("self_proof_fleet_w0.run_pinned_w0_json") as native, \
                 contextlib.redirect_stderr(io.StringIO()) as error, self.assertRaises(SystemExit) as failed:
                fleet.main()
            self.assertEqual(failed.exception.code, 2)
            self.assertIn("--native-w0", error.getvalue())
            snapshot.assert_not_called()
            planning.assert_not_called()
            native.assert_not_called()

    def test_native_w0_planning_design_matches_the_full_incumbent_json(self):
        build = ("candidate clean", "build receipt.json", "a" * 64)
        raw = scoreboard.serialize(scoreboard.derive(fleet.ROOT)).encode("utf-8")
        args = ["fleet", "--planning", "design", "--json"]
        with patch.object(fleet, "clean_revision", return_value="a" * 40), \
             patch("self_proof_fleet_product.product_status") as status, \
             patch("self_proof_fleet_product.sync_product") as sync:
            with patch.object(sys, "argv", args), contextlib.redirect_stdout(io.StringIO()) as incumbent:
                self.assertEqual(fleet.main(), 0)
            with patch.object(sys, "argv", [*args, "--native-w0", *build]), \
                 patch.object(fleet, "snapshot", wraps=fleet.snapshot) as snapshot, \
                 patch.object(scoreboard, "derive", side_effect=AssertionError("Python derive used")), \
                 patch("self_proof_fleet_w0.run_pinned_w0_json", return_value=raw) as native, \
                 contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(fleet.main(), 0)
        snapshot.assert_called_once_with(native_w0=build)
        native.assert_called_once_with(build, git_root=fleet.ROOT, data_root=fleet.ROOT)
        status.assert_not_called()
        sync.assert_not_called()
        self.assertEqual(output.getvalue(), incumbent.getvalue())
        packages = {row["key"]: row for row in json.loads(output.getvalue())["packages"]}
        self.assertEqual(
            {key: (packages[key]["status"], packages[key]["waiting_on"]) for key in ("C4-C5", "W4", "W5")},
            {"C4-C5": ("bounded_evidence", []), "W4": ("needs_gate_evidence", ["W3", "C4-C5"]),
             "W5": ("needs_gate_evidence", ["W4"])},
        )

    def test_native_w0_planning_design_failure_produces_no_plan_or_tracker_call(self):
        build = ("candidate", "receipt.json", "a" * 64)
        args = ["fleet", "--planning", "design", "--json", "--native-w0", *build]
        failures = (
            ({"side_effect": ValueError("native candidate refused")}, "native candidate refused"),
            ({"return_value": b"not JSON"}, "invalid native W0 JSON"),
        )
        for response, diagnostic in failures:
            with self.subTest(diagnostic=diagnostic), patch.object(sys, "argv", args), \
                 patch.object(scoreboard, "derive", side_effect=AssertionError("Python fallback used")), \
                 patch("self_proof_fleet_w0.run_pinned_w0_json", **response) as native, \
                 patch("self_proof_fleet_product.product_plan") as plan, \
                 patch("self_proof_fleet_product.product_status") as status, \
                 patch("self_proof_fleet_product.sync_product") as sync, \
                 contextlib.redirect_stdout(io.StringIO()) as stdout, \
                 contextlib.redirect_stderr(io.StringIO()) as stderr:
                self.assertEqual(fleet.main(), 2)
            native.assert_called_once_with(build, git_root=fleet.ROOT, data_root=fleet.ROOT)
            plan.assert_not_called()
            status.assert_not_called()
            sync.assert_not_called()
            self.assertEqual(stdout.getvalue(), "")
            self.assertIn(diagnostic, stderr.getvalue())

    def test_native_w0_presentation_renders_the_complete_incumbent_deck(self):
        build = ("candidate clean", "build receipt.json", "a" * 64)
        raw = scoreboard.serialize(scoreboard.derive(fleet.ROOT)).encode("utf-8")
        planning = {"state": "unavailable", "backend": "publication", "goal": "E1"}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            publication = root / "publication"
            incumbent = root / "incumbent.html"
            candidate = root / "native.html"
            options = ["--publication-root", str(publication), "--presentation"]
            with patch.object(fleet, "clean_revision", return_value="a" * 40), \
                 patch.object(fleet, "planning_view", return_value=planning) as status:
                with patch.object(sys, "argv", ["fleet", *options, str(incumbent)]), \
                     contextlib.redirect_stdout(io.StringIO()) as output:
                    self.assertEqual(fleet.main(), 0)
                self.assertEqual(output.getvalue(), f"{incumbent}\n")

                with patch.object(sys, "argv", ["fleet", "--native-w0", *build, *options, str(candidate)]), \
                     patch.object(fleet, "snapshot", wraps=fleet.snapshot) as snapshot, \
                     patch.object(scoreboard, "derive", side_effect=AssertionError("Python derive used")), \
                     patch("self_proof_fleet_w0.run_pinned_w0_json", return_value=raw) as native, \
                     contextlib.redirect_stdout(io.StringIO()) as output:
                    self.assertEqual(fleet.main(), 0)
                self.assertEqual(output.getvalue(), f"{candidate}\n")
            snapshot.assert_called_once_with(native_w0=build)
            native.assert_called_once_with(build, git_root=fleet.ROOT, data_root=fleet.ROOT)
            self.assertEqual(status.call_count, 2)
            status.assert_called_with("status", publication)
            expected = incumbent.read_bytes()
            self.assertTrue(expected.lower().startswith(b"<!doctype html>"))
            self.assertEqual(candidate.read_bytes(), expected)

    def test_native_w0_presentation_failure_preserves_an_existing_deck(self):
        build = ("candidate", "receipt.json", "a" * 64)
        failures = (
            ({"side_effect": ValueError("native candidate refused")}, "native candidate refused"),
            ({"return_value": b"not JSON"}, "invalid native W0 JSON"),
        )
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "existing deck.html"
            original = b"<!doctype html><title>Existing deck</title>\n"
            output.write_bytes(original)
            args = ["fleet", "--native-w0", *build, "--presentation", str(output)]
            for response, diagnostic in failures:
                with self.subTest(diagnostic=diagnostic), patch.object(sys, "argv", args), \
                     patch.object(fleet, "planning_view", return_value={}), \
                     patch.object(scoreboard, "derive", side_effect=AssertionError("Python fallback used")), \
                     patch("self_proof_fleet_w0.run_pinned_w0_json", **response) as native, \
                     contextlib.redirect_stdout(io.StringIO()) as stdout, \
                     contextlib.redirect_stderr(io.StringIO()) as stderr:
                    self.assertEqual(fleet.main(), 2)
                native.assert_called_once_with(build, git_root=fleet.ROOT, data_root=fleet.ROOT)
                self.assertEqual(stdout.getvalue(), "")
                self.assertIn(diagnostic, stderr.getvalue())
                self.assertEqual(output.read_bytes(), original)

    def test_optional_timeline_input_hash_is_a_full_sha256(self):
        event = {"date": "2026-11-17", "kind": "measurement", "unit": "Q4",
                 "summary": "Checked this export.", "source": "reports/quorum.json"}
        def parsed(row):
            return fleet.timeline({"schema": "clean.self_proof_fleet_timeline.v1", "events": [row]})

        self.assertEqual(parsed(event), [event])
        bound = {**event, "input_sha256": "7a" * 32}
        self.assertEqual(parsed(bound), [bound])
        for malformed in (None, 7, "a" * 63, "a" * 65, "G" * 64):
            with self.subTest(malformed=malformed), self.assertRaises(ValueError):
                parsed({**event, "input_sha256": malformed})
            with self.subTest(qualification=malformed), self.assertRaises(ValueError):
                parsed({**event, "qualification_sha256": malformed})

    def test_component_proof_and_quorum_qualification_keep_their_scope(self):
        snapshot = fleet.snapshot()
        design = product_plan(snapshot, "1" * 40, events=fleet.unit_history())
        packages = {row["key"]: row for row in design["packages"]}
        w1 = packages["W1"]["history"]
        original = next(row for row in w1 if row["date"] == "2026-11-14")
        self.assertEqual(original["kind"], "blocker")
        self.assertIn("KCheckLabelledMain.lean", original["summary"])
        decoder = next(row for row in w1 if row["source"].endswith("#isolated-utf-8-decoder"))
        self.assertEqual((decoder["kind"], decoder["date"]), ("proof", "2026-11-17"))
        self.assertIn("b71adf4772", decoder["summary"])

        q4 = packages["Q4"]["history"]
        full_root = next(row for row in q4 if row["source"].endswith("root-export-2026-11-17/README.md"))
        member = next(row for row in q4 if row["source"].endswith("l4l-patched-2026-11-17/README.md"))
        self.assertEqual(full_root["date"], member["date"])
        self.assertIn("4,906 of 4,912", full_root["summary"])
        self.assertIn("unqualified", member["summary"])
        self.assertEqual(packages["W1"]["status"], "needs_gate_evidence")
        self.assertEqual(packages["Q4"]["status"], "needs_gate_evidence")
        trial, = fleet.unit_history("PR-28")
        self.assertEqual(trial["obligation"], "Q4")
        self.assertIn(trial, fleet.unit_history("Q4"))
        self.assertEqual(q4.count(trial), 1)
        self.assertEqual(fleet.unit_history().count(trial), 1)

        # The entire projection, including claims, dependencies and every
        # current status, is identical once display-only history is removed.
        for row in design["packages"] + design["external_prerequisites"]:
            row.pop("history", None)
        self.assertEqual(design, product_plan(snapshot, "1" * 40))

    def test_w5_prints_the_frozen_fourth_vote_separately_from_pr29(self):
        snapshot = fleet.snapshot()
        w5 = next(row for row in snapshot["units"] if row["id"] == "W5")
        quorum = snapshot["soundness_root_quorum"]
        current = snapshot["source_qualification"]
        event = next(row for row in fleet.recorded_events(fleet.ROOT) if row["source"] == quorum["source"])

        def summary(report):
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                fleet.render(report, [w5], focused=True)
            return output.getvalue()

        text = summary(snapshot)
        later = next(line for line in text.splitlines() if line.startswith("Q4 on "))
        for expected in (event["date"], "4/4", "qualified Lean4Lean", "4913-name",
                         "frozen Clean source " + quorum["epoch"], current["input_sha256"]):
            self.assertIn(expected, later)
        self.assertIn("0 consecutive records out of 4403, then refused Iff", text)
        production = snapshot["metrics"]["production"].get("real_declarations_decided", "unverified")
        self.assertIn(f"Production decisions by compiled kcheck: {production}", text)
        self.assertIn(f"W5  {w5['kind']}  {w5['status']}", text)
        self.assertIn("PR-29 recorded no qualified Lean4Lean vote", text)
        self.assertNotIn("still lacks a qualified vote", text)

        damaged = {**event, "source_sha256": "0" * 64}
        refused = fleet.read_soundness_quorum(fleet.ROOT, [damaged], current)
        self.assertIsNone(refused)
        for unavailable in ({k: v for k, v in snapshot.items() if k != "soundness_root_quorum"},
                            {**snapshot, "soundness_root_quorum": refused}):
            with self.subTest(has_key="soundness_root_quorum" in unavailable):
                earlier = summary(unavailable)
                self.assertIn("PR-29 recorded no qualified Lean4Lean vote", earlier)
                self.assertNotIn(later, earlier)
                self.assertNotIn("4/4", earlier)
                self.assertEqual(fleet.change_summary(unavailable, snapshot), [later])
                self.assertIn("unavailable", fleet.change_summary(snapshot, unavailable)[0])
        older = {**snapshot, "soundness_root_quorum": {k: v for k, v in quorum.items() if k != "date"}}
        self.assertIn("frozen Clean source " + quorum["epoch"], summary(older))
        self.assertEqual(fleet.change_summary(older, snapshot), [])

    def test_q4_replay_history_selects_the_latest_verified_root_and_links_its_bytes(self):
        from self_proof_fleet_slides import render_slides

        report = fleet.snapshot()
        current = report["source_qualification"]
        events = fleet.recorded_events(fleet.ROOT)
        history = report["soundness_root_quorum_history"]
        self.assertEqual([row["epoch"][:10] for row in history], ["6196c31005", "cfaa8ca036"])
        old, latest = history
        dated = [next(event for event in events if event["source"] == row["source"]) for row in history]
        self.assertEqual(report["soundness_root_quorum"], latest)
        self.assertEqual(old["input_sha256"], latest["input_sha256"])
        self.assertEqual(fleet.displayed_events(dated, current, quorum_history=history), dated)
        for bad_field in ("source_sha256", "input_sha256"):
            damaged = [dated[0], {**dated[1], bad_field: "0" * 64}]
            retained = fleet.read_soundness_quorum_history(fleet.ROOT, damaged, current)
            self.assertEqual(retained, [old])
            self.assertEqual(fleet.displayed_events(damaged, current, quorum_history=retained), dated[:1])
        html = render_slides(report, events, revision="1" * 40)
        url = f"https://github.com/alabsystems/clean/blob/{latest['source_revision']}/{latest['source']}"
        for section in ("answer", "boundary"):
            slide = html.split(f'id="{section}"', 1)[1].split("</section>", 1)[0]
            self.assertIn("At frozen source <code>" + latest["epoch"][:12], slide)
            self.assertIn(url, slide)

    def test_admission_views_share_one_current_refusal_and_preserve_historical_subjects(self):
        events = fleet.recorded_events(fleet.ROOT)
        current = fleet.source_event(events)
        self.assertEqual(current["obligation"], "Q4")
        self.assertEqual(current["source"], "reports/self-proof-const-helper-adoption/README.md")
        snapshot = fleet.snapshot()
        qualified = snapshot["source_qualification"]
        self.assertEqual(qualified["state"], "qualified")
        self.assertEqual(current["input_sha256"], qualified["input_sha256"])
        first = qualified["first_refusal"]
        self.assertIn(f"{first['name']} at line {first['line']}", current["summary"])
        self.assertIn(f"{qualified['prefix_accepted']} of {qualified['records']:,} records", current["summary"])
        original = [row for row in events if row["unit"] == "self-admission-prefix"]
        self.assertTrue(original)
        self.assertNotEqual(snapshot["literal_export"]["sha256"], qualified["input_sha256"])

        def packages(report):
            return {p["key"]: p for p in product_plan(report, "1" * 40, events=events)["packages"]}

        live = packages(snapshot)
        for unit in ("self-admission-prefix", "self-admission", "Q4"):
            self.assertEqual(live[unit]["history"].count(current), 1)
            self.assertEqual(live[unit]["history"], fleet.displayed_events(fleet.recorded_events(fleet.ROOT, unit), qualified,
                                                                            snapshot["followups"], snapshot["soundness_root_quorum_history"],
                                                                            receipts=snapshot["execution_receipts"]))
        self.assertEqual(events.count(current), 1)
        replay = next(row for row in events if row["unit"] == "PR-30")
        paths = next(row for row in events if row["unit"] == "PR-31")
        standalone = [row for row in events if row["unit"] == "S2-S3"
                      and "self-admission-prefix" in row.get("related_obligations", [])]
        self.assertEqual(live["self-admission-prefix"]["history"], original + [current, replay] + standalone)
        self.assertEqual(live["self-admission"]["history"], [current, replay, paths])
        self.assertEqual(live["self-admission"]["status"], "measured_refusal")
        self.assertEqual(live["Q4"]["status"], "needs_gate_evidence")
        for unit in ("self-admission-prefix", "self-admission"):
            self.assertEqual(live[unit]["source"], fleet.REPORT + "/README.md")

        for invalid in (None, {"state": "unverified"}, {**qualified, "qualification_sha256": "f" * 64},
                        {**qualified, "input_sha256": "f" * 64}):
            old = packages({**snapshot, "source_qualification": invalid})
            self.assertEqual(old["self-admission"]["history"], [replay, paths])
            self.assertEqual(old["self-admission-prefix"]["history"], original + [replay] + standalone)
            self.assertNotIn(current, old["Q4"]["history"])

    def test_w6_console_observation_routes_both_failures_to_the_existing_compiler_obligation(self):
        event = next(row for row in fleet.unit_history("W6") if row.get("source_revision") == "550b430cc9db12d8c40ff85ca4fcc62dfad34a13")
        self.assertEqual((event["kind"], event["obligation"]), ("blocker", "X3-X5"))
        report = subprocess.check_output(["git", "show", f"{event['source_revision']}:{event['source']}"], cwd=fleet.ROOT)
        self.assertEqual(hashlib.sha256(report).hexdigest(), event["source_sha256"])
        self.assertIn(event["clean_binary_revision"].encode(), report)
        self.assertIn(event["clean_binary_sha256"].encode(), report)
        for observed in ("14 bytes", "link-demand", "native-eager-io"):
            self.assertIn(observed, event["summary"])
            self.assertIn(observed.encode(), report)
        with contextlib.redirect_stdout(io.StringIO()) as captured:
            fleet.render_events([event])
        self.assertEqual(captured.getvalue().splitlines()[-1],
                         f"  {event['source']} (Clean {event['source_revision']})")
        self.assertEqual(fleet.unit_history("X3-X5").count(event), 1)
        self.assertNotIn(event, fleet.unit_history("W1"))
        snapshot = fleet.snapshot()
        planned = product_plan(snapshot, "1" * 40, events=fleet.unit_history())
        package = next(row for row in planned["packages"] if row["key"] == "X3-X5")
        self.assertEqual(package["history"].count(event), 1)
        bare = product_plan(snapshot, "1" * 40)
        self.assertEqual({key: value for key, value in package.items() if key != "history"},
                         next(row for row in bare["packages"] if row["key"] == "X3-X5"))

    def test_w6_console_success_keeps_its_binary_and_sequencing_boundary(self):
        event, = fleet.recorded_events(fleet.ROOT, "PR-32")
        observations = fleet.followup_results(fleet.ROOT, [event])
        reading = observations["PR-32"]
        self.assertEqual((reading["stdout_bytes"], reading["runtime"], reading["lowered"], reading["pair_refusal"]),
                         (14, "C via cc", "clean-compiler-unvalidated", "native-eager-io"))
        self.assertEqual(fleet.displayed_events([event], None, observations), [event])
        self.assertEqual(fleet.displayed_events([event], None, {}), [])
        for key in ("source_sha256", "source_revision", "receipt_sha256", "module_digest", "clean_binary_sha256"):
            wrong = {**event, key: "0" * len(event[key])}
            self.assertEqual(fleet.followup_results(fleet.ROOT, [wrong]), {}, key)

    def test_w1_string_observations_pin_the_report_and_replay_at_each_producer(self):
        history = fleet.unit_history("W1")
        events = {row.get("source_revision"): row for row in history}
        bridge = events["c72b68371186c66ab0debdd8e2714877d3bab6c7"]
        meaning = events["c08933d6cd27e219f820c4bb797dea0af5de7fde"]
        self.assertEqual((bridge["kind"], meaning["kind"]), ("measurement", "proof"))
        for row in (bridge, meaning):
            for path, pin in ((row["source"].split("#", 1)[0], row["source_sha256"]),
                              (row["replay_source"], row["replay_sha256"])):
                content = subprocess.check_output(["git", "show", f"{row['source_revision']}:{path}"], cwd=fleet.ROOT)
                self.assertEqual(hashlib.sha256(content).hexdigest(), pin)
            self.assertIn("W1 still requires", row["summary"])
        self.assertIn("six inputs", bridge["summary"])
        self.assertIn("native-string-carrier", bridge["summary"])
        self.assertIn("every Lean String", meaning["summary"])
        self.assertIn("Classical.choice", meaning["summary"])

    def test_w1_fenced_decoder_replay_pins_the_portable_subject_and_named_kernel_controls(self):
        fixture_revision = "34a11f22a01f19a1c5b3bb770fc488c9c8c0f2dd"
        matches = [row for row in fleet.unit_history("W1") if row.get("replay_revision") == fixture_revision]
        self.assertEqual(len(matches), 1)
        event = matches[0]
        self.assertEqual(event["kind"], "measurement")
        self.assertEqual(event["replayer_source_revision"], "c08933d6cd27e219f820c4bb797dea0af5de7fde")
        transcript = subprocess.check_output(["git", "show", f"{event['source_revision']}:{event['source']}"], cwd=fleet.ROOT)
        fixture = subprocess.check_output(["git", "show", f"{fixture_revision}:{event['replay_source']}"], cwd=fleet.ROOT)
        self.assertEqual(hashlib.sha256(transcript).hexdigest(), event["source_sha256"])
        self.assertEqual(hashlib.sha256(fixture).hexdigest(), event["replay_sha256"])
        subject = json.loads(fixture)
        self.assertEqual(subject["roots"], ["encodedCodepoints", "literalCodepoints", "tableStringCodepoints"])
        expected = [f"CONTROL {outcome} {case['proof']} {case['goal']}"
                    for group, outcome in (("positive", "accepted"), ("negative", "kernel-type-mismatch"))
                    for case in subject[group]]
        lines = transcript.decode().splitlines()
        self.assertEqual([line for line in lines if line.startswith("CONTROL ")], expected)
        self.assertEqual(lines[-1], "MODEL_REFERENCE_REPLAY roots=3 admitted=3582 positive=2 negative=2 "
                         "manifest=34cf5dd1000135fee1a9fec8be29e17d952bcd75c662220c6fd8ee27f50fff0f")
        self.assertIn("W1 still requires", event["summary"])

    def test_planning_w0_shadow_is_preview_only_and_exposes_its_exit(self):
        shadow = ["candidate clean", "build receipt.json", "a" * 64]
        args = ["fleet", "--planning", "preview", "--json", "--planning-shadow-w0", *shadow]
        for state, exit_code in (("matched", 0), ("deferred", 1)):
            with self.subTest(state=state), patch.object(sys, "argv", args), \
                 patch.object(fleet, "planning_view", return_value={"w0_native_shadow": {"state": state}}) as preview, \
                 contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(fleet.main(), exit_code)
            self.assertEqual(json.loads(output.getvalue())["w0_native_shadow"]["state"], state)
            preview.assert_called_once_with("preview", Path.home() / "publication", w0_shadow=shadow)

        for selector in ([], ["--planning", "status"], ["--planning", "design"], ["--planning", "publish"]):
            with self.subTest(selector=selector), \
                 patch.object(sys, "argv", ["fleet", *selector, "--planning-shadow-w0", *shadow]), \
                 patch.object(fleet, "planning_view") as preview, contextlib.redirect_stderr(io.StringIO()), \
                 self.assertRaises(SystemExit) as refused:
                fleet.main()
            self.assertEqual(refused.exception.code, 2)
            preview.assert_not_called()

    def test_planning_native_w0_is_preview_only_and_exposes_its_exit(self):
        build = ("candidate clean", "build receipt.json", "a" * 64)
        flag = ["--planning-native-w0", *build]
        for state, exit_code in (("matched", 0), ("deferred", 1)):
            with self.subTest(state=state), \
                 patch.object(sys, "argv", ["fleet", "--planning", "preview", "--json", *flag]), \
                 patch.object(fleet, "planning_view", return_value={"w0_native": {"state": state}}) as preview, \
                 contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(fleet.main(), exit_code)
            self.assertEqual(json.loads(output.getvalue())["w0_native"]["state"], state)
            preview.assert_called_once_with("preview", Path.home() / "publication", w0_native=build)
        for selector in ([], ["--planning", "status"], ["--planning", "design"], ["--planning", "publish"],
                         ["--planning", "preview", "--planning-shadow-w0", *build]):
            with self.subTest(selector=selector), patch.object(sys, "argv", ["fleet", *selector, *flag]), \
                 patch.object(fleet, "planning_view") as preview, contextlib.redirect_stderr(io.StringIO()), \
                 self.assertRaises(SystemExit) as refused:
                fleet.main()
            self.assertEqual(refused.exception.code, 2)
            preview.assert_not_called()

    def test_planning_native_w0_defers_derivation_without_reading_python(self):
        import self_proof_fleet_product as product
        import self_proof_fleet_w0 as w0

        build = ("candidate", "receipt", "a" * 64)
        commit = "b" * 40
        publication = Path("preview tracker")
        failure = "native board derivation failed"
        with patch.object(w0, "run_pinned_w0_json", side_effect=ValueError(failure)) as run, \
             patch.object(scoreboard, "derive", side_effect=AssertionError("Python W0 called")), \
             patch.object(fleet, "clean_revision", return_value=commit), \
             patch.object(product, "sync_product") as sync:
            self.assertIs(fleet.planning_view("preview", publication, w0_native=build), sync.return_value)
            with self.assertRaisesRegex(ValueError, failure):
                fleet.snapshot(native_w0=build)
        self.assertEqual(run.call_count, 2)
        run.assert_called_with(build, git_root=fleet.ROOT, data_root=fleet.ROOT)
        report, actual_commit, actual_publication = sync.call_args.args
        self.assertEqual((actual_commit, actual_publication), (commit, publication))
        self.assertEqual(sync.call_args.kwargs, {"clean_root": fleet.ROOT, "w0_native": build})
        self.assertEqual(report["scoreboard_warning"], failure)
        self.assertEqual(report["metrics"], {})
        self.assertIn("literal_export", report)

    def test_focused_history_agrees_with_timeline_without_affecting_snapshot(self):
        baseline = fleet.snapshot()

        def focused(args):
            output = io.StringIO()
            with patch.object(sys, "argv", ["fleet", "--unit", "W1", *args]), \
                 patch.object(fleet, "snapshot", return_value=copy.deepcopy(baseline)), \
                 contextlib.redirect_stdout(output):
                self.assertEqual(fleet.main(), 0)
            return output.getvalue()

        expected = fleet.unit_history("W1")
        document = json.loads(focused(["--json"]))
        self.assertEqual(document.pop("selected_units"), ["W1"])
        unit = next(row for row in document["units"] if row["id"] == "W1")
        self.assertEqual(unit.pop("history"), expected)
        self.assertEqual(document, baseline)
        plain = focused([])
        for event in expected:
            self.assertIn(event["date"], plain)
            self.assertIn(event["summary"], plain)
            source = event["source"]
            if "source_revision" in event:
                source += f" (Clean {event['source_revision']})"
            self.assertIn("  " + source, plain.splitlines())
        with tempfile.TemporaryDirectory() as empty, patch.object(fleet, "ROOT", Path(empty)):
            document = json.loads(focused(["--json"]))
            document.pop("selected_units")
            self.assertEqual(document, baseline)

    def test_catalog_rejects_broken_dependencies(self):
        a = {"id": "a", "kind": "proof", "goal": "A", "prerequisites": [],
             "closes_with": "A proof", "source": "plan"}
        b = {**a, "id": "b", "prerequisites": ["a"]}
        self.assertEqual(set(fleet.catalog([a, b])), {"a", "b"})
        for rows in ([a, a], [b], [{**a, "prerequisites": ["b"]}, b]):
            with self.assertRaises(ValueError):
                fleet.catalog(rows)

    def test_a0_waits_for_trust_ph4_without_creating_a_clean_assignment(self):
        snapshot = fleet.snapshot()
        by_id = {row["id"]: row for row in snapshot["units"]}
        self.assertEqual(by_id["Trust-Ph4"]["status"], "needs_gate_evidence")
        self.assertIn("Trust-Ph4", by_id["A0"]["waiting_on"])
        ready = {row["id"] for row in fleet.ready_units(snapshot["units"])}
        self.assertTrue({"A0", "Trust-Ph4"}.isdisjoint(ready))
        for key in ("W1", "C4-C5", "Q4"):
            row = by_id[key]
            self.assertEqual(key in ready, not row["waiting_on"] and row["status"] != "qualified_snapshot")

        design = product_plan(snapshot, "1" * 40)
        packages = {row["key"]: row for row in design["packages"]}
        self.assertNotIn("Trust-Ph4", packages)
        self.assertIn("Trust-Ph4", packages["A0"]["depends_on"])
        self.assertIn("Trust-Ph4", packages["A0"]["waiting_on"])
        self.assertEqual(packages["W1"]["recorded_claims"], by_id["W1"]["recorded_claims"])
        external = next(row for row in design["external_prerequisites"] if row["id"] == "Trust-Ph4")
        self.assertEqual(external["closes_with"], by_id["Trust-Ph4"]["closes_with"])

    def test_claims_bind_to_the_unit_label(self):
        plan = """## 9. Claims
| Units | Claimed by | Since |
|---|---|---|
| W1/E4/X2: finish executable; W3 is deferred | owner | date |
| W10: another unit | other | date |
| Lane A A1.1 only: scalar leaf | arithmetic owner | date |
| Q1: earlier qualification | Complete, claim released | date |

Historical allocations
| W1 | former owner | yesterday |"""
        claims = fleet.plan_claims(plan)
        for unit in ("W1", "E4", "X2"):
            self.assertEqual([c["owner"] for c in fleet.claims_for(unit, claims)], ["owner"])
        self.assertFalse(fleet.claims_for("W3", claims))
        self.assertFalse(fleet.claims_for("Q1", claims))
        self.assertEqual(fleet.claims_for(["W1", "W10"], claims), claims[:2])
        self.assertEqual(fleet.claims_for("A1.1", claims)[0]["owner"], "arithmetic owner")

    def test_explicit_release_closes_the_claim_but_a_partial_release_does_not(self):
        plan = """## 9. Claims
| Units | Claimed by | Since |
|---|---|---|
| W1 first qualification | Released. Evidence recorded. | date |
| W1 next qualification | Released by Codex. Evidence recorded. | date |
| W1 current entry | Codex | date |
| W1 term data | Codex in the landing worktree, source qualification released | date |
| W1 follow-up | Released the source qualification only. Codex owns the replay. | date |

Historical allocations
| W1 former entry | former owner | yesterday |"""
        self.assertEqual(
            [row["task"] for row in fleet.claims_for("W1", fleet.plan_claims(plan))],
            ["W1 current entry", "W1 term data", "W1 follow-up"],
        )

    def test_changed_input_is_not_a_prefix_gain(self):
        old = {"schema": fleet.SCHEMA, "metrics": {}, "units": [], "literal_export":
               {"sha256": "a", "root": "T", "state": "measured", "prefix_accepted": 0}}
        now = copy.deepcopy(old)
        now["literal_export"].update(sha256="b", prefix_accepted=8)
        changes = fleet.change_summary(old, now)
        self.assertEqual(len(changes), 1)
        self.assertIn("different input bytes", changes[0])
        now["literal_export"]["sha256"] = "a"
        self.assertIn("0 -> 8", fleet.change_summary(old, now)[0])
        self.assertEqual(fleet.change_summary(old, old), [])
        now["literal_export"] = {"state": "unverified", "reason": "missing receipts"}
        self.assertIn("no comparable prefix counts", fleet.change_summary(old, now)[0])

    def test_candidate_root_vote_changes_keep_the_input_and_receipt(self):
        old = {"schema": fleet.SCHEMA, "metrics": {}, "units": [], "literal_export": {"state": "measured"}}
        trial = {"state": "recorded", "input_sha256": "a" * 64, "baseline_input_sha256": "b" * 64,
                 "result_sha256": "c" * 64, "stock_admitted": 3, "named": 3, "root": "soundness"}
        now = {**old, "const_helper_trial": trial}
        change, = fleet.change_summary(old, now)
        for expected in ("experimental stock ck0", "3 of 3", "soundness", "a" * 64, "b" * 64, "c" * 64):
            self.assertIn(expected, change)
        self.assertEqual(fleet.change_summary(now, now), [])
        expanded = {**trial, "baseline_stock_admitted": 1, "baseline_named": 2}
        self.assertEqual(fleet.change_summary(now, {**now, "const_helper_trial": expanded}), [])
        revised = {**trial, "result_sha256": "d" * 64}
        self.assertIn("d" * 64, fleet.change_summary(now, {**now, "const_helper_trial": revised})[0])
        missing = {"state": "unverified", "reason": "candidate artifact differs"}
        self.assertIn("candidate artifact differs", fleet.change_summary(now, {**old, "const_helper_trial": missing})[0])
        self.assertIn("unavailable", fleet.change_summary(now, old)[0])

    def test_pr29_comparison_reports_only_qualified_source_and_preserves_historical_observations(self):
        old = {"schema": fleet.SCHEMA, "metrics": {}, "units": [], "literal_export": {"state": "measured"}}
        current = {"state": "qualified", "qualified_revision": "d" * 40, "input_sha256": "a" * 64,
                   "qualification_sha256": "b" * 64, "stock_admitted": 5, "resident_equal": 5, "declarations": 5,
                   "root": "KCheck.root", "prefix_accepted": 0, "records": 4, "first_refusal": {"name": "Packet", "line": 11}}
        now = {**old, "source_qualification": current}
        diff, = fleet.change_summary(old, now)
        for expected in ("5 of 5", "0 consecutive records out of 4", "Packet", "Lean4Lean", "b" * 64):
            self.assertIn(expected, diff)
        self.assertFalse(fleet.change_summary(now, now))
        self.assertIn("unavailable", fleet.change_summary(now, old)[0])
        dated = {"unit": "PR-29", "obligation": "Q4", "kind": "measurement",
                 "input_sha256": current["input_sha256"], "qualification_sha256": current["qualification_sha256"]}
        historical = {"unit": "PR-28", "kind": "measurement"}
        events = [historical, dated]
        self.assertEqual(fleet.displayed_events(events, current), events)
        for missing in (None, {"state": "unverified"}, {**current, "qualification_sha256": "c" * 64}):
            self.assertEqual(fleet.displayed_events(events, missing), [historical])

    def test_requalified_semantic_theorem_is_visible(self):
        old = {"schema": fleet.SCHEMA, "metrics": {}, "units": [], "literal_export": {"state": "unverified"},
               "c3": {"revision": "a", "state": "qualified_snapshot"}}
        now = copy.deepcopy(old)
        now["c3"]["revision"] = "b"
        self.assertIn("C3 qualification: a -> b", fleet.change_summary(old, now))

    def test_provenance_changes_are_visible_when_values_stay_equal(self):
        old = {"schema": fleet.SCHEMA, "metrics": {"planted_false_clean":
               {"minted_under_mutant": 1, "sites": 2, "measured_commit": "A"}},
               "literal_export": {"state": "unverified"}, "units": []}
        now = copy.deepcopy(old)
        now["metrics"]["planted_false_clean"]["measured_commit"] = "B"
        self.assertIn("counts unchanged", fleet.change_summary(old, now)[0])


class W0GateResultTest(unittest.TestCase):
    def setUp(self):
        from self_proof_fleet_product_test import W0BuildExportTest

        self.fixture = W0BuildExportTest()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        source = self.fixture.source
        crate = source / "crates/clean"
        main = crate / "src/bin/clean.rs"
        main.parent.mkdir(parents=True)
        main.write_text("fn main() {}\n", encoding="utf-8")
        manifest = crate / "Cargo.toml"
        manifest.write_text('[package]\nname = "clean"\nversion.workspace = true\n', encoding="utf-8")
        self.fixture.git("add", "--", "crates/clean")
        self.fixture.git(
            "-c", "user.name=W0 fixture", "-c", "user.email=w0@example.invalid",
            "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null",
            "commit", "-qm", "Add the local Clean target",
        )
        commit = self.fixture.git("rev-parse", "HEAD").decode("ascii").strip()
        self.fixture.commit = commit
        self.fixture.version = f"clean 0.9.4+g{commit}"
        self.fixture.candidate = source / "target/w0-scoreboard-gate/debug/clean"
        self.fixture.candidate.parent.mkdir(parents=True)
        image_digest = self.fixture.write_candidate("normal")
        executable = str(self.fixture.candidate)
        self.record_path = source.parent / "gate result.json"

        cargo_artifact = {
            "reason": "compiler-artifact",
            "package_id": f"path+{crate.as_uri()}#0.9.4",
            "manifest_path": str(manifest),
            "target": {"name": "clean", "kind": ["bin"], "crate_types": ["bin"], "src_path": str(main)},
            "profile": {"test": False},
            "filenames": [executable],
            "executable": executable,
            "trust_executable_sha256": image_digest,
        }
        # Use the actual producer's public source, independently of the consumer's allowlist.
        qualified_at = "3ae1f67626406b1ec004d00f03f6592f5cea3fec"
        scripts = (
            "scripts/run_w0_scoreboard_gate.sh", "scripts/self_proof_fleet_w0.py",
            "scripts/kcheck_coverage_export.py", "scripts/cargo_test_nonvacuous.sh",
        )
        self.record = {
            "schema": "clean.w0_gate_result.v1",
            "source_checkout": str(source),
            "source_commit": commit,
            "source_tree": self.fixture.git("rev-parse", "HEAD^{tree}").decode("ascii").strip(),
            "board_sha256": hashlib.sha256(self.fixture.git("cat-file", "blob", "HEAD:data/self_proof_scoreboard.json")).hexdigest(),
            "coverage_sha256": hashlib.sha256(self.fixture.git("cat-file", "blob", "HEAD:data/kcheck_coverage.json")).hexdigest(),
            "executable": executable,
            "executable_sha256": image_digest,
            "version": self.fixture.version,
            "cargo_artifact": cargo_artifact,
            "cargo_log_sha256": hashlib.sha256(json.dumps(cargo_artifact).encode("utf-8") + b"\n").hexdigest(),
            "qualification_sha256": {
                path: hashlib.sha256(subprocess.check_output(
                    ["git", "--no-replace-objects", "cat-file", "blob", f"{qualified_at}:{path}"],
                    cwd=fleet.ROOT, timeout=10,
                )).hexdigest()
                for path in scripts
            },
        }

    @staticmethod
    def encode(record):
        return (json.dumps(record, indent=2, sort_keys=True) + "\n").encode("utf-8")

    def cli(self, *args):
        with patch.object(sys, "argv", ["fleet", *args]), \
             contextlib.redirect_stdout(io.StringIO()) as stdout, \
             contextlib.redirect_stderr(io.StringIO()) as stderr:
            status = fleet.main()
        return status, stdout.getvalue(), stderr.getvalue()

    def gate_args(self, digest):
        return ("--export-w0-gate-result", str(self.record_path), digest, str(self.fixture.output))

    def export_result(self, raw=None, *, digest=None):
        raw = self.encode(self.record) if raw is None else raw
        self.record_path.write_bytes(raw)
        pin = hashlib.sha256(raw).hexdigest() if digest is None else digest
        return self.cli(*self.gate_args(pin), "--json")

    def assert_gate_refusal(self, result, diagnostic, *, candidate_calls=0):
        status, stdout, stderr = result
        self.assertEqual((status, stdout), (2, ""), stderr)
        self.assertIn(diagnostic, stderr)
        self.assertEqual(len(self.fixture.calls()), candidate_calls, stderr)
        self.fixture.assert_failed_child_cleaned_up()

    def test_gate_result_export_agrees_with_direct_export_receipt(self):
        direct = self.cli("--export-w0-build", str(self.fixture.source), str(self.fixture.candidate),
                          self.record["executable_sha256"], str(self.fixture.output))
        result = self.export_result()
        self.assertEqual((direct[0], direct[2]), (0, ""), direct[2])
        self.assertEqual((result[0], result[2]), (0, ""), result[2])
        earlier = json.loads(direct[1])
        exported = json.loads(result[1])
        self.assertEqual(set(exported), {"executable", "receipt", "receipt_sha256"})
        receipt = Path(exported["receipt"]).read_bytes()
        self.assertEqual(receipt, Path(earlier["receipt"]).read_bytes())
        self.assertEqual(exported["receipt_sha256"], earlier["receipt_sha256"])
        self.assertEqual(exported["receipt_sha256"], hashlib.sha256(receipt).hexdigest())
        self.assertEqual(Path(exported["executable"]).read_bytes(), self.fixture.candidate.read_bytes())
        commands = [args for _, args, _ in self.fixture.calls()]
        self.assertEqual(len(commands), 4)
        self.assertEqual(commands[:2], commands[2:])
        self.assertEqual(commands[0], ["--version"])

    def test_gate_result_export_refuses_wrong_independent_digest_and_bad_json(self):
        raw = self.encode(self.record)
        duplicate = raw.replace(b"{\n", b'{\n  "schema": "clean.w0_gate_result.v1",\n', 1)
        missing = {name: value for name, value in self.record.items() if name != "coverage_sha256"}
        for content, digest, diagnostic in (
            (raw, "0" * 64, "differs from its supplied SHA-256"),
            (b"{\n", None, "invalid W0 gate result"),
            (duplicate, None, "a key is written twice in one object"),
            (self.encode({**self.record, "extra": True}), None, "unsupported W0 gate result schema or fields"),
            (self.encode(missing), None, "unsupported W0 gate result schema or fields"),
            (self.encode({**self.record, "cargo_log_sha256": "not a digest"}), None,
             "invalid W0 gate result cargo_log_sha256"),
        ):
            with self.subTest(diagnostic=diagnostic):
                self.assert_gate_refusal(self.export_result(content, digest=digest), diagnostic)

    def test_gate_result_export_refuses_wrong_source_artifact_or_qualifier(self):
        wrong_source = "W0 gate result producing source or executable has changed"
        wrong_image = "W0 gate result does not select the normal Clean Cargo artifact"
        artifact = self.record["cargo_artifact"]
        qualification = self.record["qualification_sha256"]
        cases = (
            ("source_tree", "0" * 40, wrong_source),
            ("board_sha256", "0" * 64, wrong_source),
            ("coverage_sha256", "0" * 64, wrong_source),
            ("cargo_artifact", {**artifact, "profile": {"test": True}}, wrong_image),
            ("cargo_artifact", {**artifact, "package_id": "path+file:///elsewhere/clean#0.9.4"}, wrong_image),
            ("cargo_artifact", {**artifact, "trust_executable_sha256": "0" * 64}, wrong_image),
            ("qualification_sha256", {**qualification, "scripts/run_w0_scoreboard_gate.sh": "0" * 64},
             "does not match a qualified script set"),
        )
        for field, value, diagnostic in cases:
            with self.subTest(field=field, value=value):
                raw = self.encode({**self.record, field: value})
                self.assert_gate_refusal(self.export_result(raw), diagnostic)

    def test_gate_result_export_accepts_only_a_complete_replayed_registry_tuple(self):
        import self_proof_fleet_w0_result as gate_result

        runner, helper = "scripts/run_w0_scoreboard_gate.sh", "scripts/self_proof_fleet_w0.py"
        historical = self.record["qualification_sha256"]
        current = {**historical, runner: "1" * 64, helper: "2" * 64}
        inputs = {path: digest for path, digest in current.items() if path != runner}
        pin = {
            "script_sha256": current[runner],
            "inputs": inputs,
            "replayed": {
                "script_sha256": current[runner],
                "inputs_sha256": hashlib.sha256(json.dumps(sorted(inputs.items())).encode("utf-8")).hexdigest(),
            },
        }
        registry = Path(gate_result.__file__).resolve().parents[1] / "data" / "gate_registry.json"
        row = {"id": "run_w0_scoreboard_gate", "path": runner, "demonstrated": pin}
        current_record = self.encode({**self.record, "qualification_sha256": current})
        mixed = self.encode({**self.record, "qualification_sha256": {**current, helper: historical[helper]}})
        diagnostic = "does not match a qualified script set"
        stale_pin = {**pin, "replayed": {**pin["replayed"], "inputs_sha256": "0" * 64}}
        registry_row = {**row, "demonstrated": stale_pin}
        read_bytes = Path.read_bytes

        def read_fixture(path):
            if path == registry:
                return self.encode({"rows": [registry_row]})
            return read_bytes(path)

        with patch.object(Path, "read_bytes", read_fixture):
            self.assert_gate_refusal(self.export_result(current_record), diagnostic)
            registry_row = row
            self.assert_gate_refusal(self.export_result(mixed), diagnostic)
            rc, stdout, stderr = self.export_result(current_record)
        self.assertEqual((rc, stderr), (0, ""), stderr)
        self.assertEqual(set(json.loads(stdout)), {"executable", "receipt", "receipt_sha256"})

    def test_gate_result_export_checks_the_exact_recorded_version_before_the_board(self):
        wrong = {**self.record, "version": f"clean 0.8.0+g{self.fixture.commit}"}
        self.assert_gate_refusal(self.export_result(self.encode(wrong)),
                                 "executable version differs from the record", candidate_calls=1)
        self.assertEqual(self.fixture.calls()[0][1], ["--version"])

    def test_gate_result_export_refuses_an_image_changed_after_the_gate(self):
        with self.fixture.candidate.open("ab") as binary:
            binary.write(b"\n# different image\n")
        self.assert_gate_refusal(self.export_result(), "W0 gate result producing source or executable has changed")

    def test_gate_result_export_rejects_other_views_before_candidate_execution(self):
        raw = self.encode(self.record)
        self.record_path.write_bytes(raw)
        args = self.gate_args(hashlib.sha256(raw).hexdigest())
        for mode in (("--planning", "design"), ("--timeline",), ("--native-w0", "clean", "receipt", "a" * 64)):
            with self.subTest(mode=mode), patch.object(sys, "argv", ["fleet", *args, *mode]), \
                 contextlib.redirect_stdout(io.StringIO()) as stdout, \
                 contextlib.redirect_stderr(io.StringIO()) as stderr, self.assertRaises(SystemExit) as refused:
                fleet.main()
            self.assertEqual(refused.exception.code, 2)
            self.assertEqual(stdout.getvalue(), "")
            self.assertIn("--export-w0-gate-result", stderr.getvalue())
            self.assertEqual(self.fixture.calls(), [])
            self.fixture.assert_failed_child_cleaned_up()


if __name__ == "__main__":
    unittest.main()
