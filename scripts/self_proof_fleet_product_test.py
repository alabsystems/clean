# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Exercise product planning synchronization without a live tracker or Git pushes."""

import copy
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import self_proof_fleet_product as product
import self_proof_fleet_w0 as w0

COMMIT = "a" * 40
METRICS = ("date", "goal", "metric", "value", "unit", "machine", "source", "note")
FAMILY_ABSENT = "aterm db table: no typed table of that name in this build (see `aterm db table ls`)"
PUBLICATION_CAPS = {"schema": 1, "product": "aGoals", "backend": "publication", "family_registered": False}


def tsv(columns, rows):
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=columns, delimiter="\t", lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return output.getvalue()


class Tracker:
    def __init__(self, clean, publication, blobs):
        self.clean = clean
        self.publication = publication
        self.blobs = blobs
        self.rows = []
        self.calls = []
        self.writes = []
        self.native = None
        self.measure_help = None
        self.capability_response = None
        self.show_response = None
        self.absent_scan = ("", 1, FAMILY_ABSENT)
        self.native_writes = []
        self.unreadable_native = False
        self.native_commit = COMMIT
        self.fail_after_append = False
        self.prior_differs = False
        self.stale = self.dirty = self.ahead = self.drop = self.off_main = False
        self.origin = "https://github.com/alabsystems/publication.git"
        self.publication_commit = "1" * 40
        self.central_tables = {path.name: path.read_text() for path in (publication / "goals/data").glob("*.tsv")}
        self.offline = False

    def shown_goal(self):
        def ref(table, line):
            return f"{self.publication_commit}:goals/data/{table}.tsv:{line}"

        package = next(csv.DictReader(io.StringIO(self.central_tables["packages.tsv"]), delimiter="\t"))
        deps = [x.strip() for x in package["depends"].replace(";", ",").split(",") if x.strip()]
        package = {**package, "pk": package["id"], "publication_ref": ref("packages", 2),
                   "depends": deps, "claim": package["claimed_by"], "dispatchable": False,
                   "exit": {"command": package["exit_command"], "expect": package["exit_expect"]}}
        measures, units = [], {}
        for line, row in enumerate(self.rows, 2):
            key = "E1." + row["metric"]
            measures.append({**row, "metric": key, "at": row["date"], "pk": ref("metrics", line),
                             "publication_ref": ref("metrics", line)})
            units.setdefault(key, set()).add(row["unit"])
        definitions = [{"id": k, "pk": k, "goal": "E1", "name": k[3:], "units": sorted(v),
                        "unit": next(iter(v)) if len(v) == 1 else None} for k, v in units.items()]
        return {"source": "Publication at " + self.publication_commit,
                "goals": [{"id": "E1", "pk": "E1", "title": "Goal returned by aGoals", "target": "Self-admission",
                           "state": "measured", "baseline": "Open", "publication_ref": ref("goals", 2)}],
                "packages": [package], "metrics": definitions, "measures": measures, "findings": [],
                "lanes": [{"id": "proof", "pk": "proof", "name": "Proof", "goals": ["E2"],
                           "publication_ref": ref("lanes", 3)}],
                "decisions": [{"id": "D1", "pk": "D1", "lane": "proof", "decision": "Use W1",
                               "reason": "Run the checker", "publication_ref": ref("decisions", 4)}]}

    def __call__(self, argv, cwd):
        self.calls.append((argv, cwd))
        result = lambda stdout="", code=0, stderr="": subprocess.CompletedProcess(argv, code, stdout, stderr)
        if argv[0] == "aterm":
            if argv[1:3] == ["goals", "measure"] and argv[3:] == ["--help"]:
                if self.measure_help is not None:
                    return result(*self.measure_help)
                if self.native is None and self.capability_response is None:
                    return result(code=2, stderr="aterm: unknown command 'goals' (try --help)")
                return result("measure METRIC VALUE --source SOURCE")
            if argv[1:] == ["goals", "capabilities", "--json"]:
                assert self.capability_response is not None
                return result(*self.capability_response)
            if argv[1:] == ["goals", "show", "E1", "--json"]:
                assert cwd == self.publication
                return result(*self.show_response) if self.show_response else result(json.dumps(self.shown_goal()))
            if self.native is None:
                return result(*self.absent_scan)
            if argv[1:3] == ["goals", "measure"]:
                assert cwd == self.clean and argv[5] == "--source" and len(argv) == 7
                self.native_writes.append(argv)
                self.native.setdefault("measure", []).append({"metric": argv[3], "value": argv[4],
                                                             "source": argv[6], "commit": self.native_commit})
                if self.fail_after_append:
                    self.unreadable_native = True
                return result("recorded locally")
            self.assert_scan(argv)
            collection = argv[5]
            if collection == "measure":
                if self.unreadable_native:
                    return result(code=1, stderr="log scan unavailable")
                metric = argv[7].split("=", 1)[1]
                rows = [r for r in self.native.get("measure", []) if r["metric"] == metric]
            else:
                rows = self.native[collection]
            return result(json.dumps({"collection": collection, "rows": rows, "malformed": 0}))
        if argv[:4] == ["git", "ls-tree", "-r", "--name-only"]:
            return result("\n".join(argv[argv.index("--") + 1:]))
        if argv[:2] == ["git", "show"]:
            spec = argv[2]
            if cwd == self.clean:
                rev, path = spec.split(":", 1)
                if rev != COMMIT or path not in self.blobs:
                    return result(code=1, stderr="no blob")
                return result(self.blobs[path])
            if spec == "refs/remotes/origin/main:goals/data/metrics.tsv":
                return result(tsv(METRICS, self.rows))
            if spec.startswith(self.publication_commit + ":goals/data/"):
                table = spec.split("/")[-1]
                return result(tsv(METRICS, self.rows) if table == "metrics.tsv" else self.central_tables[table])
        if argv[:2] == ["git", "rev-parse"]:
            if argv[2:] == ["--show-toplevel"]:
                return result(code=1, stderr="not a git repository") if self.offline else result(str(cwd))
            if argv[2:] == ["--verify", "refs/remotes/origin/main^{commit}"]:
                return result(self.publication_commit) if self.publication_commit else result(code=1, stderr="no revision")
            return result(COMMIT)
        if argv[:3] == ["git", "merge-base", "--is-ancestor"]:
            return result(code=int(self.ahead if cwd == self.publication else self.off_main))
        if argv[:2] == ["git", "status"]:
            return result("M goals/data/metrics.tsv" if self.dirty else "")
        if argv[:2] == ["git", "remote"]:
            return result(self.origin)
        if argv[:2] == ["git", "diff"]:
            return result(code=int(self.prior_differs and len(argv) >= 6 and argv[4] == COMMIT))
        if argv[:2] == ["git", "fetch"]:
            return result()
        if argv[-1] == "--check" and argv[-2] == str(self.clean / "scripts/self_proof_scoreboard.py"):
            return result("SELF_PROOF_SCOREBOARD=ok the record matches its sources" if not self.stale else "",
                          int(self.stale), "scoreboard stale" if self.stale else "")
        if argv[2] == str(self.publication / "goals/tools/goals.py") and argv[3:5] == ["measure", "E1"]:
            assert argv[-1] == "--push"
            self.writes.append(argv)
            read = lambda key: argv[argv.index("--" + key) + 1]
            row = {k: read(k) for k in ("metric", "value", "unit", "source", "note")}
            if not self.drop:
                self.rows.append({**row, "goal": "E1", "date": "2026-11-17", "machine": "fake"})
            return result()
        raise AssertionError(f"unexpected command {argv!r} in {cwd}")

    @staticmethod
    def assert_scan(argv):
        assert argv[1:5] == ["db", "table", "scan", "lab/tracker"]
        if argv[5] == "measure":
            assert argv[6] == "--where" and argv[7].startswith("metric=E1.") and argv[8:] == ["--json"]
        else:
            assert argv[6:] == ["--where", "goal=E1", "--json"]


class ProductTest(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.clean = Path(scratch.name).resolve() / "clean"
        self.pub = Path(scratch.name).resolve() / "publication"
        data = self.pub / "goals/data"
        data.mkdir(parents=True)
        (self.pub / "goals/tools").mkdir()
        (self.pub / "goals/tools/goals.py").touch()
        (data / "goals.tsv").write_text("id\ttitle\ttarget\nE1\tClean proves itself\tSelf-admission\n")
        (data / "packages.tsv").write_text(
            "id\tgoal\tdepends\tstate\tclaimed_by\texit_expect\tevidence\tlane\ttitle\texit_command\tclaimed_on\n"
            "PR-03\tE1\tPR-02\trunning\tholder\tfull checker\topen\tproof\tCheck\tcheck-proof\ttoday\n"
            "PR-04\tE2\t\tdone\t\tx\ty\tproof\tOther\tcheck-other\t\n")
        (data / "metrics.tsv").write_text(tsv(METRICS, []))
        self.production = {"source": str(product.COVERAGE), "real_declarations_decided": 0,
                           "reason": "no site consults compiled kcheck"}
        self.blobs = {}
        self.put(product.BOARD, {"headline": {"decided_by_compiled_kcheck": self.production}})
        self.put(product.COVERAGE, {"real_declarations_decided": 0})
        self.put(product.REPORT / "receipt-set.json", {"input_sha256": "b" * 64})
        self.receipt = {"state": "measured", "sha256": "b" * 64, "root": "KCheck.root", "declarations": 4,
                        "resident_equal": 4, "prefix_accepted": 0, "first_refusal": {"name": "Decl", "line": 9},
                        "public_source_commit": "c" * 40, "lean_module_source": "d" * 40}
        self.snapshot = {"schema": product.SCHEMA, "literal_export": copy.deepcopy(self.receipt),
                         "scoreboard_warning": None, "metrics": {"production": copy.deepcopy(self.production)},
                         "units": [{"id": "C3", "kind": "proof", "goal": "Model soundness", "prerequisites": ["M4"],
                                    "closes_with": "qualified proof gate", "source": "plan.md#C3",
                                    "status": "qualified_snapshot", "waiting_on": [],
                                    "recorded_claims": [{"by": "holder", "state": "hold"}]}]}
        self.tracker = Tracker(self.clean, self.pub, self.blobs)
        self.reader = patch.object(product, "read_export_evidence", return_value=self.receipt).start()
        self.addCleanup(patch.stopall)

    def put(self, path, value):
        raw = json.dumps(value) + "\n"
        self.blobs[str(path)] = raw
        dest = self.clean / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(raw)

    def sync(self, publish=False, **options):
        return product.sync_product(self.snapshot, COMMIT, self.pub, clean_root=self.clean,
                                    runner=self.tracker, publish=publish, **options)

    def w0_shadow(self, **updates):
        self.w0_executable = self.clean.parent / "candidate clean"
        self.w0_executable.write_bytes(b"candidate executable fixture")
        self.w0_executable.chmod(0o755)
        self.w0_receipt = self.clean.parent / "build receipt.json"
        self.w0_version = "clean 0.0.0+g" + COMMIT
        row = {"schema": "clean.w0_planning_build.v1", "source_commit": COMMIT, "source_tree": COMMIT,
               "executable_sha256": hashlib.sha256(self.w0_executable.read_bytes()).hexdigest(),
               "version": self.w0_version,
               "board_sha256": hashlib.sha256((self.clean / product.BOARD).read_bytes()).hexdigest(),
               "coverage_sha256": hashlib.sha256((self.clean / product.COVERAGE).read_bytes()).hexdigest()}
        self.w0_receipt.write_text(json.dumps({**row, **updates}) + "\n")
        return self.w0_executable, self.w0_receipt, hashlib.sha256(self.w0_receipt.read_bytes()).hexdigest()

    def w0_candidate(self, argv, cwd):
        self.assertEqual(cwd, self.clean)
        self.assertEqual(argv[0], str(self.w0_executable))
        if argv[1:] == ["--version"]:
            output = self.w0_version.encode() + b"\n"
        else:
            self.assertEqual(argv[1:], ["evidence", "status", "--scoreboard", "--check",
                                       "--repo-root", str(self.clean)])
            output = b"SELF_PROOF_SCOREBOARD=ok the record matches its sources\n"
        return subprocess.CompletedProcess(argv, 0, output, b"")

    def native_w0_preview(self, build):
        def runner(argv, cwd):
            if str(self.clean / "scripts/self_proof_scoreboard.py") in argv:
                raise AssertionError("Python W0 checker ran in native preview")
            return self.tracker(argv, cwd)

        return product.sync_product(self.snapshot, COMMIT, self.pub, clean_root=self.clean,
                                    runner=runner, w0_native=build)

    def test_w0_native_preview_preserves_the_incumbent_rows_without_python_check(self):
        expected = self.sync()["measurements"]
        with patch.object(product, "_run_w0_candidate", side_effect=self.w0_candidate):
            result = self.native_w0_preview(self.w0_shadow())
        self.assertEqual(result["state"], "preview")
        self.assertEqual(result["measurements"], expected)
        self.assertEqual(result["w0_native"]["state"], "matched")
        self.assertEqual(result["w0_native"]["method"], "clean evidence status --scoreboard --check")
        self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))

    def test_w0_native_preview_recognizes_existing_evidence_in_both_backends(self):
        production = next(row for row in self.sync()["measurements"] if row["metric"] == "compiled_kcheck_decisions")
        sample = {**{key: production[key] for key in ("metric", "unit", "source")},
                  "goal": "E1", "value": str(production["value"]),
                  "date": "2000-01-01", "machine": "another", "note": "original retained evidence"}
        for backend in ("publication", "aterm"):
            with self.subTest(backend=backend):
                if backend == "publication":
                    self.tracker.rows = [sample]
                else:
                    self.native_tracker()
                    self.tracker.native["measure"] = [{**sample, "metric": "E1.compiled_kcheck_decisions", "commit": COMMIT}]
                with patch.object(product, "_run_w0_candidate", side_effect=self.w0_candidate):
                    result = self.native_w0_preview(self.w0_shadow())
                observed = next(row for row in result["measurements"] if row["metric"] == production["metric"])
                self.assertEqual(product._identity(observed), product._identity(production))
                self.assertEqual(observed["state"], "present")
                self.assertEqual(result["w0_native"]["state"], "matched")
                self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))

    def test_w0_native_refusal_defers_only_production_without_python_fallback(self):
        expected = [row for row in self.sync()["measurements"] if row["metric"] != "compiled_kcheck_decisions"]
        original = copy.deepcopy(self.snapshot)
        for case in ("exit", "stderr", "moved_pin", "invalid_snapshot", "version_replaced"):
            with self.subTest(case=case):
                self.snapshot = copy.deepcopy(original)
                build = self.w0_shadow()
                if case == "moved_pin":
                    self.w0_receipt.write_bytes(self.w0_receipt.read_bytes() + b"\n")
                elif case == "invalid_snapshot":
                    self.snapshot.update(scoreboard_warning="native derivation failed", metrics={})

                def candidate(argv, cwd):
                    good = self.w0_candidate(argv, cwd)
                    if case == "version_replaced" and argv[1:] == ["--version"]:
                        replacement = self.w0_executable.with_name("replacement")
                        replacement.write_bytes(self.w0_executable.read_bytes())
                        replacement.chmod(0o755)
                        replacement.replace(self.w0_executable)
                    if argv[1:] != ["--version"]:
                        if case == "exit":
                            return subprocess.CompletedProcess(argv, 1, b"", b"refused")
                        if case == "stderr":
                            return subprocess.CompletedProcess(argv, 0, good.stdout, b"\n")
                    return good

                with patch.object(product, "_run_w0_candidate", side_effect=candidate) as child:
                    result = self.native_w0_preview(build)
                self.assertEqual(result["state"], "partial")
                self.assertEqual(result["measurements"], expected)
                self.assertEqual(result["w0_native"]["state"], "deferred")
                self.assertEqual(result["w0_native"]["method"], "clean evidence status --scoreboard --check")
                if case == "invalid_snapshot":
                    self.assertIn("native derivation failed", result["deferred"])
                if case == "version_replaced":
                    child.assert_called_once_with([str(self.w0_executable), "--version"], self.clean)
                self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))

    def test_w0_native_publish_and_shadow_are_rejected_before_tracker_access(self):
        build = self.w0_shadow()
        for options in ({"publish": True, "w0_native": build}, {"w0_native": build, "w0_shadow": build}):
            with self.subTest(options=options), patch.object(product, "_run_w0_candidate") as candidate:
                with self.assertRaises(product.ProductUnavailable):
                    self.sync(**options)
                self.assertEqual(self.tracker.calls, [])
                candidate.assert_not_called()
                self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))

    def test_w0_shadow_preview_preserves_the_incumbent_production_identity(self):
        baseline = self.sync()
        shadow = self.w0_shadow()
        with patch.object(product, "_run_w0_candidate", side_effect=self.w0_candidate) as candidate:
            result = self.sync(w0_shadow=shadow)
        self.assertEqual(result["w0_native_shadow"]["state"], "matched")
        self.assertEqual(result["state"], "preview")
        self.assertEqual(result["measurements"], baseline["measurements"])
        candidate.assert_any_call([str(self.w0_executable), "--version"], self.clean)
        candidate.assert_any_call([str(self.w0_executable), "evidence", "status", "--scoreboard", "--check",
                                   "--repo-root", str(self.clean)], self.clean)
        self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))

    def test_w0_shadow_refusal_omits_only_production_without_falling_back(self):
        expected = [row for row in self.sync()["measurements"] if row["metric"] != "compiled_kcheck_decisions"]
        for phase, code, stdout, stderr in (
                ("version", 0, ("clean 0.0.0+g" + COMMIT + "\r\n").encode(), b""),
                ("version", 0, ("clean 0.0.0+g" + "b" * 40 + "\n").encode(), b""),
                ("check", 1, b"", b"refused"),
                ("check", 0, b"SELF_PROOF_SCOREBOARD=ok the record matches its sources\n", b"\n"),
                ("check", 0, b"SELF_PROOF_SCOREBOARD=ok the record matches its sources", b"")):
            def refused(argv, cwd):
                good = self.w0_candidate(argv, cwd)
                return (subprocess.CompletedProcess(argv, code, stdout, stderr)
                        if (argv[1:] == ["--version"]) == (phase == "version") else good)

            with self.subTest(phase=phase, code=code, stdout=stdout, stderr=stderr), \
                 patch.object(product, "_run_w0_candidate", side_effect=refused):
                result = self.sync(w0_shadow=self.w0_shadow())
                self.assertEqual(result["w0_native_shadow"]["state"], "deferred")
                self.assertEqual(result["state"], "partial")
                self.assertEqual(result["measurements"], expected)
                self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))

    def test_w0_shadow_binds_the_receipt_to_its_bytes_binary_source_and_inputs(self):
        changes = ({"schema": "other"}, {"source_commit": "b" * 40}, {"source_tree": "b" * 40},
                   {"executable_sha256": "0" * 64}, {"version": "another version"},
                   {"board_sha256": "0" * 64}, {"coverage_sha256": "0" * 64}, {"unexpected": True})
        for updates in changes:
            with self.subTest(updates=updates), \
                 patch.object(product, "_run_w0_candidate", side_effect=self.w0_candidate):
                result = self.sync(w0_shadow=self.w0_shadow(**updates))
                self.assertEqual(result["w0_native_shadow"]["state"], "deferred")
                self.assertEqual({row["metric"] for row in result["measurements"]},
                                 {"soundness_root_resident_equal", "adopted_kcheck_first_prefix_accepted"})
        shadow = self.w0_shadow()
        with patch.object(product, "_run_w0_candidate") as candidate:
            result = self.sync(w0_shadow=(*shadow[:2], "0" * 64))
        self.assertEqual(result["w0_native_shadow"]["state"], "deferred")
        candidate.assert_not_called()

    def test_w0_shadow_rechecks_bound_bytes_after_the_native_check(self):
        for changed in ("executable", "receipt", "board", "coverage"):
            shadow = self.w0_shadow()
            path = {"executable": self.w0_executable, "receipt": self.w0_receipt,
                    "board": self.clean / product.BOARD, "coverage": self.clean / product.COVERAGE}[changed]
            original = path.read_bytes()

            def changed_during_check(argv, cwd):
                result = self.w0_candidate(argv, cwd)
                if argv[1:] != ["--version"]:
                    path.write_bytes(path.read_bytes() + b"\n")
                return result

            with self.subTest(changed=changed):
                try:
                    with patch.object(product, "_run_w0_candidate", side_effect=changed_during_check):
                        result = self.sync(w0_shadow=shadow)
                finally:
                    path.write_bytes(original)
                self.assertEqual(result["w0_native_shadow"]["state"], "deferred")
                self.assertEqual({row["metric"] for row in result["measurements"]},
                                 {"soundness_root_resident_equal", "adopted_kcheck_first_prefix_accepted"})

    def test_native_fleet_reader_stops_if_version_changes_the_build_inputs(self):
        git = {
            ("rev-parse", "--is-inside-work-tree", "--show-prefix"): b"true\n\n",
            ("cat-file", "-t", COMMIT): b"commit\n",
            ("rev-parse", "--verify", COMMIT + "^{tree}"): (COMMIT + "\n").encode(),
        }
        for path in (product.BOARD, product.COVERAGE):
            git["cat-file", "blob", f"{COMMIT}:{path}"] = self.blobs[str(path)].encode()

        def read_git(root, *args):
            self.assertEqual(root, self.clean)
            return git[args]

        for changed in ("executable", "receipt"):
            build = self.w0_shadow()

            def change_during_version(argv, cwd):
                if changed == "executable":
                    replacement = self.w0_executable.with_name("replacement")
                    replacement.write_bytes(self.w0_executable.read_bytes())
                    replacement.chmod(0o755)
                    replacement.replace(self.w0_executable)
                else:
                    self.w0_receipt.write_bytes(self.w0_receipt.read_bytes() + b"\n")
                return subprocess.CompletedProcess(argv, 0, (self.w0_version + "\n").encode(), b"")

            with self.subTest(changed=changed), patch.object(w0, "_read_git", side_effect=read_git), \
                 patch.object(w0, "run_candidate", side_effect=change_during_version) as candidate:
                with self.assertRaisesRegex(w0.W0BuildError, "build inputs changed during the version check"):
                    w0.run_pinned_w0_json(build, git_root=self.clean, data_root=self.pub)
                candidate.assert_called_once_with([str(self.w0_executable), "--version"], self.pub)

    def test_w0_shadow_requires_the_same_clean_source_before_and_after_check(self):
        for field in ("head", "tree", "dirty"):
            for when in ("before", "after"):
                shadow = self.w0_shadow()
                source = {"head": COMMIT, "tree": COMMIT, "dirty": False}

                def change():
                    source[field] = True if field == "dirty" else "b" * 40

                if when == "before":
                    change()

                def runner(argv, cwd):
                    if cwd == self.clean:
                        if argv == ["git", "rev-parse", "HEAD"]:
                            return subprocess.CompletedProcess(argv, 0, source["head"] + "\n", "")
                        if argv == ["git", "rev-parse", COMMIT + "^{tree}"]:
                            return subprocess.CompletedProcess(argv, 0, source["tree"] + "\n", "")
                        if argv == ["git", "diff", "--quiet", "--no-ext-diff", COMMIT, "--"]:
                            return subprocess.CompletedProcess(argv, int(source["dirty"]), "", "")
                    return self.tracker(argv, cwd)

                def changed_during_check(argv, cwd):
                    result = self.w0_candidate(argv, cwd)
                    if when == "after" and argv[1:] != ["--version"]:
                        change()
                    return result

                with self.subTest(field=field, when=when), \
                     patch.object(product, "_run_w0_candidate", side_effect=changed_during_check):
                    result = product.sync_product(self.snapshot, COMMIT, self.pub, clean_root=self.clean,
                                                  runner=runner, w0_shadow=shadow)
                    self.assertEqual(result["w0_native_shadow"]["state"], "deferred")
                    self.assertEqual({row["metric"] for row in result["measurements"]},
                                     {"soundness_root_resident_equal", "adopted_kcheck_first_prefix_accepted"})

    def test_w0_shadow_publish_is_rejected_before_any_tracker_operation(self):
        with self.assertRaises(product.ProductUnavailable):
            self.sync(publish=True, w0_shadow=self.w0_shadow())
        self.assertEqual(self.tracker.calls, [])
        self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))

    def test_agoals_publication_backend_reads_the_pinned_goal_and_uses_one_measurement_store(self):
        self.tracker.capability_response = (json.dumps(PUBLICATION_CAPS), 0, "")
        status = product.product_status(self.pub, clean_root=self.clean, runner=self.tracker)
        self.assertEqual((status["state"], status["backend"], status["publication_commit"]),
                         ("available", "publication", self.tracker.publication_commit))
        self.assertEqual(status["capabilities"]["agoals"], PUBLICATION_CAPS)
        self.assertEqual(status["goal_row"]["title"], "Goal returned by aGoals")
        self.assertEqual(status["packages"][0]["dispatchable"], False)
        self.assertEqual(status["packages"][0]["claimed_on"], "today")
        self.assertEqual(status["packages"][0]["exit"], {"command": "check-proof", "expect": "full checker"})
        self.assertEqual(status["decisions"][0]["id"], "D1")
        self.assertEqual(status["lanes"][0]["id"], "proof")
        reads = [a[2] for a, _ in self.tracker.calls if a[:2] == ["git", "show"]]
        self.assertEqual(reads, [self.tracker.publication_commit + ":goals/data/packages.tsv"])
        self.assertFalse(status["capabilities"]["native_measure"])
        self.assertEqual(self.sync()["state"], "preview")
        self.assertEqual(self.tracker.writes, [])
        self.assertEqual(self.sync(publish=True)["state"], "published")
        self.assertEqual(self.sync(publish=True)["state"], "unchanged")
        self.assertEqual(len(self.tracker.writes), 3)
        self.assertEqual(self.tracker.native_writes, [])

    def test_show_uses_the_selected_publication_checkout_in_its_child_environment(self):
        command = ["aterm", "goals", "show", "E1", "--json"]
        with patch.dict(product.os.environ, {"ATERM_GOALS_PUBLICATION": "/other/checkout"}):
            with patch.object(product.subprocess, "run") as child:
                product._run(command, self.pub)
                self.assertEqual(child.call_args.kwargs["env"]["ATERM_GOALS_PUBLICATION"], str(self.pub))
            self.assertEqual(product.os.environ["ATERM_GOALS_PUBLICATION"], "/other/checkout")

    def test_show_preserves_published_dependency_spelling_and_the_unit_of_each_observation(self):
        self.tracker.capability_response = (json.dumps(PUBLICATION_CAPS), 0, "")
        self.tracker.central_tables["packages.tsv"] = self.tracker.central_tables["packages.tsv"].replace(
            "PR-02\t", "PR-02;  PR-01\t")
        self.tracker.rows = [
            {"goal": "E1", "metric": "depth", "date": "2026-11-10", "machine": "m1", "value": "2",
             "unit": "levels", "source": "measurement A", "note": "observed A"},
            {"goal": "E1", "metric": "depth", "date": "2026-11-17", "machine": "m9", "value": "7",
             "unit": "items", "source": "measurement B", "note": "observed B"}]
        status = product.product_status(self.pub, clean_root=self.clean, runner=self.tracker)
        self.assertEqual(status["packages"][0]["depends"], "PR-02;  PR-01")
        self.assertEqual(status["packages"][0]["depends_ids"], ["PR-02", "PR-01"])
        for index, sample in enumerate(status["measurements"]):
            self.assertEqual({k: sample[k] for k in METRICS}, self.tracker.rows[index])
            self.assertEqual(sample["metric_id"], "E1.depth")
            self.assertEqual(sample["pk"], f"{self.tracker.publication_commit}:goals/data/metrics.tsv:{index + 2}")
        self.assertIsNone(status["metrics"][0]["unit"])

    def test_mismatched_or_incomplete_modern_show_defers_without_falling_back_or_writing(self):
        self.tracker.capability_response = (json.dumps(PUBLICATION_CAPS), 0, "")
        self.tracker.rows = [{"goal": "E1", "metric": "x", "date": "today", "machine": "m1", "value": "0",
                              "unit": "cases", "source": "qualified", "note": "observed"}]
        good = self.tracker.shown_goal()
        changes = (
            lambda x: x.update(source="Publication at " + "2" * 40),
            lambda x: x["goals"].clear(), lambda x: x["goals"][0].update(id="E2", pk="E2"),
            lambda x: x["packages"].clear(), lambda x: x["packages"].append(x["packages"][0]),
            lambda x: x["packages"][0].update(publication_ref=f"{self.tracker.publication_commit}:goals/data/packages.tsv:3"),
            lambda x: x["packages"][0].update(goal="E2"), lambda x: x["packages"][0].update(claim=None),
            lambda x: x["packages"][0].update(claim="new owner", claimed_by="new owner"),
            lambda x: x["packages"][0].update(exit={"command": "different", "expect": "full checker"}),
            lambda x: x["packages"][0].update(depends=[]), lambda x: x["packages"][0].update(dispatchable="false"),
            lambda x: x["packages"][0].update(dispatchable=True), lambda x: x.update(extra=float("nan")),
            lambda x: x["lanes"].clear(), lambda x: x["decisions"][0].update(lane="unrelated"),
            lambda x: x["measures"].clear(), lambda x: x["metrics"].clear(),
            lambda x: x["measures"][0].update(goal="E2"), lambda x: x["measures"][0].update(metric="X2.x"),
            lambda x: x["measures"][0].update(pk="same source"), lambda x: x["measures"][0].update(at="earlier"),
            lambda x: x["measures"][0].update(value=0), lambda x: x["measures"][0].pop("source"),
            lambda x: x["metrics"][0].update(units=["other"]), lambda x: x.update(findings=None),
        )
        cases = [("{}", 0, ""), ("{garbled", 0, ""), ("", 1, "permission denied"),
                 (json.dumps(good), 0, "permission denied"),
                 ('{"source":"ambiguous",' + json.dumps(good)[1:], 0, "")]
        for change in changes:
            view = copy.deepcopy(good)
            change(view)
            cases.append((json.dumps(view), 0, ""))
        for case in cases:
            with self.subTest(response=case):
                self.tracker.calls.clear()
                self.tracker.show_response = case
                result = self.sync(publish=True)
                self.assertEqual((result["backend"], result["state"]), ("publication", "deferred"))
                self.assertEqual(result["measurements"], [])
                self.assertFalse(any(a[:2] == ["git", "show"] and a[2].endswith(("/metrics.tsv", "/goals.tsv"))
                                     for a, _ in self.tracker.calls))
        self.assertEqual((self.tracker.writes, self.tracker.native_writes), ([], []))
        self.tracker.offline = True
        self.tracker.calls.clear()
        self.assertEqual(self.sync()["state"], "deferred")
        self.assertFalse(any(a[1:3] == ["goals", "show"] for a, _ in self.tracker.calls))

    def test_agoals_ambiguous_unauthorized_or_incompatible_capabilities_defer_publication(self):
        cases = [
            ("", 1, "permission denied"), ("{}", 0, ""), ("unparseable", 0, ""),
            (json.dumps(PUBLICATION_CAPS), 0, "permission denied"),
            ('{"backend":"lab/tracker",' + json.dumps(PUBLICATION_CAPS)[1:], 0, ""),
            ("[]", 0, ""), (json.dumps([PUBLICATION_CAPS]), 0, ""),
        ]
        for change in ({"backend": "lab/tracker"}, {"product": "Clean"}, {"family_registered": True},
                       {"family_registered": 0}, {"schema": True}, {"schema": 1.0}, {"schema": "1"},
                       {"schema": 2}, {"backend2": "lab/tracker"}):
            cases.append((json.dumps({**PUBLICATION_CAPS, **change}), 0, ""))
        for response in cases:
            with self.subTest(response=response):
                self.tracker.capability_response = response
                self.tracker.calls.clear()
                result = self.sync(publish=True)
                self.assertEqual((result["backend"], result["state"]), ("aterm", "deferred"))
                self.assertFalse(any(cwd == self.pub for _, cwd in self.tracker.calls))
        self.assertEqual((self.tracker.native_writes, self.tracker.writes), ([], []))

    def test_measure_help_failures_cannot_activate_the_publication_capability_probe(self):
        self.tracker.capability_response = (json.dumps(PUBLICATION_CAPS), 0, "")
        for response in (("", 1, "permission denied"), ("measure METRIC VALUE", 0, ""),
                         ("measure METRIC VALUE --source SOURCE", 0, "read refused"),
                         ("", 2, "aterm: unknown command 'goals' (try --help)\npermission denied")):
            with self.subTest(response=response):
                self.tracker.measure_help = response
                self.tracker.calls.clear()
                result = self.sync(publish=True)
                self.assertEqual((result["backend"], result["state"]), ("aterm", "deferred"))
                self.assertFalse(any(cmd[1:3] == ["goals", "capabilities"] or cwd == self.pub
                                     for cmd, cwd in self.tracker.calls))

    def test_only_the_exact_missing_package_scan_can_probe_the_publication_backend(self):
        self.tracker.capability_response = (json.dumps(PUBLICATION_CAPS), 0, "")
        for response in (("", 1, "permission denied"), ("", 1, FAMILY_ABSENT + "\nread failed"),
                         ("partial", 1, FAMILY_ABSENT), (FAMILY_ABSENT, 1, ""),
                         ("", 2, FAMILY_ABSENT), ("{}", 0, "")):
            with self.subTest(response=response):
                self.tracker.absent_scan = response
                self.tracker.calls.clear()
                result = self.sync(publish=True)
                self.assertEqual((result["backend"], result["state"]), ("aterm", "deferred"))
                self.assertFalse(any(cmd[1:3] == ["goals", "capabilities"] or cwd == self.pub
                                     for cmd, cwd in self.tracker.calls))
        self.assertEqual((self.tracker.native_writes, self.tracker.writes), ([], []))

    def test_absent_executable_uses_publication_but_a_missing_dependency_does_not(self):
        def status_with_error(message):
            def runner(args, cwd):
                if args[0] == "aterm":
                    return subprocess.CompletedProcess(args, 127, "", message)
                return self.tracker(args, cwd)
            return product.product_status(self.pub, clean_root=self.clean, runner=runner)
        missing = "[Errno 2] No such file or directory"
        status = status_with_error(missing + ": 'aterm'")
        self.assertEqual((status["backend"], status["state"]), ("publication", "available"))
        for error in (missing + ": 'package.tsv'", "permission denied"):
            with self.subTest(error=error):
                status = status_with_error(error)
                self.assertEqual((status["backend"], status["state"]), ("aterm", "unavailable"))

    def test_const_trial_publication_preserves_separate_inputs_and_rejects_a_stale_observation(self):
        raw = b'sealed trial'
        candidate = {"state": "recorded", "stock_admitted": 3, "named": 3, "root": "Sound",
                     "result_sha256": product._digest(raw), "input_sha256": "b" * 64,
                     "baseline_input_sha256": "a" * 64}
        event = {"unit": "PR-28", "result_sha256": product._digest(raw)}
        history = json.dumps({"events": [event]}).encode()
        snapshot = {"const_helper_trial": candidate, "literal_export": {"state": "measured"}}
        with patch.object(product, "_canonical", side_effect=[raw, history, raw, history]), \
                patch.object(product, "_checked"), patch.object(product, "read_const_trial", return_value=candidate):
            reading, = product._const_trial_readings(snapshot, Path("."), COMMIT, None)
            self.assertEqual((reading["metric"], reading["value"]), ("stock_ck0_const_helper_candidate_admitted", 3))
            self.assertIn("candidate_sha256=" + "b" * 64, reading["source"])
            self.assertIn("baseline_sha256=" + "a" * 64, reading["source"])
            with self.assertRaises(product.ProductUnavailable):
                product._const_trial_readings({**snapshot, "const_helper_trial": {**candidate, "stock_admitted": 4}},
                                              Path("."), COMMIT, None)

    def test_qualified_source_reuses_root_series_and_binds_older_native_samples(self):
        self.native_tracker()
        path = product.PR29_REPORT / "qualification.json"
        replay_path = product.PR29_REPORT / "replay.json"
        self.put(path, {"input_sha256": "c" * 64, "artifacts": {"replay.json": "d" * 64, "labelled/result.json": "b" * 64}})
        manifest_hash = product._digest((self.clean / path).read_bytes())
        self.put(replay_path, {"retained_export": "../self-proof-const-branch-trial/candidate.ndjson.gz",
                               "replay": {"input_sha256": "c" * 64}})
        history_path = Path("data/self_proof_fleet_timeline.json")
        event = {"unit": "PR-29", "obligation": "Q4", "kind": "measurement", "date": "2026-11-17",
                 "qualification_sha256": manifest_hash, "input_sha256": "c" * 64}
        self.put(history_path, {"events": [event]})
        observed = {"state": "qualified", "qualified_revision": "d" * 40, "qualification_sha256": manifest_hash,
                    "input_sha256": "c" * 64, "root": "KCheck.root", "stock_admitted": 5, "declarations": 5,
                    "resident_equal": 5, "prefix_accepted": 0, "records": 4, "first_refusal": {"name": "Packet", "line": 9}}
        self.snapshot["source_qualification"] = observed
        with patch.object(product, "read_source_qualification", return_value=observed):
            result = self.sync()
            items = {row["metric"]: row for row in result["measurements"]}
            self.assertEqual({key: row["value"] for key, row in items.items()}, {
                "stock_ck0_soundness_root_admitted": 5, "soundness_root_resident_equal": 5,
                "adopted_kcheck_first_prefix_accepted": 0, "compiled_kcheck_decisions": 0})
            for key, denominator in (("stock_ck0_soundness_root_admitted", "5 of 5"),
                                     ("soundness_root_resident_equal", "5 of 5"), ("adopted_kcheck_first_prefix_accepted", "0 consecutive declaration records out of 4")):
                self.assertIn(manifest_hash, items[key]["source"])
                self.assertIn("qualified_revision=" + "d" * 40, items[key]["source"])
                self.assertIn(denominator, items[key]["note"])
            self.assertFalse(self.tracker.native_writes)
            self.snapshot["source_qualification"] = {**observed, "stock_admitted": 4}
            deferred = self.sync()
            self.assertEqual([row["metric"] for row in deferred["measurements"]], ["compiled_kcheck_decisions"])
            self.assertTrue(deferred["deferred"])

        current = items["adopted_kcheck_first_prefix_accepted"]
        sample = {"metric": "E1." + current["metric"], "value": "0", "source": current["source"], "commit": "b" * 40}
        old_history = {"events": [event]}
        def earlier(argv, cwd):
            if argv[:2] == ["git", "show"]:
                return subprocess.CompletedProcess(argv, 0, json.dumps(old_history), "")
            if argv[:3] == ["git", "diff", "--quiet"]:
                for source in (str(path), str(replay_path), str(product.PR29_REPORT / "labelled/result.json"),
                               "reports/self-proof-const-branch-trial/candidate.ndjson.gz"):
                    self.assertIn(source, argv)
            return self.tracker(argv, cwd)

        self.assertTrue(product._resident_sample([sample], current, COMMIT, earlier, self.clean))
        old_history["events"] = [{**event, "qualification_sha256": "0" * 64}]
        with self.assertRaisesRegex(product.ProductUnavailable, "no matching PR-29 observation"):
            product._resident_sample([sample], current, COMMIT, earlier, self.clean)

    def test_preview_holds_existing_claim_and_reports_three_gated_metrics(self):
        status = product.product_status(self.pub, runner=self.tracker)
        self.assertEqual([(r["id"], r["claimed_by"], r["depends"]) for r in status["packages"]],
                         [("PR-03", "holder", "PR-02")])
        result = self.sync()
        self.assertEqual(result["state"], "preview")
        self.assertFalse(result["capabilities"]["native_measure"])
        self.assertEqual({r["metric"]: r["value"] for r in result["measurements"]},
                         {"soundness_root_resident_equal": 4, "adopted_kcheck_first_prefix_accepted": 0,
                          "compiled_kcheck_decisions": 0})
        self.assertEqual(self.tracker.writes, [])
        for row in result["measurements"]:
            self.assertIn("sha256=", row["source"])
            self.assertIn(COMMIT, row["note"])
        plan = product.product_plan(self.snapshot, COMMIT)
        self.assertEqual(plan["packages"][0]["depends_on"], ["M4"])
        self.assertEqual(plan["packages"][0]["recorded_claims"], self.snapshot["units"][0]["recorded_claims"])
        self.assertEqual(plan["packages"][0]["exit_expect"], "qualified proof gate")

    def test_confirmed_identical_evidence_is_idempotent_across_dates_and_hosts(self):
        self.assertEqual(self.sync(publish=True)["state"], "published")
        self.assertEqual(len(self.tracker.writes), 3)
        for row in self.tracker.rows:
            row.update(date="2000-01-01", machine="another", note="original retained evidence")
        retry = self.sync(publish=True)
        self.assertEqual(retry["state"], "unchanged")
        self.assertEqual({r["state"] for r in retry["measurements"]}, {"present"})
        self.assertEqual(len(self.tracker.writes), 3)

    def test_lagging_or_dirty_publication_checkout_reads_one_central_revision_without_fetch(self):
        data = self.pub / "goals/data"
        (data / "goals.tsv").write_text("missing the central goal")
        (data / "packages.tsv").write_text("abandoned local edit")
        (self.pub / "goals/tools/goals.py").unlink()
        self.tracker.rows.append({"goal": "E1", "metric": "recorded_centrally", "value": "3",
                                  "unit": "declarations", "source": "retained"})
        status = product.product_status(self.pub, runner=self.tracker)
        sha = self.tracker.publication_commit
        self.assertEqual((status["publication_source"], status["publication_commit"]), ("refs/remotes/origin/main", sha))
        self.assertEqual((status["goal_row"]["title"], status["packages"][0]["claimed_by"],
                          status["measurements"][0]["value"]), ("Clean proves itself", "holder", "3"))
        reads = [argv[2] for argv, cwd in self.tracker.calls if cwd == self.pub and argv[:2] == ["git", "show"]]
        self.assertEqual(reads, [f"{sha}:goals/data/{table}.tsv" for table in ("goals", "packages", "metrics")])
        self.assertFalse(any(argv[:2] == ["git", "fetch"] for argv, _ in self.tracker.calls))
        self.tracker.publication_commit = ""
        self.assertEqual(product.product_status(self.pub, runner=self.tracker)["state"], "unavailable")

    def test_offline_working_copy_is_labelled_and_cannot_publish(self):
        self.tracker.offline = True
        status = product.product_status(self.pub, runner=self.tracker)
        self.assertEqual((status["publication_commit"], status["publication_source"]), (None, "offline-working-copy"))
        self.assertEqual(self.sync(publish=True)["state"], "deferred")
        self.assertFalse(self.tracker.writes)


    def test_false_or_stale_facts_are_never_published_as_zeros(self):
        self.snapshot["metrics"]["production"]["real_declarations_decided"] = False
        self.assertEqual(len(self.sync()["measurements"]), 2)
        self.snapshot["metrics"]["production"] = copy.deepcopy(self.production)
        self.snapshot["literal_export"]["prefix_accepted"] = False
        self.assertEqual([r["metric"] for r in self.sync()["measurements"]], ["compiled_kcheck_decisions"])
        self.snapshot["literal_export"] = copy.deepcopy(self.receipt)
        self.tracker.stale = True
        self.assertEqual(len(self.sync(publish=True)["measurements"]), 2)
        self.assertEqual(len(self.tracker.writes), 2)
        self.assertIn("scoreboard stale", self.sync()["deferred"])

    def test_missing_or_uncommitted_receipts_defer_one_workstream(self):
        (self.clean / product.COVERAGE).unlink()
        self.assertEqual(len(self.sync()["measurements"]), 2)
        (self.clean / product.REPORT / "receipt-set.json").write_text("{}")
        result = self.sync(publish=True)
        self.assertEqual(result["state"], "deferred")
        self.assertEqual(result["measurements"], [])
        self.assertEqual(self.tracker.writes, [])

    def test_unverified_provenance_or_nonowned_work_prevents_any_push(self):
        for field in ("ahead", "dirty", "off_main"):
            with self.subTest(field=field):
                setattr(self.tracker, field, True)
                self.assertEqual(self.sync(publish=True)["state"], "deferred")
                setattr(self.tracker, field, False)
        self.tracker.origin = "https://github.com/somebody-else/publication.git"
        self.assertEqual(self.sync(publish=True)["state"], "deferred")
        self.assertEqual(self.tracker.writes, [])

    def test_pending_write_requires_confirmation_on_remote_ref_and_can_be_retried(self):
        self.tracker.drop = True
        failed = self.sync(publish=True)
        self.assertNotEqual(failed["state"], "published")
        self.assertTrue(any("could not be confirmed" in reason for reason in failed["deferred"]))
        self.assertEqual(len(self.tracker.rows), 0)
        self.tracker.drop = False
        self.assertEqual(self.sync(publish=True)["state"], "published")
        self.assertEqual(len(self.tracker.rows), 3)

    def test_native_preview_only_stages_a_live_registered_scoped_and_unit_matching_metric(self):
        pk = "E1.adopted_kcheck_first_prefix_accepted"
        row = {"pk": pk, "goal": "E1", "row": "live", "unit": "declarations"}
        self.tracker.native = {"package": [], "metric": [row, {**row, "pk": "E1.compiled_kcheck_decisions",
                                                                "row": {"conflict": ["live", "retired"]}},
                                                        {**row, "pk": "E1.soundness_root_resident_equal",
                                                         "unit": "percent"}]}
        report = self.sync()
        caps = report["capabilities"]
        self.assertEqual(caps["native_metric_ids"], [pk])
        natives = [r["native_candidate"] for r in report["measurements"] if "native_candidate" in r]
        self.assertEqual(len(natives), 1)
        self.assertEqual(natives[0][:5], ["aterm", "goals", "measure", pk, "0"])
        self.assertEqual(self.tracker.writes, [])

    def native_tracker(self):
        self.tracker.native = {
            "package": [{"pk": "PR-03", "goal": "E1", "state": "running", "claim": "existing human hold"}],
            "metric": [{"pk": metric, "row": "live", "goal": "E1", "unit": "declarations"}
                       for metric in sorted(product.E1_METRICS)],
            "measure": [],
        }

    def test_native_only_publish_and_confirm_retries_without_publication_checkout(self):
        self.native_tracker()
        stock = "E1.stock_ck0_soundness_root_admitted"
        self.tracker.native["measure"].append({"metric": stock, "value": "4906",
                                                "source": "stock ck0 transcript on the corrected input", "commit": COMMIT})
        missing = self.pub.parent / "no-publication-checkout"
        status = product.product_status(missing, clean_root=self.clean, runner=self.tracker)
        self.assertEqual((status["state"], status["backend"]), ("available", "aterm"))
        self.assertEqual(status["packages"][0]["claim"], "existing human hold")
        self.assertEqual([(r["metric"], r["value"]) for r in status["measurements"]], [(stock, "4906")])
        publish = lambda: product.sync_product(self.snapshot, COMMIT, missing, clean_root=self.clean, publish=True,
                                               runner=self.tracker)
        result = publish()
        self.assertEqual(result["state"], "published")
        self.assertEqual(len(self.tracker.native_writes), 3)
        self.assertTrue(all(argv[3] != stock for argv in self.tracker.native_writes))
        self.assertTrue(all(r["confirmation"] == "local typed measure log" for r in result["measurements"]))
        self.assertEqual(publish()["state"], "unchanged")
        self.assertEqual(len(self.tracker.native_writes), 3)
        self.assertFalse(any(cwd == missing for _, cwd in self.tracker.calls))
        self.assertEqual(self.tracker.writes, [])

    def test_native_preexisting_sample_checked_against_its_earlier_retained_evidence(self):
        self.native_tracker()
        self.assertEqual(self.sync(publish=True)["state"], "published")
        for row in self.tracker.native["measure"]:
            row["commit"] = "b" * 40
        self.assertEqual(self.sync(publish=True)["state"], "unchanged")
        self.tracker.prior_differs = True
        failed = self.sync(publish=True)
        self.assertEqual(failed["state"], "deferred")
        self.assertTrue(all("cannot be bound" in reason for reason in failed["deferred"]))
        self.assertEqual(len(self.tracker.native_writes), 3)
        self.assertEqual(self.tracker.writes, [])

    def test_native_candidate_sample_requires_its_own_archive_at_the_recorded_revision(self):
        report = self.clean / product.TRIAL_REPORT
        report.mkdir(parents=True)
        (report / "result.json").write_text(json.dumps({"artifacts": {"votes.gz": {}}}))
        item = {"metric": "stock_ck0_const_helper_candidate_admitted", "value": 3, "source": "candidate"}
        samples = [{"metric": "E1." + item["metric"], "value": "3", "source": "candidate", "commit": "b" * 40}]
        archive = str(product.TRIAL_REPORT / "votes.gz")

        def history(argv, cwd):
            if argv[:3] == ["git", "diff", "--quiet"]:
                self.assertIn(str(product.TRIAL_REPORT / "result.json"), argv)
                self.assertIn(str(product.REPORT / "receipt-set.json"), argv)
                return subprocess.CompletedProcess(argv, int(archive in argv))
            return self.tracker(argv, cwd)

        with self.assertRaisesRegex(product.ProductUnavailable, "cannot be bound"):
            product._resident_sample(samples, item, COMMIT, history, self.clean)

    def test_partial_native_deployment_never_writes_blind_or_falls_back(self):
        self.native_tracker()
        self.tracker.unreadable_native = True
        result = self.sync(publish=True)
        self.assertEqual((result["backend"], result["state"]), ("aterm", "deferred"))
        self.assertIn("log scan unavailable", result["deferred"])
        status = product.product_status(self.pub, clean_root=self.clean, runner=self.tracker)
        self.assertEqual(status["packages"][0]["claim"], "existing human hold")
        self.assertEqual(self.tracker.native_writes, [])
        self.assertEqual(self.tracker.writes, [])

    def test_unknown_native_append_is_reconciled_on_next_read(self):
        self.native_tracker()
        self.tracker.fail_after_append = True
        result = self.sync(publish=True)
        self.assertEqual((result["state"], len(self.tracker.native_writes)), ("deferred", 1))
        self.tracker.unreadable_native = self.tracker.fail_after_append = False
        self.assertEqual(self.sync(publish=True)["state"], "published")
        self.assertEqual(len(self.tracker.native_writes), 3)
        self.assertEqual(self.tracker.writes, [])

    def test_native_preflight_and_readback_reject_conflicting_values_and_unbound_commits(self):
        self.native_tracker()
        self.tracker.native_commit = "b" * 40
        result = self.sync(publish=True)
        self.assertEqual(result["state"], "deferred")
        self.assertIn("did not record the publishing Clean commit", result["deferred"][0])
        self.assertEqual(len(self.tracker.native_writes), 1)
        for row in self.tracker.native["measure"]:
            row["value"] = "9000"
        before = len(self.tracker.native_writes)
        self.tracker.native_commit = COMMIT
        result = self.sync(publish=True)
        self.assertTrue(any("conflicting value" in reason for reason in result["deferred"]))
        self.assertEqual(len(self.tracker.native_writes), before + 2)
        self.assertEqual(result["state"], "partial")
        self.assertEqual(self.tracker.writes, [])


class W0BuildExportTest(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory(prefix="w0-export-")
        self.addCleanup(scratch.cleanup)
        root = Path(scratch.name).resolve()
        self.source = root / "qualified checkout"
        self.source.mkdir()
        self.candidate = root / "qualified candidate"
        self.calls_path = root / "candidate calls.jsonl"
        self.output = root / "handoff directory"
        self.output.mkdir()
        self.sibling = self.output / "existing handoff"
        self.sibling.mkdir()
        (self.sibling / "keep").write_bytes(b"existing contents\n")

        self.git("init", "-q")
        self.git("config", "--local", "filter.w0-fixture.clean", r"tr '\015' '\012'")
        self.marker = self.source / "source.txt"
        self.marker.write_bytes(b"qualified source\n")
        root_manifest = self.source / "Cargo.toml"
        root_manifest.write_text('[workspace]\n[workspace.package]\nversion = "0.9.4"\n')
        (self.source / ".gitattributes").write_text(
            f"{w0.BOARD} -text filter=w0-fixture\n{w0.COVERAGE} -text filter=w0-fixture\n",
        )
        for relative in (w0.BOARD, w0.COVERAGE):
            path = self.source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((product.ROOT / relative).read_bytes())
        self.git("add", ".")
        self.git(
            "-c", "user.name=W0 fixture", "-c", "user.email=w0@example.invalid",
            "-c", "commit.gpgsign=false", "-c", "core.hooksPath=" + os.devnull,
            "commit", "-qm", "Qualified input fixture",
        )
        self.commit = self.git("rev-parse", "HEAD").decode().strip()
        self.version = f"clean 0.9.4+g{self.commit}"

    def git(self, *args):
        env = {key: value for key, value in os.environ.items() if not key.upper().startswith("GIT_")}
        env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        return subprocess.check_output(
            ["git", *args], cwd=self.source, env=env, stderr=subprocess.PIPE, timeout=10,
        )

    def write_candidate(self, mode):
        self.candidate.write_text(f"""#!/bin/sh
exec {shlex.quote(sys.executable)} - "$0" "$@" <<'PY'
import json
from pathlib import Path
import sys

binary, *args = sys.argv[1:]
root = Path({str(self.source)!r})
calls = Path({str(self.calls_path)!r})
mode = {mode!r}
with calls.open("a", encoding="utf-8") as log:
    log.write(json.dumps([binary, args, str(Path.cwd())]) + "\\n")

if args == ["--version"]:
    version = {self.version!r}
    if mode == "copy-changes-at-version":
        with Path(binary).open("ab") as stream:
            stream.write(b"# changed during version\\n")
    print("clean 0.9.4+g" + ("0" * 40) if mode == "wrong-version" else version)
elif args == ["evidence", "status", "--scoreboard", "--json", "--repo-root", str(root)]:
    sys.stdout.buffer.write((root / {str(w0.BOARD)!r}).read_bytes())
elif args == ["evidence", "status", "--scoreboard", "--check", "--repo-root", str(root)]:
    if mode == "check-fails":
        print("saved board refused", file=sys.stderr)
        sys.exit(17)
    changes = {{
        "source-changes": Path({str(self.marker)!r}),
        "candidate-changes": Path({str(self.candidate)!r}),
        "copy-changes": Path(binary),
    }}
    if mode in changes:
        with changes[mode].open("ab") as stream:
            stream.write(b"# changed during check\\n")
    if mode == "check-output-differs":
        print("SELF_PROOF_SCOREBOARD=ok different result")
    else:
        print("SELF_PROOF_SCOREBOARD=ok the record matches its sources")
else:
    raise AssertionError(args)
PY
""", encoding="utf-8")
        self.candidate.chmod(0o700)
        return hashlib.sha256(self.candidate.read_bytes()).hexdigest()

    def export(self, mode="normal", *, digest=None):
        self.calls_path.unlink(missing_ok=True)
        expected = self.write_candidate(mode)
        return w0.export_w0_build(self.source, self.candidate, digest or expected, self.output)

    def calls(self):
        if not self.calls_path.exists():
            return []
        return [json.loads(line) for line in self.calls_path.read_text(encoding="utf-8").splitlines()]

    def assert_failed_child_cleaned_up(self):
        self.assertEqual(list(self.output.iterdir()), [self.sibling])
        self.assertEqual((self.sibling / "keep").read_bytes(), b"existing contents\n")

    def test_exported_copy_is_checked_and_consumed_through_the_pinned_reader(self):
        exported = self.export()
        self.assertEqual(set(exported), {"executable", "receipt", "receipt_sha256"})
        executable, receipt = (Path(exported[key]) for key in ("executable", "receipt"))
        child = executable.parent
        self.assertEqual(child.parent, self.output)
        self.assertEqual(executable, child / "clean")
        self.assertEqual(receipt, child / "build-receipt.json")
        self.assertEqual({path.name for path in child.iterdir()},
                         {"clean", "build-receipt.json", "build-receipt.sha256"})
        self.assertFalse(executable.samefile(self.candidate))
        self.assertEqual(executable.read_bytes(), self.candidate.read_bytes())
        receipt_digest = hashlib.sha256(receipt.read_bytes()).hexdigest()
        self.assertEqual(exported["receipt_sha256"], receipt_digest)
        self.assertEqual((child / "build-receipt.sha256").read_bytes(), (receipt_digest + "\n").encode("ascii"))
        self.assertEqual(self.calls(), [
            [str(executable), ["--version"], str(self.source)],
            [str(executable), ["evidence", "status", "--scoreboard", "--check",
                               "--repo-root", str(self.source)], str(self.source)],
        ])
        self.assertEqual((self.sibling / "keep").read_bytes(), b"existing contents\n")

        build = (exported["executable"], exported["receipt"], exported["receipt_sha256"])
        pinned = w0.read_pinned_build(build, expected_commit=self.commit)
        self.assertEqual(pinned.receipt, {
            "schema": w0.BUILD_SCHEMA,
            "version": self.version,
            "source_commit": self.commit,
            "source_tree": self.git("rev-parse", "HEAD^{tree}").decode().strip(),
            "executable_sha256": hashlib.sha256(self.candidate.read_bytes()).hexdigest(),
            "board_sha256": hashlib.sha256(self.git("cat-file", "blob", f"HEAD:{w0.BOARD}")).hexdigest(),
            "coverage_sha256": hashlib.sha256(
                self.git("cat-file", "blob", f"HEAD:{w0.COVERAGE}")
            ).hexdigest(),
        })
        self.candidate.unlink()
        self.assertEqual(w0.run_pinned_w0_json(build, git_root=self.source, data_root=self.source),
                         (self.source / w0.BOARD).read_bytes())

    def test_refuses_dirty_tracked_source_before_executing(self):
        self.marker.write_bytes(b"moved tracked source\n")
        for staged in (False, True):
            with self.subTest(staged=staged):
                if staged:
                    self.git("add", "--", self.marker.name)
                with self.assertRaisesRegex(w0.W0BuildError, "source has dirty tracked files"):
                    self.export()
                self.assertEqual(self.calls(), [])
                self.assert_failed_child_cleaned_up()

    def test_refuses_index_shortcuts_that_hide_tracked_changes(self):
        for relative, flag in ((w0.BOARD, "assume-unchanged"), (w0.COVERAGE, "skip-worktree")):
            with self.subTest(flag=flag):
                path = self.source / relative
                original = path.read_bytes()
                self.git("update-index", f"--{flag}", "--", str(relative))
                try:
                    path.write_bytes(original + b"\n")
                    self.assertEqual(self.git("status", "--porcelain", "-uno"), b"")
                    with self.assertRaisesRegex(w0.W0BuildError, "requires checked-out tracked files without index shortcuts"):
                        self.export()
                    self.assertEqual(self.calls(), [])
                    self.assert_failed_child_cleaned_up()
                finally:
                    path.write_bytes(original)
                    self.git("update-index", f"--no-{flag}", "--", str(relative))

    def test_refuses_saved_bytes_that_git_normalizes_to_the_committed_blob(self):
        for relative in (w0.BOARD, w0.COVERAGE):
            with self.subTest(relative=relative):
                path = self.source / relative
                original = path.read_bytes()
                path.write_bytes(original.replace(b"\n", b"\r"))
                try:
                    self.assertEqual(self.git("status", "--porcelain", "-uno"), b"")
                    self.assertEqual(self.git("hash-object", f"--path={relative}", str(path)),
                                     self.git("rev-parse", f"HEAD:{relative}"))
                    with self.assertRaisesRegex(w0.W0BuildError, "differs from its committed bytes"):
                        self.export()
                    self.assertEqual(self.calls(), [])
                    self.assert_failed_child_cleaned_up()
                finally:
                    path.write_bytes(original)

    def test_refuses_wrong_independent_executable_digest_before_executing(self):
        with self.assertRaisesRegex(w0.W0BuildError, "differs from its supplied SHA-256"):
            self.export(digest="0" * 64)
        self.assertEqual(self.calls(), [])
        self.assert_failed_child_cleaned_up()

    def test_refuses_bad_version_or_check_and_removes_the_copy(self):
        cases = (
            ("wrong-version", 1, "version must name the exact Clean commit"),
            ("copy-changes-at-version", 1, "copy changed during the version check"),
            ("check-fails", 2, "handoff saved-board check did not match"),
            ("check-output-differs", 2, "handoff saved-board check did not match"),
        )
        for mode, expected_calls, diagnostic in cases:
            with self.subTest(mode=mode):
                with self.assertRaisesRegex(w0.W0BuildError, diagnostic):
                    self.export(mode)
                calls = self.calls()
                self.assertEqual(len(calls), expected_calls)
                copied = Path(calls[0][0])
                self.assertEqual(copied.parent.parent, self.output)
                self.assertFalse(copied.parent.exists())
                self.assert_failed_child_cleaned_up()

    def test_refuses_source_and_executable_changes_during_the_check(self):
        cases = (
            ("source-changes", "source has dirty tracked files"),
            ("candidate-changes", "inputs changed during verification"),
            ("copy-changes", "inputs changed during verification"),
        )
        for mode, diagnostic in cases:
            with self.subTest(mode=mode):
                try:
                    with self.assertRaisesRegex(w0.W0BuildError, diagnostic):
                        self.export(mode)
                    self.assertEqual(len(self.calls()), 2)
                    self.assert_failed_child_cleaned_up()
                finally:
                    self.marker.write_bytes(b"qualified source\n")


if __name__ == "__main__":
    unittest.main()
