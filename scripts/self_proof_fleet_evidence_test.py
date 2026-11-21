# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Small receipt-contract controls. Everything synthesized here is test data."""

from __future__ import annotations

import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

if __package__:
    from .self_proof_fleet_evidence import (PR29_COMMAND, displayed_events, read_const_trial,
                                          read_export_evidence, read_followup, read_native_init_slice, read_soundness_quorum, read_source_qualification)
else:
    from self_proof_fleet_evidence import (PR29_COMMAND, displayed_events, read_const_trial,
                                          read_export_evidence, read_followup, read_native_init_slice, read_soundness_quorum, read_source_qualification)


ROOT = "KCheck.CompleteSound.kcheck_sound"
SDK = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
BASIS = ["Quot.sound", "propext"]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return json.dumps(value, separators=(",", ":")).encode() + b"\n"


class ReceiptFixture:
    def __init__(self):
        self.meta = {"lean": {"version": "4.30.0-rc2", "githash": SDK},
                     "exporter": {"name": "clean-export", "version": "fixture"}, "format": {"version": "3.1.0"}}
        self.rows = [{"meta": self.meta}]
        for idx, (parent, name) in enumerate([(0, "Packet"), (1, "mk"), (0, "propext"), (0, "Quot"),
                                              (4, "sound"), (0, "KCheck"), (6, "CompleteSound"), (7, "kcheck_sound")], 1):
            self.rows.append({"in": idx, "str": {"pre": parent, "str": name}})
        self.rows += [{"ie": 0, "sort": 0},
                      {"inductive": {"types": [{"name": 1}], "ctors": [{"name": 2}], "recs": []}},
                      {"axiom": {"name": 3}}, {"axiom": {"name": 5}}, {"thm": {"name": 8, "type": 0, "value": 0}}]
        self.first_line = 11
        self.refusal = "refused name=Packet reason=KCheck.Refusal.inductiveBlock `Packet\n"
        self.trace = f"line={self.first_line} name=Packet knownFamily=false recognisedRows=false unitTemplate=false\n"
        world = {"lean_version": "4.30.0-rc2", "lean_githash": SDK}
        self.receipts = {
            "writer.json": {**world, "modules": ["KCheck.CompleteSound"], "targets": 1,
                            "round_trip": "read back by Clean's reader and written again, byte-identical",
                            "written": {"axioms": BASIS, "names": 8, "exprs": 1, "levels": 0,
                                        "declarations": 5, "records": 4}},
            "corrected-upstream.json": {**world, "reader": "lean4export Export.parseStream",
                                        "kernel": "Lean.Environment.replay", "declarations": 5, "order": 5,
                                        "permitted": BASIS, "axioms": BASIS, "verdict": "accepted"},
            "corrected-resident.json": {**world, "modules": ["KCheck.CompleteSound"],
                                        "reader": "lean4export Export.parseStream", "against": "Lean's environment (importModules)",
                                        "equal": 5, "compared": 5, "differing_count": 0, "differing_by_field": {},
                                        "absent": [], "differing": [], "verdict": "equal"},
            "fenced-clean.json": {"accepted": True, "reader_error": None, "declarations": 5,
                                  "admitted": 5, "axioms": BASIS, "unpermitted_axioms": [], "refusals": [],
                                  "meta": {**world, "rule_set": "lean-v4-30-rc2", "format_version": "3.1.0",
                                           "exporter_name": "clean-export", "exporter_version": "fixture"}},
            "provenance.json": {"public_source_commit": "a" * 40, "lean_module_source": "b" * 40,
                                "theory_libs_revision": "b" * 40, "sdk_githash": SDK, "tracked_inputs_clean": True,
                                "writer_command": ["writer", "--target", ROOT],
                                "fenced_command": ["checker", "--reference", "--permit", "propext", "--permit", "Quot.sound"]},
            "prefix-comparison.json": {"cone-final": {"first": "Packet", "label": "cone-final",
                                                      "lines": self.first_line, "checker_exit": 1, "checker_stderr": "",
                                                      "checker_stdout": self.trace + self.refusal}},
        }
        self.control = b"exit 1\nlean_export_replay: REJECTED: axioms outside the permitted set: #[Quot.sound]\n"

    def write(self, directory):
        lines = list(map(encoded, self.rows))
        raw = b"".join(lines)
        written = self.receipts["writer.json"]["written"]
        written.update(sha256=sha(raw), bytes=len(raw), lines=len(lines))
        self.receipts["provenance.json"].update(export_sha256=sha(raw), export_bytes=len(raw))
        comparison = self.receipts["prefix-comparison.json"]
        comparison["source_stream_sha256"] = sha(raw)
        probe = comparison["cone-final"]
        prefix = b"".join(lines[:probe["lines"]])
        probe.update(bytes=len(prefix), prefix_sha256=sha(prefix), header_sha256=sha(lines[0]),
                     terminal_record_sha256=sha(lines[probe["lines"] - 1]),
                     all_non_header_bytes=len(prefix) - len(lines[0]),
                     all_non_header_sha256=sha(prefix[len(lines[0]):]))
        files = {name: encoded(doc) for name, doc in self.receipts.items()}
        files["clean-kcheck-sound.ndjson.gz"] = gzip.compress(raw, mtime=0)
        files["missing-axiom.txt"] = self.control
        for name, data in files.items():
            (directory / name).write_bytes(data)
        manifest = {"schema": "clean-self-proof-root-receipts-v1", "root": ROOT,
                    "input_sha256": sha(raw), "files": {name: sha(data) for name, data in files.items()}}
        (directory / "receipt-set.json").write_bytes(encoded(manifest))


class TestHistoricalEvidence(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)

    def refused(self):
        result = read_export_evidence(self.directory)
        self.assertEqual(set(result), {"state", "reason"}, result)
        self.assertEqual(result["state"], "unverified", result)
        self.assertTrue(result["reason"])

    def test_complete_denominators_first_family_and_historical_source(self):
        data = ReceiptFixture()
        data.write(self.directory)
        measured = read_export_evidence(self.directory)
        self.assertEqual(measured["state"], "measured", measured)
        self.assertEqual(measured["root"], ROOT)
        self.assertEqual(measured["records"], 4)
        self.assertEqual(measured["inductive_blocks"], 1)
        self.assertEqual(measured["outside_named_seed_types"], 1)
        self.assertEqual(measured["quotient_records"], 0)
        for key in ("declarations", "fenced_admitted", "resident_equal", "upstream_admitted"):
            self.assertEqual(measured[key], 5)
        self.assertEqual(measured["prefix_accepted"], 0)
        self.assertEqual(measured["first_refusal"], {"name": "Packet", "line": 11, "reason": "KCheck.Refusal.inductiveBlock `Packet"})
        self.assertEqual(measured["public_source_commit"], "a" * 40)
        self.assertEqual(measured["lean_module_source"], "b" * 40)
        probe = data.receipts["prefix-comparison.json"]["cone-final"]
        probe.update(checker_exit=0, checker_stdout=data.trace + "accepted receipt=Packet\n")
        data.write(self.directory)
        positive = read_export_evidence(self.directory)
        self.assertEqual(positive["prefix_accepted"], 1, positive)
        self.assertIsNone(positive["first_refusal"])

    def test_file_manifest_and_payload_binding(self):
        for name in ("receipt-set.json", "missing-axiom.txt", "fenced-clean.json", "clean-kcheck-sound.ndjson.gz"):
            with self.subTest(name=name):
                ReceiptFixture().write(self.directory)
                (self.directory / name).unlink()
                self.refused()
        ReceiptFixture().write(self.directory)
        (self.directory / "writer.json").write_bytes(b"{}\n")
        self.refused()
        data = ReceiptFixture()
        data.write(self.directory)
        path = self.directory / "receipt-set.json"
        manifest = json.loads(path.read_bytes())
        manifest["input_sha256"] = "0" * 64
        path.write_bytes(encoded(manifest))
        self.refused()

    def test_resealed_contradictory_receipts(self):
        changes = [
            ("corrected-resident.json", {"equal": 4}), ("corrected-resident.json", {"absent": ["Packet"]}),
            ("corrected-upstream.json", {"order": 0}), ("corrected-upstream.json", {"permitted": ["propext"]}),
            ("corrected-upstream.json", {"axioms": ["propext", "propext"]}), ("fenced-clean.json", {"admitted": True}),
            ("fenced-clean.json", {"unpermitted_axioms": ["sorryAx"]}), ("fenced-clean.json", {"refusals": ["Packet"]}),
            ("writer.json", {"round_trip": "unknown"}), ("provenance.json", {"public_source_commit": ""}),
            ("provenance.json", {"writer_command": ["writer", "--target", "Other"]}),
        ]
        for filename, changeset in changes:
            with self.subTest(file=filename, changes=changeset):
                data = ReceiptFixture()
                data.receipts[filename].update(changeset)
                data.write(self.directory)
                self.refused()

    def test_resealed_spliced_prefix_or_control(self):
        for delta in ({"lines": 12}, {"first": "Other"}, {"checker_exit": 0},
                      {"checker_stdout": "accepted receipt=Packet\n"}, {"checker_stderr": "loader refused"},
                      {"checker_stdout": "line=12 name=Packet knownFamily=false recognisedRows=false unitTemplate=false\n"
                                         "refused name=Packet reason=KCheck.Refusal.inductiveBlock `Packet\n"}):
            with self.subTest(delta=delta):
                data = ReceiptFixture()
                data.receipts["prefix-comparison.json"]["cone-final"].update(delta)
                data.write(self.directory)
                self.refused()
        data = ReceiptFixture()
        data.control = b"exit 0\n"
        data.write(self.directory)
        self.refused()

    def test_resealed_prefix_fingerprints_and_full_counts_are_rederived(self):
        for name, keys, field, false_value in [
            ("prefix-comparison.json", (), "source_stream_sha256", "0" * 64),
            ("prefix-comparison.json", ("cone-final",), "prefix_sha256", "0" * 64),
            ("prefix-comparison.json", ("cone-final",), "terminal_record_sha256", "0" * 64),
            ("prefix-comparison.json", ("cone-final",), "header_sha256", "0" * 64),
            ("prefix-comparison.json", ("cone-final",), "all_non_header_bytes", 3),
            ("writer.json", ("written",), "declarations", 4),
            ("writer.json", ("written",), "records", 5),
        ]:
            with self.subTest(name=name, field=field):
                ReceiptFixture().write(self.directory)
                path = self.directory / name
                receipt = json.loads(path.read_bytes())
                row = receipt
                for key in keys:
                    row = row[key]
                row[field] = false_value
                changed = encoded(receipt)
                path.write_bytes(changed)
                manifest_path = self.directory / "receipt-set.json"
                manifest = json.loads(manifest_path.read_bytes())
                manifest["files"][name] = sha(changed)
                manifest_path.write_bytes(encoded(manifest))
                self.refused()

    def test_resealed_terminal_theorem_needs_real_identity_and_stored_value(self):
        for end in ({"axiom": {"name": 8}}, {"thm": {"name": 8, "type": 0}},
                    {"thm": {"name": 8, "type": 0, "value": 1}}, {"thm": {"name": 7, "type": 0, "value": 0}}):
            with self.subTest(end=end):
                data = ReceiptFixture()
                data.rows[-1] = end
                data.write(self.directory)
                self.refused()
        data = ReceiptFixture()
        data.rows[8]["str"] = {"pre": 0, "str": ROOT}
        data.write(self.directory)
        self.refused()


class SourceQualificationTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.directory = Path(tmp.name) / "adoption"
        self.directory.mkdir()
        candidate = Path(tmp.name) / "self-proof-const-branch-trial"
        candidate.mkdir()
        fixture = ReceiptFixture()
        self.caller = "KCheck.conv_sound_step"
        self.helper = self.caller + "._proof_1_10"
        fixture.rows[-1:-1] = [
            {"in": 9, "str": {"pre": 6, "str": "conv_sound_step"}},
            {"in": 10, "str": {"pre": 9, "str": "_proof_1_10"}},
            {"thm": {"name": 9, "type": 0, "value": 0}},
            {"thm": {"name": 10, "type": 0, "value": 0}},
        ]
        self.rows = fixture.rows
        raw = b"".join(map(encoded, self.rows))
        prefix_digest = sha(b"".join(map(encoded, fixture.rows[:fixture.first_line])))
        self.subject = candidate / "candidate.ndjson.gz"
        self.subject.write_bytes(gzip.compress(raw))
        digest = sha(raw)
        names = [[{"str": part} for part in name.split(".")] for name in ("Packet", "Packet.mk", "propext", "Quot.sound", self.caller, self.helper, ROOT)]
        stocks = b"".join(encoded({"kind": "declaration", "name": name, "accepted": True}) for name in names)
        stocks += encoded({"kind": "coverage", "accepted": 7, "total": 7, "refused": {}, "axioms": names[2:4]})
        ledger = b"".join(encoded({"name": name, "lean": "admitted", "fenced": "admitted", "stock": True}) for name in names)
        for response, fields in (("corrected-resident.json", ("compared", "equal")),
                                 ("corrected-upstream.json", ("order", "declarations")),
                                 ("fenced-clean.json", ("admitted", "declarations"))):
            fixture.receipts[response].update({field: len(names) for field in fields})
        outputs = {"resident.stdout": json.dumps(fixture.receipts["corrected-resident.json"]),
                   "lean.stdout": json.dumps(fixture.receipts["corrected-upstream.json"]),
                   "fenced.stdout": json.dumps(fixture.receipts["fenced-clean.json"]),
                   "adopted-prefix.stdout": fixture.trace + fixture.refusal, "adopted-prefix.stderr": ""}
        for m in ("lean", "fenced", "resident"):
            outputs[m + ".stderr"] = ""
        logs = {"outputs.json.gz": gzip.compress(encoded(outputs)), "stock-verdicts.ndjson.gz": gzip.compress(stocks),
                "per-name.ndjson.gz": gzip.compress(ledger)}
        runs = {m: {"input_sha256": digest, "exit": 0} for m in ("lean", "fenced", "resident", "stock")}
        runs["stock"]["stdout_sha256"] = sha(stocks)
        runs["adopted-prefix"] = {"input_sha256": prefix_digest, "exit": 1}
        for m in ("lean", "fenced", "resident", "adopted-prefix"):
            for ch in ("stdout", "stderr"):
                runs[m][ch + "_sha256"] = sha(outputs[m + "." + ch].encode())
        vote = {"accepted": 7, "named": 7, "root_accepted": True, "helper_accepted": True, "caller_accepted": True}
        self.replay = {"root": ROOT, "helper": self.helper, "input_sha256": digest, "resident_equal": 7, "records": 6, "bytes": len(raw),
                       "declarations": 7, "members": {m: dict(vote) for m in ("lean", "fenced", "stock")},
                       "stock_stdout_sha256": sha(stocks), "per_name_sha256": sha(ledger),
                       "adopted_admissions_before_first_refusal": 0, "adopted_first_refusal": "Packet",
                       "adopted_prefix_sha256": prefix_digest, "fourth_member": {"qualified": False},
                       "trial_input_identical": True}
        self.manifest = {"schema": 1, "replay": self.replay, "identities": {"runs": runs},
                         "retained_export": "../self-proof-const-branch-trial/candidate.ndjson.gz",
                         "files": {k: sha(v) for k, v in logs.items()}}
        self.exit = {"input_sha256": digest, "names": 7, "root": ROOT, "lean_fenced_stock_all_admitted": True,
                     "adopted_first_refusal": "Packet", "external_member_qualified": False, "scope": "PR-29 package exit"}
        self.data = {**logs, "aggregate.stderr.gz": gzip.compress(b"")}
        for name in ("record_qualification.py", "verify.py", "replay.py", "labelled.py", "verify_census.py"):
            self.data[name] = b"# qualification fixture\n"
        labelled = {"target": "kcheck_labelled", "helper": self.helper, "passed": 2, "failed": 0,
                    "filtered": 0, "helper_statement_pin": "c" * 64,
                    "helper_closure": sorted(BASIS + ["Quot", "Quot.ind", "Quot.lift", "Quot.mk"]),
                    "preserved_closure_rows": 7, "closure_rows": 8,
                    "preserved_statement_or_body_pins": 10, "statement_or_body_pins": 11,
                    "controls": ["labelled full index: 3 owned theorem statements", "kcheck_labelled subjects 11",
                                 "partial C3: 3 subjects, 2 positive/False pairs; both fresh kernels passed"]}
        for phase, code, tally in (("initial", 101, "FAILED. 1 passed; 1 failed"), ("final", 0, "ok. 2 passed; 0 failed")):
            log = f"test result: {tally}; 0 ignored; 0 measured; 0 filtered out; finished in 0.1s\n".encode()
            if phase == "initial":
                log += b"observed axiom closures differ from theories/kcheck_labelled/axiom_closures.json\n"
            else:
                log += ("\n".join(labelled["controls"]) + "\n").encode()
            self.data[f"labelled/{phase}.log.gz"] = gzip.compress(log)
            run = {"source_commit": "a" * 40, "exit": code, "stdout_stderr_sha256": sha(log)}
            self.data[f"labelled/{phase}.json"] = encoded(run)
            labelled[f"{phase}_run"] = {"source": run["source_commit"], "exit": code,
                                        "transcript": f"{phase}.log.gz", "stdout_stderr_sha256": sha(log)}
        self.data["labelled/result.json"] = encoded(labelled)
        census = {"schema": "clean.pr29.census.v1", "qualified_revision": "b" * 40,
                  "helper": {"declaration": self.helper, "kind": "theorem", "module": "KCheck.ConvSound",
                             "package": "kcheck_labelled", "axiom_closure": BASIS},
                  "helper_statement_pin": labelled["helper_statement_pin"], "helper_labelled_closure": labelled["helper_closure"], "runs": {}}
        for phase, count in (("baseline", 10), ("mint", 11), ("comparison", 11)):
            verdict = "LEAN_AXIOM_CENSUS=ok" + (" minted" if phase == "mint" else "")
            log = f"kcheck_labelled: declarations={count} Quot.sound=2 propext=2\n{verdict}\n".encode()
            self.data[f"e7-{phase}.log.gz"] = gzip.compress(log)
            census["runs"][phase] = {"log_sha256": sha(log), "exit": 0}
        self.data["census.json"] = encoded(census)
        self.e7 = {"packages": 1, "before": 10, "after": 11, "added": self.helper, "qualified_source": "b" * 40}
        self.data["aggregate.stdout.gz"] = gzip.compress(encoded(labelled) + encoded(self.e7) + encoded(self.exit))
        self.event = {"unit": "PR-29", "kind": "measurement", "obligation": "Q4", "date": "2026-11-17", "input_sha256": digest}

    def seal(self):
        files = {**self.data, "replay.json": encoded(self.manifest), "exit.json": encoded(self.exit)}
        for name, data in files.items():
            path = self.directory / name
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(data)
        raw = encoded({"schema": "clean.pr29.source-qualification.v1", "qualified_revision": "d" * 40,
                       "input_sha256": self.event["input_sha256"], "exit_command": PR29_COMMAND, "exit": 0,
                       "artifacts": {k: sha(v) for k, v in files.items()}})
        (self.directory / "qualification.json").write_bytes(raw)
        return {**self.event, "qualification_sha256": sha(raw)}

    def test_full_exit_counts_the_export_and_adopted_refusal_separately(self):
        event = self.seal()
        result = read_source_qualification(self.directory, event)
        self.assertEqual(result["state"], "qualified", result)
        self.assertEqual((result["stock_admitted"], result["declarations"], result["resident_equal"]), (7, 7, 7))
        self.assertEqual((result["prefix_accepted"], result["records"], result["first_refusal"]["name"]), (0, 6, "Packet"))
        self.assertFalse(result["fourth_member_qualified"])
        for replacement in ({"unit": "PR-28"}, {"obligation": "W1"}, {"date": "invalid"},
                            {"input_sha256": "0" * 64}, {"qualification_sha256": "0" * 64}):
            with self.subTest(replacement=replacement):
                refused = read_source_qualification(self.directory, {**event, **replacement})
                self.assertEqual(set(refused), {"state", "reason"}, refused)
        (self.directory / "census.json").unlink()
        self.assertEqual(read_source_qualification(self.directory, event)["state"], "unverified")
        self.seal()
        self.subject.write_bytes(gzip.compress(b"other subject"))
        self.assertEqual(read_source_qualification(self.directory, event)["state"], "unverified")

    def test_rebound_inconsistent_receipts_cannot_promote_the_current_source(self):
        for obj, field, val in ((self.replay, "records", 99), (self.replay, "resident_equal", 4),
                                (self.replay, "adopted_first_refusal", "other"),
                                (self.replay["members"]["stock"], "root_accepted", False),
                                (self.exit, "scope", "replay evidence only"), (self.exit, "external_member_qualified", True),
                                (self.manifest, "retained_export", "../self-proof-const-branch-trial/outside.gz")):
            with self.subTest(field=field):
                old, obj[field] = obj[field], val
                refused = read_source_qualification(self.directory, self.seal())
                self.assertEqual(set(refused), {"state", "reason"}, refused)
                obj[field] = old

    def test_registered_subchecks_must_run_and_report_matching_results(self):
        labelled = json.loads(self.data["labelled/result.json"])
        for name, value in (("missing labelled", encoded(self.e7) + encoded(self.exit)),
                            ("missing census", encoded(labelled) + encoded(self.exit)),
                            ("incorrect E7 delta", encoded(labelled) + encoded({**self.e7, "after": 10}) + encoded(self.exit)),
                            ("labelled verdict is partial", encoded({**labelled, "passed": 1}) + encoded(self.e7) + encoded(self.exit)),
                            ("exit only", encoded(self.exit))):
            with self.subTest(name=name):
                self.data["aggregate.stdout.gz"] = gzip.compress(value)
                self.assertEqual(read_source_qualification(self.directory, self.seal())["state"], "unverified")

    def test_resealed_subject_must_contain_both_named_theorems(self):
        for name_id in (9, 10):
            with self.subTest(name_id=name_id):
                row = next(row for row in self.rows if row.get("thm", {}).get("name") == name_id)
                body = row.pop("thm")
                row["opaque"] = body
                changed = b"".join(map(encoded, self.rows))
                digest = sha(changed)
                self.subject.write_bytes(gzip.compress(changed))
                self.event["input_sha256"] = self.replay["input_sha256"] = self.exit["input_sha256"] = digest
                self.replay["bytes"] = len(changed)
                for member in ("lean", "fenced", "stock", "resident"):
                    self.manifest["identities"]["runs"][member]["input_sha256"] = digest
                result = read_source_qualification(self.directory, self.seal())
                self.assertEqual(result["state"], "unverified")
                self.assertIn("caller or helper theorem", result["reason"])
                row["thm"] = row.pop("opaque")

    def test_incomplete_or_contradictory_command_archives_are_refused(self):
        for name in ("aggregate.stdout.gz", "aggregate.stderr.gz", "labelled.py"):
            with self.subTest(missing=name):
                saved = self.data.pop(name)
                self.assertEqual(read_source_qualification(self.directory, self.seal())["state"], "unverified")
                self.data[name] = saved
        for output in (b"refused\n", encoded(self.exit) + b"later failure\n"):
            with self.subTest(output=output):
                self.data["aggregate.stdout.gz"] = gzip.compress(output)
                self.assertEqual(read_source_qualification(self.directory, self.seal())["state"], "unverified")


class ConstTrialReceiptTests(unittest.TestCase):
    def test_archived_vote_is_bound_to_the_timeline_the_original_export_and_the_payloads(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            parts = {}
            for name in ("candidate.ndjson.gz", "candidate-ck0-verdicts.ndjson.gz", "adopted-prefix.json",
                         "candidate-lean.json", "candidate-fenced.json"):
                content = name.encode()
                (directory / name).write_bytes(content)
                parts[name] = {"bytes": len(content), "sha256": sha(content)}
            result = {"schema": "clean.q4.const-branch-trial.v1", "root": ROOT,
                      "baseline_input_sha256": "a" * 64, "input_sha256": "b" * 64,
                      "artifacts": parts, "stock_outcomes": {"candidate": {
                          "root_accepted": True, "accepted": 3, "named": 3}}}
            raw = encoded(result)
            (directory / "result.json").write_bytes(raw)
            event = {"baseline_input_sha256": "a" * 64, "input_sha256": "b" * 64, "result_sha256": sha(raw)}
            baseline = {"state": "measured", "sha256": "a" * 64}
            self.assertEqual(read_const_trial(directory, event, baseline)["stock_admitted"], 3)
            for field in ("baseline_input_sha256", "input_sha256", "result_sha256"):
                with self.subTest(field=field):
                    self.assertEqual(read_const_trial(directory, {**event, field: "c" * 64}, baseline)["state"], "unverified")
            (directory / "candidate-fenced.json").write_bytes(b"other")
            self.assertEqual(read_const_trial(directory, event, baseline)["state"], "unverified")



class FollowupReceiptTests(unittest.TestCase):

    def test_fourth_vote_requires_the_same_export_and_all_three_controls(self):
        root = Path(__file__).resolve().parents[1]
        path = "reports/self-proof-q4-corrected-reference-2026-11-18/root/replay.json"
        event = {"unit": "Q4", "kind": "measurement", "source": path, "source_revision": "a" * 40,
                 "date": "2026-11-18"}
        record = json.loads((root / path).read_bytes())
        subject = record["subjects"][0]
        adoption = {"input_sha256": subject["sha256"], "declarations": subject["declarations"]}

        def read(current):
            blob = encoded(record)
            bound = {**event, "source_sha256": hashlib.sha256(blob).hexdigest()}
            with patch(read_soundness_quorum.__module__ + "._historical_blob", return_value=blob):
                return read_soundness_quorum(root, [bound], current)

        result = read(adoption)
        self.assertEqual(len(result["members"]), 4)
        self.assertEqual(result["date"], event["date"])
        self.assertIsNone(read({**adoption, "input_sha256": "b" * 64}))
        for invalid in (False, 1):
            record["controls"]["extra-axiom"]["refused_for_reason"]["lean4lean"] = invalid
            self.assertIsNone(read(adoption))

    def test_named_init_slice_counts_require_original_export_and_native_frames(self):
        repo = Path(__file__).resolve().parents[1]
        directory = "reports/self-proof-native-init-slice"
        path = directory + "/qualification.json"
        event = {"unit": "PR-49", "kind": "measurement", "source": path, "source_revision": "a" * 40,
                 "source_sha256": hashlib.sha256((repo / path).read_bytes()).hexdigest()}
        def read_blob(root, revision, name):
            return (root / name).read_bytes()
        target = read_native_init_slice.__module__ + "._historical_blob"
        with patch(target, side_effect=read_blob):
            reading = read_native_init_slice(repo, event)
            self.assertEqual((reading["accepted"], reading["target_declarations"]), (39, 39))
            self.assertEqual(displayed_events([event], {}, {"PR-49": reading}), [event])
            self.assertIsNone(read_native_init_slice(repo, {**event, "source_sha256": "0" * 64}))
        def wrong_wire(root, revision, name):
            return b"\x00" if Path(name).name == "advice.bin" else read_blob(root, revision, name)
        with patch(target, side_effect=wrong_wire):
            self.assertIsNone(read_native_init_slice(repo, event))
        self.assertEqual(displayed_events([event], {}, {}), [])

    repo = Path(__file__).resolve().parents[1]
    packages = {
        "PR-30": ("self-proof-prefix-measurement", "qualification.json", "434c489988450bba3ba4fc2bebb13872e47bd315",
                  ("clean-current.json", "upstream-historical.json", "controls.json")),
        "PR-31": ("self-proof-statement-dependencies", "verification.json", "19397daa48131bc0aa5845af4b6bb3c47cb95add",
                  ("paths.json", "Resident.lean")),
    }

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        # Share the immutable source commits, and edit only this scratch checkout's copies.
        subprocess.run(["git", "clone", "--quiet", "--shared", "--no-checkout", str(self.repo), str(self.root)], check=True)
        for package, manifest, _, names in self.packages.values():
            dest = self.root / "reports" / package
            dest.mkdir(parents=True)
            for name in ("README.md", manifest, *names):
                shutil.copyfile(self.repo / "reports" / package / name, dest / name)
        for filename in ("reports/self-proof-const-branch-trial/candidate.ndjson.gz",
                         "reports/self-proof-root-export-2026-11-17/kcheck_sound.ndjson.gz"):
            dest = self.root / filename
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(self.repo / filename)

    def event(self, unit):
        package, manifest, revision, _ = self.packages[unit]
        readme = Path("reports") / package / "README.md"
        return {"unit": unit, "kind": "measurement", "source": readme.as_posix(), "source_revision": revision,
                "source_sha256": sha((self.root / readme).read_bytes()),
                "qualification_sha256": sha((self.root / readme.parent / manifest).read_bytes()),
                "input_sha256": "17e3501dbd8689e7a241227c1711df4b06b3edd6184353feb01af672c9284f62"}

    def test_historical_readings_and_visibility_require_three_matching_pins(self):
        events = [self.event("PR-30"), self.event("PR-31")]
        readings = {event["unit"]: read_followup(self.root, event) for event in events}
        self.assertEqual(readings["PR-30"]["current"]["first_refusal"], "Iff")
        self.assertEqual(readings["PR-30"]["historical"]["accepted_named_declarations"], 4)
        self.assertEqual(readings["PR-31"]["targets"], ["Iff", "List", "Quot"])
        self.assertIs(readings["PR-31"]["root_proof_body_used"], False)
        self.assertEqual(readings["PR-31"]["edges_checked"], 13)
        self.assertEqual(displayed_events(events, None, readings), events)
        self.assertEqual(displayed_events(events, None), [])
        for event in events:
            for key in ("source_revision", "input_sha256", "qualification_sha256"):
                with self.subTest(unit=event["unit"], key=key):
                    self.assertEqual(displayed_events([{**event, key: "unknown"}], None, readings), [])
        other = {"unit": "W1", "kind": "measurement"}
        self.assertEqual(displayed_events([other], None), [other])

    def test_iff_wire_observation_preserves_the_qualified_prefix_in_the_ledger(self):
        events = json.loads((self.repo / "data/self_proof_fleet_timeline.json").read_bytes())["events"]
        prefix_event = next(e for e in events if e["unit"] == "PR-30")
        directory = Path(prefix_event["source"]).parent
        wire_path = (directory / "iff-wire.json").as_posix()
        wire_event = next(e for e in events if e["unit"] == "S2" and e["source"] == wire_path)
        prefix = read_followup(self.root, prefix_event)
        self.assertIsNotNone(prefix)
        self.assertEqual(prefix["current"]["accepted_records"], 0)

        wire_bytes = (self.repo / wire_path).read_bytes()
        recorded = subprocess.check_output(["git", "show", f"{wire_event['source_revision']}:{wire_path}"], cwd=self.repo)
        self.assertEqual(wire_bytes, recorded)
        self.assertEqual(sha(wire_bytes), wire_event["source_sha256"])
        wire = json.loads(wire_bytes)
        current = json.loads((self.root / directory / "clean-current.json").read_bytes())
        self.assertEqual((wire["record"], wire["line"], wire["original"]["sha256"]),
                         (prefix["current"]["first_refusal"], prefix["current"]["line"], current["prefix_sha256"]))

    def test_wrong_readme_revision_or_subject_suppresses_the_event(self):
        for unit in self.packages:
            event = self.event(unit)
            for key, value in (("source", "docs/README.md"), ("source_revision", "1" * 39),
                               ("source_revision", "0" * 40), ("input_sha256", "a" * 64),
                               ("source_sha256", "b" * 64), ("qualification_sha256", "c" * 64)):
                with self.subTest(unit=unit, key=key):
                    self.assertIsNone(read_followup(self.root, {**event, key: value}))
            (self.root / event["source"]).write_text("stale README")
            self.assertIsNone(read_followup(self.root, self.event(unit)))

    def test_missing_subjects_and_stale_subordinate_evidence_suppress_the_events(self):
        for unit, (package, _, _, names) in self.packages.items():
            event = self.event(unit)
            for name in names:
                with self.subTest(unit=unit, name=name):
                    path = self.root / "reports" / package / name
                    path.unlink()
                    self.assertIsNone(read_followup(self.root, event))
                    path.write_text("replacement")
                    self.assertIsNone(read_followup(self.root, event))
                    shutil.copyfile(self.repo / "reports" / package / name, path)
        (self.root / "reports/self-proof-root-export-2026-11-17/kcheck_sound.ndjson.gz").unlink()
        self.assertIsNone(read_followup(self.root, self.event("PR-30")))

    def test_resealed_counter_or_negative_control_cannot_replace_the_qualified_exit(self):
        for unit, field, value in (("PR-30", "current_records_admitted", 1), ("PR-31", "wrong_edge_exit", 0)):
            package, filename, _, _ = self.packages[unit]
            path = self.root / "reports" / package / filename
            manifest = json.loads(path.read_bytes())
            manifest[field] = value
            path.write_bytes(encoded(manifest))
            self.assertIsNone(read_followup(self.root, self.event(unit)))


if __name__ == "__main__":
    unittest.main()
