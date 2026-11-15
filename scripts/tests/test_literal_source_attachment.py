#!/usr/bin/env python3
"""Refusal-path tests for a diagnostic, not source-refinement proof evidence."""

import copy
from contextlib import redirect_stderr
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "literal_source_attachment.py"
SPEC = importlib.util.spec_from_file_location("literal_source_attachment", SCRIPT)
PROBE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROBE)

BINARY_NAME = "clean_kernel.trust-ir.bin"
TEXT_NAME = "clean_kernel.trust-ir.txt"
ARTIFACTS = {
    BINARY_NAME: b"synthetic binary\x00\xff",
    TEXT_NAME: b"synthetic text IR\n",
}


def fixture_digest(payload):
    """Independent producer framing, without calling the probe's hash helper."""
    domain = b"trust.thir-lower.artifact.v1"
    frame = (b"trust-ir.sha256-domain.v1\x00"
             + len(domain).to_bytes(8, "big") + domain
             + len(payload).to_bytes(8, "big") + payload)
    return "sha256:" + hashlib.sha256(frame).hexdigest()


def coverage_fixture():
    return {
        "schema": PROBE.COVERAGE_SCHEMA,
        "crate": "clean_kernel",
        "proof_authority": False,
        "publication": {
            "schema": "trust.thir-lower.artifact-set.v1",
            "digest_algorithm": "sha256-domain-v1",
            "digest_domain": "trust.thir-lower.artifact.v1",
            "commit_marker": True,
            "artifacts": [
                {"name": name, "bytes": len(payload), "digest": fixture_digest(payload)}
                for name, payload in ARTIFACTS.items()
            ],
        },
        "bodies": [{
            "def_path": PROBE.FUNCTION,
            "kind": "fn",
            "lowered": False,
            "symbolic": False,
            "spliced": False,
            "func_id": None,
            "unsupported": [["StaticRef(interior mutable)", 2]],
        }],
    }


def write_fixture(root, coverage=None):
    for path in PROBE.SOURCE_PATHS:
        destination = root / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text("synthetic test source, never proof evidence\n")
    for name, payload in ARTIFACTS.items():
        (root / name).write_bytes(payload)
    (root / "clean_kernel.coverage.json").write_text(
        json.dumps(coverage_fixture() if coverage is None else coverage))
    mir = root / "built.mir"
    mir.write_text("\n".join(PROBE.MIR_ANCHORS))
    return ["--repo", str(root), "--dump-dir", str(root),
            "--built-mir", str(mir), "--output", str(root / "report.json")]


def definition_fixture(path, local_hash):
    return {"def_path": path, "def_path_hash": {
        "stable_crate_id": "0123456789abcdef", "local_hash": f"{local_hash:016x}",
    }}


def direct_fixture():
    """Synthetic producer declarations, not a capture or initialized Name."""
    fixture = coverage_fixture()
    fixture.update(direct_obligation_capability="obligation-bearing-pending-v2",
                   native_verification_requests=False)
    fixture["bodies"][0]["def_index"] = 7
    definitions = [definition_fixture(path, index + 2)
                   for index, path in enumerate(("tc::infer::NAME_NAT", "tc::infer::NAME_STRING"))]
    roots = [{"definition": definition, "allocation_id": index}
             for index, definition in enumerate(definitions)]
    nodes = [{"allocation_id": index, "kind": "static", "definition": definition,
              "initializer": {"bytes": [None, 0, None]}}
             for index, definition in enumerate(definitions)]
    body = {
        "owner": definition_fixture("tc::infer::infer_literal_type", 1), "def_index": 7,
        "source": {"diagnostic": "synthetic infer.rs source, never attestation"},
        "uses": [{"expr_index": index, "static_definition": definition,
                  "source": {"diagnostic": "synthetic StaticRef"}}
                 for index, definition in enumerate(definitions)],
        "graph": {"capture_status": "complete", "errors": [], "statics": roots, "nodes": nodes},
    }
    fixture["source_static_readback"] = {
        "schema": "trust.thir.source-static-readback.v1", "producer": "thir_static_ref",
        "storage_phase": "cold_initializer_only", "evaluator_dependency": "rustc_ctfe",
        "allocation_namespace": "per_body", "proof_authority": False,
        "native_verification_requests": False, "inventory_complete": True,
        "capture_status": "complete", "body_count": 1, "complete_bodies": 1,
        "refused_bodies": 0, "errors": [], "bodies": [body],
        "target": {"triple": "synthetic-target", "data_layout": "synthetic-layout",
                   "pointer_size_bytes": 8, "little_endian": True},
        "limits": {"nodes": 64, "bytes": 65536, "relocations": 1024,
                   "body_expressions": 65536, "body_occurrences": 4096,
                   "bodies": 65536, "source_snippet_bytes": 65536},
    }
    return fixture


def write_direct_fixture(root, fixture=None, surface="dump"):
    argv = write_fixture(root, direct_fixture() if fixture is None else fixture)
    # No raw MIR exists: successful direct diagnostics cannot accidentally
    # depend on its anchors, filename, or a copied handwritten stand-in.
    (root / "built.mir").unlink()
    if surface == "emit":
        (root / "clean_kernel.coverage.json").rename(root / "clean_kernel.trust-ir.coverage.json")
    return argv[:4] + ["--direct-thir", "--surface", surface] + argv[6:]


class LiteralSourceProbeTests(unittest.TestCase):
    def assert_cli_refused(self, root, argv):
        stderr = io.StringIO()
        with redirect_stderr(stderr):
            result = PROBE.main(argv)
        self.assertEqual(result, 2, stderr.getvalue())
        self.assertIn("literal source probe refused:", stderr.getvalue())
        self.assertFalse((root / "report.json").exists())

    def assert_marker_refused(self, mutate):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = coverage_fixture()
            mutate(fixture)
            self.assert_cli_refused(root, write_fixture(root, fixture))

    def test_output_never_overwrites_any_captured_input(self):
        lanes = (("mir", None), ("direct", "dump"), ("direct", "emit"))
        for lane, surface in lanes:
            paths = list(PROBE.SOURCE_PATHS) + list(ARTIFACTS)
            paths += (["clean_kernel.coverage.json", "built.mir"] if lane == "mir"
                      else [PROBE.COVERAGE_NAMES[surface]])
            for path in paths:
                with self.subTest(lane=lane, surface=surface, path=path), \
                        tempfile.TemporaryDirectory() as td:
                    root = Path(td)
                    argv = (write_fixture(root) if lane == "mir"
                            else write_direct_fixture(root, surface=surface))
                    captured = root / path
                    before = captured.read_bytes()
                    argv[-1] = str(captured)
                    stderr = io.StringIO()
                    with redirect_stderr(stderr):
                        self.assertEqual(PROBE.main(argv), 2, stderr.getvalue())
                    self.assertIn("literal source probe refused:", stderr.getvalue())
                    self.assertEqual(captured.read_bytes(), before)
                    self.assertFalse((root / "report.json").exists())

    def test_existing_report_is_preserved_on_refused_second_publication(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            argv = write_direct_fixture(root)
            with redirect_stderr(io.StringIO()):
                self.assertEqual(PROBE.main(argv), 1)
            output = root / "report.json"
            before = output.read_bytes()
            fixture = direct_fixture()
            fixture["bodies"][0]["unsupported"] = [["changed synthetic diagnostic", 1]]
            (root / "clean_kernel.coverage.json").write_text(json.dumps(fixture))
            # A fresh diagnostic really differs, but cannot replace the
            # previously published report, even though neither is a proof.
            changed = PROBE.probe(root, root, direct_thir=True)
            self.assertNotEqual(changed["producer_record"]["unsupported"],
                                json.loads(before)["producer_record"]["unsupported"])
            with redirect_stderr(io.StringIO()):
                self.assertEqual(PROBE.main(argv), 2)
            self.assertEqual(output.read_bytes(), before)

    def test_output_refuses_existing_and_dangling_symlinks(self):
        for dangling in (False, True):
            with self.subTest(dangling=dangling), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                argv = write_direct_fixture(root)
                output = root / "report.json"
                target = root / ("not-created.json" if dangling else TEXT_NAME)
                before = None if dangling else target.read_bytes()
                output.symlink_to(target)
                with redirect_stderr(io.StringIO()):
                    self.assertEqual(PROBE.main(argv), 2)
                self.assertTrue(output.is_symlink())
                self.assertEqual(output.readlink(), target)
                if dangling:
                    self.assertFalse(target.exists())
                else:
                    self.assertEqual(target.read_bytes(), before)

    def test_source_snapshot_includes_all_three_real_literal_callers(self):
        # Independent literal paths: deriving this roster from SOURCE_PATHS
        # would let a forgotten caller disappear from both fixture and check.
        callers = {
            "crates/clean-kernel/src/tc/infer.rs",
            "crates/clean-kernel/src/tc/cert/infer_core.rs",
            "crates/clean-kernel/src/tc/def_eq/proof_irrel.rs",
        }
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            write_fixture(root)
            before = PROBE.probe(root, root, root / "built.mir")
            self.assertTrue(callers <= before["source_sha256"].keys())
            quick = "crates/clean-kernel/src/tc/def_eq/proof_irrel.rs"
            payload = b"changed synthetic quick caller, never proof evidence\n"
            (root / quick).write_bytes(payload)
            after = PROBE.probe(root, root, root / "built.mir")
            self.assertEqual(after["source_sha256"][quick],
                             hashlib.sha256(payload).hexdigest())
            self.assertNotEqual(before["source_sha256"][quick],
                                after["source_sha256"][quick])
            for path in callers - {quick}:
                self.assertEqual(before["source_sha256"][path],
                                 after["source_sha256"][path])
            self.assertFalse(after["source_attachment_verified"])
            self.assertFalse(after["proof_authority"])
            self.assertEqual(after["status"], "blocked")

    def test_missing_quick_literal_caller_is_cli_input_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            argv = write_fixture(root)
            quick = root / "crates/clean-kernel/src/tc/def_eq/proof_irrel.rs"
            self.assertTrue(quick.is_file(), "quick caller must be a required input")
            quick.unlink()
            self.assert_cli_refused(root, argv)

    def test_independent_publication_framing_known_vector(self):
        self.assertEqual(
            fixture_digest(b""),
            "sha256:a28e05a07a056643c31e80c62a564f20fa655ef4b90d22a2728ef057745e496b",
        )
        for payload in (b"", b"abc", bytes(range(256))):
            with self.subTest(payload=payload):
                self.assertEqual(PROBE.artifact_digest(payload), fixture_digest(payload))

    def test_same_length_binary_corruption_is_cli_input_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            argv = write_fixture(root)
            self.assertEqual(PROBE.main(argv), 1)
            output = root / "report.json"
            output.unlink()
            payload = ARTIFACTS[BINARY_NAME]
            corrupted = bytes([payload[0] ^ 1]) + payload[1:]
            self.assertEqual(len(corrupted), len(payload))
            (root / BINARY_NAME).write_bytes(corrupted)
            self.assertEqual(PROBE.main(argv), 2)
            self.assertFalse(output.exists())

    def test_same_length_text_corruption_is_cli_input_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            argv = write_fixture(root)
            payload = ARTIFACTS[TEXT_NAME]
            corrupted = bytes([payload[0] ^ 1]) + payload[1:]
            self.assertEqual(len(corrupted), len(payload))
            (root / TEXT_NAME).write_bytes(corrupted)
            self.assert_cli_refused(root, argv)

    def test_mixed_generation_refuses_either_stale_artifact(self):
        next_generation = {
            name: bytes([payload[0] ^ 1]) + payload[1:]
            for name, payload in ARTIFACTS.items()
        }
        for stale_name in ARTIFACTS:
            with self.subTest(stale_name=stale_name), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                fixture = coverage_fixture()
                for entry in fixture["publication"]["artifacts"]:
                    entry["digest"] = fixture_digest(next_generation[entry["name"]])
                argv = write_fixture(root, fixture)
                for name, payload in next_generation.items():
                    if name != stale_name:
                        (root / name).write_bytes(payload)
                self.assert_cli_refused(root, argv)

    def test_missing_or_nonobject_publication_is_refused(self):
        self.assert_marker_refused(lambda f: f.pop("publication"))
        for value in (None, False, 1, "marker", []):
            with self.subTest(value=value):
                self.assert_marker_refused(lambda f: f.update(publication=value))

    def test_publication_identity_fields_are_exact(self):
        expected = {
            "schema": "trust.thir-lower.artifact-set.v1",
            "digest_algorithm": "sha256-domain-v1",
            "digest_domain": "trust.thir-lower.artifact.v1",
        }
        for key, good in expected.items():
            with self.subTest(key=key, missing=True):
                self.assert_marker_refused(lambda f: f["publication"].pop(key))
            for value in (None, True, [], {}, good + ".unknown"):
                with self.subTest(key=key, value=value):
                    self.assert_marker_refused(
                        lambda f: f["publication"].update({key: value}))

    def test_commit_marker_requires_literal_true(self):
        self.assert_marker_refused(lambda f: f["publication"].pop("commit_marker"))
        for value in (None, False, 0, 1, "true", [], {}):
            with self.subTest(value=value):
                self.assert_marker_refused(
                    lambda f: f["publication"].update(commit_marker=value))

    def test_exactly_two_unique_artifacts_are_required(self):
        artifacts = coverage_fixture()["publication"]["artifacts"]
        malformed = (
            None, {}, "artifacts", [], artifacts[:1],
            [artifacts[0], artifacts[0]], artifacts + [artifacts[0]],
            [None, artifacts[1]], [[], artifacts[1]], ["row", artifacts[1]],
        )
        self.assert_marker_refused(lambda f: f["publication"].pop("artifacts"))
        for value in malformed:
            with self.subTest(value=value):
                self.assert_marker_refused(
                    lambda f: f["publication"].update(artifacts=value))

    def test_only_exact_local_artifact_filenames_are_allowed(self):
        for name in (
            "another.bin", "../clean_kernel.trust-ir.bin", "/clean_kernel.trust-ir.bin",
            "./clean_kernel.trust-ir.bin", "subdir/clean_kernel.trust-ir.bin",
            "..\\clean_kernel.trust-ir.bin", "clean_kernel.trust-ir.bin\x00",
            "CLEAN_KERNEL.trust-ir.bin", None, 1, [], {},
        ):
            with self.subTest(name=name):
                self.assert_marker_refused(
                    lambda f: f["publication"]["artifacts"][0].update(name=name))

    def test_artifact_fields_must_exist(self):
        for index in (0, 1):
            for key in ("name", "bytes", "digest"):
                with self.subTest(index=index, key=key):
                    self.assert_marker_refused(
                        lambda f: f["publication"]["artifacts"][index].pop(key))

    def test_artifact_lengths_are_positive_integers_not_booleans(self):
        for index in (0, 1):
            good = coverage_fixture()["publication"]["artifacts"][index]["bytes"]
            for length in (None, False, True, 0, -1, float(good), str(good), [], {}):
                with self.subTest(index=index, length=length):
                    self.assert_marker_refused(
                        lambda f: f["publication"]["artifacts"][index].update(bytes=length))

    def test_boolean_length_refuses_even_when_it_equals_payload_length(self):
        for index, name in enumerate(ARTIFACTS):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                fixture = coverage_fixture()
                fixture["publication"]["artifacts"][index].update(
                    bytes=True, digest=fixture_digest(b"x"))
                argv = write_fixture(root, fixture)
                (root / name).write_bytes(b"x")
                self.assert_cli_refused(root, argv)

    def test_artifact_digests_are_well_formed_and_framed(self):
        for index, payload in enumerate(ARTIFACTS.values()):
            raw = hashlib.sha256(payload).hexdigest()
            for digest in (
                None, True, 123, [], {}, "", raw, "sha256:" + raw,
                "sha256:" + "0" * 64, "sha256:" + "g" * 64,
                "sha256:" + "0" * 63, "sha256:" + "0" * 65,
                fixture_digest(payload) + "\n",
            ):
                with self.subTest(index=index, digest=digest):
                    self.assert_marker_refused(
                        lambda f: f["publication"]["artifacts"][index].update(digest=digest))

    def test_length_mismatch_and_matching_empty_artifacts_are_refused(self):
        for index, name in enumerate(ARTIFACTS):
            with self.subTest(name=name, mismatch=True), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                argv = write_fixture(root)
                (root / name).write_bytes(ARTIFACTS[name] + b"x")
                self.assert_cli_refused(root, argv)
            with self.subTest(name=name, empty=True), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                fixture = coverage_fixture()
                fixture["publication"]["artifacts"][index].update(
                    bytes=0, digest=fixture_digest(b""))
                argv = write_fixture(root, fixture)
                (root / name).write_bytes(b"")
                self.assert_cli_refused(root, argv)

    def test_missing_artifacts_and_directory_substitutes_are_refused(self):
        for name in ARTIFACTS:
            for as_directory in (False, True):
                with self.subTest(name=name, directory=as_directory), tempfile.TemporaryDirectory() as td:
                    root = Path(td)
                    argv = write_fixture(root)
                    (root / name).unlink()
                    if as_directory:
                        (root / name).mkdir()
                    self.assert_cli_refused(root, argv)

    def test_duplicate_publication_json_key_is_cli_input_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            argv = write_fixture(root)
            path = root / "clean_kernel.coverage.json"
            text = path.read_text()
            self.assertEqual(text.count('"commit_marker": true'), 1)
            path.write_text(text.replace('"commit_marker": true',
                                         '"commit_marker": false, "commit_marker": true'))
            self.assert_cli_refused(root, argv)

    def test_each_artifact_is_read_once_and_raw_hashes_remain_diagnostic(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            write_fixture(root)
            reads = {name: 0 for name in ARTIFACTS}
            original_read = Path.read_bytes

            def counted_read(path):
                if path.parent == root and path.name in reads:
                    reads[path.name] += 1
                return original_read(path)

            with mock.patch.object(Path, "read_bytes", counted_read):
                report = PROBE.probe(root, root, root / "built.mir")
            self.assertEqual(reads, {BINARY_NAME: 1, TEXT_NAME: 1})
            for key, name in (("trust_ir_binary", BINARY_NAME), ("trust_ir_text", TEXT_NAME)):
                self.assertEqual(report["artifact_sha256"][key],
                                 hashlib.sha256(ARTIFACTS[name]).hexdigest())
            self.assertEqual(report["artifact_set_consistency"],
                             "checked against producer publication marker; not source attestation or proof")
            self.assertEqual(report["source_binding"],
                             "Snapshot only; hashes are not compiler-to-source attestation.")
            self.assertFalse(report["source_attachment_verified"])
            self.assertFalse(report["proof_authority"])
            self.assertEqual(report["status"], "blocked")

    def test_valid_publication_set_does_not_require_row_order(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = coverage_fixture()
            fixture["publication"]["artifacts"].reverse()
            argv = write_fixture(root, fixture)
            self.assertEqual(PROBE.main(argv), 1)
            report = json.loads((root / "report.json").read_text())
            self.assertEqual(report["schema_version"], "clean.literal-source-attachment-probe.v2")
            self.assertEqual(report["artifact_publication"], fixture["publication"])
            self.assertFalse(report["source_attachment_verified"])
            self.assertFalse(report["proof_authority"])

    def test_exact_unique_production_function_required(self):
        fixture = coverage_fixture()
        for rows in ([], [fixture["bodies"][0]] * 2):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                PROBE.extraction_record({**fixture, "bodies": rows})
        fixture["bodies"][0]["def_path"] += "_handwritten_model"
        with self.assertRaises(ValueError):
            PROBE.extraction_record(fixture)

    def test_missing_or_malformed_fields_are_refused(self):
        for mutate in (
            lambda f: f.pop("schema"),
            lambda f: f.update(crate="another_crate"),
            lambda f: f.update(proof_authority=True),
            lambda f: f["bodies"][0].update(lowered=1),
            lambda f: f["bodies"][0].pop("unsupported"),
            lambda f: f["bodies"][0].update(unsupported=[["x", 0]]),
        ):
            fixture = coverage_fixture()
            mutate(fixture)
            with self.assertRaises(ValueError):
                PROBE.extraction_record(fixture)

    def test_duplicate_json_keys_are_refused(self):
        with self.assertRaises(ValueError):
            json.loads('{"proof_authority":true,"proof_authority":false}',
                       object_pairs_hook=PROBE.unique_object)

    def test_even_clean_lowering_and_samples_do_not_certify_source(self):
        for lowered in (False, True):
            with self.subTest(lowered=lowered), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                fixture = copy.deepcopy(coverage_fixture())
                if lowered:
                    fixture["bodies"][0].update(
                        lowered=True, spliced=True, func_id=0, unsupported=[],
                        differentials={"interpreter": {"verdict": "agreed", "samples": 1000}},
                    )
                argv = write_fixture(root, fixture)
                mir = root / "built.mir"
                output = root / "report.json"
                result = PROBE.main(argv)
                self.assertEqual(result, 1)
                report = json.loads(output.read_text())
                self.assertFalse(report["source_attachment_verified"])
                self.assertFalse(report["proof_authority"])
                self.assertEqual(report["status"], "blocked")
                mir.write_text("not the actual production body")
                with self.assertRaises(ValueError):
                    PROBE.probe(root, root, mir)


class DirectLiteralSourceProbeTests(unittest.TestCase):
    def assert_refused(self, mutate):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = direct_fixture()
            mutate(fixture)
            argv = write_direct_fixture(root, fixture)
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                self.assertEqual(PROBE.main(argv), 2, stderr.getvalue())
            self.assertFalse((root / "report.json").exists())

    def test_actual_metadata_hash_implementation_is_in_the_source_snapshot(self):
        metadata = "crates/clean-kernel/src/expr/meta.rs"
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            write_direct_fixture(root)
            before = PROBE.probe(root, root, direct_thir=True)
            self.assertIn(metadata, before["source_sha256"])
            payload = b"changed synthetic metadata code, never proof evidence\n"
            (root / metadata).write_bytes(payload)
            after = PROBE.probe(root, root, direct_thir=True)
            self.assertEqual(after["source_sha256"][metadata], hashlib.sha256(payload).hexdigest())
            self.assertNotEqual(before["source_sha256"][metadata], after["source_sha256"][metadata])
            self.assertFalse(after["source_attachment_verified"])
            (root / metadata).unlink()
            with self.assertRaises(OSError):
                PROBE.probe(root, root, direct_thir=True)

    def test_direct_dump_and_emit_do_not_read_or_require_mir(self):
        for surface in ("dump", "emit"):
            with self.subTest(surface=surface), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                argv = write_direct_fixture(root, surface=surface)
                original_read = Path.read_bytes
                reads = []

                def observed_read(path):
                    reads.append(path.name)
                    return original_read(path)

                with mock.patch.object(Path, "read_bytes", observed_read):
                    self.assertEqual(PROBE.main(argv), 1)
                report = json.loads((root / "report.json").read_text())
                self.assertEqual(report["schema_version"], "clean.literal-source-attachment-probe.v3")
                self.assertEqual(report["capture_lane"], "direct-thir")
                self.assertEqual(report["publication_surface"], surface)
                self.assertNotIn("built.mir", reads)
                self.assertNotIn("built_mir", report["artifact_sha256"])
                self.assertNotIn("observed_mir_anchors", report)
                self.assertFalse(report["proof_authority"])
                self.assertFalse(report["source_attachment_verified"])
                self.assertEqual(report["status"], "blocked")
                readback = report["producer_source_static_readback"]
                self.assertEqual(readback["storage_phase"], "cold_initializer_only")
                self.assertEqual(readback["production_body"]["graph"]["nodes"][0]
                                 ["initializer"]["bytes"], [None, 0, None])
                self.assertIn("no storage-semantic or runtime-state validation", readback["interpretation"])

    def test_wrong_surface_never_falls_back_or_globs(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            argv = write_direct_fixture(root, surface="emit")
            argv[argv.index("emit")] = "dump"
            self.assertEqual(PROBE.main(argv), 2)
            self.assertFalse((root / "report.json").exists())

    def test_direct_mode_rejects_mir_even_if_anchors_match(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            write_fixture(root, direct_fixture())
            with self.assertRaisesRegex(ValueError, "does not consume MIR"):
                PROBE.probe(root, root, root / "built.mir", direct_thir=True)
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                PROBE.main(["--dump-dir", str(root), "--direct-thir",
                            "--built-mir", str(root / "built.mir")])
            self.assertEqual(error.exception.code, 2)

    def test_capability_and_both_authority_layers_fail_closed(self):
        for mutate in (
            lambda f: f.pop("direct_obligation_capability"),
            lambda f: f.update(direct_obligation_capability="verified-future-lane"),
            lambda f: f.pop("native_verification_requests"),
            lambda f: f.update(native_verification_requests=0),
            lambda f: f.update(native_verification_requests=True),
            lambda f: f.update(proof_authority=True),
            lambda f: f["source_static_readback"].update(proof_authority=True),
            lambda f: f["source_static_readback"].update(native_verification_requests=0),
            lambda f: f["source_static_readback"].update(native_verification_requests=True),
        ):
            with self.subTest(mutate=mutate):
                self.assert_refused(mutate)

    def test_source_readback_identity_is_exact(self):
        for key in ("schema", "producer", "storage_phase", "evaluator_dependency", "allocation_namespace"):
            with self.subTest(key=key):
                self.assert_refused(lambda f: f["source_static_readback"].update({key: "wrong"}))
        self.assert_refused(lambda f: f.pop("source_static_readback"))

    def test_body_owner_requires_exact_path_hash_and_coverage_index(self):
        for mutate in (
            lambda b: b["owner"].update(def_path="tc::def_eq::proof_irrel::infer_literal_type"),
            lambda b: b["owner"].update(def_path="clean_kernel::tc::infer::infer_literal_type"),
            lambda b: b.update(def_index=8),
            lambda b: b.update(def_index=True),
            lambda b: b.update(def_index=1 << 32),
            lambda b: b["owner"]["def_path_hash"].update(local_hash="short"),
            lambda b: b["owner"].pop("def_path_hash"),
        ):
            with self.subTest(mutate=mutate):
                self.assert_refused(lambda f: mutate(f["source_static_readback"]["bodies"][0]))
        self.assert_refused(lambda f: f["source_static_readback"]["bodies"].append(
            copy.deepcopy(f["source_static_readback"]["bodies"][0])))

    def test_same_leaf_static_in_another_module_is_not_the_builtin(self):
        for path in ("tc::def_eq::proof_irrel::NAME_NAT", "NAME_NAT", "tc::infer::NAME_NAT_model"):
            with self.subTest(path=path):
                self.assert_refused(lambda f: f["source_static_readback"]["bodies"][0]
                                    ["uses"][0]["static_definition"].update(def_path=path))

    def test_static_uses_require_distinct_definitions_and_expression_indices(self):
        for mutate in (
            lambda uses: uses.append(copy.deepcopy(uses[0])),
            lambda uses: uses.pop(),
            lambda uses: uses[1].update(expr_index=uses[0]["expr_index"]),
            lambda uses: uses[0].update(expr_index=True),
            lambda uses: uses[0].update(expr_index=1 << 32),
            lambda uses: uses[0].update(expr_index=65536),
            lambda uses: uses[0].update(expr_index=(1 << 32) - 1),
            lambda uses: uses[1]["static_definition"].update(
                def_path_hash=copy.deepcopy(uses[0]["static_definition"]["def_path_hash"])),
            lambda uses: uses[0]["static_definition"]["def_path_hash"].update(stable_crate_id="0" * 16),
        ):
            with self.subTest(mutate=mutate):
                self.assert_refused(lambda f: mutate(f["source_static_readback"]["bodies"][0]["uses"]))

    def test_complete_root_identities_must_match_actual_source_uses(self):
        for mutate in (
            lambda roots: roots.pop(),
            lambda roots: roots.append(copy.deepcopy(roots[0])),
            lambda roots: roots[0]["definition"]["def_path_hash"].update(local_hash="f" * 16),
        ):
            with self.subTest(mutate=mutate):
                # Fixture roots and source uses deliberately share definition
                # objects; break that alias so corruption changes ROOTS only.
                def corrupt(f):
                    graph = f["source_static_readback"]["bodies"][0]["graph"]
                    graph["statics"] = copy.deepcopy(graph["statics"])
                    mutate(graph["statics"])
                self.assert_refused(corrupt)

    def test_readback_census_and_inventory_status_are_internally_consistent(self):
        for key, value in (("body_count", 0), ("body_count", True), ("complete_bodies", 0),
                           ("refused_bodies", 1), ("inventory_complete", 1), ("capture_status", "partial")):
            with self.subTest(key=key, value=value):
                self.assert_refused(lambda f: f["source_static_readback"].update({key: value}))
        self.assert_refused(lambda f: f["source_static_readback"].update(errors=["inventory omission"]))

    def test_generated_coverage_body_is_not_assumed_to_have_a_hir_readback_owner(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = direct_fixture()
            fixture["bodies"].append({**fixture["bodies"][0], "def_index": 8,
                                      "def_path": "generated_coroutine_body"})
            self.assertEqual(PROBE.main(write_direct_fixture(root, fixture)), 1)
            report = json.loads((root / "report.json").read_text())
            self.assertEqual(report["producer_source_static_readback"]["body_count"], 1)
            self.assertIn("Producer-declared HIR inventory",
                          report["producer_source_static_readback"]["inventory_scope"])

    def test_other_refused_owner_does_not_hide_complete_helper_graph(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = direct_fixture()
            fixture["bodies"].append({**fixture["bodies"][0], "def_path": "other", "def_index": 8})
            readback = fixture["source_static_readback"]
            refused = {"owner": definition_fixture("other", 4), "def_index": 8, "source": None,
                       "uses": [], "graph": {"capture_status": "refused", "errors": ["budget refusal"],
                                               "statics": [], "nodes": []}}
            readback["bodies"].append(refused)
            readback.update(body_count=2, refused_bodies=1, capture_status="partial")
            self.assertEqual(PROBE.main(write_direct_fixture(root, fixture)), 1)
            report = json.loads((root / "report.json").read_text())
            self.assertEqual(report["producer_source_static_readback"]["capture_status"], "partial")
            self.assertEqual(report["producer_source_static_readback"]["production_body"]
                             ["graph"]["capture_status"], "complete")
            self.assertEqual(report["producer_source_static_readback"]["other_refused_owners"],
                             [{"owner": refused["owner"], "def_index": 8, "errors": ["budget refusal"]}])
            self.assertEqual(report["producer_source_static_readback"]["target"], readback["target"])
            self.assertEqual(report["producer_source_static_readback"]["limits"], readback["limits"])
            self.assertFalse(report["source_attachment_verified"])

    def test_global_inventory_refusal_cannot_coexist_with_complete_helper(self):
        self.assert_refused(lambda f: f["source_static_readback"].update(
            inventory_complete=False, capture_status="refused", errors=["missing HIR body"]))

    def test_non_json_numbers_cannot_enter_cold_graph_diagnostics(self):
        for constant in ("NaN", "Infinity", "-Infinity", "1e999"):
            with self.subTest(constant=constant), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                argv = write_direct_fixture(root)
                path = root / "clean_kernel.coverage.json"
                text = path.read_text()
                self.assertIn('"bytes": [null, 0, null]', text)
                path.write_text(text.replace('"bytes": [null, 0, null]',
                                             f'"bytes": [null, {constant}, null]'))
                with redirect_stderr(io.StringIO()):
                    self.assertEqual(PROBE.main(argv), 2)
                self.assertFalse((root / "report.json").exists())

    def test_deeply_nested_invalid_capture_exits_two_without_traceback(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            argv = write_direct_fixture(root)
            (root / "clean_kernel.coverage.json").write_text("[" * 10000 + "0" + "]" * 10000)
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                self.assertEqual(PROBE.main(argv), 2)
            self.assertIn("literal source probe refused:", stderr.getvalue())
            self.assertFalse((root / "report.json").exists())

    def test_cold_roster_entries_target_and_limits_require_json_shapes(self):
        for mutate in (
            lambda r: r["bodies"][0]["graph"].update(nodes=[None]),
            lambda r: r.pop("target"),
            lambda r: r["target"].update(pointer_size_bytes=True),
            lambda r: r["target"].update(little_endian=1),
            lambda r: r.pop("limits"),
            lambda r: r["limits"].update(nodes=True),
        ):
            with self.subTest(mutate=mutate):
                self.assert_refused(lambda f: mutate(f["source_static_readback"]))

    def test_refused_helper_retains_source_uses_without_partial_storage(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = direct_fixture()
            readback = fixture["source_static_readback"]
            readback.update(capture_status="refused", complete_bodies=0, refused_bodies=1)
            body = readback["bodies"][0]
            body["graph"] = {"capture_status": "refused", "errors": ["actual CTFE refusal"],
                             "statics": [], "nodes": []}
            self.assertEqual(PROBE.main(write_direct_fixture(root, fixture)), 1)
            report = json.loads((root / "report.json").read_text())
            self.assertEqual(report["producer_source_static_readback"]["production_body"]["uses"], body["uses"])
            self.assertFalse(report["source_attachment_verified"])
        self.assert_refused(lambda f: f["source_static_readback"]["bodies"][0]["graph"].update(
            capture_status="refused", errors=["refusal"]))

    def test_scan_refusal_retains_unavailable_static_roster_as_diagnostic(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = direct_fixture()
            readback = fixture["source_static_readback"]
            readback.update(capture_status="refused", complete_bodies=0, refused_bodies=1)
            body = readback["bodies"][0]
            body.update(source=None, uses=[], graph={
                "capture_status": "refused",
                "errors": ["source static readback exceeds scan budget of 65536 expressions"],
                "statics": [], "nodes": [],
            })
            self.assertEqual(PROBE.main(write_direct_fixture(root, fixture)), 1)
            report = json.loads((root / "report.json").read_text())
            observed = report["producer_source_static_readback"]
            self.assertEqual(observed["production_static_use_inventory"], "unavailable_or_partial_due_refusal")
            self.assertEqual(observed["production_body"]["uses"], [])
            self.assertEqual(observed["production_body"]["graph"]["errors"], body["graph"]["errors"])
            self.assertFalse(report["source_attachment_verified"])


if __name__ == "__main__":
    unittest.main()
