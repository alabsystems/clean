# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

MODULE_PATH = Path(__file__).with_name("generated_count_runner.py")
SPEC = importlib.util.spec_from_file_location("generated_count_runner", MODULE_PATH)
assert SPEC is not None, (
    "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:18"
)
runner = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None, (
    "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:20"
)
sys.modules[SPEC.name] = runner
SPEC.loader.exec_module(runner)


def _without_first_manifest_runner_path(text: str) -> str:
    """The registry text with the first generated-count manifest's
    ``runner_path`` line removed."""
    lines = text.splitlines(keepends=True)
    start = next(
        i for i, line in enumerate(lines) if line.strip() == "generated_count_manifests:"
    )
    for i in range(start + 1, len(lines)):
        if lines[i].strip().startswith("runner_path:"):
            return "".join(lines[:i] + lines[i + 1 :])
    raise AssertionError("the registry's first manifest has no runner_path line")


class _Captured:
    def __init__(self, out: str, err: str) -> None:
        self.out = out
        self.err = err


class _CapturedOutput:
    """stdout and stderr since the last ``readouterr()``, as pytest's capsys
    reported them."""

    def __init__(self) -> None:
        self.stdout = io.StringIO()
        self.stderr = io.StringIO()

    def readouterr(self) -> _Captured:
        captured = _Captured(self.stdout.getvalue(), self.stderr.getvalue())
        for stream in (self.stdout, self.stderr):
            stream.seek(0)
            stream.truncate()
        return captured


class GeneratedCountRunnerTests(unittest.TestCase):
    def make_tmp_path(self) -> Path:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        return Path(tmp.name)

    def capture_output(self) -> _CapturedOutput:
        capture = _CapturedOutput()
        stack = contextlib.ExitStack()
        stack.enter_context(contextlib.redirect_stdout(capture.stdout))
        stack.enter_context(contextlib.redirect_stderr(capture.stderr))
        self.addCleanup(stack.close)
        return capture

    def test_dry_run_skeleton_has_complete_contract_shape(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)

        artifact = runner.dry_run_artifact(manifest, corpus)

        assert set(artifact) >= {
            "schema_version",
            "tactic_lane",
            "run_id",
            "cases_total",
            "lean4_successes",
            "clean_successes",
            "matched_successes",
            "source_corpus_path",
            "source_corpus_sha256",
            "runner_path",
            "runner_command",
            "artifact_status",
            "dry_run",
            "case_ids",
        }, "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:31"
        assert artifact["schema_version"] == runner.CONTRACT_VERSION, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:47"
        )
        assert artifact["artifact_status"] == runner.FAIL_CLOSED_STATUS, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:48"
        )
        assert artifact["dry_run"] is True, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:49"
        )
        assert artifact["lean4_successes"] is None, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:50"
        )
        assert artifact["clean_successes"] is None, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:51"
        )
        assert artifact["matched_successes"] is None, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:52"
        )
        assert artifact["runner_path"] == runner.RUNNER_REPO_PATH, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:53"
        )
        assert artifact["runner_command"] == manifest.runner_command, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:54"
        )
        assert artifact["cases_total"] == 1, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:55"
        )
        assert artifact["case_ids"] == ["simp_all_opaque_target_no_progress"], (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:56"
        )
        assert not runner.validate_artifact(
            artifact, manifest, corpus, allow_dry_run=True
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:57"


    def test_artifact_contract_output_is_stable(self) -> None:
        contract = runner.artifact_contract()

        assert contract == {
            "schema_version": runner.CONTRACT_SCHEMA_VERSION,
            "artifact_contract_version": runner.CONTRACT_VERSION,
            "artifact_format": "json",
            "required_fields": [
                "schema_version",
                "tactic_lane",
                "run_id",
                "cases_total",
                "lean4_successes",
                "clean_successes",
                "matched_successes",
                "source_corpus_path",
                "source_corpus_sha256",
                "runner_path",
                "runner_command",
            ],
            "integer_count_fields": [
                "cases_total",
                "lean4_successes",
                "clean_successes",
                "matched_successes",
            ],
            "dry_run_nullable_fields": [
                "lean4_successes",
                "clean_successes",
                "matched_successes",
            ],
            "optional_fields": [
                "artifact_status",
                "dry_run",
                "case_ids",
            ],
            "forbidden_fields": [
                "engine",
                "tactic",
            ],
            "missing_or_mismatched_artifact_status": runner.FAIL_CLOSED_STATUS,
            "print_contract_produces_evidence": False,
            "dry_run_produces_evidence": False,
            "readiness_effect": "none",
        }, "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:63"


    def test_cli_print_contract_outputs_json_without_lane_or_evidence(self) -> None:
        capsys = self.capture_output()
        exit_code = runner.main(["--print-contract"])

        captured = capsys.readouterr()
        contract = json.loads(captured.out)

        assert exit_code == 0, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:113"
        )
        assert captured.err == "", (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:114"
        )
        assert contract == runner.artifact_contract(), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:115"
        )
        assert "tactic_lane" not in contract, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:116"
        )
        assert "run_id" not in contract, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:117"
        )
        assert "cases_total" not in contract, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:118"
        )
        assert contract["print_contract_produces_evidence"] is False, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:119"
        )
        assert contract["readiness_effect"] == "none", (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:120"
        )


    def test_contract_output_is_not_a_generated_count_artifact(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)

        errors = runner.validate_artifact(runner.artifact_contract(), manifest, corpus)

        assert errors == ["--print-contract output is not a generated-count artifact"], (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:129"
        )


    def test_artifact_rejects_non_canonical_tactic_and_engine_fields(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)
        artifact.pop("artifact_status")
        artifact.pop("dry_run")
        artifact.pop("case_ids")
        artifact["run_id"] = "unit-test-run"
        artifact["lean4_successes"] = 1
        artifact["clean_successes"] = 1
        artifact["matched_successes"] = 1
        artifact["tactic"] = "simp"
        artifact["engine"] = "lean4"

        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert (
            "forbidden artifact field 'engine': generated-count artifacts must compare Lean4 and clean counts"
            in errors
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:148"
        assert (
            "forbidden artifact field 'tactic': use tactic_lane to bind evidence to a generated-count manifest"
            in errors
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:152"


    def test_every_manifest_lane_advertises_runner_and_valid_dry_run(self) -> None:
        registry = runner.load_yaml(runner.DEFAULT_REGISTRY)
        manifests = registry["inputs"]["generated_count_manifests"]

        for raw_manifest in manifests:
            lane = raw_manifest["tactic_lane"]
            manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, lane)
            corpus = runner.load_source_corpus(manifest)
            artifact = runner.dry_run_artifact(manifest, corpus)

            assert manifest.runner_path == runner.RUNNER_REPO_PATH, (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:168"
            )
            assert Path(runner.REPO_ROOT / manifest.runner_path).is_file(), (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:169"
            )
            assert (
                manifest.runner_command
                == f"python3 {manifest.runner_path} --lane {lane} --dry-run"
            ), (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:170"
            )
            assert artifact["schema_version"] == runner.CONTRACT_VERSION, (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:174"
            )
            assert artifact["tactic_lane"] == lane, (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:175"
            )
            assert artifact["dry_run"] is True, (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:176"
            )
            assert artifact["artifact_status"] == runner.FAIL_CLOSED_STATUS, (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:177"
            )
            assert not runner.validate_artifact(
                artifact, manifest, corpus, allow_dry_run=True
            ), (
                "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:178"
            )


    def test_manifest_lane_rejects_missing_runner_path(self) -> None:
        tmp_path = self.make_tmp_path()
        registry = runner.load_yaml(runner.DEFAULT_REGISTRY)
        registry["inputs"]["generated_count_manifests"][0].pop("runner_path")
        registry_path = tmp_path / "tactic-parity.yaml"
        registry_path.write_text(
            _without_first_manifest_runner_path(
                runner.DEFAULT_REGISTRY.read_text(encoding="utf-8")
            ),
            encoding="utf-8",
        )
        assert runner.load_yaml(registry_path) == registry, (
            "the edited registry must differ from the committed one only by the "
            "first manifest's runner_path"
        )

        try:
            runner.load_lane_manifest(registry_path, "simp")
        except ValueError as err:
            if "runner_path" not in str(err):
                raise AssertionError(
                    "missing runner_path error should mention runner_path"
                ) from err
        else:
            raise AssertionError("missing runner_path should fail")


    def test_dry_run_checksum_tracks_source_corpus_bytes(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "rw")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)

        expected = hashlib.sha256(corpus.path.read_bytes()).hexdigest()

        assert (
            artifact["source_corpus_path"]
            == "evals/tactic-parity/corpora/rw-count-corpus.yaml"
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:200"
        assert artifact["source_corpus_sha256"] == expected, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:204"
        )
        assert artifact["cases_total"] == 2, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:205"
        )


    def test_incomplete_json_shape_is_rejected(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)
        del artifact["clean_successes"]

        errors = runner.validate_artifact(artifact, manifest, corpus, allow_dry_run=True)

        assert "missing required field 'clean_successes'" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:216"
        )


    def test_dry_run_skeleton_is_not_real_generated_counts(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)

        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert "dry-run skeleton is not a real generated-count artifact" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:226"
        )


    def test_real_artifact_shape_requires_bounded_integer_counts(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)
        artifact.pop("artifact_status")
        artifact.pop("dry_run")
        artifact.pop("case_ids")
        artifact["run_id"] = "unit-test-run"
        artifact["lean4_successes"] = 1
        artifact["clean_successes"] = 1
        artifact["matched_successes"] = 1

        assert not runner.validate_artifact(artifact, manifest, corpus), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:241"
        )

        artifact["matched_successes"] = 2
        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert "matched_successes must not exceed cases_total" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:246"
        )
        assert "matched_successes must not exceed either engine success count" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:247"
        )


    def test_real_artifact_rejects_missing_empty_or_mismatched_runner_command_provenance(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)
        artifact.pop("artifact_status")
        artifact.pop("dry_run")
        artifact.pop("case_ids")
        artifact["run_id"] = "unit-test-run"
        artifact["lean4_successes"] = 1
        artifact["clean_successes"] = 1
        artifact["matched_successes"] = 1

        missing_artifact = dict(artifact)
        missing_artifact.pop("runner_command")
        errors = runner.validate_artifact(missing_artifact, manifest, corpus)

        assert "missing required field 'runner_command'" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:268"
        )

        artifact["runner_command"] = ""

        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert "runner_command must be a non-empty string" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:274"
        )

        artifact["runner_command"] = "python3 wrong.py --lane simp --dry-run"
        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert "runner_command does not match generated-count manifest" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:279"
        )


    def test_real_artifact_rejects_engine_successes_over_cases_total(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)
        artifact.pop("artifact_status")
        artifact.pop("dry_run")
        artifact.pop("case_ids")
        artifact["run_id"] = "unit-test-run"
        artifact["lean4_successes"] = corpus.cases_total + 1
        artifact["clean_successes"] = corpus.cases_total + 1
        artifact["matched_successes"] = corpus.cases_total

        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert "lean4_successes must not exceed cases_total" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:296"
        )
        assert "clean_successes must not exceed cases_total" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:297"
        )
        assert (
            "matched_successes must not exceed either engine success count" not in errors
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:298"


    def test_real_artifact_rejects_mismatched_case_ids(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)
        artifact.pop("artifact_status")
        artifact.pop("dry_run")
        artifact["run_id"] = "unit-test-run"
        artifact["lean4_successes"] = 1
        artifact["clean_successes"] = 1
        artifact["matched_successes"] = 1
        artifact["case_ids"] = ["wrong-case-id"]

        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert "case_ids does not match source corpus order" in errors, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:315"
        )


    def test_partial_real_count_shape_reports_error_without_crashing(self) -> None:
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)
        artifact = runner.dry_run_artifact(manifest, corpus)
        artifact.pop("artifact_status")
        artifact.pop("dry_run")
        artifact.pop("case_ids")
        artifact["run_id"] = "unit-test-run"
        artifact["lean4_successes"] = 1
        artifact["clean_successes"] = None
        artifact["matched_successes"] = 1

        errors = runner.validate_artifact(artifact, manifest, corpus)

        assert (
            "generated-count artifact must define non-negative integer field 'clean_successes'"
            in errors
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:332"


    def test_cli_check_missing_artifact_fails_closed(self) -> None:
        tmp_path = self.make_tmp_path()
        capsys = self.capture_output()
        missing_artifact = tmp_path / "missing.json"

        exit_code = runner.main(
            ["--lane", "simp", "--check-artifact", str(missing_artifact)]
        )

        captured = capsys.readouterr()
        assert exit_code == 2, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:346"
        )
        assert runner.FAIL_CLOSED_STATUS in captured.err, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:347"
        )


    def test_cli_dry_run_outputs_valid_json(self) -> None:
        capsys = self.capture_output()
        exit_code = runner.main(["--lane", "simp", "--dry-run"])

        captured = capsys.readouterr()
        artifact = json.loads(captured.out)

        assert exit_code == 0, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:356"
        )
        assert artifact["schema_version"] == runner.CONTRACT_VERSION, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:357"
        )
        assert artifact["dry_run"] is True, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:358"
        )


    def test_cli_write_dry_run_creates_parent_dirs_and_schema(self) -> None:
        tmp_path = self.make_tmp_path()
        artifact_path = tmp_path / "nested" / "counts" / "simp-counts.json"

        exit_code = runner.main(["--lane", "simp", "--write-dry-run", str(artifact_path)])

        assert exit_code == 0, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:366"
        )
        assert artifact_path.is_file(), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:367"
        )
        artifact = json.loads(artifact_path.read_text(encoding="utf-8"))
        manifest = runner.load_lane_manifest(runner.DEFAULT_REGISTRY, "simp")
        corpus = runner.load_source_corpus(manifest)

        assert artifact == runner.dry_run_artifact(manifest, corpus), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:372"
        )
        assert artifact["schema_version"] == runner.CONTRACT_VERSION, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:373"
        )
        assert artifact["artifact_status"] == runner.FAIL_CLOSED_STATUS, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:374"
        )
        assert artifact["dry_run"] is True, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:375"
        )
        assert list(artifact_path.parent.glob("*.tmp")) == [], (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:376"
        )


    def test_write_json_object_atomic_replaces_from_target_parent(self) -> None:
        tmp_path = self.make_tmp_path()
        artifact_path = tmp_path / "nested" / "counts" / "simp-counts.json"
        calls: list[tuple[Path, Path]] = []
        real_replace = runner.os.replace

        def record_replace(source, target) -> None:
            calls.append((Path(source), Path(target)))
            real_replace(source, target)

        patcher = mock.patch.object(runner.os, "replace", record_replace)
        patcher.start()
        self.addCleanup(patcher.stop)

        runner.write_json_object_atomic(
            artifact_path,
            {"schema_version": runner.CONTRACT_VERSION},
        )

        assert len(calls) == 1, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:397"
        )
        temp_path, target_path = calls[0]
        assert target_path == artifact_path, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:399"
        )
        assert temp_path.parent == artifact_path.parent, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:400"
        )
        assert temp_path.name.startswith(f".{artifact_path.name}."), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:401"
        )
        assert temp_path.name.endswith(".tmp"), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:402"
        )
        assert artifact_path.is_file(), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:403"
        )


    def test_cli_write_dry_run_is_deterministic(self) -> None:
        tmp_path = self.make_tmp_path()
        first_path = tmp_path / "first.json"
        second_path = tmp_path / "second.json"

        assert runner.main(["--lane", "rw", "--write-dry-run", str(first_path)]) == 0, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:410"
        )
        assert runner.main(["--lane", "rw", "--write-dry-run", str(second_path)]) == 0, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:411"
        )

        assert first_path.read_bytes() == second_path.read_bytes(), (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:413"
        )


    def test_cli_check_rejects_written_dry_run_as_launch_evidence(self) -> None:
        tmp_path = self.make_tmp_path()
        capsys = self.capture_output()
        artifact_path = tmp_path / "metrics" / "simp-counts.json"
        assert (
            runner.main(["--lane", "simp", "--write-dry-run", str(artifact_path)]) == 0
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:420"

        exit_code = runner.main(["--lane", "simp", "--check-artifact", str(artifact_path)])

        captured = capsys.readouterr()
        assert exit_code == 1, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:425"
        )
        assert "dry-run skeleton is not a real generated-count artifact" in captured.err, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:426"
        )


    def test_cli_check_allows_written_dry_run_only_when_explicit(self) -> None:
        tmp_path = self.make_tmp_path()
        artifact_path = tmp_path / "metrics" / "simp-counts.json"
        assert (
            runner.main(["--lane", "simp", "--write-dry-run", str(artifact_path)]) == 0
        ), "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:431"

        exit_code = runner.main(
            [
                "--lane",
                "simp",
                "--check-artifact",
                str(artifact_path),
                "--allow-dry-run",
            ]
        )

        assert exit_code == 0, (
            "assertion failed in scripts/tactic_parity/test_generated_count_runner.py:443"
        )


if __name__ == "__main__":
    unittest.main()
