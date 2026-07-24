# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Regression tests for scripts.research_lock."""

from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import research_lock

SHA256_A = "a" * 64
SHA256_B = "b" * 64
REVISION_A = "0123456789abcdef0123456789abcdef01234567"


def sample_lock() -> dict[str, object]:
    return {
        "schema_version": 1,
        "manifest_kind": "research_program_lock",
        "lock_id": "test-lock",
        "generated_at": "2026-04-23T00:00:00Z",
        "schema": {
            "$defs": {
                "component": {
                    "properties": {
                        "kind": {
                            "enum": [
                                "git_repository",
                                "git_dependency",
                                "artifact_release",
                                "json_schema",
                            ]
                        }
                    }
                }
            }
        },
        "components": [
            {
                "id": "clean",
                "kind": "git_repository",
                "version": "1.1.0",
                "revision": REVISION_A,
                "source": "https://example.invalid/clean",
            }
        ],
        "artifact_schemas": {
            "proof_artifact_manifest_v1": {
                "schema_id": "clean.proof_artifact_manifest.v1",
                "schema_version": 1,
                "required_fields": [
                    "schema_version",
                    "artifact_id",
                    "lock_id",
                    "claim",
                    "producer",
                    "proof",
                    "artifacts",
                    "reproduction",
                ],
                "trust_fields": [
                    "proof.quality",
                    "proof.kernel_checked",
                    "proof.sorry_count",
                    "proof.trusted_ay_count",
                    "proof.axiom_closure",
                    "proof.external_certificates",
                ],
                "quality_enum": ["constructive", "unchecked"],
                "artifact_kinds": ["source_manifest", "input_fixture"],
            }
        },
        "example": {
            "proof_artifact_manifest": {
                "schema_version": 1,
                "artifact_id": "proof-artifact-test",
                "lock_id": "test-lock",
                "claim": "Test.claim",
                "producer": {
                    "repo": "clean",
                    "revision": REVISION_A,
                },
                "proof": {
                    "quality": "constructive",
                    "kernel_checked": True,
                    "sorry_count": 0,
                    "trusted_ay_count": 0,
                    "axiom_closure": [],
                    "external_certificates": [],
                },
                "artifacts": [
                    {
                        "kind": "source_manifest",
                        "uri": "artifact://tests/axiom-audit",
                        "sha256": SHA256_A,
                    }
                ],
                "reproduction": {
                    "commands": ["python3 scripts/research_dashboard.py"],
                },
            }
        },
        "artifact_registry": {
            "schema_id": "clean.artifact_registry.v1",
            "schema_version": 1,
            "entries": [
                {
                    "artifact_id": "proof-artifact-test",
                    "kind": "source_manifest",
                    "schema_ref": "proof_artifact_manifest_v1",
                    "producer": {
                        "repo": "clean",
                        "revision": REVISION_A,
                    },
                    "storage": {
                        "type": "external_uri",
                        "uri": "artifact://tests/axiom-audit",
                    },
                    "content_address": {
                        "algorithm": "sha256",
                        "digest": SHA256_A,
                    },
                    "links": {
                        "issues": [3690],
                        "dashboard_anchor": "artifact:proof-artifact-test",
                    },
                }
            ],
        },
    }


def write_json(path: Path, payload: object) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return path


class ResearchLockTests(unittest.TestCase):
    def test_valid_lock(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", sample_lock())

            result = research_lock.validate_lock_file(lock_path)

        self.assertTrue(result.valid)
        self.assertEqual(result.errors, [])
        self.assertEqual(result.warnings, [])

    def test_missing_required_field_is_error(self) -> None:
        payload = sample_lock()
        del payload["lock_id"]

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(result.errors[0].path, "$.lock_id")
        self.assertIn("non-empty string", result.errors[0].message)

    def test_invalid_component_kind_is_error(self) -> None:
        payload = sample_lock()
        components = payload["components"]
        assert isinstance(components, list), "expected components to be a list"
        component = components[0]
        assert isinstance(component, dict), "expected first component to be a dict"
        component["kind"] = "spreadsheet"

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(result.errors[0].path, "$.components[0].kind")
        self.assertIn("unknown component kind", result.errors[0].message)

    def test_git_component_revision_must_be_full(self) -> None:
        payload = sample_lock()
        components = payload["components"]
        assert isinstance(components, list), "expected components to be a list"
        component = components[0]
        assert isinstance(component, dict), "expected first component to be a dict"
        component["revision"] = "abc123"

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(result.errors[0].path, "$.components[0].revision")
        self.assertIn("full non-null", result.errors[0].message)

    def test_artifact_schema_trust_fields_are_required(self) -> None:
        payload = sample_lock()
        del payload["example"]
        artifact_schemas = payload["artifact_schemas"]
        assert isinstance(artifact_schemas, dict), (
            "expected artifact_schemas to be a dict"
        )
        schema = artifact_schemas["proof_artifact_manifest_v1"]
        assert isinstance(schema, dict), "expected proof artifact schema to be a dict"
        del schema["trust_fields"]

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.artifact_schemas.proof_artifact_manifest_v1.trust_fields",
        )
        self.assertIn("must be present", result.errors[0].message)

    def test_proof_example_required_fields_are_required(self) -> None:
        payload = sample_lock()
        example = payload["example"]
        assert isinstance(example, dict), "expected example to be a dict"
        manifest = example["proof_artifact_manifest"]
        assert isinstance(manifest, dict), (
            "expected proof artifact manifest to be a dict"
        )
        del manifest["claim"]

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path, "$.example.proof_artifact_manifest.claim"
        )
        self.assertIn("required field 'claim'", result.errors[0].message)

    def test_proof_example_trust_fields_are_required(self) -> None:
        payload = sample_lock()
        example = payload["example"]
        assert isinstance(example, dict), "expected example to be a dict"
        manifest = example["proof_artifact_manifest"]
        assert isinstance(manifest, dict), (
            "expected proof artifact manifest to be a dict"
        )
        proof = manifest["proof"]
        assert isinstance(proof, dict), "expected proof payload to be a dict"
        del proof["external_certificates"]

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.example.proof_artifact_manifest.proof.external_certificates",
        )
        self.assertIn(
            "trust field 'proof.external_certificates'", result.errors[0].message
        )

    def test_proof_quality_enum_is_enforced(self) -> None:
        payload = sample_lock()
        example = payload["example"]
        assert isinstance(example, dict), "expected example to be a dict"
        manifest = example["proof_artifact_manifest"]
        assert isinstance(manifest, dict), (
            "expected proof artifact manifest to be a dict"
        )
        proof = manifest["proof"]
        assert isinstance(proof, dict), "expected proof payload to be a dict"
        proof["quality"] = "headline_only"

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.example.proof_artifact_manifest.proof.quality",
        )
        self.assertIn("unknown proof quality", result.errors[0].message)

    def test_artifact_kind_enum_is_enforced(self) -> None:
        payload = sample_lock()
        example = payload["example"]
        assert isinstance(example, dict), "expected example to be a dict"
        manifest = example["proof_artifact_manifest"]
        assert isinstance(manifest, dict), (
            "expected proof artifact manifest to be a dict"
        )
        artifacts = manifest["artifacts"]
        assert isinstance(artifacts, list), "expected artifacts to be a list"
        artifact = artifacts[0]
        assert isinstance(artifact, dict), "expected first artifact to be a dict"
        artifact["kind"] = "spreadsheet"

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.example.proof_artifact_manifest.artifacts[0].kind",
        )
        self.assertIn("unknown artifact kind", result.errors[0].message)

    def test_artifact_registry_accepts_external_reference(self) -> None:
        payload = sample_lock()
        payload["artifact_registry"] = {
            "schema_id": "clean.artifact_registry.v1",
            "schema_version": 1,
            "entries": [
                {
                    "artifact_id": "large-proof-log",
                    "kind": "source_manifest",
                    "schema_ref": "proof_artifact_manifest_v1",
                    "producer": {
                        "repo": "clean",
                        "revision": REVISION_A,
                    },
                    "storage": {
                        "type": "external_uri",
                        "uri": "s3://clean-artifacts/large-proof-log.json",
                    },
                    "content_address": {
                        "algorithm": "sha256",
                        "digest": SHA256_B,
                    },
                    "links": {
                        "issues": [3690],
                        "dashboard_anchor": "artifact:large-proof-log",
                    },
                }
            ],
        }

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertTrue(result.valid)
        self.assertEqual(result.errors, [])

    def test_artifact_registry_requires_linkable_id_producer_and_content_address(
        self,
    ) -> None:
        payload = sample_lock()
        payload["artifact_registry"] = {
            "schema_id": "clean.artifact_registry.v1",
            "schema_version": 1,
            "entries": [
                {
                    "kind": "source_manifest",
                    "schema_ref": "proof_artifact_manifest_v1",
                    "storage": {
                        "type": "git_path",
                        "path": "artifacts/large-proof-log.json",
                    },
                }
            ],
        }

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        paths = {error.path for error in result.errors}
        self.assertEqual(
            paths,
            {
                "$.artifact_registry.entries[0].artifact_id",
                "$.artifact_registry.entries[0].producer",
                "$.artifact_registry.entries[0].content_address",
                "$.artifact_registry.entries[0].links",
            },
        )

    def test_artifact_registry_requires_dashboard_link_metadata(self) -> None:
        payload = sample_lock()
        registry = payload["artifact_registry"]
        assert isinstance(registry, dict), "expected artifact_registry to be a dict"
        entries = registry["entries"]
        assert isinstance(entries, list), "expected registry entries to be a list"
        entry = entries[0]
        assert isinstance(entry, dict), "expected first registry entry to be a dict"
        entry["links"] = {"issues": [3690]}

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.artifact_registry.entries[0].links.dashboard_anchor",
        )

    def test_artifact_registry_requires_producer_revision(self) -> None:
        payload = sample_lock()
        registry = payload["artifact_registry"]
        assert isinstance(registry, dict), "expected artifact_registry to be a dict"
        entries = registry["entries"]
        assert isinstance(entries, list), "expected registry entries to be a list"
        entry = entries[0]
        assert isinstance(entry, dict), "expected first registry entry to be a dict"
        producer = entry["producer"]
        assert isinstance(producer, dict), "expected registry producer to be a dict"
        producer.pop("revision")
        producer["version"] = "2026.04"

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.artifact_registry.entries[0].producer.revision",
        )
        self.assertIn("producer revision", result.errors[0].message)

    def test_artifact_registry_git_producer_revision_must_be_full(self) -> None:
        payload = sample_lock()
        registry = payload["artifact_registry"]
        assert isinstance(registry, dict), "expected artifact_registry to be a dict"
        entries = registry["entries"]
        assert isinstance(entries, list), "expected registry entries to be a list"
        entry = entries[0]
        assert isinstance(entry, dict), "expected first registry entry to be a dict"
        producer = entry["producer"]
        assert isinstance(producer, dict), "expected registry producer to be a dict"
        producer["revision"] = "abc123"

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.artifact_registry.entries[0].producer.revision",
        )
        self.assertIn("full non-null", result.errors[0].message)

    def test_artifact_registry_requires_structured_content_address(self) -> None:
        payload = sample_lock()
        registry = payload["artifact_registry"]
        assert isinstance(registry, dict), "expected artifact_registry to be a dict"
        entries = registry["entries"]
        assert isinstance(entries, list), "expected registry entries to be a list"
        entry = entries[0]
        assert isinstance(entry, dict), "expected first registry entry to be a dict"
        entry.pop("content_address")
        entry["sha256"] = SHA256_A

        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", payload)

            result = research_lock.validate_lock_file(lock_path)

        self.assertFalse(result.valid)
        self.assertEqual(len(result.errors), 1)
        self.assertEqual(
            result.errors[0].path,
            "$.artifact_registry.entries[0].content_address",
        )
        self.assertIn("content_address", result.errors[0].message)

    def test_local_mismatch_is_warning_not_error(self) -> None:
        payload = sample_lock()
        components = payload["components"]
        assert isinstance(components, list), "expected components to be a list"
        component = components[0]
        assert isinstance(component, dict), "expected first component to be a dict"

        with tempfile.TemporaryDirectory() as td:
            workspace = Path(td) / "workspace"
            workspace.mkdir()
            component["workspace"] = str(workspace)
            lock_path = write_json(Path(td) / "lock.json", payload)

            with patch.object(
                research_lock,
                "git_head_revision",
                return_value=("def456", None),
            ):
                result = research_lock.validate_lock_file(lock_path, check_local=True)

        self.assertTrue(result.valid)
        self.assertEqual(result.errors, [])
        self.assertEqual(len(result.warnings), 1)
        self.assertEqual(result.warnings[0].path, "$.components[0].revision")
        self.assertIn("local revision mismatch", result.warnings[0].message)

    def test_cli_json_for_valid_lock(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            lock_path = write_json(Path(td) / "lock.json", sample_lock())
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = research_lock.main(["--lock", str(lock_path), "--json"])

        output = json.loads(stdout.getvalue())
        self.assertEqual(rc, 0)
        self.assertTrue(output["valid"])
        self.assertEqual(output["error_count"], 0)
        self.assertEqual(output["warning_count"], 0)

    def test_self_check_cli(self) -> None:
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            rc = research_lock.main(["--self-check"])

        self.assertEqual(rc, 0)
        self.assertIn("research_lock self-check: ok", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
