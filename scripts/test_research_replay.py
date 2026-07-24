# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Regression tests for scripts.research_replay."""

from __future__ import annotations

import contextlib
import io
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts.research_replay import (
    STATUS_FAILED,
    STATUS_PASSED,
    STATUS_SKIPPED,
    build_summary,
    main,
    render_markdown,
    run_clean_research_status,
    validate_gamma_crown_registry_truth,
    validate_local_producer_checkouts,
    validate_lock_shape,
    validate_manifest_shape,
)

SHA256_A = "a" * 64
REVISION_A = "0123456789abcdef0123456789abcdef01234567"
REVISION_B = "89abcdef012345670123456789abcdef01234567"


def _write_json(path: Path, payload: object) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return path


def _write_inputs(root: Path) -> tuple[Path, Path]:
    lock = _write_json(
        root / "research_program_lock.json",
        {
            "schema_version": 1,
            "manifest_kind": "research_program_lock",
            "lock_id": "test-replay-lock",
            "generated_at": "2026-04-23T00:00:00Z",
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
                    "required_fields": ["schema_version", "artifact_id"],
                    "trust_fields": ["proof.quality"],
                    "artifact_kinds": ["source_manifest"],
                }
            },
            "artifact_registry": {
                "schema_id": "clean.artifact_registry.v1",
                "schema_version": 1,
                "entries": [
                    {
                        "artifact_id": "replay-lock-artifact",
                        "kind": "source_manifest",
                        "schema_ref": "proof_artifact_manifest_v1",
                        "content_address": {
                            "algorithm": "sha256",
                            "digest": SHA256_A,
                        },
                        "producer": {
                            "repo": "clean",
                            "revision": REVISION_A,
                        },
                        "storage": {
                            "type": "external_uri",
                            "uri": "artifact://tests/replay-lock-artifact",
                        },
                        "links": {
                            "issues": [3690],
                            "dashboard_anchor": "artifact:replay-lock-artifact",
                        },
                    }
                ],
            },
        },
    )
    manifest = _write_json(
        root / "research_program_manifest.json",
        {
            "schema_version": 1,
            "generated_at": "2026-04-23T00:00:00Z",
            "source": "test",
            "items": [
                {
                    "id": "C004",
                    "title": "CROWN through LayerNorm",
                    "owner_repo": "alabsystems/clean",
                    "domain": "gamma-crown",
                    "family": "gamma-crown",
                    "status": "Axiomatized",
                    "artifact_state": "NotApplicable",
                    "promotion_gate": "TrustReportAgreement",
                    "summary": "test item",
                    "dependencies": [],
                    "evidence": [],
                    "references": [],
                    "tags": [],
                }
            ],
        },
    )
    return lock, manifest


def _write_fake_clean(root: Path, payload: object) -> Path:
    script = root / "fake-clean"
    script.write_text(
        "#!/usr/bin/env python3\n"
        "import json\n"
        f"print(json.dumps(json.loads({json.dumps(json.dumps(payload))})))\n",
        encoding="utf-8",
    )
    os.chmod(script, 0o755)
    return script


def _run_git(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _make_git_checkout(path: Path) -> tuple[Path, str]:
    path.mkdir(parents=True)
    _run_git(path, "init")
    _run_git(path, "config", "user.email", "research-replay@example.invalid")
    _run_git(path, "config", "user.name", "Research Replay")
    (path / "README.md").write_text("test checkout\n", encoding="utf-8")
    _run_git(path, "add", "README.md")
    _run_git(path, "commit", "-m", "initial")
    return path, _run_git(path, "rev-parse", "HEAD")


def _producer_lock(*components: object) -> dict[str, object]:
    return {
        "schema_version": 1,
        "manifest_kind": "research_program_lock",
        "lock_id": "producer-lock",
        "generated_at": "2026-04-23T00:00:00Z",
        "owner_repo": "clean",
        "components": list(components),
        "artifact_schemas": {
            "proof_artifact_manifest_v1": {
                "schema_id": "clean.proof_artifact_manifest.v1",
                "schema_version": 1,
                "required_fields": ["schema_version", "artifact_id"],
                "trust_fields": ["proof.quality"],
                "artifact_kinds": ["source_manifest"],
            }
        },
        "artifact_registry": {
            "schema_id": "clean.artifact_registry.v1",
            "schema_version": 1,
            "entries": [],
        },
    }


class ResearchReplayTests(unittest.TestCase):
    def test_dry_run_skips_clean_command(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            lock, manifest = _write_inputs(Path(td))
            summary = build_summary(
                lock=lock,
                manifest=manifest,
                clean_bin=Path(td) / "missing-clean",
                gamma_crown_registry=Path(td) / "missing-registry.toml",
                dry_run=True,
                require_clean_bin=False,
                generated_at="2026-04-23T00:00:00Z",
            )

        self.assertEqual(summary["overall_status"], STATUS_PASSED)
        statuses = {check["name"]: check["status"] for check in summary["checks"]}
        self.assertEqual(statuses["load_lock_json"], STATUS_PASSED)
        self.assertEqual(statuses["load_manifest_json"], STATUS_PASSED)
        self.assertEqual(statuses["clean_research_status"], STATUS_SKIPPED)
        clean_check = next(
            check
            for check in summary["checks"]
            if check["name"] == "clean_research_status"
        )
        self.assertEqual(clean_check["detail"], "dry-run requested")

    def test_can_skip_local_producer_checkouts_for_ci(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lock, manifest = _write_inputs(root)
            payload = json.loads(lock.read_text(encoding="utf-8"))
            payload["owner_repo"] = "clean"
            payload["components"].append(
                {
                    "id": "gamma-crown",
                    "kind": "git_repository",
                    "lock_role": "proof-artifact-producer",
                    "version": "unreleased-main",
                    "revision": REVISION_B,
                    "source": "local:/missing/gamma-crown",
                }
            )
            lock.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

            summary = build_summary(
                lock=lock,
                manifest=manifest,
                clean_bin=root / "missing-clean",
                gamma_crown_registry=root / "missing-registry.toml",
                dry_run=True,
                require_clean_bin=False,
                skip_local_producer_checkouts=True,
                generated_at="2026-04-23T00:00:00Z",
            )

        self.assertEqual(summary["overall_status"], STATUS_PASSED)
        checkout_check = next(
            check
            for check in summary["checks"]
            if check["name"] == "local_producer_checkouts"
        )
        self.assertEqual(checkout_check["status"], STATUS_SKIPPED)
        self.assertIn("--skip-local-producer-checkouts", checkout_check["detail"])

    def test_lock_validation_rejects_invalid_artifact_registry(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            lock, _ = _write_inputs(Path(td))
            payload = json.loads(lock.read_text(encoding="utf-8"))
            payload["artifact_registry"]["entries"][0].pop("content_address")
            lock.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

            _, check = validate_lock_shape(lock)

        self.assertEqual(check["status"], STATUS_FAILED)
        self.assertIn("content_address", check["detail"])

    def test_lock_validation_rejects_weak_git_producer_revision(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            lock, _ = _write_inputs(Path(td))
            payload = json.loads(lock.read_text(encoding="utf-8"))
            payload["components"][0]["revision"] = "abc123"
            payload["artifact_registry"]["entries"][0]["producer"]["revision"] = (
                "abc123"
            )
            lock.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

            _, check = validate_lock_shape(lock)

        self.assertEqual(check["status"], STATUS_FAILED)
        self.assertIn("$.components[0].revision", check["detail"])
        self.assertIn(
            "$.artifact_registry.entries[0].producer.revision", check["detail"]
        )
        self.assertIn("full non-null", check["detail"])

    def test_local_producer_checkouts_accept_clean_matching_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            workspace, revision = _make_git_checkout(root / "gamma-crown")
            lock_path = _write_json(
                root / "research_program_lock.json",
                _producer_lock(
                    {
                        "id": "gamma-crown",
                        "kind": "git_repository",
                        "lock_role": "proof-artifact-producer",
                        "version": "unreleased-main",
                        "revision": revision,
                        "source": f"local:{workspace}",
                        "workspace": str(workspace),
                        "observed_checkout": {
                            "revision": revision,
                            "dirty": False,
                        },
                    }
                ),
            )
            payload = json.loads(lock_path.read_text(encoding="utf-8"))

            check = validate_local_producer_checkouts(payload, lock_path)

        self.assertEqual(check["status"], STATUS_PASSED)
        self.assertEqual(check["checkout_count"], 1)
        checkout = check["checkouts"][0]
        self.assertEqual(checkout["id"], "gamma-crown")
        self.assertEqual(checkout["actual_revision"], revision)
        self.assertFalse(checkout["dirty"])

    def test_local_producer_checkouts_require_locked_revision(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            workspace, revision = _make_git_checkout(root / "gamma-crown")
            lock_path = _write_json(
                root / "research_program_lock.json",
                _producer_lock(
                    {
                        "id": "gamma-crown",
                        "kind": "git_repository",
                        "lock_role": "proof-artifact-producer",
                        "version": "unreleased-main",
                        "source": f"local:{workspace}",
                        "workspace": str(workspace),
                        "observed_checkout": {
                            "revision": revision,
                            "dirty": False,
                        },
                    }
                ),
            )
            payload = json.loads(lock_path.read_text(encoding="utf-8"))

            check = validate_local_producer_checkouts(payload, lock_path)

        self.assertEqual(check["status"], STATUS_FAILED)
        issues = "; ".join(check["checkouts"][0]["issues"])
        self.assertIn("missing locked revision", issues)

    def test_local_producer_checkouts_reject_weak_locked_revision(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            workspace, revision = _make_git_checkout(root / "gamma-crown")
            lock_path = _write_json(
                root / "research_program_lock.json",
                _producer_lock(
                    {
                        "id": "gamma-crown",
                        "kind": "git_repository",
                        "lock_role": "proof-artifact-producer",
                        "version": "unreleased-main",
                        "revision": revision[:12],
                        "source": f"local:{workspace}",
                        "workspace": str(workspace),
                        "observed_checkout": {
                            "revision": revision,
                            "dirty": False,
                        },
                    }
                ),
            )
            payload = json.loads(lock_path.read_text(encoding="utf-8"))

            check = validate_local_producer_checkouts(payload, lock_path)

        self.assertEqual(check["status"], STATUS_FAILED)
        issues = "; ".join(check["checkouts"][0]["issues"])
        self.assertIn("weak locked revision", issues)

    def test_local_producer_checkouts_report_missing_workspace(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            missing_workspace = root / "missing-gamma-crown"
            lock_path = _write_json(
                root / "research_program_lock.json",
                _producer_lock(
                    {
                        "id": "gamma-crown",
                        "kind": "git_repository",
                        "lock_role": "proof-artifact-producer",
                        "version": "unreleased-main",
                        "revision": REVISION_B,
                        "source": f"local:{missing_workspace}",
                        "workspace": str(missing_workspace),
                    }
                ),
            )
            payload = json.loads(lock_path.read_text(encoding="utf-8"))

            check = validate_local_producer_checkouts(payload, lock_path)

        self.assertEqual(check["status"], STATUS_FAILED)
        self.assertIn("missing workspace", check["detail"])
        self.assertIn(
            "workspace path does not exist", check["checkouts"][0]["issues"][0]
        )

    def test_local_producer_checkouts_report_observed_ahead_of_remote(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            workspace, revision = _make_git_checkout(root / "gamma-crown")
            lock_path = _write_json(
                root / "research_program_lock.json",
                _producer_lock(
                    {
                        "id": "gamma-crown",
                        "kind": "git_repository",
                        "lock_role": "proof-artifact-producer",
                        "version": "unreleased-main",
                        "revision": revision,
                        "source": f"local:{workspace}",
                        "workspace": str(workspace),
                        "observed_checkout": {
                            "revision": revision,
                            "dirty": False,
                            "ahead_of_remote": 2,
                        },
                    }
                ),
            )
            payload = json.loads(lock_path.read_text(encoding="utf-8"))

            check = validate_local_producer_checkouts(payload, lock_path)

        self.assertEqual(check["status"], STATUS_FAILED)
        issues = "; ".join(check["checkouts"][0]["issues"])
        self.assertIn("ahead_of_remote is positive", issues)

    def test_local_producer_checkouts_report_revision_dirty_and_observed_drift(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            workspace, revision = _make_git_checkout(root / "ay")
            (workspace / "dirty.txt").write_text("uncommitted\n", encoding="utf-8")
            locked_revision = REVISION_B
            observed_revision = "1" * 40
            lock_path = _write_json(
                root / "research_program_lock.json",
                _producer_lock(
                    {
                        "id": "ay",
                        "kind": "git_dependency",
                        "lock_role": "smt-proof-certificate-producer",
                        "version": "cargo-git-rev",
                        "revision": locked_revision,
                        "source": "https://example.invalid/ay.git",
                        "observed_checkout": {
                            "workspace": str(workspace),
                            "revision": observed_revision,
                            "dirty": False,
                        },
                    }
                ),
            )
            payload = json.loads(lock_path.read_text(encoding="utf-8"))

            check = validate_local_producer_checkouts(payload, lock_path)

        self.assertEqual(check["status"], STATUS_FAILED)
        checkout = check["checkouts"][0]
        issues = "; ".join(checkout["issues"])
        self.assertEqual(checkout["actual_revision"], revision)
        self.assertTrue(checkout["dirty"])
        self.assertIn("revision mismatch", issues)
        self.assertIn("dirty checkout state", issues)
        self.assertIn("observed_checkout revision drift", issues)
        self.assertIn("observed_checkout stale", issues)

    def test_manifest_validation_requires_owner_repo_artifact_state_and_promotion_gate(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            _, manifest = _write_inputs(Path(td))
            payload = json.loads(manifest.read_text(encoding="utf-8"))
            payload["items"][0].pop("owner_repo")
            payload["items"][0].pop("artifact_state")
            manifest.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

            _, check = validate_manifest_shape(manifest)

        self.assertEqual(check["status"], STATUS_FAILED)
        self.assertIn("owner_repo", check["detail"])
        self.assertIn("artifact_state", check["detail"])

    def test_gamma_crown_registry_truth_rejects_proven_without_kernel(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _, manifest_path = _write_inputs(root)
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            registry = root / "conjectures" / "registry.toml"
            registry.parent.mkdir(parents=True)
            registry.write_text(
                """
[[conjecture]]
id = "C004"
title = "CROWN through LayerNorm"
status = "PROVEN"
confirmed_by = "Experimental, pending clean formalization"
""".lstrip(),
                encoding="utf-8",
            )

            check = validate_gamma_crown_registry_truth(
                manifest=manifest,
                registry_path=registry,
            )

        self.assertEqual(check["status"], STATUS_FAILED)
        self.assertIn("requires clean KernelProved", check["detail"])
        self.assertIn("proof-risk", "; ".join(check["errors"]))

    def test_gamma_crown_registry_truth_rejects_stale_doc_proof_claim(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _, manifest_path = _write_inputs(root)
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            registry = root / "conjectures" / "registry.toml"
            registry.parent.mkdir(parents=True)
            registry.write_text(
                """
[[conjecture]]
id = "C004"
title = "CROWN through LayerNorm"
status = "EMPIRICALLY_SUPPORTED"
""".lstrip(),
                encoding="utf-8",
            )
            stale = root / "crates" / "demo.rs"
            stale.parent.mkdir(parents=True)
            stale.write_text(
                "//! Proved sound: clean C004 -- exact global theorem.\n",
                encoding="utf-8",
            )

            check = validate_gamma_crown_registry_truth(
                manifest=manifest,
                registry_path=registry,
            )

        self.assertEqual(check["status"], STATUS_FAILED)
        self.assertIn("clean proof claim for C004", check["detail"])

    def test_missing_binary_skips_unless_required(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            lock, manifest = _write_inputs(Path(td))
            missing_bin = Path(td) / "target/debug/clean"
            summary = build_summary(
                lock=lock,
                manifest=manifest,
                clean_bin=missing_bin,
                gamma_crown_registry=Path(td) / "missing-registry.toml",
                dry_run=False,
                require_clean_bin=False,
                generated_at="2026-04-23T00:00:00Z",
            )
            required_summary = build_summary(
                lock=lock,
                manifest=manifest,
                clean_bin=missing_bin,
                gamma_crown_registry=Path(td) / "missing-registry.toml",
                dry_run=False,
                require_clean_bin=True,
                generated_at="2026-04-23T00:00:00Z",
            )

        clean_check = next(
            check
            for check in summary["checks"]
            if check["name"] == "clean_research_status"
        )
        self.assertEqual(summary["overall_status"], STATUS_PASSED)
        self.assertEqual(clean_check["status"], STATUS_SKIPPED)
        self.assertIn("clean binary not found", clean_check["detail"])

        required_check = next(
            check
            for check in required_summary["checks"]
            if check["name"] == "clean_research_status"
        )
        self.assertEqual(required_summary["overall_status"], STATUS_FAILED)
        self.assertEqual(required_check["status"], STATUS_FAILED)

    def test_research_status_check_accepts_actual_json_shape(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _, manifest = _write_inputs(root)
            fake_clean = _write_fake_clean(
                root,
                {
                    "manifest_path": str(manifest),
                    "manifest_schema_version": 1,
                    "generated_at": "2026-04-23T00:00:00Z",
                    "source": "test",
                    "total_entries": 1,
                    "status_counts": {"Axiomatized": 1},
                    "domain_counts": {"gamma-crown": 1},
                    "family_counts": {"gamma-crown": 1},
                    "key_entries": [],
                    "entries": [
                        {
                            "id": "C004",
                            "title": "CROWN through LayerNorm",
                            "owner_repo": "alabsystems/clean",
                            "domain": "gamma-crown",
                            "family": "gamma-crown",
                            "status": "Axiomatized",
                            "status_class": "Axiomatized",
                            "artifact_state": "NotApplicable",
                            "promotion_gate": "TrustReportAgreement",
                            "summary": "test item",
                            "dependency_count": 0,
                            "evidence_count": 0,
                            "reference_count": 0,
                        }
                    ],
                    "registries": {},
                },
            )

            check = run_clean_research_status(
                clean_bin=fake_clean,
                manifest=manifest,
                dry_run=False,
                require_clean_bin=True,
            )

        self.assertEqual(check["status"], STATUS_PASSED)
        self.assertEqual(check["manifest_item_count"], 1)
        self.assertEqual(check["status_counts"], {"Axiomatized": 1})

    def test_research_status_check_rejects_missing_entry_fields(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _, manifest = _write_inputs(root)
            fake_clean = _write_fake_clean(
                root,
                {
                    "total_entries": 1,
                    "status_counts": {"Axiomatized": 1},
                    "entries": [
                        {
                            "id": "C004",
                            "status": "Axiomatized",
                            "artifact_state": "NotApplicable",
                            "promotion_gate": "TrustReportAgreement",
                        }
                    ],
                },
            )

            check = run_clean_research_status(
                clean_bin=fake_clean,
                manifest=manifest,
                dry_run=False,
                require_clean_bin=True,
            )

        self.assertEqual(check["status"], STATUS_FAILED)
        self.assertIn("owner_repo", check["detail"])

    def test_markdown_output_contains_issue_comment_report(self) -> None:
        summary = {
            "generated_at": "2026-04-23T00:00:00Z",
            "overall_status": STATUS_PASSED,
            "inputs": {
                "lock": "data/research_program_lock.json",
                "manifest": "data/research_program_manifest.json",
                "clean_bin": "target/debug/clean",
                "dry_run": True,
                "require_clean_bin": False,
            },
            "checks": [
                {
                    "name": "load_lock_json",
                    "status": STATUS_PASSED,
                    "detail": "schema_version=1; components=1; artifact_schemas=1",
                },
                {
                    "name": "clean_research_status",
                    "status": STATUS_SKIPPED,
                    "detail": "dry-run requested",
                    "command": [
                        "target/debug/clean",
                        "research",
                        "status",
                        "--json",
                        "--manifest",
                        "data/research_program_manifest.json",
                    ],
                },
            ],
        }

        markdown = render_markdown(summary)

        self.assertIn("# clean Research Replay", markdown)
        self.assertIn("Overall status: `passed`", markdown)
        self.assertIn("| load_lock_json | passed |", markdown)
        self.assertIn("dry-run requested", markdown)
        self.assertIn("clean research status --json --manifest", markdown)

    def test_cli_writes_json_and_markdown_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lock, manifest = _write_inputs(root)
            json_output = root / "replay.json"
            markdown_output = root / "replay.md"
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "--lock",
                        str(lock),
                        "--manifest",
                        str(manifest),
                        "--clean-bin",
                        str(root / "missing-clean"),
                        "--gamma-crown-registry",
                        str(root / "missing-registry.toml"),
                        "--dry-run",
                        "--json-output",
                        str(json_output),
                        "--markdown-output",
                        str(markdown_output),
                    ]
                )

            written_json = json.loads(json_output.read_text(encoding="utf-8"))
            written_markdown = markdown_output.read_text(encoding="utf-8")

        self.assertEqual(rc, 0)
        self.assertEqual(stdout.getvalue(), "")
        self.assertEqual(written_json["overall_status"], STATUS_PASSED)
        self.assertIn("# clean Research Replay", written_markdown)
        self.assertIn("dry-run requested", written_markdown)

    def test_cli_deterministic_timestamp(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lock, manifest = _write_inputs(root)
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        "--lock",
                        str(lock),
                        "--manifest",
                        str(manifest),
                        "--clean-bin",
                        str(root / "missing-clean"),
                        "--gamma-crown-registry",
                        str(root / "missing-registry.toml"),
                        "--dry-run",
                        "--deterministic",
                    ]
                )

        output = json.loads(stdout.getvalue())
        self.assertEqual(rc, 0)
        self.assertEqual(output["generated_at"], "1970-01-01T00:00:00Z")


if __name__ == "__main__":
    unittest.main()
