# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Regression tests for scripts.research_dashboard."""

from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import research_dashboard
from scripts.research_dashboard import (
    build_dashboard,
    main,
    parse_timestamp,
    render_markdown,
    validate_dashboard_freshness,
)


def _write_json(path: Path, payload: object) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return path


class ResearchDashboardTests(unittest.TestCase):
    def test_build_dashboard_summarizes_lock_and_queue(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lock = _write_json(
                root / "research_program_lock.json",
                {
                    "schema_version": 1,
                    "manifest_kind": "research_program_lock",
                    "lock_id": "test-lock",
                    "generated_at": "2026-04-23T00:00:00Z",
                    "issues": [3686, 3688],
                    "components": [{"id": "clean"}, {"id": "gamma-crown"}],
                    "artifact_schemas": {"proof_artifact_manifest_v1": {}},
                    "artifact_registry": {
                        "entries": [
                            {
                                "artifact_id": "proof-artifact-registry",
                                "links": {"issues": [3688, 3690]},
                            }
                        ]
                    },
                    "example": {
                        "proof_artifact_manifest": {
                            "artifact_id": "proof-artifact-test-C008",
                            "issue": 3690,
                            "lock_id": "test-lock",
                        }
                    },
                },
            )
            queue = _write_json(
                root / "proof_queue.json",
                {
                    "generated_at": "2026-04-23T00:00:00Z",
                    "queue": [
                        {"issue": 1, "labels": ["blocked"], "claimed": False},
                        {"issue": 2, "labels": ["tracking"], "claimed": True},
                    ],
                },
            )

            dashboard = build_dashboard(
                [lock, queue],
                generated_at="2026-04-23T00:00:00Z",
                title="Test Dashboard",
            )

        self.assertEqual(dashboard["schema_version"], 1)
        self.assertEqual(dashboard["summary"]["input_count"], 2)
        self.assertEqual(dashboard["summary"]["by_kind"]["research_program_lock"], 1)
        self.assertEqual(dashboard["summary"]["by_kind"]["proof_queue"], 1)
        self.assertEqual(dashboard["summary"]["issue_refs"], [1, 2, 3686, 3688, 3690])
        self.assertEqual(
            dashboard["summary"]["artifact_ids"],
            ["proof-artifact-registry", "proof-artifact-test-C008"],
        )
        self.assertEqual(
            dashboard["summary"]["artifact_links"],
            [
                {
                    "artifact_id": "proof-artifact-registry",
                    "issue": 3688,
                    "source": str(lock),
                },
                {
                    "artifact_id": "proof-artifact-registry",
                    "issue": 3690,
                    "source": str(lock),
                },
                {
                    "artifact_id": "proof-artifact-test-C008",
                    "issue": 3690,
                    "source": str(lock),
                },
            ],
        )
        self.assertEqual(dashboard["inputs"][0]["totals"]["components"], 2)
        self.assertEqual(
            dashboard["inputs"][0]["totals"]["artifact_registry_entries"], 1
        )
        self.assertEqual(
            dashboard["inputs"][0]["artifact_ids"],
            ["proof-artifact-registry", "proof-artifact-test-C008"],
        )
        self.assertEqual(dashboard["inputs"][1]["status_counts"]["blocked"], 1)
        self.assertEqual(dashboard["inputs"][1]["status_counts"]["claimed"], 1)

    def test_build_dashboard_summarizes_research_program_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "research_program_manifest.json",
                {
                    "schema_version": 1,
                    "generated_at": "2026-04-23T00:00:00Z",
                    "source": "test",
                    "items": [
                        {
                            "id": "C004",
                            "title": "LayerNorm CROWN",
                            "owner_repo": "alabsystems/clean",
                            "domain": "gamma-crown",
                            "family": "gamma-crown core conjectures",
                            "status": "Axiomatized",
                            "artifact_state": "NotApplicable",
                            "promotion_gate": "TrustReportAgreement",
                            "summary": "test",
                            "dependencies": [],
                            "evidence": ["data/axiom_audit.json"],
                            "references": ["issue #3373"],
                            "tags": ["crown"],
                        },
                        {
                            "id": "S40",
                            "title": "Haken lower bound",
                            "owner_repo": "alabsystems/clean",
                            "domain": "sat-frontier",
                            "family": "boolean-analysis frontier S40-S51",
                            "status": "DerivedPending",
                            "artifact_state": "Planned",
                            "promotion_gate": "KernelProofAndAxiomAudit",
                            "summary": "test",
                            "dependencies": [{"id": "S41", "reason": "basis"}],
                            "evidence": [],
                            "references": [],
                            "tags": ["resolution", "lower-bound"],
                            "artifact_ids": ["proof-artifact-S40"],
                        },
                    ],
                },
            )

            dashboard = build_dashboard([path], generated_at="2026-04-23T00:00:00Z")

        item = dashboard["inputs"][0]
        self.assertEqual(item["kind"], "research_program_manifest")
        self.assertEqual(item["totals"]["items"], 2)
        self.assertEqual(item["totals"]["dependencies"], 1)
        self.assertEqual(item["totals"]["evidence_refs"], 1)
        self.assertEqual(item["totals"]["references"], 1)
        self.assertEqual(item["totals"]["tags"], 3)
        self.assertEqual(item["status_counts"]["Axiomatized"], 1)
        self.assertEqual(item["status_counts"]["DerivedPending"], 1)
        self.assertEqual(
            item["detail_counts"]["domain_counts"],
            {"gamma-crown": 1, "sat-frontier": 1},
        )
        self.assertEqual(item["artifact_ids"], ["proof-artifact-S40"])

        markdown = render_markdown(dashboard)
        self.assertIn("research_program_manifest | 1 |", markdown)
        self.assertIn("items=2", markdown)
        self.assertIn("Axiomatized=1, DerivedPending=1", markdown)
        self.assertIn("proof-artifact-S40", markdown)

    def test_build_dashboard_summarizes_axiom_audit(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "axiom_audit.json",
                {
                    "last_updated": "2026-04-21",
                    "total_domain_axioms": 35,
                    "total_theorems": 522,
                    "conjectures": {
                        "C001": {"axioms": 3, "theorems": 2, "definitions": 1},
                        "C002": {"axioms": 4, "theorems": 5, "opaques": 6},
                    },
                },
            )

            dashboard = build_dashboard([path], generated_at="2026-04-23T00:00:00Z")

        item = dashboard["inputs"][0]
        self.assertEqual(item["kind"], "axiom_audit")
        self.assertEqual(item["totals"]["total_domain_axioms"], 35)
        self.assertEqual(item["totals"]["conjectures"], 2)
        self.assertEqual(item["totals"]["axioms"], 7)
        self.assertEqual(item["totals"]["theorems"], 7)

    def test_build_dashboard_summarizes_research_status_report(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "research_status.json",
                {
                    "manifest_path": "data/research_program_manifest.json",
                    "manifest_schema_version": 1,
                    "generated_at": "2026-04-23T00:00:00Z",
                    "source": "synthetic",
                    "total_entries": 3,
                    "status_counts": {
                        "Axiomatized": 1,
                        "ExecutableChecked": 2,
                    },
                    "domain_counts": {"sat": 2, "gamma": 1},
                    "family_counts": {"frontier": 3},
                    "key_entries": [],
                    "entries": [],
                    "registries": {
                        "proof_library": {"total_proofs": 17},
                        "sat_frontier": {"total_entries": 5},
                        "gamma_crown": {"total_conjectures": 12},
                    },
                },
            )

            dashboard = build_dashboard([path], generated_at="2026-04-23T00:00:00Z")

        item = dashboard["inputs"][0]
        self.assertEqual(item["kind"], "research_status_report")
        self.assertEqual(item["totals"]["total_entries"], 3)
        self.assertEqual(item["totals"]["proof_library.total_proofs"], 17)
        self.assertEqual(item["totals"]["sat_frontier.total_entries"], 5)
        self.assertEqual(item["totals"]["gamma_crown.total_conjectures"], 12)
        self.assertEqual(item["status_counts"]["Axiomatized"], 1)
        self.assertEqual(item["status_counts"]["ExecutableChecked"], 2)

        markdown = render_markdown(dashboard)
        self.assertIn("research_status.json | research_status_report", markdown)
        self.assertIn("total_entries=3", markdown)
        self.assertIn("proof_library.total_proofs=17", markdown)
        self.assertIn("Axiomatized=1, ExecutableChecked=2", markdown)

    def test_render_markdown_contains_compact_table(self) -> None:
        dashboard = {
            "title": "Test Dashboard",
            "generated_at": "2026-04-23T00:00:00Z",
            "inputs": [
                {
                    "path": "data/proof_queue.json",
                    "kind": "proof_queue",
                    "version": None,
                    "updated_at": "2026-04-23T00:00:00Z",
                    "totals": {"queue": 2},
                    "status": None,
                    "status_counts": {"blocked": 1, "claimed": 1},
                    "artifact_ids": [],
                }
            ],
            "summary": {
                "input_count": 1,
                "by_kind": {"proof_queue": 1},
                "issue_refs": [3690],
                "artifact_ids": [],
                "artifact_links": [],
            },
        }

        markdown = render_markdown(dashboard)

        self.assertIn("# Test Dashboard", markdown)
        self.assertIn("| data/proof_queue.json | proof_queue |", markdown)
        self.assertIn("queue=2", markdown)
        self.assertIn("blocked=1, claimed=1", markdown)
        self.assertIn("#3690", markdown)

    def test_render_markdown_contains_artifact_issue_links(self) -> None:
        dashboard = {
            "title": "Test Dashboard",
            "generated_at": "2026-04-23T00:00:00Z",
            "inputs": [
                {
                    "path": "data/research_program_lock.json",
                    "kind": "research_program_lock",
                    "version": "1",
                    "updated_at": "2026-04-23T00:00:00Z",
                    "totals": {"components": 1},
                    "status": "scaffold",
                    "status_counts": {},
                    "artifact_ids": ["proof-artifact-gamma-crown-C008"],
                }
            ],
            "summary": {
                "input_count": 1,
                "by_kind": {"research_program_lock": 1},
                "issue_refs": [3690],
                "artifact_ids": ["proof-artifact-gamma-crown-C008"],
                "artifact_links": [
                    {
                        "artifact_id": "proof-artifact-gamma-crown-C008",
                        "dashboard_anchor": "artifact:proof-artifact-gamma-crown-C008",
                        "issue": 3690,
                        "source": "data/research_program_lock.json",
                    }
                ],
            },
        }

        markdown = render_markdown(dashboard)

        self.assertIn("Artifact IDs", markdown)
        self.assertIn("proof-artifact-gamma-crown-C008", markdown)
        self.assertIn(
            "#3690 -> `proof-artifact-gamma-crown-C008` @ `artifact:proof-artifact-gamma-crown-C008`",
            markdown,
        )
        self.assertNotIn("Artifact issue links: `#3690", markdown)

    def test_artifact_links_preserve_dashboard_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "lock.json",
                {
                    "manifest_kind": "research_program_lock",
                    "lock_id": "anchor-lock",
                    "components": [],
                    "artifact_schemas": {},
                    "artifact_registry": {
                        "entries": [
                            {
                                "artifact_id": "proof-artifact-anchor",
                                "links": {
                                    "issues": [3690],
                                    "dashboard_anchor": "artifact:proof-artifact-anchor",
                                },
                            }
                        ]
                    },
                },
            )

            dashboard = build_dashboard([path], generated_at="2026-04-23T00:00:00Z")

        self.assertEqual(
            dashboard["summary"]["artifact_links"],
            [
                {
                    "artifact_id": "proof-artifact-anchor",
                    "dashboard_anchor": "artifact:proof-artifact-anchor",
                    "issue": 3690,
                    "source": str(path),
                }
            ],
        )

    def test_artifact_links_collect_plain_issue_refs_from_references(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "lock.json",
                {
                    "manifest_kind": "research_program_lock",
                    "lock_id": "reference-lock",
                    "components": [],
                    "artifact_schemas": {},
                    "example": {
                        "artifact_id": "proof-artifact-reference",
                        "references": [
                            "see #3691",
                            "(#3692)",
                            "issue #3693",
                            "not an issue ref foo#3694",
                        ],
                    },
                },
            )

            dashboard = build_dashboard([path], generated_at="2026-04-23T00:00:00Z")

        self.assertEqual(
            dashboard["summary"]["artifact_links"],
            [
                {
                    "artifact_id": "proof-artifact-reference",
                    "issue": 3691,
                    "source": str(path),
                },
                {
                    "artifact_id": "proof-artifact-reference",
                    "issue": 3692,
                    "source": str(path),
                },
                {
                    "artifact_id": "proof-artifact-reference",
                    "issue": 3693,
                    "source": str(path),
                },
            ],
        )
        self.assertEqual(dashboard["summary"]["issue_refs"], [3691, 3692, 3693])

    def test_self_check_cli(self) -> None:
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            rc = main(["--self-check"])
        self.assertEqual(rc, 0)
        self.assertIn("research_dashboard self-check: ok", stdout.getvalue())

    def test_cli_emits_markdown_for_input(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "mathverse_summary.json",
                {
                    "version": "1.0.0",
                    "release_date": "2026-04-16",
                    "source_systems": 68,
                    "mathverse_shards_lean4": 15,
                },
            )
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                rc = main(
                    [
                        str(path),
                        "--format",
                        "markdown",
                        "--generated-at",
                        "2026-04-23T00:00:00Z",
                    ]
                )

        self.assertEqual(rc, 0)
        self.assertIn("mathverse_summary", stdout.getvalue())
        self.assertIn("source_systems=68", stdout.getvalue())

    def test_cli_default_inputs_and_deterministic_timestamp(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "lock.json",
                {
                    "schema_version": 1,
                    "manifest_kind": "research_program_lock",
                    "lock_id": "deterministic-lock",
                    "generated_at": "2026-04-23T00:00:00Z",
                    "issues": [3690],
                    "components": [{"id": "clean"}],
                    "artifact_schemas": {"proof_artifact_manifest_v1": {}},
                },
            )
            stdout = io.StringIO()
            with patch.object(research_dashboard, "DEFAULT_INPUTS", (path,)):
                with contextlib.redirect_stdout(stdout):
                    rc = research_dashboard.main(
                        ["--default-inputs", "--deterministic"]
                    )

        output = json.loads(stdout.getvalue())
        self.assertEqual(rc, 0)
        self.assertEqual(output["generated_at"], "1970-01-01T00:00:00Z")
        self.assertEqual(output["summary"]["input_count"], 1)

    def test_freshness_validation_flags_stale_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "lock.json",
                {
                    "schema_version": 1,
                    "manifest_kind": "research_program_lock",
                    "lock_id": "stale-lock",
                    "generated_at": "2026-04-01T00:00:00Z",
                    "components": [{"id": "clean"}],
                    "artifact_schemas": {"proof_artifact_manifest_v1": {}},
                },
            )
            dashboard = build_dashboard([path], generated_at="2026-04-24T00:00:00Z")

        findings = validate_dashboard_freshness(
            dashboard,
            max_age_days=7,
            reference_at=parse_timestamp("2026-04-24T00:00:00Z"),
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("stale-lock", dashboard["inputs"][0]["title"])
        self.assertIn("23 day(s) old", findings[0])

    def test_cli_freshness_guard_uses_reference_timestamp(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "lock.json",
                {
                    "schema_version": 1,
                    "manifest_kind": "research_program_lock",
                    "lock_id": "fresh-lock",
                    "generated_at": "2026-04-23T00:00:00Z",
                    "components": [{"id": "clean"}],
                    "artifact_schemas": {"proof_artifact_manifest_v1": {}},
                },
            )
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                rc = main(
                    [
                        str(path),
                        "--deterministic",
                        "--max-input-age-days",
                        "2",
                        "--freshness-reference-at",
                        "2026-04-24T00:00:00Z",
                    ]
                )

        output = json.loads(stdout.getvalue())
        self.assertEqual(rc, 0)
        self.assertEqual(stderr.getvalue(), "")
        self.assertEqual(output["generated_at"], "1970-01-01T00:00:00Z")

    def test_cli_freshness_guard_rejects_stale_input(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = _write_json(
                Path(td) / "lock.json",
                {
                    "schema_version": 1,
                    "manifest_kind": "research_program_lock",
                    "lock_id": "stale-lock",
                    "generated_at": "2026-04-20T00:00:00Z",
                    "components": [{"id": "clean"}],
                    "artifact_schemas": {"proof_artifact_manifest_v1": {}},
                },
            )
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                rc = main(
                    [
                        str(path),
                        "--deterministic",
                        "--max-input-age-days",
                        "1",
                        "--freshness-reference-at",
                        "2026-04-24T00:00:00Z",
                    ]
                )

        self.assertEqual(rc, 1)
        self.assertIn("stale dashboard input", stderr.getvalue())
        self.assertIn("4 day(s) old", stderr.getvalue())

    def test_cli_freshness_guard_rejects_before_writing_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            path = _write_json(
                root / "lock.json",
                {
                    "schema_version": 1,
                    "manifest_kind": "research_program_lock",
                    "lock_id": "stale-lock",
                    "generated_at": "2026-04-20T00:00:00Z",
                    "components": [{"id": "clean"}],
                    "artifact_schemas": {"proof_artifact_manifest_v1": {}},
                },
            )
            selected_output = root / "dashboard.txt"
            json_output = root / "dashboard.json"
            markdown_output = root / "dashboard.md"
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                rc = main(
                    [
                        str(path),
                        "--deterministic",
                        "--max-input-age-days",
                        "1",
                        "--freshness-reference-at",
                        "2026-04-24T00:00:00Z",
                        "--output",
                        str(selected_output),
                        "--json-output",
                        str(json_output),
                        "--markdown-output",
                        str(markdown_output),
                    ]
                )

        self.assertEqual(rc, 1)
        self.assertEqual(stdout.getvalue(), "")
        self.assertIn("stale dashboard input", stderr.getvalue())
        self.assertFalse(selected_output.exists())
        self.assertFalse(json_output.exists())
        self.assertFalse(markdown_output.exists())

    def test_local_dashboard_docs_use_deterministic_output(self) -> None:
        docs = Path("docs/research-replay.md")
        text = docs.read_text(encoding="utf-8")
        self.assertIn("--default-inputs", text)
        self.assertIn("--deterministic", text)
        self.assertIn("--max-input-age-days", text)


if __name__ == "__main__":
    unittest.main()
