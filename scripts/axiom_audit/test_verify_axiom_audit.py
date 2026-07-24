# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Targeted tests for scripts.axiom_audit.verify (#3640).

These cover the live-row reconciliation gate added to
`verify_axiom_audit.py`:

  * A stale per-conjecture row fails even when there are no constructive
    claims to audit.
  * The default live row-check path uses `verify_gamma_crown` output and
    fails fast on drift.
  * A clean snapshot passes.
  * Custom/offline audit fixtures can opt out via `--skip-live-row-check`.
  * The Rust subprocess path used for constructive-closure audits is
    exercised with a mocked `subprocess.run`.
"""

from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.axiom_audit.verify import _resolve_invocation, _run_rust_audit, main


SYNTHETIC_AUDIT: dict = {
    "last_updated": "2026-04-21",
    "total_domain_axioms": 1,
    "total_theorems": 4,
    "constructive_theorems": 0,
    "total_all_axioms": 1,
    "conjectures": {
        "C001": {
            "axioms": 1,
            "theorems": 4,
            "definitions": 10,
            "opaques": 0,
            "constructive": False,
            "tc_verified": True,
            "proof_mechanism": "masquerade_demoted",
        }
    },
}


def _live_snapshot(*, theorems: int) -> dict:
    return {
        "timestamp": "2026-04-21T00:00:00Z",
        "total_conjectures": 1,
        "total_domain_axioms": 1,
        "total_theorems": theorems,
        "conjectures": [
            {
                "id": "C001",
                "domain_axioms": 1,
                "theorems": theorems,
                "definitions": 10,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            }
        ],
    }


class VerifyAxiomAuditRowGateTests(unittest.TestCase):
    def _write_json(self, tmp: Path, name: str, payload: dict) -> Path:
        path = tmp / name
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        return path

    def test_row_check_snapshot_fails_on_drift_without_constructive_claims(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit = self._write_json(tmp, "axiom_audit.json", SYNTHETIC_AUDIT)
            snapshot = self._write_json(tmp, "live.json", _live_snapshot(theorems=5))
            rc = main([
                "--audit", str(audit),
                "--row-check-snapshot", str(snapshot),
            ])
            self.assertEqual(rc, 1)

    def test_row_check_snapshot_passes_when_rows_match(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit = self._write_json(tmp, "axiom_audit.json", SYNTHETIC_AUDIT)
            snapshot = self._write_json(tmp, "live.json", _live_snapshot(theorems=4))
            rc = main([
                "--audit", str(audit),
                "--row-check-snapshot", str(snapshot),
            ])
            self.assertEqual(rc, 0)

    def test_row_check_snapshot_fails_on_live_backed_boolean_drift(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit = self._write_json(tmp, "axiom_audit.json", SYNTHETIC_AUDIT)
            snapshot = self._write_json(
                tmp,
                "live.json",
                {
                    "timestamp": "2026-04-21T00:00:00Z",
                    "total_conjectures": 1,
                    "total_domain_axioms": 1,
                    "total_theorems": 4,
                    "conjectures": [
                        {
                            "id": "C001",
                            "domain_axioms": 1,
                            "theorems": 4,
                            "definitions": 10,
                            "opaques": 0,
                            "tc_verified": False,
                            "constructive": True,
                        }
                    ],
                },
            )
            rc = main([
                "--audit", str(audit),
                "--row-check-snapshot", str(snapshot),
            ])
            self.assertEqual(rc, 1)

    def test_row_check_snapshot_fails_closed_on_duplicate_live_ids(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit = self._write_json(tmp, "axiom_audit.json", SYNTHETIC_AUDIT)
            snapshot = self._write_json(
                tmp,
                "live.json",
                {
                    "timestamp": "2026-04-21T00:00:00Z",
                    "total_conjectures": 2,
                    "total_domain_axioms": 2,
                    "total_theorems": 8,
                    "conjectures": [
                        {
                            "id": "C001",
                            "domain_axioms": 1,
                            "theorems": 4,
                            "definitions": 10,
                            "opaques": 0,
                            "tc_verified": True,
                            "constructive": False,
                        },
                        {
                            "id": "C001",
                            "domain_axioms": 1,
                            "theorems": 4,
                            "definitions": 10,
                            "opaques": 0,
                            "tc_verified": True,
                            "constructive": False,
                        },
                    ],
                },
            )
            rc = main([
                "--audit", str(audit),
                "--row-check-snapshot", str(snapshot),
            ])
            self.assertEqual(rc, 2)

    def test_row_check_snapshot_fails_closed_on_missing_live_counter_field(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit = self._write_json(tmp, "axiom_audit.json", SYNTHETIC_AUDIT)
            snapshot = self._write_json(
                tmp,
                "live.json",
                {
                    "timestamp": "2026-04-21T00:00:00Z",
                    "total_conjectures": 1,
                    "total_domain_axioms": 1,
                    "total_theorems": 4,
                    "conjectures": [
                        {
                            "id": "C001",
                            "domain_axioms": 1,
                            "theorems": 4,
                            "definitions": 10,
                            "tc_verified": True,
                            "constructive": False,
                        }
                    ],
                },
            )
            rc = main([
                "--audit", str(audit),
                "--row-check-snapshot", str(snapshot),
            ])
            self.assertEqual(rc, 2)

    @mock.patch("scripts.axiom_audit.verify.run_verify_gamma_crown")
    @mock.patch("scripts.axiom_audit.verify._repo_root")
    def test_default_live_row_check_fails_on_drift_without_snapshot(
        self, mock_repo_root: mock.Mock, mock_run_live: mock.Mock
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo_root = Path(td)
            (repo_root / "data").mkdir(parents=True)
            self._write_json(repo_root / "data", "axiom_audit.json", SYNTHETIC_AUDIT)

            mock_repo_root.return_value = repo_root
            mock_run_live.return_value = _live_snapshot(theorems=5)

            rc = main([])

            self.assertEqual(rc, 1)
            mock_run_live.assert_called_once_with(repo_root=repo_root, verbose=False)

    def test_skip_live_row_check_preserves_offline_fixture_mode(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit = self._write_json(tmp, "axiom_audit.json", SYNTHETIC_AUDIT)
            rc = main([
                "--audit", str(audit),
                "--skip-live-row-check",
            ])
            self.assertEqual(rc, 0)

    @mock.patch("scripts.axiom_audit.verify._run_rust_audit")
    def test_skip_live_row_check_does_not_treat_row_constructive_as_claim(
        self, mock_run_rust_audit: mock.Mock
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit_payload = json.loads(json.dumps(SYNTHETIC_AUDIT))
            audit_payload["conjectures"]["C001"]["constructive"] = True
            audit = self._write_json(tmp, "axiom_audit.json", audit_payload)

            rc = main([
                "--audit", str(audit),
                "--skip-live-row-check",
            ])

            self.assertEqual(rc, 0)
            mock_run_rust_audit.assert_not_called()

    @mock.patch("scripts.axiom_audit.verify._run_rust_audit")
    def test_skip_live_row_check_uses_proof_mechanism_for_claim_selection(
        self, mock_run_rust_audit: mock.Mock
    ) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit_payload = json.loads(json.dumps(SYNTHETIC_AUDIT))
            audit_payload["conjectures"]["C001"]["proof_mechanism"] = "constructive"
            audit_payload["conjectures"]["C001"]["constructive"] = False
            audit = self._write_json(tmp, "axiom_audit.json", audit_payload)
            mock_run_rust_audit.return_value = {
                "theorems": [
                    {"name": "T001", "is_constructive": True, "closure": []}
                ]
            }

            rc = main([
                "--audit", str(audit),
                "--skip-live-row-check",
            ])

            self.assertEqual(rc, 0)
            mock_run_rust_audit.assert_called_once()
            self.assertEqual(mock_run_rust_audit.call_args.args[0], "C001")
            self.assertEqual(
                mock_run_rust_audit.call_args.kwargs["verbose"],
                False,
            )


class RustAuditSubprocessTests(unittest.TestCase):
    def test_resolve_invocation_uses_unified_cargo_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo_root = Path(td)
            with mock.patch.dict("os.environ", {}, clear=True):
                with mock.patch("scripts.axiom_audit.verify.shutil.which", return_value=None):
                    cmd = _resolve_invocation(repo_root)

        self.assertEqual(
            cmd,
            [
                "cargo",
                "run",
                "--locked",
                "--quiet",
                "--message-format=short",
                "-j",
                "1",
                "-p",
                "clean",
                "--features",
                "math-overlays",
                "--bin",
                "clean",
                "--",
                "kernel",
                "verify-constructive-claims",
            ],
        )

    def test_resolve_invocation_honors_cargo_build_jobs_for_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo_root = Path(td)
            with mock.patch.dict("os.environ", {"CARGO_BUILD_JOBS": "2"}, clear=True):
                with mock.patch("scripts.axiom_audit.verify.shutil.which", return_value=None):
                    cmd = _resolve_invocation(repo_root)

        self.assertEqual(cmd[cmd.index("-j") + 1], "2")

    def test_resolve_invocation_prefers_repo_clean_over_path_legacy_binary(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo_root = Path(td)
            target_dir = repo_root / "target" / "debug"
            target_dir.mkdir(parents=True)
            clean = target_dir / "clean"
            clean.write_text("#!/usr/bin/env bash\n", encoding="utf-8")
            clean.chmod(0o755)

            def fake_which(name: str) -> str | None:
                if name == "verify_constructive_claims":
                    return "/tmp/path/verify_constructive_claims"
                return None

            with mock.patch.dict("os.environ", {}, clear=True):
                with mock.patch("scripts.axiom_audit.verify.shutil.which", side_effect=fake_which):
                    cmd = _resolve_invocation(repo_root)

        self.assertEqual(cmd, [str(clean), "kernel", "verify-constructive-claims"])

    def test_resolve_invocation_accepts_legacy_binary_from_clean_bin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            legacy = Path(td) / "verify_constructive_claims"
            legacy.write_text("#!/usr/bin/env bash\n", encoding="utf-8")
            legacy.chmod(0o755)

            with mock.patch.dict("os.environ", {"clean_BIN": str(legacy)}, clear=True):
                cmd = _resolve_invocation(Path(td))

        self.assertEqual(cmd, [str(legacy)])

    @mock.patch("scripts.axiom_audit.verify._resolve_invocation")
    @mock.patch("scripts.axiom_audit.verify.subprocess.run")
    def test_run_rust_audit_parses_json_from_subprocess(
        self,
        mock_run: mock.Mock,
        mock_resolve: mock.Mock,
    ) -> None:
        mock_resolve.return_value = ["clean", "kernel", "verify-constructive-claims"]
        payload = {
            "theorems": [
                {"name": "T001", "is_constructive": True, "closure": ["A1"]},
                {"name": "T002", "is_constructive": False, "closure": ["A2"]},
            ]
        }
        mock_run.return_value = subprocess.CompletedProcess(
            args=["clean", "kernel", "verify-constructive-claims", "--conjecture", "C001"],
            returncode=0,
            stdout=json.dumps(payload),
            stderr="",
        )

        report = _run_rust_audit("C001", repo_root=Path("/repo"), verbose=True)

        self.assertEqual(report, payload)
        mock_resolve.assert_called_once_with(Path("/repo"))
        mock_run.assert_called_once()


if __name__ == "__main__":
    unittest.main()
