# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Tests for scripts.axiom_audit.reconcile (#3640).

Covers the behavioral requirements:

  * `check_drift` identifies per-row counter mismatches and categorizes
    them into drift / missing_from_live / missing_from_audit.
  * `reconcile_rows` is idempotent, overwrites the live-backed row
    fields (counts plus `tc_verified` / `constructive`), preserves
    audit-semantic fields (`proof_mechanism`, notes), and refreshes
    top-level aggregates.
  * Live snapshots with malformed rows raise ValueError.
  * CLI `--check` returns exit 1 on drift and exit 0 on clean state.
  * CLI `--write` reconciles and is idempotent on a second run.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from types import SimpleNamespace
from unittest import mock
from pathlib import Path

from scripts.axiom_audit.reconcile import (
    check_drift,
    main,
    reconcile_rows,
    run_verify_gamma_crown,
)
from scripts.axiom_audit.aggregates import load_audit


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

SYNTHETIC_AUDIT: dict = {
    "last_updated": "2026-04-20",
    "total_domain_axioms": 5,
    "total_theorems": 15,
    "constructive_theorems": 0,
    "total_all_axioms": 5,
    "conjectures": {
        "C001": {
            "axioms": 2,
            "theorems": 10,
            "definitions": 100,
            "opaques": 1,
            "constructive": False,
            "tc_verified": True,
            "proof_mechanism": "masquerade_demoted",
            "notes": "preserve me",
        },
        "C002": {
            "axioms": 3,
            "theorems": 5,
            "definitions": 50,
            "opaques": 0,
            "constructive": False,
            "tc_verified": True,
            "proof_mechanism": "sorry_inhabited",
        },
    },
}


def _live_snapshot(rows: list[dict]) -> dict:
    """Shape a minimal live snapshot from per-conjecture counter tuples."""
    return {
        "timestamp": "2026-04-20T00:00:00Z",
        "total_conjectures": len(rows),
        "total_domain_axioms": sum(r.get("domain_axioms", 0) for r in rows),
        "total_theorems": sum(r.get("theorems", 0) for r in rows),
        "conjectures": rows,
    }


# ---------------------------------------------------------------------------
# Unit tests: check_drift
# ---------------------------------------------------------------------------


class CheckDriftTests(unittest.TestCase):
    def test_clean_when_counters_match(self) -> None:
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": True,
                "constructive": False,
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        result = check_drift(SYNTHETIC_AUDIT, live)
        self.assertTrue(result.is_clean)
        self.assertEqual(result.drift_rows, ())

    def test_detects_counter_drift(self) -> None:
        # C001 axiom count drifts 2 -> 3; C002 is clean
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 3,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": True,
                "constructive": False,
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        result = check_drift(SYNTHETIC_AUDIT, live)
        self.assertFalse(result.is_clean)
        self.assertEqual(len(result.drift_rows), 1)
        row = result.drift_rows[0]
        self.assertEqual(row.conjecture, "C001")
        self.assertEqual(row.deltas, (("axioms", 2, 3),))

    def test_detects_live_backed_boolean_drift(self) -> None:
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": False,
                "constructive": True,
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        result = check_drift(SYNTHETIC_AUDIT, live)
        self.assertFalse(result.is_clean)
        self.assertEqual(len(result.drift_rows), 1)
        row = result.drift_rows[0]
        self.assertEqual(row.conjecture, "C001")
        self.assertEqual(
            row.deltas,
            (
                ("tc_verified", True, False),
                ("constructive", False, True),
            ),
        )

    def test_detects_missing_from_live(self) -> None:
        # C002 absent from live
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        result = check_drift(SYNTHETIC_AUDIT, live)
        self.assertEqual(result.missing_from_live, ("C002",))
        self.assertEqual(result.drift_rows, ())

    def test_detects_missing_from_audit(self) -> None:
        # New C099 in live but not in audit
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": True,
                "constructive": False,
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
            {
                "id": "C099",
                "domain_axioms": 0,
                "theorems": 1,
                "definitions": 1,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        result = check_drift(SYNTHETIC_AUDIT, live)
        self.assertEqual(result.missing_from_audit, ("C099",))

    def test_raises_on_malformed_live_row(self) -> None:
        live = {"conjectures": [{"not_id": "oops"}]}
        with self.assertRaises(ValueError):
            check_drift(SYNTHETIC_AUDIT, live)

    def test_raises_on_duplicate_live_conjecture_ids(self) -> None:
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": True,
                "constructive": False,
            },
            {
                "id": "C001",
                "domain_axioms": 3,
                "theorems": 11,
                "definitions": 101,
                "opaques": 2,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        with self.assertRaisesRegex(ValueError, "duplicate conjecture id"):
            check_drift(SYNTHETIC_AUDIT, live)

    def test_raises_on_missing_required_live_counter_field(self) -> None:
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "tc_verified": True,
                "constructive": False,
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        with self.assertRaisesRegex(ValueError, "missing required field"):
            check_drift(SYNTHETIC_AUDIT, live)

    def test_raises_on_missing_live_boolean_field(self) -> None:
        base_rows = [
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": True,
                "constructive": False,
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ]
        for missing_field in ("tc_verified", "constructive"):
            with self.subTest(missing_field=missing_field):
                rows = json.loads(json.dumps(base_rows))
                rows[0].pop(missing_field)
                with self.assertRaisesRegex(ValueError, "missing required field"):
                    check_drift(SYNTHETIC_AUDIT, _live_snapshot(rows))

    def test_raises_on_wrong_live_boolean_type(self) -> None:
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": 1,
                "constructive": False,
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        with self.assertRaisesRegex(ValueError, "expected bool"):
            check_drift(SYNTHETIC_AUDIT, live)

    def test_raises_on_wrong_live_constructive_boolean_type(self) -> None:
        live = _live_snapshot([
            {
                "id": "C001",
                "domain_axioms": 2,
                "theorems": 10,
                "definitions": 100,
                "opaques": 1,
                "tc_verified": True,
                "constructive": "yes",
            },
            {
                "id": "C002",
                "domain_axioms": 3,
                "theorems": 5,
                "definitions": 50,
                "opaques": 0,
                "tc_verified": True,
                "constructive": False,
            },
        ])
        with self.assertRaisesRegex(ValueError, "expected bool"):
            check_drift(SYNTHETIC_AUDIT, live)


# ---------------------------------------------------------------------------
# Unit tests: reconcile_rows (write path)
# ---------------------------------------------------------------------------


class ReconcileRowsTests(unittest.TestCase):
    def _write_fixture(self, tmp: Path) -> Path:
        path = tmp / "axiom_audit.json"
        path.write_text(
            json.dumps(SYNTHETIC_AUDIT, indent=2) + "\n", encoding="utf-8"
        )
        return path

    def test_write_updates_counters_and_aggregates(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            path = self._write_fixture(tmp)
            live = _live_snapshot([
                {
                    "id": "C001",
                    "domain_axioms": 4,
                    "theorems": 12,
                    "definitions": 110,
                    "opaques": 2,
                    "tc_verified": False,
                    "constructive": True,
                },
                {
                    "id": "C002",
                    "domain_axioms": 1,
                    "theorems": 7,
                    "definitions": 55,
                    "opaques": 3,
                    "tc_verified": True,
                    "constructive": False,
                },
            ])
            before, changed = reconcile_rows(path, live)
            self.assertTrue(changed)
            self.assertEqual(len(before.drift_rows), 2)

            audit = load_audit(path)
            self.assertEqual(audit["conjectures"]["C001"]["axioms"], 4)
            self.assertEqual(audit["conjectures"]["C001"]["theorems"], 12)
            self.assertEqual(audit["conjectures"]["C001"]["definitions"], 110)
            self.assertEqual(audit["conjectures"]["C001"]["opaques"], 2)
            self.assertEqual(audit["conjectures"]["C001"]["tc_verified"], False)
            self.assertEqual(audit["conjectures"]["C001"]["constructive"], True)
            # audit-semantic fields preserved
            self.assertEqual(audit["conjectures"]["C001"]["proof_mechanism"], "masquerade_demoted")
            self.assertEqual(audit["conjectures"]["C001"]["notes"], "preserve me")
            # top-level aggregates refreshed
            self.assertEqual(audit["total_domain_axioms"], 5)  # 4 + 1
            self.assertEqual(audit["total_theorems"], 19)  # 12 + 7

    def test_write_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            path = self._write_fixture(tmp)
            live = _live_snapshot([
                {
                    "id": "C001",
                    "domain_axioms": 2,
                    "theorems": 10,
                    "definitions": 100,
                    "opaques": 1,
                    "tc_verified": True,
                    "constructive": False,
                },
                {
                    "id": "C002",
                    "domain_axioms": 3,
                    "theorems": 5,
                    "definitions": 50,
                    "opaques": 0,
                    "tc_verified": True,
                    "constructive": False,
                },
            ])
            # First run: clean (file already matches), changed=False since
            # aggregates also already reconcile.
            _before, changed_a = reconcile_rows(path, live)
            # Second run: definitely no change.
            _before2, changed_b = reconcile_rows(path, live)
            self.assertFalse(changed_a)
            self.assertFalse(changed_b)

    def test_write_preserves_proof_mechanism_when_live_constructive_changes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            path = tmp / "axiom_audit.json"
            audit = json.loads(json.dumps(SYNTHETIC_AUDIT))
            audit["conjectures"]["C001"]["constructive"] = True
            audit["conjectures"]["C001"]["proof_mechanism"] = "constructive"
            path.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")

            live = _live_snapshot([
                {
                    "id": "C001",
                    "domain_axioms": 2,
                    "theorems": 10,
                    "definitions": 100,
                    "opaques": 1,
                    "tc_verified": True,
                    "constructive": False,
                },
                {
                    "id": "C002",
                    "domain_axioms": 3,
                    "theorems": 5,
                    "definitions": 50,
                    "opaques": 0,
                    "tc_verified": True,
                    "constructive": False,
                },
            ])

            before, changed = reconcile_rows(path, live)

            self.assertTrue(changed)
            self.assertEqual(
                before.drift_rows[0].deltas,
                (("constructive", True, False),),
            )
            refreshed = load_audit(path)
            self.assertFalse(refreshed["conjectures"]["C001"]["constructive"])
            self.assertEqual(
                refreshed["conjectures"]["C001"]["proof_mechanism"],
                "constructive",
            )


# ---------------------------------------------------------------------------
# CLI integration tests
# ---------------------------------------------------------------------------


class CliTests(unittest.TestCase):
    def _write_audit(self, tmp: Path, audit: dict) -> Path:
        path = tmp / "axiom_audit.json"
        path.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
        return path

    def _write_snapshot(self, tmp: Path, live: dict) -> Path:
        path = tmp / "live.json"
        path.write_text(json.dumps(live), encoding="utf-8")
        return path

    def test_cli_check_exit_1_on_drift(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit_path = self._write_audit(tmp, SYNTHETIC_AUDIT)
            snapshot = self._write_snapshot(tmp, _live_snapshot([
                {
                    "id": "C001",
                    "domain_axioms": 99,
                    "theorems": 10,
                    "definitions": 100,
                    "opaques": 1,
                    "tc_verified": True,
                    "constructive": False,
                },
                {
                    "id": "C002",
                    "domain_axioms": 3,
                    "theorems": 5,
                    "definitions": 50,
                    "opaques": 0,
                    "tc_verified": True,
                    "constructive": False,
                },
            ]))
            rc = main([
                "--audit", str(audit_path),
                "--snapshot", str(snapshot),
                "--check",
            ])
            self.assertEqual(rc, 1)

    def test_cli_check_exit_0_on_clean(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit_path = self._write_audit(tmp, SYNTHETIC_AUDIT)
            snapshot = self._write_snapshot(tmp, _live_snapshot([
                {
                    "id": "C001",
                    "domain_axioms": 2,
                    "theorems": 10,
                    "definitions": 100,
                    "opaques": 1,
                    "tc_verified": True,
                    "constructive": False,
                },
                {
                    "id": "C002",
                    "domain_axioms": 3,
                    "theorems": 5,
                    "definitions": 50,
                    "opaques": 0,
                    "tc_verified": True,
                    "constructive": False,
                },
            ]))
            rc = main([
                "--audit", str(audit_path),
                "--snapshot", str(snapshot),
                "--check",
            ])
            self.assertEqual(rc, 0)

    def test_cli_check_exit_1_on_live_backed_boolean_drift(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit_path = self._write_audit(tmp, SYNTHETIC_AUDIT)
            snapshot = self._write_snapshot(tmp, _live_snapshot([
                {
                    "id": "C001",
                    "domain_axioms": 2,
                    "theorems": 10,
                    "definitions": 100,
                    "opaques": 1,
                    "tc_verified": False,
                    "constructive": True,
                },
                {
                    "id": "C002",
                    "domain_axioms": 3,
                    "theorems": 5,
                    "definitions": 50,
                    "opaques": 0,
                    "tc_verified": True,
                    "constructive": False,
                },
            ]))
            rc = main([
                "--audit", str(audit_path),
                "--snapshot", str(snapshot),
                "--check",
            ])
            self.assertEqual(rc, 1)

    def test_cli_write_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            audit_path = self._write_audit(tmp, SYNTHETIC_AUDIT)
            snapshot = self._write_snapshot(tmp, _live_snapshot([
                {
                    "id": "C001",
                    "domain_axioms": 4,
                    "theorems": 12,
                    "definitions": 110,
                    "opaques": 2,
                    "tc_verified": False,
                    "constructive": True,
                },
                {
                    "id": "C002",
                    "domain_axioms": 1,
                    "theorems": 7,
                    "definitions": 55,
                    "opaques": 3,
                    "tc_verified": True,
                    "constructive": False,
                },
            ]))
            rc_a = main([
                "--audit", str(audit_path),
                "--snapshot", str(snapshot),
            ])
            rc_b = main([
                "--audit", str(audit_path),
                "--snapshot", str(snapshot),
            ])
            self.assertEqual(rc_a, 0)
            self.assertEqual(rc_b, 0)
            # After two runs, the file should equal itself (idempotent).
            data = json.loads(audit_path.read_text(encoding="utf-8"))
            self.assertEqual(data["conjectures"]["C001"]["axioms"], 4)
            self.assertEqual(data["conjectures"]["C001"]["tc_verified"], False)
            self.assertEqual(data["conjectures"]["C001"]["constructive"], True)
            self.assertEqual(data["total_domain_axioms"], 5)


class RepoAuditAnchorTest(unittest.TestCase):
    """Guard that the checked-in audit file stays self-consistent."""

    def test_checked_in_audit_is_self_consistent(self) -> None:
        repo_root = Path(__file__).resolve().parents[2]
        audit_path = repo_root / "data" / "axiom_audit.json"
        if not audit_path.exists():  # pragma: no cover
            self.skipTest("data/axiom_audit.json missing")
        audit = load_audit(audit_path)
        rows = []
        for cid, entry in audit["conjectures"].items():
            if not isinstance(entry, dict):
                continue
            rows.append({
                "id": cid,
                "domain_axioms": entry.get("axioms", 0),
                "theorems": entry.get("theorems", 0),
                "definitions": entry.get("definitions", 0),
                "opaques": entry.get("opaques", 0),
                "tc_verified": entry.get("tc_verified", False),
                "constructive": entry.get("constructive", False),
            })
        live = _live_snapshot(rows)
        result = check_drift(audit, live)
        self.assertTrue(
            result.is_clean,
            f"axiom_audit.json is not self-consistent: "
            f"{len(result.drift_rows)} drift rows, "
            f"{len(result.missing_from_live)} missing_from_live, "
            f"{len(result.missing_from_audit)} missing_from_audit",
        )


class LiveCargoInvocationTests(unittest.TestCase):
    def test_run_verify_gamma_crown_uses_bounded_short_cargo_run(self) -> None:
        live = _live_snapshot([])
        with mock.patch.dict("os.environ", {}, clear=True):
            with mock.patch(
                "scripts.axiom_audit.reconcile.subprocess.run",
                return_value=SimpleNamespace(
                    returncode=0,
                    stdout=json.dumps(live),
                    stderr="",
                ),
            ) as mock_run:
                result = run_verify_gamma_crown(repo_root=Path("/repo"))

        self.assertEqual(result, live)
        self.assertEqual(
            mock_run.call_args.args[0],
            [
                "cargo",
                "run",
                "--locked",
                "--quiet",
                "--message-format=short",
                "-j",
                "1",
                "-p",
                "clean-kernel",
                "--bin",
                "verify_gamma_crown",
                "--features",
                "test-utils math-overlays",
                "--",
                "--json",
            ],
        )
        self.assertEqual(mock_run.call_args.kwargs["cwd"], "/repo")
        self.assertTrue(mock_run.call_args.kwargs["capture_output"])
        self.assertTrue(mock_run.call_args.kwargs["text"])
        self.assertFalse(mock_run.call_args.kwargs["check"])

    def test_run_verify_gamma_crown_honors_cargo_build_jobs(self) -> None:
        live = _live_snapshot([])
        with mock.patch.dict("os.environ", {"CARGO_BUILD_JOBS": "2"}, clear=True):
            with mock.patch(
                "scripts.axiom_audit.reconcile.subprocess.run",
                return_value=SimpleNamespace(
                    returncode=0,
                    stdout=json.dumps(live),
                    stderr="",
                ),
            ) as mock_run:
                run_verify_gamma_crown(repo_root=Path("/repo"))

        cmd = mock_run.call_args.args[0]
        self.assertEqual(cmd[cmd.index("-j") + 1], "2")


if __name__ == "__main__":
    unittest.main()
