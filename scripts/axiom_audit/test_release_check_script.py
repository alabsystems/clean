# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Tests for the release-facing axiom audit evidence check."""

from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "axiom_audit_release_check.sh"
RELEASE_READINESS = REPO_ROOT / "docs" / "RELEASE_READINESS.md"


class AxiomAuditReleaseCheckScriptTests(unittest.TestCase):
    def test_release_check_runs_non_mutating_axiom_audit_gates_in_order(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            call_log = tmp / "calls.txt"
            python_stub = tmp / "python-stub"
            python_stub.write_text(
                '#!/bin/sh\nprintf "%s\\n" "$*" >> "$AXIOM_AUDIT_STUB_LOG"\n',
                encoding="utf-8",
            )
            python_stub.chmod(0o755)

            env = os.environ.copy()
            env["PYTHON"] = str(python_stub)
            env["AXIOM_AUDIT_STUB_LOG"] = str(call_log)
            env["AXIOM_AUDIT_EVIDENCE_PATH"] = str(
                tmp / "axiom-audit-launch-evidence.json"
            )

            proc = subprocess.run(
                [str(SCRIPT)],
                cwd="/",
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("Axiom Audit Release Check: PASS", proc.stdout)
            self.assertEqual(
                call_log.read_text(encoding="utf-8").splitlines(),
                [
                    "-m scripts.axiom_audit.aggregates --check",
                    "-m scripts.axiom_audit.verify",
                ],
            )

    def test_release_readiness_docs_reference_axiom_audit_release_check(self) -> None:
        text = RELEASE_READINESS.read_text(encoding="utf-8")
        self.assertIn("./scripts/axiom_audit_release_check.sh", text)
        self.assertIn("non-mutating axiom-audit lane", text)

    def test_release_check_defaults_to_single_cargo_job(self) -> None:
        source = SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"',
            source,
        )

    def test_release_check_emits_launch_evidence_after_passed_lanes(self) -> None:
        source = SCRIPT.read_text(encoding="utf-8")

        self.assertIn(
            'EVIDENCE_PATH="${AXIOM_AUDIT_EVIDENCE_PATH:-reports/axiom-audit-launch-evidence.json}"',
            source,
        )
        self.assertIn(
            'EVIDENCE_SCHEMA_VERSION="clean-axiom-audit-launch-evidence-v1"',
            source,
        )
        self.assertIn('rm -f "$EVIDENCE_PATH"', source)
        self.assertIn('write_evidence "passed"', source)
        self.assertLess(
            source.index('"$PYTHON_BIN" -m scripts.axiom_audit.verify'),
            source.index('write_evidence "passed"'),
        )

    def test_release_check_has_no_unbounded_cargo_lanes(self) -> None:
        source = SCRIPT.read_text(encoding="utf-8")
        cargo_lines = [
            line.strip()
            for line in source.splitlines()
            if "cargo " in line
            and not line.lstrip().startswith("#")
            and not line.lstrip().startswith("export ")
        ]

        self.assertEqual(cargo_lines, [], "release check is currently Python-only")
        self.assertTrue(
            all('-j "$CARGO_BUILD_JOBS"' in line for line in cargo_lines),
            "future release-check cargo lanes must pass the explicit job bound",
        )
        self.assertTrue(
            all("--message-format=short" in line for line in cargo_lines),
            "future release-check cargo lanes must keep diagnostics compact",
        )


if __name__ == "__main__":
    unittest.main()
