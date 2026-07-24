#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Non-mutating release check for the checked-in axiom audit evidence.
#
# This lane intentionally does not run `scripts.axiom_audit.reconcile` or
# regenerate any report. It fails when `data/axiom_audit.json` has stale
# aggregates, per-conjecture row drift against live kernel output, or an
# unsupported `proof_mechanism: constructive` claim.
#
# Usage: ./scripts/axiom_audit_release_check.sh
#
# On completion the gate writes reports/axiom-audit-launch-evidence.json. The
# evidence file is cleared at startup so a failed or interrupted run cannot
# leave an old passing artifact behind.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"

cd "$REPO_ROOT"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

EVIDENCE_SCHEMA_VERSION="Clean-axiom-audit-launch-evidence-v1"
EVIDENCE_PATH="${AXIOM_AUDIT_EVIDENCE_PATH:-reports/axiom-audit-launch-evidence.json}"
EXPECTED_STEPS=2

mkdir -p "$(dirname "$EVIDENCE_PATH")"
rm -f "$EVIDENCE_PATH"

write_evidence() {
    local gate_status="$1"

    AXIOM_AUDIT_EVIDENCE_SCHEMA_VERSION="$EVIDENCE_SCHEMA_VERSION" \
        AXIOM_AUDIT_EVIDENCE_PATH="$EVIDENCE_PATH" \
        AXIOM_AUDIT_GATE_STATUS="$gate_status" \
        AXIOM_AUDIT_EXPECTED_STEPS="$EXPECTED_STEPS" \
        python3 <<'PY'
import hashlib
import json
import os
from datetime import UTC, datetime
from pathlib import Path

SCHEMA_VERSION = os.environ["AXIOM_AUDIT_EVIDENCE_SCHEMA_VERSION"]
EVIDENCE_PATH = Path(os.environ["AXIOM_AUDIT_EVIDENCE_PATH"])
AUDIT_PATH = Path("data/axiom_audit.json")
SOURCE_PATHS = [
    Path("scripts/axiom_audit_release_check.sh"),
    Path("scripts/axiom_audit/aggregates.py"),
    Path("scripts/axiom_audit/verify.py"),
    AUDIT_PATH,
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


audit = json.loads(AUDIT_PATH.read_text(encoding="utf-8"))
conjectures = audit.get("conjectures", {})
nonzero_axiom_rows = sum(
    1
    for entry in conjectures.values()
    if isinstance(entry, dict) and int(entry.get("axioms", 0)) > 0
)
expected_steps = int(os.environ["AXIOM_AUDIT_EXPECTED_STEPS"])
artifact = {
    "schema_version": SCHEMA_VERSION,
    "generated_by": "./scripts/axiom_audit_release_check.sh",
    "generated_at": datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
    "gate_command": "./scripts/axiom_audit_release_check.sh",
    "status": os.environ["AXIOM_AUDIT_GATE_STATUS"],
    "summary": {
        "expected_steps": expected_steps,
        "steps": expected_steps,
        "passed": expected_steps,
        "failed": 0,
    },
    "axiom_audit": {
        "path": str(AUDIT_PATH),
        "total_domain_axioms": audit["total_domain_axioms"],
        "total_all_axioms": audit["total_all_axioms"],
        "total_theorems": audit["total_theorems"],
        "constructive_theorems": audit["constructive_theorems"],
        "conjecture_rows": len(conjectures),
        "nonzero_axiom_rows": nonzero_axiom_rows,
        "sha256": sha256_file(AUDIT_PATH),
    },
    "source_sha256": {str(path): sha256_file(path) for path in SOURCE_PATHS},
    "lanes": [
        {
            "id": "aggregate_consistency",
            "description": "Aggregate consistency (data/axiom_audit.json)",
            "status": "passed",
        },
        {
            "id": "live_row_reconciliation_and_constructive_claims",
            "description": "Live row reconciliation and constructive-claim closure",
            "status": "passed",
        },
    ],
}
EVIDENCE_PATH.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(f"Evidence: {EVIDENCE_PATH}")
PY
}

echo "=== Axiom Audit Release Check ==="
echo ""

echo "--- Lane 1: Aggregate consistency (data/axiom_audit.json) ---"
"$PYTHON_BIN" -m scripts.axiom_audit.aggregates --check
echo ""

echo "--- Lane 2: Live row reconciliation and constructive-claim closure ---"
"$PYTHON_BIN" -m scripts.axiom_audit.verify
echo ""

write_evidence "passed"

echo "=== Axiom Audit Release Check: PASS ==="
