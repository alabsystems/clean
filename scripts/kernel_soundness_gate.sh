#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Kernel soundness gate — runs all soundness lanes in sequence.
# Fails closed on the first mismatch.
#
# Usage: ./scripts/kernel_soundness_gate.sh
#
# On completion the gate writes reports/kernel-soundness-launch-evidence.json.
# The evidence file is cleared at startup so a failed or interrupted run cannot
# leave an old passing artifact behind.
#
# Issue: #2134
# Design: designs/2026-03-11-2134-structured-kernel-soundness-gate.md

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

EVIDENCE_SCHEMA_VERSION="Clean-kernel-soundness-launch-evidence-v1"
EVIDENCE_PATH="${KERNEL_SOUNDNESS_EVIDENCE_PATH:-reports/kernel-soundness-launch-evidence.json}"
EXPECTED_STEPS=3

PASS=0
FAIL=0
STEPS=0
LANES_FILE="$(mktemp "${TMPDIR:-/tmp}/Clean-kernel-soundness-gate-lanes.XXXXXX")"

cleanup() {
    rm -f "$LANES_FILE"
}

trap cleanup EXIT

mkdir -p "$(dirname "$EVIDENCE_PATH")"
rm -f "$EVIDENCE_PATH"

record_lane() {
    local id="$1"
    local description="$2"
    local expected_tests="$3"
    local expected_output="$4"
    local matched_expected_count="$5"
    local matched_expected_output="$6"
    local status="$7"

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$id" "$description" "$expected_tests" "$expected_output" \
        "$matched_expected_count" "$matched_expected_output" "$status" \
        >>"$LANES_FILE"
}

write_evidence() {
    local gate_status="$1"

    KERNEL_SOUNDNESS_EVIDENCE_SCHEMA_VERSION="$EVIDENCE_SCHEMA_VERSION" \
        KERNEL_SOUNDNESS_EVIDENCE_PATH="$EVIDENCE_PATH" \
        KERNEL_SOUNDNESS_GATE_STATUS="$gate_status" \
        KERNEL_SOUNDNESS_EXPECTED_STEPS="$EXPECTED_STEPS" \
        KERNEL_SOUNDNESS_STEPS="$STEPS" \
        KERNEL_SOUNDNESS_PASS="$PASS" \
        KERNEL_SOUNDNESS_FAIL="$FAIL" \
        KERNEL_SOUNDNESS_LANES_FILE="$LANES_FILE" \
        python3 <<'PY'
import hashlib
import json
import os
from datetime import UTC, datetime
from pathlib import Path

SCHEMA_VERSION = os.environ["KERNEL_SOUNDNESS_EVIDENCE_SCHEMA_VERSION"]
EVIDENCE_PATH = Path(os.environ["KERNEL_SOUNDNESS_EVIDENCE_PATH"])
LANES_FILE = Path(os.environ["KERNEL_SOUNDNESS_LANES_FILE"])
EXPRESSIONS_PATH = Path("tests/differential/expressions.txt")
BASELINE_PATH = Path("tests/differential/lean4_baseline.json")
SOURCE_PATHS = [
    Path("scripts/kernel_soundness_gate.sh"),
    BASELINE_PATH,
    EXPRESSIONS_PATH,
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def active_expressions(path: Path) -> list[str]:
    return [
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.strip().startswith("#")
    ]


def sha256_expressions(expressions: list[str]) -> str:
    digest = hashlib.sha256()
    for expression in expressions:
        digest.update(expression.encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


lanes = []
if LANES_FILE.exists():
    for line in LANES_FILE.read_text(encoding="utf-8").splitlines():
        (
            lane_id,
            description,
            expected_tests,
            expected_output,
            matched_expected_count,
            matched_expected_output,
            status,
        ) = line.split("\t")
        lanes.append(
            {
                "id": lane_id,
                "description": description,
                "expected_tests": int(expected_tests) if expected_tests else None,
                "expected_output": expected_output or None,
                "matched_expected_count": matched_expected_count == "true",
                "matched_expected_output": matched_expected_output == "true",
                "status": status,
            }
        )

expressions = active_expressions(EXPRESSIONS_PATH)
baseline = json.loads(BASELINE_PATH.read_text(encoding="utf-8"))
artifact = {
    "schema_version": SCHEMA_VERSION,
    "generated_by": "./scripts/kernel_soundness_gate.sh",
    "generated_at": datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
    "gate_command": "./scripts/kernel_soundness_gate.sh",
    "status": os.environ["KERNEL_SOUNDNESS_GATE_STATUS"],
    "summary": {
        "expected_steps": int(os.environ["KERNEL_SOUNDNESS_EXPECTED_STEPS"]),
        "steps": int(os.environ["KERNEL_SOUNDNESS_STEPS"]),
        "passed": int(os.environ["KERNEL_SOUNDNESS_PASS"]),
        "failed": int(os.environ["KERNEL_SOUNDNESS_FAIL"]),
    },
    "kernel_differential": {
        "baseline_path": str(BASELINE_PATH),
        "expressions_path": str(EXPRESSIONS_PATH),
        "baseline_schema_version": baseline["schema_version"],
        "normalization_version": baseline["normalization_version"],
        "baseline_cases": len(baseline["cases"]),
        "expression_count": len(expressions),
        "expressions_sha256": sha256_expressions(expressions),
        "baseline_sha256": sha256_file(BASELINE_PATH),
        "expressions_file_sha256": sha256_file(EXPRESSIONS_PATH),
    },
    "source_sha256": {str(path): sha256_file(path) for path in SOURCE_PATHS},
    "lanes": lanes,
}
EVIDENCE_PATH.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(f"Evidence: {EVIDENCE_PATH}")
PY
}

validate_differential_artifacts() {
    python3 <<'PY'
import hashlib
import json
import sys
from pathlib import Path

BASELINE_SCHEMA_VERSION = 1
NORMALIZATION_VERSION = 2
EXPRESSIONS_PATH = Path("tests/differential/expressions.txt")
BASELINE_PATH = Path("tests/differential/lean4_baseline.json")


def fail(message: str) -> None:
    print(f"kernel differential artifacts: FAIL: {message}", file=sys.stderr)
    sys.exit(1)


if not EXPRESSIONS_PATH.is_file():
    fail(f"missing {EXPRESSIONS_PATH}")
if not BASELINE_PATH.is_file():
    fail(f"missing {BASELINE_PATH}")

try:
    lines = EXPRESSIONS_PATH.read_text(encoding="utf-8").splitlines()
except OSError as exc:
    fail(f"failed to read {EXPRESSIONS_PATH}: {exc}")

expressions = [
    line.strip()
    for line in lines
    if line.strip() and not line.strip().startswith("#")
]
if not expressions:
    fail(f"{EXPRESSIONS_PATH} contains no expressions")

hasher = hashlib.sha256()
for expression in expressions:
    hasher.update(expression.encode("utf-8"))
    hasher.update(b"\n")
expressions_sha256 = hasher.hexdigest()

try:
    baseline = json.loads(BASELINE_PATH.read_text(encoding="utf-8"))
except OSError as exc:
    fail(f"failed to read {BASELINE_PATH}: {exc}")
except json.JSONDecodeError as exc:
    fail(f"failed to parse {BASELINE_PATH}: {exc}")

schema_version = baseline.get("schema_version")
if schema_version != BASELINE_SCHEMA_VERSION:
    fail(f"schema_version {schema_version!r} != {BASELINE_SCHEMA_VERSION}")

normalization_version = baseline.get("normalization_version")
if normalization_version != NORMALIZATION_VERSION:
    fail(
        f"normalization_version {normalization_version!r} != "
        f"{NORMALIZATION_VERSION}"
    )

baseline_sha256 = baseline.get("expressions_sha256")
if baseline_sha256 != expressions_sha256:
    fail(
        "expressions_sha256 mismatch "
        f"(baseline {baseline_sha256!r}, current {expressions_sha256})"
    )

cases = baseline.get("cases")
if not isinstance(cases, list):
    fail("cases is not a list")
if len(cases) != len(expressions):
    fail(f"case count {len(cases)} != expression count {len(expressions)}")

for idx, (case, expression) in enumerate(zip(cases, expressions)):
    if not isinstance(case, dict):
        fail(f"case {idx} is not an object")
    if case.get("expr") != expression:
        fail(f"case {idx} expr does not match expressions.txt")
    if not isinstance(case.get("type_norm"), str) or not case["type_norm"]:
        fail(f"case {idx} type_norm is missing or empty")

print(
    "kernel differential artifacts: PASS "
    f"({len(expressions)} expressions, sha256={expressions_sha256})"
)
PY
}

run_expected_cargo_test() {
    local expected_tests="$1"
    shift

    local output_file
    output_file="$(mktemp "${TMPDIR:-/tmp}/Clean-kernel-soundness-gate.XXXXXX")"

    if ! "$@" >"$output_file" 2>&1; then
        cat "$output_file"
        rm -f "$output_file"
        return 1
    fi

    if grep -Eq "running ${expected_tests} tests?$" "$output_file" &&
        grep -Eq "test result: ok\\. ${expected_tests} passed; 0 failed" "$output_file"; then
        cat "$output_file"
        rm -f "$output_file"
        return 0
    fi

    cat "$output_file"
    rm -f "$output_file"
    return 1
}

run_expected_output() {
    local expected_text="$1"
    shift

    local output_file
    output_file="$(mktemp "${TMPDIR:-/tmp}/Clean-kernel-soundness-gate.XXXXXX")"

    if ! "$@" >"$output_file" 2>&1; then
        cat "$output_file"
        rm -f "$output_file"
        return 1
    fi

    if grep -Fq "$expected_text" "$output_file"; then
        cat "$output_file"
        rm -f "$output_file"
        return 0
    fi

    cat "$output_file"
    rm -f "$output_file"
    return 1
}

echo "=== Kernel Soundness Gate ==="
echo ""

echo "--- Lane 0: Differential artifact preflight ---"
STEPS=$((STEPS + 1))
if validate_differential_artifacts; then
    PASS=$((PASS + 1))
    record_lane "differential_artifact_preflight" "Differential artifact preflight" "" "" "true" "true" "passed"
else
    FAIL=$((FAIL + 1))
    record_lane "differential_artifact_preflight" "Differential artifact preflight" "" "" "false" "false" "failed"
    write_evidence "failed"
    echo "=== Kernel Soundness Gate: FAILED ==="
    exit 1
fi
echo ""

unset REGEN_BASELINE

echo "--- Lane 1: Expression-level parity (Clean-kernel) ---"
STEPS=$((STEPS + 1))
if run_expected_cargo_test 1 cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" \
    -p clean-kernel --test lean4_parity --features test-utils -- \
    lean4_parity_check; then
    PASS=$((PASS + 1))
    record_lane "kernel_lean4_parity" "Expression-level parity (Clean-kernel)" "1" "" "true" "true" "passed"
else
    FAIL=$((FAIL + 1))
    record_lane "kernel_lean4_parity" "Expression-level parity (Clean-kernel)" "1" "" "false" "false" "failed"
    write_evidence "failed"
    echo "=== Kernel Soundness Gate: FAILED ==="
    exit 1
fi
echo ""

echo "--- Lane 2: File-level accept/reject gate (Clean-elab) ---"
STEPS=$((STEPS + 1))
if run_expected_output "soundness_gate: PASS" cargo run --locked --message-format=short \
    -j "$CARGO_BUILD_JOBS" -p clean-elab --bin soundness_gate; then
    PASS=$((PASS + 1))
    record_lane "elab_soundness_gate" "File-level accept/reject gate (Clean-elab)" "" "soundness_gate: PASS" "true" "true" "passed"
else
    FAIL=$((FAIL + 1))
    record_lane "elab_soundness_gate" "File-level accept/reject gate (Clean-elab)" "" "soundness_gate: PASS" "false" "false" "failed"
    write_evidence "failed"
    echo "=== Kernel Soundness Gate: FAILED ==="
    exit 1
fi
echo ""

write_evidence "passed"
echo "=== Kernel Soundness Gate: PASS ==="
