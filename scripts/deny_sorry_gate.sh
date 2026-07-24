#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Curated DENY_SORRY clean gate.
#
# Runs a bounded set of tests that are expected to stay sorry-free, with
# DENY_SORRY=1 so that any sorry term creation causes a hard failure.
#
# This is the enforcement side of GAP 4 (#2085). The ratchet
# (scripts/sorry_census.sh, sorry_baseline.json) handles broad regression
# tracking; this gate handles hard-fail for curated clean paths.
#
# Allowlist policy:
#   - A test belongs here only if it already succeeds with zero sorry terms
#   - Intentional provenance/sorry tests stay outside this lane
#   - Expand by adding more already-clean targets one by one
#
# Usage: ./scripts/deny_sorry_gate.sh
#
# On completion the gate writes reports/deny-sorry-launch-evidence.json. The
# evidence file is cleared at startup so a failed or interrupted run cannot
# leave an old passing artifact behind.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

EVIDENCE_SCHEMA_VERSION="Clean-deny-sorry-launch-evidence-v1"
EVIDENCE_PATH="${DENY_SORRY_EVIDENCE_PATH:-reports/deny-sorry-launch-evidence.json}"
EXPECTED_STEPS=6

PASS=0
FAIL=0
STEPS=0
LANES_FILE="$(mktemp "${TMPDIR:-/tmp}/Clean-deny-sorry-gate-lanes.XXXXXX")"

cleanup() {
    rm -f "$LANES_FILE"
}

trap cleanup EXIT

mkdir -p "$(dirname "$EVIDENCE_PATH")"
rm -f "$EVIDENCE_PATH"

step() {
    STEPS=$((STEPS + 1))
    echo ""
    echo "[$STEPS] $1"
}

pass() {
    PASS=$((PASS + 1))
    echo "  PASS"
}

fail() {
    FAIL=$((FAIL + 1))
    echo "  FAIL: $1"
}

record_lane() {
    local id="$1"
    local description="$2"
    local expected_tests="$3"
    local matched_expected_count="$4"
    local status="$5"

    printf '%s\t%s\t%s\t%s\t%s\n' \
        "$id" "$description" "$expected_tests" "$matched_expected_count" "$status" \
        >>"$LANES_FILE"
}

check_unchecked_decl_ratchet_zero() {
    python3 <<'PY'
import json
import sys
from pathlib import Path

RATCHET_PATH = Path("data/unchecked_decl_ratchet.json")


def fail(message: str) -> None:
    print(f"unchecked-decl ratchet: FAIL: {message}", file=sys.stderr)
    sys.exit(1)


try:
    ratchet = json.loads(RATCHET_PATH.read_text(encoding="utf-8"))
except OSError as exc:
    fail(f"failed to read {RATCHET_PATH}: {exc}")
except json.JSONDecodeError as exc:
    fail(f"failed to parse {RATCHET_PATH}: {exc}")

structural = ratchet.get("add_decl_structural_count")
unchecked = ratchet.get("add_decl_unchecked_count")
if not isinstance(structural, int) or not isinstance(unchecked, int):
    fail("top-level structural/unchecked counts must be integers")

files = ratchet.get("files")
if not isinstance(files, list):
    fail("files must be a list")

structural_sum = 0
unchecked_sum = 0
for index, entry in enumerate(files):
    if not isinstance(entry, dict):
        fail(f"files[{index}] is not an object")
    method = entry.get("method")
    count = entry.get("count")
    if method not in {"add_decl_structural", "add_decl_unchecked"}:
        fail(f"files[{index}] has unsupported method {method!r}")
    if not isinstance(count, int) or count <= 0:
        fail(f"files[{index}] has non-positive count {count!r}")
    if method == "add_decl_structural":
        structural_sum += count
    else:
        unchecked_sum += count

# Individually-accounted live production sites (G3 honesty correction,
# 2026-07-01) contribute to the per-method counts alongside legacy file rows.
# Mirrors validate_unchecked_decl_ratchet in
# crates/clean-cli/src/cmd_replacement/gate_checks.rs.
for sites_key, expected_method in (
    ("add_decl_structural_production_sites", "add_decl_structural"),
    ("add_decl_unchecked_production_sites", "add_decl_unchecked"),
):
    sites = ratchet.get(sites_key, [])
    if not isinstance(sites, list):
        fail(f"{sites_key} must be a list")
    for index, site in enumerate(sites):
        if not isinstance(site, dict):
            fail(f"{sites_key}[{index}] is not an object")
        if site.get("method") != expected_method:
            fail(
                f"{sites_key}[{index}] records method {site.get('method')!r} "
                f"under {sites_key}"
            )
        trust = site.get("trust")
        if not isinstance(trust, str) or not trust.strip():
            fail(f"{sites_key}[{index}] is missing its SOUNDNESS trust justification")
        occurrences = site.get("occurrences", 1)
        if not isinstance(occurrences, int) or occurrences <= 0:
            fail(f"{sites_key}[{index}] has non-positive occurrences {occurrences!r}")
        if expected_method == "add_decl_structural":
            structural_sum += occurrences
        else:
            unchecked_sum += occurrences

if structural_sum != structural:
    fail(
        f"add_decl_structural_count={structural} but file rows + "
        f"production sites sum to {structural_sum}"
    )
if unchecked_sum != unchecked:
    fail(
        f"add_decl_unchecked_count={unchecked} but file rows + "
        f"production sites sum to {unchecked_sum}"
    )
if structural != 0 or unchecked != 0:
    fail(f"expected add_decl_structural_count=0 and add_decl_unchecked_count=0, got {structural}/{unchecked}")

print("unchecked-decl ratchet: PASS (add_decl_structural_count=0, add_decl_unchecked_count=0)")
PY
}

write_evidence() {
    local gate_status="$1"

    DENY_SORRY_EVIDENCE_SCHEMA_VERSION="$EVIDENCE_SCHEMA_VERSION" \
        DENY_SORRY_EVIDENCE_PATH="$EVIDENCE_PATH" \
        DENY_SORRY_GATE_STATUS="$gate_status" \
        DENY_SORRY_EXPECTED_STEPS="$EXPECTED_STEPS" \
        DENY_SORRY_STEPS="$STEPS" \
        DENY_SORRY_PASS="$PASS" \
        DENY_SORRY_FAIL="$FAIL" \
        DENY_SORRY_LANES_FILE="$LANES_FILE" \
        python3 <<'PY'
import hashlib
import json
import os
from datetime import UTC, datetime
from pathlib import Path

SCHEMA_VERSION = os.environ["DENY_SORRY_EVIDENCE_SCHEMA_VERSION"]
EVIDENCE_PATH = Path(os.environ["DENY_SORRY_EVIDENCE_PATH"])
LANES_FILE = Path(os.environ["DENY_SORRY_LANES_FILE"])
RATCHET_PATH = Path("data/unchecked_decl_ratchet.json")
SOURCE_PATHS = [
    Path("scripts/deny_sorry_gate.sh"),
    # lint_sorry_bypass migrated to cargo test in Wave 72; the test source
    # is the new source of truth for the static-lint lane.
    Path("crates/clean-kernel/tests/lint_sorry_bypass.rs"),
    RATCHET_PATH,
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


lanes = []
if LANES_FILE.exists():
    for line in LANES_FILE.read_text(encoding="utf-8").splitlines():
        lane_id, description, expected_tests, matched_expected_count, status = line.split("\t")
        lanes.append(
            {
                "id": lane_id,
                "description": description,
                "expected_tests": int(expected_tests) if expected_tests else None,
                "matched_expected_count": matched_expected_count == "true",
                "status": status,
            }
        )

ratchet = json.loads(RATCHET_PATH.read_text(encoding="utf-8"))
artifact = {
    "schema_version": SCHEMA_VERSION,
    "generated_by": "./scripts/deny_sorry_gate.sh",
    "generated_at": datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
    "gate_command": "./scripts/deny_sorry_gate.sh",
    "status": os.environ["DENY_SORRY_GATE_STATUS"],
    "summary": {
        "expected_steps": int(os.environ["DENY_SORRY_EXPECTED_STEPS"]),
        "steps": int(os.environ["DENY_SORRY_STEPS"]),
        "passed": int(os.environ["DENY_SORRY_PASS"]),
        "failed": int(os.environ["DENY_SORRY_FAIL"]),
    },
    "ratchet": {
        "path": str(RATCHET_PATH),
        "add_decl_structural_count": ratchet["add_decl_structural_count"],
        "add_decl_unchecked_count": ratchet["add_decl_unchecked_count"],
        "sha256": sha256_file(RATCHET_PATH),
    },
    "source_sha256": {str(path): sha256_file(path) for path in SOURCE_PATHS},
    "lanes": lanes,
}
EVIDENCE_PATH.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(f"Evidence: {EVIDENCE_PATH}")
PY
}

run_filtered_cargo_test() {
    local expected_tests="$1"
    shift

    local output_file
    output_file="$(mktemp "${TMPDIR:-/tmp}/Clean-deny-sorry-gate.XXXXXX")"

    if ! "$@" >"$output_file" 2>&1; then
        cat "$output_file"
        rm -f "$output_file"
        return 1
    fi

    if grep -Eq "running ${expected_tests} tests?$" "$output_file" &&
        grep -Eq "test result: ok\\. ${expected_tests} passed; 0 failed" "$output_file"; then
        rm -f "$output_file"
        return 0
    fi

    cat "$output_file"
    rm -f "$output_file"
    return 1
}

echo "=== DENY_SORRY CLEAN GATE ==="
echo "Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Step 1: Static lint — no direct sorry constructor bypasses
# Migrated to a cargo integration test in Wave 72.
step "Static lint: lint_sorry_bypass"
if cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" \
    -p clean-kernel --test lint_sorry_bypass -- --exact \
    lint_sorry_bypass_finds_no_direct_constructions; then
    pass
    record_lane "lint_sorry_bypass" "Static lint: lint_sorry_bypass" "" "true" "passed"
else
    fail "lint_sorry_bypass found direct constructor bypasses"
    record_lane "lint_sorry_bypass" "Static lint: lint_sorry_bypass" "" "false" "failed"
fi

# Step 2: Unchecked-decl ratchet closure must stay at 0/0
step "Unchecked-decl ratchet: structural 0 / unchecked 0"
if check_unchecked_decl_ratchet_zero; then
    pass
    record_lane "unchecked_decl_ratchet_zero" "Unchecked-decl ratchet: structural 0 / unchecked 0" "" "true" "passed"
else
    fail "unchecked-decl ratchet is not closed at 0/0"
    record_lane "unchecked_decl_ratchet_zero" "Unchecked-decl ratchet: structural 0 / unchecked 0" "" "false" "failed"
fi

# Step 3: Subprocess enforcement proof — DENY_SORRY actually blocks sorry
step "Subprocess enforcement: deny_sorry_gate integration test"
if run_filtered_cargo_test 11 env DENY_SORRY=1 cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-kernel --test deny_sorry_gate; then
    pass
    record_lane "kernel_deny_sorry_gate" "Subprocess enforcement: deny_sorry_gate integration test" "11" "true" "passed"
else
    fail "deny_sorry_gate subprocess tests failed"
    record_lane "kernel_deny_sorry_gate" "Subprocess enforcement: deny_sorry_gate integration test" "11" "false" "failed"
fi

# Step 4: Lean 4 parity lane under DENY_SORRY
step "Lean4 parity: lean4_parity_check under DENY_SORRY=1"
if run_filtered_cargo_test 1 env DENY_SORRY=1 cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-kernel --features test-utils --test lean4_parity -- lean4_parity_check; then
    pass
    record_lane "kernel_lean4_parity" "Lean4 parity: lean4_parity_check under DENY_SORRY=1" "1" "true" "passed"
else
    fail "lean4_parity_check failed under DENY_SORRY=1"
    record_lane "kernel_lean4_parity" "Lean4 parity: lean4_parity_check under DENY_SORRY=1" "1" "false" "failed"
fi

# Step 5: Soundness gate clean lanes under DENY_SORRY
step "Soundness gate accept lane under DENY_SORRY=1"
if run_filtered_cargo_test 1 env DENY_SORRY=1 cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-elab --test soundness_gate -- --exact accept::soundness_gate_accept; then
    pass
    record_lane "elab_soundness_gate_accept" "Soundness gate accept lane under DENY_SORRY=1" "1" "true" "passed"
else
    fail "soundness_gate_accept failed under DENY_SORRY=1"
    record_lane "elab_soundness_gate_accept" "Soundness gate accept lane under DENY_SORRY=1" "1" "false" "failed"
fi

step "Soundness gate reject lane under DENY_SORRY=1"
if run_filtered_cargo_test 1 env DENY_SORRY=1 cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-elab --test soundness_gate -- --exact reject::soundness_gate_reject; then
    pass
    record_lane "elab_soundness_gate_reject" "Soundness gate reject lane under DENY_SORRY=1" "1" "true" "passed"
else
    fail "soundness_gate_reject failed under DENY_SORRY=1"
    record_lane "elab_soundness_gate_reject" "Soundness gate reject lane under DENY_SORRY=1" "1" "false" "failed"
fi

# Summary
echo ""
echo "=== DENY_SORRY CLEAN GATE SUMMARY ==="
echo "Steps: $STEPS"
echo "Pass:  $PASS"
echo "Fail:  $FAIL"

if [ "$FAIL" -gt 0 ]; then
    write_evidence "failed"
    echo "GATE STATUS: FAILED"
    exit 1
fi

write_evidence "passed"
echo "GATE STATUS: PASSED"
