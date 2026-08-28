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

# The unchecked-decl ratchet lane.
#
# G6 (2026-08-23) — WHAT THIS LANE USED TO ASSERT AND WHY THAT CHANGED. It read
# `data/unchecked_decl_ratchet.json`, checked the JSON against itself, and then
# required the two counts to be the literal 0. Nothing here, and nothing
# anywhere else, ever read a line of Rust: "the unchecked-decl ratchet is at
# 0/0" was a claim about a JSON literal, and it was FALSE — the tree has always
# had one production `add_decl_unchecked` call site (the mm_axiom_only proof-drop
# arm of `Environment::add_decl`, the Metamath two-pass PASS-1), which is now
# counted, argued and pinned. A gate that can only pass while the artifact lies
# is worse than no gate.
#
# So the lane no longer asks "is the number zero". It asks the question the
# number was standing in for, and it asks the SOURCE TREE:
#   1. scripts/check_add_decl_ratchet.py --selftest, then a full re-derivation of
#      every production call site from crates/**/*.rs. That is the part the old
#      lane was missing entirely; it also enforces the // SOUNDNESS: comment and
#      the in-code SANCTIONED_SITES allowlist, so no bypass can be legalised by
#      writing JSON about it.
#   2. the artifact's own internal consistency (rows + production sites sum to
#      the declared counts) — retained verbatim from the old lane.
#   3. every counted occurrence is a SANCTIONED site, at or under its pinned cap,
#      with a non-empty trust justification. The allowlist is imported from the
#      scanner rather than copied, so the two cannot drift.
# Net: strictly more is enforced than before, on strictly more evidence. The one
# thing no longer enforced is the literal 0, which was never true.
check_unchecked_decl_ratchet_accounted() {
    python3 <<'PY'
import json
import sys
from pathlib import Path

sys.path.insert(0, "scripts")
try:
    import check_add_decl_ratchet as scanner
except ImportError as exc:  # fail closed: no scanner, no lane
    print(f"unchecked-decl ratchet: FAIL: cannot import the source scanner: {exc}", file=sys.stderr)
    sys.exit(1)

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
# Every counted occurrence must be a SANCTIONED site, at or under its pinned
# cap. The allowlist is the scanner's, imported — never a second copy.
counted: dict[tuple[str, str], int] = {}
for sites_key, expected_method in (
    ("add_decl_structural_production_sites", "add_decl_structural"),
    ("add_decl_unchecked_production_sites", "add_decl_unchecked"),
):
    for site in ratchet.get(sites_key, []) or []:
        key = (site.get("file"), site.get("method", expected_method))
        counted[key] = counted.get(key, 0) + int(site.get("occurrences", 1))

for key, occurrences in sorted(counted.items()):
    cap = scanner.SANCTIONED_SITES.get(key)
    if cap is None:
        fail(
            f"{key[0]} / {key[1]} is counted in the ratchet but is not in SANCTIONED_SITES "
            f"in scripts/check_add_decl_ratchet.py. A bypass cannot be legalised by an "
            f"artifact row; sanction it in code, with its argument, or remove it."
        )
    if occurrences > cap:
        fail(f"{key[0]} / {key[1]} counts {occurrences} occurrences, sanctioned cap is {cap}")

# `files` rows are file-granularity legacy entries with no site identity, so they
# can never be matched against the allowlist. They must stay empty.
legacy = structural_sum + unchecked_sum - sum(counted.values())
if legacy:
    fail(f"{legacy} legacy `files` occurrence(s) carry no site identity and cannot be sanctioned")

# THE PART THE OLD LANE DID NOT HAVE: re-derive from the source tree.
if scanner.selftest() != 0:
    fail("the add_decl scanner's own mutation arms no longer fire")
if scanner.run(scanner.REPO_ROOT) != 0:
    fail("the source tree disagrees with data/unchecked_decl_ratchet.json (see above)")

print(
    f"unchecked-decl ratchet: PASS (source-measured; add_decl_structural_count={structural}, "
    f"add_decl_unchecked_count={unchecked}, all occurrences sanctioned)"
)
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
# `datetime.UTC` is 3.11+ and this heredoc runs under the AMBIENT python3
# (3.9.6 on macOS CommandLineTools), so the import raised and `set -e` killed
# the gate before its own PASS/FAILED line — the same defect this script's
# sibling kernel_soundness_gate.sh documents at its line 73. `timezone.utc`
# is 3.9-safe. Fixed 2026-08-27.
from datetime import datetime, timezone
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


# TRUST-CORE PINS (added 2026-08-27). The in-binary validator
# (cmd_replacement/launch_validation.rs -> validate_trust_core_module_tree_sha)
# and scripts/check_trustcore_evidence_staleness.py both REQUIRE these two
# keys, but this minter never wrote them, so every freshly minted artifact was
# born stale and the only previous remedy was hand-editing a generated file
# (2b3ee69ee). Mint them instead.
TRUST_CORE_MODULE_FILE = Path("crates/clean-cli/src/cmd_replacement.rs")
TRUST_CORE_MODULE_DIR = Path("crates/clean-cli/src/cmd_replacement")
TRUST_CORE_MODULE_TREE_KEY = "crates/clean-cli/src/cmd_replacement/**/*.rs"


def trust_core_module_tree_digest(root: Path) -> str:
    """Byte-identical replication of `sha256_repo_module_tree` (artifact_io.rs)."""
    entries = []
    for path in root.rglob("*"):
        if path.is_symlink() or not path.is_file():
            continue
        stem, dot, ext = path.name.rpartition(".")
        if dot != "." or stem == "" or ext != "rs":
            continue
        rel = path.relative_to(root).as_posix()
        if rel.startswith("tests/"):
            continue
        entries.append((rel.encode("utf-8"), path.read_bytes()))
    entries.sort(key=lambda entry: entry[0])
    hasher = hashlib.sha256()
    for rel_bytes, data in entries:
        hasher.update(rel_bytes)
        hasher.update(b"\x00")
        hasher.update(len(data).to_bytes(8, "little"))
        hasher.update(data)
    return hasher.hexdigest()


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
    "generated_at": datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
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
    "source_sha256": {
        **{str(p): sha256_file(p) for p in SOURCE_PATHS},
        str(TRUST_CORE_MODULE_FILE): sha256_file(TRUST_CORE_MODULE_FILE),
        TRUST_CORE_MODULE_TREE_KEY: trust_core_module_tree_digest(TRUST_CORE_MODULE_DIR),
    },
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

# Step 2: every unchecked-decl bypass in the SOURCE TREE is sanctioned, argued
# and at or under its pinned cap (G6, 2026-08-23 — this used to assert a literal
# 0/0 against the JSON, which was false; see check_unchecked_decl_ratchet_accounted)
LANE_2_DESC="Unchecked-decl ratchet: every production bypass source-measured and sanctioned"
step "$LANE_2_DESC"
if check_unchecked_decl_ratchet_accounted; then
    pass
    record_lane "unchecked_decl_ratchet_accounted" "$LANE_2_DESC" "" "true" "passed"
else
    fail "an unchecked-decl bypass is unaccounted, unsanctioned, over its cap, or the artifact disagrees with the tree"
    record_lane "unchecked_decl_ratchet_accounted" "$LANE_2_DESC" "" "false" "failed"
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
