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
# Usage: ./scripts/deny_sorry_gate.sh [--selftest]
#
# On completion the gate writes a run record to $DENY_SORRY_EVIDENCE_PATH, or,
# when that is unset, to a fresh temporary file whose path it prints. The
# record is cleared at startup so a failed or interrupted run cannot leave an
# old passing artifact behind.
#
# It never writes the committed launch receipt,
# reports/deny-sorry-launch-evidence.json, and refuses a path naming it (by
# spelling or by file identity) before any lane runs. That receipt has one
# producer, `clean replacement trust-core-evidence --deny-sorry`, which stamps
# DENY_SORRY_RUST_GATE_COMMAND, the v2 schema and the shared-digest pins that
# `clean-evidence check trustcore-staleness` compares. Until the EV0 review
# (2026-11-17) a bare run of this script wrote that path: it deleted a valid
# receipt at startup and left one the Rust validator rejects, hashed with a
# Python copy of the Rust module-tree digest and without the v2 pins.
#
# --selftest runs this script's OWN refusal arms (no cargo, no build, no
# evidence written) and exits. It is what the gate registry replays.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

EVIDENCE_SCHEMA_VERSION="Clean-deny-sorry-launch-evidence-v1"
COMMITTED_RECEIPT="reports/deny-sorry-launch-evidence.json"
EVIDENCE_PATH="${DENY_SORRY_EVIDENCE_PATH:-}"
EXPECTED_STEPS=6

# names_committed_receipt <path>: true when <path> is the committed receipt,
# spelled any way (`./reports/../reports/...`, an absolute path) or reached
# through a link (`-ef` compares the files themselves).
names_committed_receipt() {
    local dir=""
    dir="$(cd "$(dirname "$1")" 2>/dev/null && pwd -P)" || dir=""
    [ "$dir/$(basename "$1")" = "$(pwd -P)/$COMMITTED_RECEIPT" ] || [ "$1" -ef "$COMMITTED_RECEIPT" ]
}

PASS=0
FAIL=0
STEPS=0
LANES_FILE="$(mktemp "${TMPDIR:-/tmp}/Clean-deny-sorry-gate-lanes.XXXXXX")"

cleanup() {
    rm -f "$LANES_FILE"
}

trap cleanup EXIT

SELFTEST=0
case "${1:-}" in
    --selftest) SELFTEST=1 ;;
    "") ;;
    # Until 2026-09-15 this script took no arguments and IGNORED every one it
    # was given, which is why `data/gate_registry.json` could carry
    # `scripts/deny_sorry_gate.sh scanner.selftest()` as this row's
    # demonstration ref: a command that is not a command, naming a different
    # gate's selftest, in a row that claims soundness.
    *) echo "usage: $0 [--selftest]" >&2; exit 2 ;;
esac

# Guarded: --selftest writes no record on its way to testing a grep.
if [ "$SELFTEST" -eq 0 ]; then
    if [ -z "$EVIDENCE_PATH" ]; then
        EVIDENCE_PATH="$(mktemp "${TMPDIR:-/tmp}/clean-deny-sorry-run.XXXXXX")"
    fi
    mkdir -p "$(dirname "$EVIDENCE_PATH")"
    if names_committed_receipt "$EVIDENCE_PATH"; then
        echo "deny-sorry gate: refusing to write $COMMITTED_RECEIPT -- its one producer is" >&2
        echo "  clean replacement trust-core-evidence --deny-sorry --evidence $COMMITTED_RECEIPT" >&2
        exit 2
    fi
    rm -f "$EVIDENCE_PATH"
fi

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
# This run record pins only the inputs above. The trust-core module-tree and
# shared-digest pins belong to the committed v2 receipt, which only the Rust
# producer writes; the Python copy of that digest that lived here was deleted
# in the EV0 review (2026-11-17).


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
    "source_sha256": {str(p): sha256_file(p) for p in SOURCE_PATHS},
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

# ---------------------------------------------------------------- selftest
#
# The gate's own refusal arms. No cargo, no build, nothing written: every arm
# drives run_filtered_cargo_test against a stand-in that PRINTS what libtest
# prints, so the thing under test is this script's acceptance rule and not a
# compiler.
#
# Arm 2 is the one this block was written for. Until 2026-09-15 step 1 ran a
# BARE `cargo test ... -- --exact <name>` with no count assertion, while steps
# 3-6 all went through run_filtered_cargo_test. Measured that day on a
# throwaway crate: a `--exact` filter that matches nothing exits 0 and prints
# `running 0 tests` / `test result: ok. 0 passed; 0 failed; ...; 1 filtered
# out`. So a renamed or drifted test name left step 1 GREEN having executed
# nothing, in a gate whose registry row claims soundness -- the same class
# CLAUDE.md records as closed at 26c9b823c for "the filtered enforcement
# legs", with this leg missed.
_selftest_emit() { printf '%s\n' "$@"; }
_selftest_every_cargo_test_is_counted() { # <shell-file>
    python3 - "$1" <<'INNER_PY'
# A gate's verdict comes from a parse, never a line count (CLAUDE.md, *Proof
# soundness rules*), and this reader needed TWO corrections to obey its own
# rule -- both caught by the arm below within a minute of it being written.
#
#   1. The first draft matched raw text and accused three of its own string
#      literals. That is the mention-vs-code defect verbatim.
#   2. The second draft blanked quoted runs with one state machine over the
#      whole file. But this file is a POLYGLOT: its embedded python heredocs
#      are full of apostrophes in prose, every one of which flipped the bash
#      quote state, so the blanking desynced and two accusations survived.
#
# What it does now is ask the only question that matters -- is `cargo test` in
# COMMAND POSITION -- which needs no string blanking at all, because a quoted
# occurrence is an ARGUMENT to whatever command heads its line. Heredoc bodies
# are removed first (they are not bash), comment lines are dropped, backslash
# continuations are joined, and each logical line is split into simple commands
# at the usual separators; leading assignments and `env`-style prefixes are
# skipped before the head is read.
import re
import sys

raw = open(sys.argv[1], encoding="utf-8").read().splitlines()

# --- strip heredoc bodies -------------------------------------------------
HEREDOC = re.compile(r"<<-?\s*['\"]?([A-Za-z_][A-Za-z0-9_]*)['\"]?")
lines, i = [], 0
while i < len(raw):
    line = raw[i]
    lines.append(line)
    m = HEREDOC.search(line)
    i += 1
    if not m:
        continue
    tag = m.group(1)
    while i < len(raw) and raw[i].strip() != tag:
        i += 1
    i += 1  # drop the closing tag too

# --- drop comment lines, join continuations -------------------------------
kept = [ln for ln in lines if not ln.strip().startswith("#")]
joined = re.sub(r"\\\n\s*", " ", "\n".join(kept))

SEPARATORS = {";", "&&", "||", "|", "(", ")", "{", "}", "!", "if", "then",
              "else", "elif", "fi", "do", "done", "while", "until", "&"}
PREFIXES = {"env", "time", "command", "exec", "nohup", "sudo"}
ASSIGNMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")

bad = []
for line in joined.splitlines():
    spaced = re.sub(r"([;()|&{}])", r" \1 ", line)
    toks = spaced.split()
    head = True
    k = 0
    while k < len(toks):
        if toks[k] in SEPARATORS:
            head = True
            k += 1
            continue
        if head:
            j = k
            while j < len(toks) and (toks[j] in PREFIXES or ASSIGNMENT.match(toks[j])):
                j += 1
            # `targo --unverified test` / `targo trust test` (the driver since
            # 2026-09-28), and the stock `cargo test` spelling as well.
            if j + 1 < len(toks) and toks[j] == "cargo" and toks[j + 1] == "test":
                bad.append(line.strip()[:140])
            elif (j + 2 < len(toks) and toks[j] == "targo"
                  and toks[j + 1] in ("--unverified", "trust") and toks[j + 2] == "test"):
                bad.append(line.strip()[:140])
            head = False
            k = j + 1
            continue
        k += 1

for b in bad:
    print("UNCOUNTED test invocation:", b)
raise SystemExit(1 if bad else 0)
INNER_PY
}
_selftest_broken_cmd() { printf 'error: could not compile `clean-kernel`\n'; return 101; }

selftest() {
    local arms=0 bad=0
    _arm() { # <name> <expected-rc-class: ok|red> <cmd...>
        local name="$1" want="$2"; shift 2
        arms=$((arms + 1))
        local rc=0
        "$@" >/dev/null 2>&1 || rc=$?
        if { [ "$want" = ok ] && [ "$rc" -eq 0 ]; } || { [ "$want" = red ] && [ "$rc" -ne 0 ]; }; then
            echo "  ok   $name"
        else
            echo "  FAIL $name (rc=$rc, wanted $want)"
            bad=$((bad + 1))
        fi
    }

    local ok1="test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s"
    local zero="test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 1 filtered out; finished in 0.00s"
    local ok2="test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s"
    local ok11="test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s"

    _arm "a lane that runs its one test is accepted" ok \
        run_filtered_cargo_test 1 _selftest_emit "running 1 test" "$ok1"
    _arm "A FILTER THAT SELECTED NOTHING IS REFUSED (exit 0, 'running 0 tests')" red \
        run_filtered_cargo_test 1 _selftest_emit "running 0 tests" "$zero"
    _arm "a lane that runs MORE tests than pinned is refused" red \
        run_filtered_cargo_test 1 _selftest_emit "running 2 tests" "$ok2"
    _arm "11 does not satisfy an expectation of 1 (no prefix collision)" red \
        run_filtered_cargo_test 1 _selftest_emit "running 11 tests" "$ok11"
    _arm "1 does not satisfy an expectation of 11 either" red \
        run_filtered_cargo_test 11 _selftest_emit "running 1 test" "$ok1"
    _arm "a multi-test lane at its exact pin is accepted" ok \
        run_filtered_cargo_test 11 _selftest_emit "running 11 tests" "$ok11"
    _arm "a command that FAILS is refused whatever it printed" red \
        run_filtered_cargo_test 1 _selftest_broken_cmd
    _arm "a passing run whose result line is absent is refused" red \
        run_filtered_cargo_test 1 _selftest_emit "running 1 test"

    # THE CALLER, not just the capability. Every arm above tests
    # run_filtered_cargo_test; none of them tests that step 1 CALLS it, and a
    # counter nothing calls is exactly the defect being fixed here -- the
    # helper existed and was used by steps 3-6 for weeks while step 1 ran bare.
    # So this arm reads this file: after joining backslash continuations and
    # dropping comment lines, every logical line that invokes `cargo test`
    # must also name run_filtered_cargo_test.
    arms=$((arms + 1))
    if _selftest_every_cargo_test_is_counted "${BASH_SOURCE[0]}" >/dev/null 2>&1; then
        echo "  ok   every cargo-test invocation in this file goes through the counter"
    else
        echo "  FAIL every cargo-test invocation in this file goes through the counter"
        _selftest_every_cargo_test_is_counted "${BASH_SOURCE[0]}" || true
        bad=$((bad + 1))
    fi

    # ...and that reader is not a rubber stamp: a file with a bare invocation
    # must be REFUSED, or the arm above passes for a scanner that finds
    # nothing.
    # One arm per driver spelling the reader claims to know -- both Targo lanes
    # and the stock spelling it still judges -- so none is recognised only in
    # a comment.
    local synthetic driver
    for driver in 'targo --unverified test' 'targo trust test' 'cargo test'; do
        arms=$((arms + 1))
        synthetic="$(mktemp "${TMPDIR:-/tmp}/Clean-deny-sorry-selftest.XXXXXX")"
        printf '%s\n' '#!/bin/bash' "$driver --locked -p clean-kernel --test lint_sorry_bypass" >"$synthetic"
        if _selftest_every_cargo_test_is_counted "$synthetic" >/dev/null 2>&1; then
            echo "  FAIL the reader refuses a BARE \`$driver\` invocation"
            bad=$((bad + 1))
        else
            echo "  ok   the reader refuses a BARE \`$driver\` invocation"
        fi
        rm -f "$synthetic"
    done

    # The committed receipt has one producer, the Rust one, so this script must
    # recognise every spelling of its path and refuse it, and must not refuse
    # an ordinary run-record path (or the guard refuses everything).
    _arm "the committed receipt is recognised by its own spelling" ok \
        names_committed_receipt "$COMMITTED_RECEIPT"
    _arm "the committed receipt is recognised through ./reports/../reports" ok \
        names_committed_receipt "./reports/../$COMMITTED_RECEIPT"
    _arm "the committed receipt is recognised by its absolute path" ok \
        names_committed_receipt "$(pwd -P)/$COMMITTED_RECEIPT"
    local link_dir
    link_dir="$(mktemp -d "${TMPDIR:-/tmp}/Clean-deny-sorry-selftest.XXXXXX")"
    ln -s "$(pwd -P)/$COMMITTED_RECEIPT" "$link_dir/receipt.json"
    _arm "a symlink to the committed receipt is recognised" ok \
        names_committed_receipt "$link_dir/receipt.json"
    _arm "a run-record path outside reports/ is not the receipt" red \
        names_committed_receipt "$link_dir/run.json"
    rm -rf "${link_dir:?}"

    # The argument contract itself: an unknown argument must refuse rather
    # than run the whole gate, which is what let a non-command sit in the
    # registry as this row's demonstration.
    arms=$((arms + 1))
    local rc=0
    bash "$0" --not-a-real-flag >/dev/null 2>&1 || rc=$?
    if [ "$rc" -eq 2 ]; then
        echo "  ok   an unknown argument refuses with usage (exit 2)"
    else
        echo "  FAIL an unknown argument refuses with usage (rc=$rc, wanted 2)"
        bad=$((bad + 1))
    fi

    if [ "$bad" -gt 0 ]; then
        echo "deny_sorry_gate selftest: $bad of $arms arm(s) failed" >&2
        return 1
    fi
    echo "deny_sorry_gate selftest: $arms/$arms arms behave"
    return 0
}

if [ "$SELFTEST" -eq 1 ]; then
    selftest
    exit $?
fi

echo "=== DENY_SORRY CLEAN GATE ==="
echo "Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Step 1: Static lint — no direct sorry constructor bypasses
# Migrated to a cargo integration test in Wave 72.
#
# COUNTED since 2026-09-15. This was the one cargo lane in the script that did
# not assert how many tests ran; see the selftest above for the measurement.
step "Static lint: lint_sorry_bypass"
if run_filtered_cargo_test 1 \
    targo --unverified test --locked --message-format=short -j "$CARGO_BUILD_JOBS" \
    -p clean-kernel --test lint_sorry_bypass -- --exact \
    lint_sorry_bypass_finds_no_direct_constructions; then
    pass
    record_lane "lint_sorry_bypass" "Static lint: lint_sorry_bypass" "1" "true" "passed"
else
    fail "lint_sorry_bypass found direct constructor bypasses, or the --exact filter selected no test at all"
    record_lane "lint_sorry_bypass" "Static lint: lint_sorry_bypass" "1" "false" "failed"
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
if run_filtered_cargo_test 11 env DENY_SORRY=1 targo --unverified test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-kernel --test deny_sorry_gate; then
    pass
    record_lane "kernel_deny_sorry_gate" "Subprocess enforcement: deny_sorry_gate integration test" "11" "true" "passed"
else
    fail "deny_sorry_gate subprocess tests failed"
    record_lane "kernel_deny_sorry_gate" "Subprocess enforcement: deny_sorry_gate integration test" "11" "false" "failed"
fi

# Step 4: Lean 4 parity lane under DENY_SORRY
step "Lean4 parity: lean4_parity_check under DENY_SORRY=1"
if run_filtered_cargo_test 1 env DENY_SORRY=1 targo --unverified test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-kernel --features test-utils --test lean4_parity -- lean4_parity_check; then
    pass
    record_lane "kernel_lean4_parity" "Lean4 parity: lean4_parity_check under DENY_SORRY=1" "1" "true" "passed"
else
    fail "lean4_parity_check failed under DENY_SORRY=1"
    record_lane "kernel_lean4_parity" "Lean4 parity: lean4_parity_check under DENY_SORRY=1" "1" "false" "failed"
fi

# Step 5: Soundness gate clean lanes under DENY_SORRY
step "Soundness gate accept lane under DENY_SORRY=1"
if run_filtered_cargo_test 1 env DENY_SORRY=1 targo --unverified test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-elab --test soundness_gate -- --exact accept::soundness_gate_accept; then
    pass
    record_lane "elab_soundness_gate_accept" "Soundness gate accept lane under DENY_SORRY=1" "1" "true" "passed"
else
    fail "soundness_gate_accept failed under DENY_SORRY=1"
    record_lane "elab_soundness_gate_accept" "Soundness gate accept lane under DENY_SORRY=1" "1" "false" "failed"
fi

step "Soundness gate reject lane under DENY_SORRY=1"
if run_filtered_cargo_test 1 env DENY_SORRY=1 targo --unverified test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-elab --test soundness_gate -- --exact reject::soundness_gate_reject; then
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
