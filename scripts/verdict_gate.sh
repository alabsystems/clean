#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# RING R2's gate: `verdict_gate.sh` over `data/verdict_set.json`.
#
# WHAT THIS COMMAND OWNS
# ----------------------
# designs/2026-08-22-spine-and-lattice-program.md §5, Ring R2:
#
#   "Gate R2: `verdict_gate.sh` over verdict_set.json, refusal predicates
#    written in the script, lane (c) inventory pinned."
#
# and §8 R7: claims are owned by fail-closed commands, never by sentences. So
# the sentence "the verdict-bearing surface is honestly partitioned" is not a
# thing anyone may write in prose — it is this command's exit status.
#
# THIS GATE IS RED TODAY, AND THAT IS THE POINT
# ---------------------------------------------
# Two of the three partitions have obligations nobody has discharged yet:
# lane (a) has no chains (the committed spine set it would chain against does
# not exist — data/spine_set.PENDING.md records why), and lane (b) has no
# assumption ledger to carry its IO-boundary contracts. A gate that went green
# on that would be the defect the whole program exists to remove: it would
# convert "we have not done the work" into "the work is done". So each
# partition prints NOT-YET-EARNED with a ledger of exactly what it still owes,
# and the command exits 1.
#
# Lane (c) is different, and deliberately so: declaring the claim-owning script
# surface TCB with a committed digest + line-count ratchet is CHEAP and real,
# so it is implemented rather than promised. Its sub-obligations print `met`
# where they are met. The gate distinguishing a met sub-obligation from an
# unmet one inside a refusing partition is what makes the refusal information
# rather than noise.
#
# LANE (b)'s REFUSAL NAMES CONTRACTS, NOT PARTITIONS (2026-08-26)
# ---------------------------------------------------------------
# Until this date lane (b) refused categorically: "N IO sites are unmodelled".
# That is a true sentence that tells nobody what to do. The gate now reads a
# SECOND artifact — `data/verdict_io_contracts.json`, minted by
# `scripts/verdict_io_contracts.py` — which classifies every one of those sites
# by EFFECT (what it does) and by DEPENDENCE (whether the verdict turns on the
# IO's content or only on its success), states the contract each effect class
# assumes, cites what checks it, and carries a §3.6 assumption-ledger row with a
# probe wherever nothing does.
#
# So `owes B2` is now one line per CONTRACT — its statement, its site and member
# counts, whether anything checks it, and the probe that exhibits its sites —
# and `owes B4` names the ledger rows. The partition is still NOT-YET-EARNED,
# because modeling an obligation is not discharging it: every contract below is
# `none` or `partial`, and a `partial` contract is an unearned contract.
#
# The gate re-derives NOTHING from that artifact's own claims: it recomputes the
# sha256 of `verdict_set.json` and refuses if the contract model was minted
# against different bytes, and it refuses if the two artifacts disagree about
# how many IO sites exist.
#
# NOT HARDWIRED RED (falsified, not assumed)
# ------------------------------------------
# `--self-test` runs the gate against synthesized artifacts in a temp dir. One
# arm is a fully-satisfied artifact, and the gate EXITS 0 on it. The other arms
# each break one thing and require the matching refusal:
#
#   1  artifact absent .................. reason=artifact-absent
#   2  artifact not JSON ................ reason=artifact-malformed
#   3  wrong schema ..................... reason=schema-mismatch
#   4  a pinned input moved ............. reason=pin-stale
#   5  a lane (c) script edited ......... reason=lane-c-digest-drift
#   6  the lane (c) ratchet exceeded .... reason=lane-c-ratchet
#   7  a lane (c) member deleted ........ reason=lane-c-member-absent
#   8  everything met .................. EARNED, rc=0
#   9  only lane (a) unmet .............. refuse, ledger names A1/A2/A3
#  10  IO contract model absent ......... refuse, ledger names `owes B1`
#  11  IO contract model not JSON ....... reason=io-contracts-malformed
#  12  IO contract model wrong schema ... reason=io-contracts-schema-mismatch
#  13  minted against other bytes ....... reason=io-contracts-stale
#  14  the two site totals disagree ..... reason=io-contracts-denominator-drift
#  15  a ledger row lacks a probe ....... reason=io-contracts-row-incomplete
#  16  the ledger row ratchet rose ...... reason=io-contracts-row-ratchet
#  17  a modelled contract is unearned .. refuse, ledger names B2.<CONTRACT-ID>
#
# WHAT IT VERIFIES ITSELF, RATHER THAN READING BACK
# -------------------------------------------------
# The artifact records digests; a gate that trusted them would only ever prove
# that a file agrees with itself. So at gate time this script RE-COMPUTES the
# sha256 and line count of every lane (c) member from the tree, and re-computes
# the digest of every pinned derivation input. A drifted script, a moved
# census, an edited registry: each is a refusal with the file named.
#
# Usage:
#   scripts/verdict_gate.sh                    # gate the committed artifacts
#   scripts/verdict_gate.sh --artifact P --io-artifact Q --root R
#   scripts/verdict_gate.sh --self-test        # refusal-path arms (incl. a green one)
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

ROOT="$REPO_ROOT"
ARTIFACT=""
IO_ARTIFACT=""
SELF_TEST=0
SCHEMA_EXPECTED="clean.verdict_set/v1"
IO_SCHEMA_EXPECTED="clean.verdict_io_contracts/v1"

while [ $# -gt 0 ]; do
  case "$1" in
    --artifact) ARTIFACT="$2"; shift 2 ;;
    --io-artifact) IO_ARTIFACT="$2"; shift 2 ;;
    --root) ROOT="$2"; shift 2 ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help) sed -n '1,95p' "$0"; exit 0 ;;
    *) echo "VERDICT_GATE=refuse reason=bad-argument arg=$1" >&2; exit 2 ;;
  esac
done
[ -n "$ARTIFACT" ] || ARTIFACT="$ROOT/data/verdict_set.json"
[ -n "$IO_ARTIFACT" ] || IO_ARTIFACT="$ROOT/data/verdict_io_contracts.json"

PYTHON_BIN=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
  if command -v "$candidate" >/dev/null 2>&1; then PYTHON_BIN="$candidate"; break; fi
done
if [ -z "$PYTHON_BIN" ]; then
  echo "VERDICT_GATE=refuse reason=no-python3-on-PATH" >&2
  exit 1
fi

# macOS ships `shasum`, Linux `sha256sum`. A gate that runs on one box is not a gate.
sha256_of() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    sha256sum "$1" | awk '{print $1}'
  fi
}

# ---------------------------------------------------------------------------
# Fact extraction. The artifact is DATA: python only flattens it to TSV, and
# every refusal predicate below is written in this script, per Gate R2.
# ---------------------------------------------------------------------------
extract_facts() {
  "$PYTHON_BIN" - "$1" <<'PY'
import json, sys
try:
    doc = json.load(open(sys.argv[1]))
except ValueError as exc:
    print(f"fatal\tartifact-malformed\t{exc}")
    raise SystemExit(0)
if not isinstance(doc, dict):
    print("fatal\tartifact-malformed\ttop level is not an object")
    raise SystemExit(0)
print(f"schema\t{doc.get('schema', '<none>')}")
try:
    p = doc["partitions"]
    a, b, c = p["a_pure_rust"], p["b_io_bearing"], p["c_script_surface"]
    ev = doc["evidence"]
    der = doc["derivation"]
except KeyError as exc:
    print(f"fatal\tschema-incomplete\tmissing key {exc}")
    raise SystemExit(0)
print(f"a_members\t{a['member_count']}")
print(f"a_chained\t{a['chained_count']}")
print(f"b_members\t{b['member_count']}")
print(f"b_ledgered\t{b['ledgered_count']}")
print(f"b_io_sites\t{b['io_site_total']}")
print(f"b_separated\t{b.get('separated_count', 0)}")
print(f"c_members\t{c['member_count']}")
print(f"c_tcb\t{c['tcb_declared_count']}")
print(f"c_rust\t{c['rewritten_to_rust_count']}")
print(f"c_undemo\t{c['undemonstrated_unwaived_count']}")
print(f"c_undemo_selftest\t{c.get('undemonstrated_with_self_test_count', 0)}")
print(f"c_baseline\t{c['line_ratchet']['baseline_total_lines']}")
print(f"c_measured_at_mint\t{c['line_ratchet']['measured_total_lines']}")
for path, digest in sorted(der.get("input_pins", {}).items()):
    print(f"pin\t{path}\t{digest}")
for m in c["members"]:
    print(f"cmember\t{m['path']}\t{m['sha256']}\t{m['lines']}\t{m['disposition']}")
for name, present in sorted(ev.get("artifacts_this_surface_depends_on", {}).items()):
    print(f"dep\t{name}\t{1 if present else 0}")
for row in ev.get("corrections", []):
    if row.get("owed"):
        print(f"owed\t{row['id']}\t{row['owed']}")
print(f"closure_limit\t{1 if der.get('closure_limit') else 0}")
PY
}

# The IO contract model. Same posture: python only FLATTENS, the predicates
# below are written in this script. Every emitted field is tab- and
# newline-scrubbed so a prose statement cannot forge a TSV row.
extract_io_facts() {
  "$PYTHON_BIN" - "$1" <<'PY'
import json, sys
def flat(s):
    return " ".join(str(s).split())
try:
    doc = json.load(open(sys.argv[1]))
except ValueError as exc:
    print(f"iofatal\tio-contracts-malformed\t{flat(exc)}")
    raise SystemExit(0)
if not isinstance(doc, dict):
    print("iofatal\tio-contracts-malformed\ttop level is not an object")
    raise SystemExit(0)
print(f"io_schema\t{doc.get('schema', '<none>')}")
try:
    der = doc["derivation"]
    cls = doc["classification"]
    contracts = doc["contracts"]
    ledger = doc["ledger"]
except KeyError as exc:
    print(f"iofatal\tio-contracts-schema-incomplete\tmissing key {flat(exc)}")
    raise SystemExit(0)
print(f"io_source\t{der.get('source_artifact', '')}\t{der.get('source_artifact_sha256', '')}")
print(f"io_sites\t{cls.get('site_total', -1)}")
print(f"io_issuing\t{cls.get('sites_issuing_io', -1)}")
print(f"io_noio\t{cls.get('sites_issuing_no_io', -1)}")
print(f"io_unclassified\t{cls.get('unclassified', -1)}")
for k, v in sorted(cls.get("by_dependence", {}).items()):
    print(f"io_dep\t{k}\t{v}")
print(f"io_declonly\t{cls.get('declaration_only_members', {}).get('count', 0)}")
for c in contracts:
    checks = len(c.get("checked_by", []))
    holes = len(c.get("holes", []))
    print(
        "iocontract\t{id}\t{dep}\t{sites}\t{members}\t{strength}\t{checks}\t{holes}\t{title}".format(
            id=flat(c.get("id")), dep=flat(c.get("dependence")), sites=c.get("site_count", -1),
            members=c.get("member_count", -1), strength=flat(c.get("check_strength")),
            checks=checks, holes=holes, title=flat(c.get("title")),
        )
    )
for c in doc.get("measured_absent", []):
    print(f"ioabsent\t{flat(c.get('id'))}\t{c.get('measured_sites', -1)}\t{flat(c.get('title'))}")
rows = ledger.get("rows", [])
print(f"io_rows\t{len(rows)}")
rat = ledger.get("row_ratchet", {})
print(f"io_row_baseline\t{rat.get('baseline_rows', -1)}")
for cid, n in sorted(ledger.get("rows_by_contract", {}).items()):
    print(f"iorowcount\t{flat(cid)}\t{n}")
for r in rows:
    missing = [f for f in ("statement", "probe", "discharge", "date", "owning_job") if not r.get(f)]
    if missing:
        print(f"iorowbad\t{flat(r.get('id'))}\t{','.join(missing)}")
for r in doc.get("recommendations", []):
    print(f"iorec\t{flat(r.get('id'))}\t{flat(r.get('contract'))}\t{flat(r.get('cheap_because'))}")
PY
}

gate_run() {
  local artifact="$1" root="$2" io_artifact="${3:-}"
  local -i earned=0
  local refusals=""

  if [ ! -f "$artifact" ]; then
    echo "VERDICT_GATE=refuse reason=artifact-absent path=$artifact"
    echo "   Ring R2's member list does not exist. Mint it: scripts/verdict_set.py"
    return 1
  fi

  local facts
  facts="$(extract_facts "$artifact")"

  fact() { printf '%s\n' "$facts" | awk -F'\t' -v k="$1" '$1==k{print $2; exit}'; }

  # schema first: a document of the wrong shape is refused for BEING the wrong
  # shape, not for whichever key the extractor happened to miss first.
  local schema; schema="$(fact schema)"
  if [ -n "$schema" ] && [ "$schema" != "$SCHEMA_EXPECTED" ]; then
    echo "VERDICT_GATE=refuse reason=schema-mismatch got=$schema want=$SCHEMA_EXPECTED"
    return 1
  fi

  local fatal
  fatal="$(printf '%s\n' "$facts" | awk -F'\t' '$1=="fatal"{print $2"\t"$3}')"
  if [ -n "$fatal" ]; then
    echo "VERDICT_GATE=refuse reason=$(printf '%s' "$fatal" | cut -f1) detail=$(printf '%s' "$fatal" | cut -f2)"
    return 1
  fi
  if [ -z "$schema" ]; then
    echo "VERDICT_GATE=refuse reason=schema-mismatch got=<none> want=$SCHEMA_EXPECTED"
    return 1
  fi

  # -- P1  pinned derivation inputs are still what the artifact was derived from
  local pin_stale=""
  while IFS=$'\t' read -r _ path digest; do
    [ -n "$path" ] || continue
    if [ ! -f "$root/$path" ]; then
      pin_stale="$pin_stale
      $path is ABSENT (the derivation input vanished)"
      continue
    fi
    local now; now="$(sha256_of "$root/$path")"
    if [ "$now" != "$digest" ]; then
      pin_stale="$pin_stale
      $path moved: pinned ${digest:0:12} now ${now:0:12}"
    fi
  done <<< "$(printf '%s\n' "$facts" | awk -F'\t' '$1=="pin"')"
  if [ -n "$pin_stale" ]; then
    echo "VERDICT_GATE=refuse reason=pin-stale"
    echo "   the verdict set was derived from inputs that have since changed:$pin_stale"
    echo "   re-mint: scripts/verdict_set.py"
    return 1
  fi

  # -- P2  lane (c) inventory: re-measure every member from the TREE
  local -i c_drift=0 c_absent=0 c_lines_now=0 c_seen=0
  local drift_list=""
  while IFS=$'\t' read -r _ path digest lines disposition; do
    [ -n "$path" ] || continue
    c_seen=$((c_seen + 1))
    if [ ! -f "$root/$path" ]; then
      c_absent=$((c_absent + 1))
      drift_list="$drift_list
      ABSENT   $path"
      continue
    fi
    local now; now="$(sha256_of "$root/$path")"
    local now_lines; now_lines="$(wc -l < "$root/$path" | tr -d ' ')"
    c_lines_now=$((c_lines_now + now_lines))
    if [ "$now" != "$digest" ]; then
      c_drift=$((c_drift + 1))
      drift_list="$drift_list
      DRIFTED  $path (pinned ${digest:0:12}, tree ${now:0:12}; pinned ${lines} lines, tree ${now_lines})"
    fi
    if [ "$disposition" != "tcb-declared" ] && [ "$disposition" != "rewritten-to-rust" ]; then
      c_drift=$((c_drift + 1))
      drift_list="$drift_list
      UNDISPOSED $path (disposition=$disposition; Ring R2 allows only rewritten-to-rust or tcb-declared)"
    fi
  done <<< "$(printf '%s\n' "$facts" | awk -F'\t' '$1=="cmember"')"

  if [ "$c_absent" -gt 0 ]; then
    echo "VERDICT_GATE=refuse reason=lane-c-member-absent count=$c_absent"
    echo "   a pinned claim-owning script is gone from the tree:$drift_list"
    return 1
  fi
  if [ "$c_drift" -gt 0 ]; then
    echo "VERDICT_GATE=refuse reason=lane-c-digest-drift count=$c_drift"
    echo "   the TCB script surface is not what the artifact pins:$drift_list"
    echo "   a drifted gate is an unpinned gate; re-mint: scripts/verdict_set.py"
    return 1
  fi

  local -i c_baseline; c_baseline="$(fact c_baseline)"
  if [ "$c_lines_now" -gt "$c_baseline" ]; then
    echo "VERDICT_GATE=refuse reason=lane-c-ratchet measured=$c_lines_now baseline=$c_baseline"
    echo "   the TCB script surface GREW by $((c_lines_now - c_baseline)) lines. It may shrink freely;"
    echo "   growth needs a dated rebase: scripts/verdict_set.py --rebase-up \"<why>\""
    return 1
  fi

  # -- P2b  the IO contract model: lane (b)'s obligation is "contract-modeled
  #         AND ledgered", so the model is a first-class input, validated the
  #         same way — never trusted because it says so about itself.
  local io_facts="" io_schema=""
  local -i io_present=0
  if [ -f "$io_artifact" ]; then
    io_present=1
    io_facts="$(extract_io_facts "$io_artifact")"
    iofact() { printf '%s\n' "$io_facts" | awk -F'\t' -v k="$1" '$1==k{print $2; exit}'; }

    io_schema="$(iofact io_schema)"
    if [ -n "$io_schema" ] && [ "$io_schema" != "$IO_SCHEMA_EXPECTED" ]; then
      echo "VERDICT_GATE=refuse reason=io-contracts-schema-mismatch got=$io_schema want=$IO_SCHEMA_EXPECTED"
      return 1
    fi
    local io_fatal
    io_fatal="$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="iofatal"{print $2"\t"$3}')"
    if [ -n "$io_fatal" ]; then
      echo "VERDICT_GATE=refuse reason=$(printf '%s' "$io_fatal" | cut -f1) detail=$(printf '%s' "$io_fatal" | cut -f2)"
      return 1
    fi
    if [ -z "$io_schema" ]; then
      echo "VERDICT_GATE=refuse reason=io-contracts-schema-mismatch got=<none> want=$IO_SCHEMA_EXPECTED"
      return 1
    fi

    # The model must have been derived over the SAME BYTES this gate is reading.
    local io_src io_src_sha artifact_sha
    io_src="$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="io_source"{print $2; exit}')"
    io_src_sha="$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="io_source"{print $3; exit}')"
    artifact_sha="$(sha256_of "$artifact")"
    if [ "$io_src_sha" != "$artifact_sha" ]; then
      echo "VERDICT_GATE=refuse reason=io-contracts-stale source=$io_src"
      echo "   the IO contract model was minted against ${io_src_sha:0:12}, this gate is reading ${artifact_sha:0:12}."
      echo "   A model of a surface that has since moved describes a surface nobody is running."
      echo "   re-mint: scripts/verdict_io_contracts.py"
      return 1
    fi

    local -i io_sites io_unclassified
    io_sites="$(iofact io_sites)"; io_unclassified="$(iofact io_unclassified)"
    local -i b_io_committed; b_io_committed="$(fact b_io_sites)"
    if [ "$io_sites" -ne "$b_io_committed" ]; then
      echo "VERDICT_GATE=refuse reason=io-contracts-denominator-drift model=$io_sites partition=$b_io_committed"
      echo "   the partition and its contract model disagree about how many IO sites exist. Two artifacts"
      echo "   counting the same thing differently is exactly what a partition exists to remove."
      return 1
    fi
    if [ "$io_unclassified" -ne 0 ]; then
      echo "VERDICT_GATE=refuse reason=io-contracts-unclassified count=$io_unclassified"
      echo "   a site with no effect class is an UNMODELLED boundary wearing a modelled artifact's name."
      return 1
    fi

    local bad_rows
    bad_rows="$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="iorowbad"{print "      "$2" is missing: "$3}')"
    if [ -n "$bad_rows" ]; then
      echo "VERDICT_GATE=refuse reason=io-contracts-row-incomplete"
      echo "   program §3.6 requires statement, probe, discharge, date and owning job on EVERY row:"
      printf '%s\n' "$bad_rows"
      return 1
    fi

    local -i io_rows io_row_baseline
    io_rows="$(iofact io_rows)"; io_row_baseline="$(iofact io_row_baseline)"
    if [ "$io_rows" -gt "$io_row_baseline" ]; then
      echo "VERDICT_GATE=refuse reason=io-contracts-row-ratchet measured=$io_rows baseline=$io_row_baseline"
      echo "   the assumption ledger GREW by $((io_rows - io_row_baseline)) row(s). It may shrink freely;"
      echo "   growth needs a dated rebase: scripts/verdict_io_contracts.py --rebase-up \"<why>\""
      return 1
    fi
  fi

  # -- P3..P5  the three partitions, each with its own ledger of what it owes
  local -i a_members a_chained b_members b_ledgered b_io b_separated c_members c_undemo c_undemo_st c_tcb c_rust
  a_members="$(fact a_members)"; a_chained="$(fact a_chained)"
  b_members="$(fact b_members)"; b_ledgered="$(fact b_ledgered)"; b_io="$(fact b_io_sites)"
  b_separated="$(fact b_separated)"
  c_members="$(fact c_members)"; c_undemo="$(fact c_undemo)"
  c_undemo_st="$(fact c_undemo_selftest)"
  c_tcb="$(fact c_tcb)"; c_rust="$(fact c_rust)"

  dep_present() { printf '%s\n' "$facts" | awk -F'\t' -v k="$1" '$1=="dep" && $2==k{print $3; exit}'; }
  local spine_present ledger_present
  spine_present="$(dep_present data/spine_set.json)"
  ledger_present="$(dep_present data/spine_assumption_ledger.json)"
  local closure_limited; closure_limited="$(fact closure_limit)"

  echo "VERDICT_GATE  Ring R2 — verdict paths, partitioned honestly"
  echo "              artifact: $artifact ($schema)"
  echo "              claim:    every path that could mint a false verdict WITH a proved kernel is"
  echo "                        enumerated, partitioned, and discharged in its lane."
  echo ""

  # ---- partition (a) -------------------------------------------------------
  local -i a_owes=0
  local a_lines=""
  if [ "$spine_present" != "1" ]; then
    a_owes=$((a_owes + 1))
    a_lines="$a_lines
      owes A1  data/spine_set.json is ABSENT (data/spine_set.PENDING.md records why: no post-a5aae3bde
               whole-crate dump exists). Lane (a)'s obligation is 'chained with the spine recipe' — the
               recipe quantifies over a spine set that has not been minted."
  else
    a_lines="$a_lines
      met  A1  data/spine_set.json is committed"
  fi
  if [ "$a_chained" -lt "$a_members" ]; then
    a_owes=$((a_owes + 1))
    a_lines="$a_lines
      owes A2  chains: $a_chained/$a_members members carry the five links. Every unchained member is a body
               that can mint a verdict with nothing proved about it."
  else
    a_lines="$a_lines
      met  A2  chains: $a_chained/$a_members"
  fi
  if [ "$closure_limited" = "1" ]; then
    a_owes=$((a_owes + 1))
    a_lines="$a_lines
      owes A3  membership is a module-granularity REFERENCE closure, not the per-body CALL closure: it can
               carry bodies no verdict path reaches and MISS a body reached only through a dyn/fn-pointer
               edge. Closing it needs the same trust-host whole-crate dump G-SPINE-SET is waiting on."
  fi
  while IFS=$'\t' read -r _ cid owed; do
    [ -n "$cid" ] || continue
    a_owes=$((a_owes + 1))
    a_lines="$a_lines
      owes A4  scope gap $cid: $owed"
  done <<< "$(printf '%s\n' "$facts" | awk -F'\t' '$1=="owed"')"
  if [ "$a_owes" -eq 0 ]; then
    earned=$((earned + 1))
    printf '[a] pure-Rust verdict code ........... EARNED           %d members\n' "$a_members"
  else
    refusals="$refusals a"
    printf '[a] pure-Rust verdict code ........... NOT-YET-EARNED   %d members, %d chained\n' "$a_members" "$a_chained"
  fi
  printf '%s\n' "$a_lines"

  # ---- partition (b) -------------------------------------------------------
  # The obligation is "contract-modeled AND ledgered". Those are two different
  # things and this ledger keeps them apart: B1/B2 are the MODEL (which exists,
  # and says what is assumed), B4 is the LEDGER's own ratchet, B3 is the
  # separation refactor, and B5 is the only line that could ever say the
  # contracts are EARNED — which none of them are.
  local -i b_owes=0
  local b_lines=""
  if [ "$io_present" != "1" ]; then
    b_owes=$((b_owes + 1))
    b_lines="$b_lines
      owes B1  data/verdict_io_contracts.json is ABSENT: lane (b)'s 211 IO sites are not contract-modeled at
               all. Mint it: scripts/verdict_io_contracts.py"
  else
    local -i io_issuing io_noio io_declonly io_content io_success
    io_issuing="$(iofact io_issuing)"; io_noio="$(iofact io_noio)"; io_declonly="$(iofact io_declonly)"
    io_content="$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="io_dep" && $2=="content-bearing"{print $3; exit}')"
    io_success="$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="io_dep" && $2=="success-only"{print $3; exit}')"
    b_lines="$b_lines
      met  B1  the IO boundary IS contract-modeled: data/verdict_io_contracts.json, minted over the same
               bytes this gate is reading, classifies all $io_sites sites with 0 unclassified —
               $io_issuing issue IO ($io_content content-bearing, $io_success success-only) and $io_noio issue none."
  fi

  # B2: one line per modelled contract. A contract nothing fully checks is an
  # UNEARNED contract, whatever its check_strength says, so every row below is
  # an `owes` — but an `owes` that names a statement, a count and a probe.
  if [ "$io_present" = "1" ]; then
    local contract_lines=""
    local -i unearned_contracts=0
    while IFS=$'\t' read -r _ cid dep sites members strength checks holes title; do
      [ -n "$cid" ] || continue
      if [ "$strength" = "full" ]; then
        contract_lines="$contract_lines
      met  B2.$cid  $sites site(s) in $members member(s) · $dep · $checks cited check(s) cover it"
        continue
      fi
      unearned_contracts=$((unearned_contracts + 1))
      local checked_txt
      if [ "$strength" = "none" ]; then
        checked_txt="NOTHING checks it"
      else
        checked_txt="$checks cited check(s), $holes cited hole(s) — PARTIAL, so unearned"
      fi
      contract_lines="$contract_lines
      owes B2.$cid  $sites site(s) in $members member(s) · $dep
               \"$title\"
               $checked_txt
               probe: scripts/verdict_io_contracts.py --sites $cid"
    done <<< "$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="iocontract"')"
    if [ "$unearned_contracts" -gt 0 ]; then
      b_owes=$((b_owes + 1))
      b_lines="$b_lines
      owes B2  $unearned_contracts modelled contract(s) are not fully checked. Each is a statement the verdict path
               assumes about what the filesystem, a subprocess or the environment handed back:$contract_lines"
    else
      b_lines="$b_lines
      met  B2  every modelled contract is fully checked:$contract_lines"
    fi
    # measured absences are stated, so silence cannot be read as coverage
    while IFS=$'\t' read -r _ aid n atitle; do
      [ -n "$aid" ] || continue
      b_lines="$b_lines
      note $aid  measured $n site(s): \"$atitle\" — a stated NEGATIVE, not a silence (see its caveat)"
    done <<< "$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="ioabsent"')"
  else
    b_owes=$((b_owes + 1))
    b_lines="$b_lines
      owes B2  no contract model, so no contract statement exists for any of the $b_io measured IO sites."
  fi

  if [ "$b_separated" -lt "$b_members" ]; then
    b_owes=$((b_owes + 1))
    local declnote=""
    if [ "$io_present" = "1" ]; then
      declnote="
               MEASURED, and it is not zero: $io_declonly of $b_members member(s) issue NO IO at all — every token
               hit in them is an import, a type or an error value. That part of the split is already true and
               had simply never been counted; the refactor is owed for the rest."
    fi
    b_lines="$b_lines
      owes B3  separation: $b_separated/$b_members members record a decode-pure / read-IO split. 'Decode-pure
               separated from read-IO where feasible' is a REFACTOR obligation: lane (b) as it stands is the
               MEASURED IO surface, not the separated one.$declnote"
  else
    b_lines="$b_lines
      met  B3  separation: $b_separated/$b_members"
  fi

  if [ "$io_present" = "1" ]; then
    if [ "$io_rows" -gt 0 ]; then
      local rowline=""
      while IFS=$'\t' read -r _ cid n; do
        [ -n "$cid" ] || continue
        rowline="$rowline $cid=$n"
      done <<< "$(printf '%s\n' "$io_facts" | awk -F'\t' '$1=="iorowcount"')"
      b_owes=$((b_owes + 1))
      b_lines="$b_lines
      owes B4  the §3.6 assumption ledger holds $io_rows row(s) (baseline $io_row_baseline, direction DOWN):$rowline
               Every row is an unproved thing a verdict stands on, with a statement, a probe, a discharge
               condition, a date and an owning job. A complete, probed ledger is what B1 buys; an EMPTY one
               is what discharging lane (b) would mean. (data/verdict_set.json's own ledgered_count reads
               $b_ledgered/$b_members because that field counts rows carried INSIDE the partition artifact, which is
               not where these rows live.)"
    else
      b_lines="$b_lines
      met  B4  the §3.6 assumption ledger is EMPTY: nothing unproved is assumed at this boundary"
    fi
  fi

  if [ "$ledger_present" != "1" ]; then
    b_owes=$((b_owes + 1))
    b_lines="$b_lines
      owes B5  data/spine_assumption_ledger.json is ABSENT: the program-wide §3.6 ledger these rows must
               eventually live in does not exist yet, so lane (b)'s rows are carried in their own artifact
               and are not counted by spine_gate's ratchet."
  else
    b_lines="$b_lines
      met  B5  data/spine_assumption_ledger.json exists"
  fi

  if [ "$b_owes" -eq 0 ]; then
    earned=$((earned + 1))
    printf '[b] IO-bearing Rust ................. EARNED           %d members\n' "$b_members"
  else
    refusals="$refusals b"
    printf '[b] IO-bearing Rust ................. NOT-YET-EARNED   %d members, %d IO sites, %d contracts, %d ledger rows\n' \
      "$b_members" "$b_io" "${unearned_contracts:-0}" "${io_rows:-0}"
  fi
  printf '%s\n' "$b_lines"

  # ---- partition (c) -------------------------------------------------------
  local -i c_owes=0
  local c_lines_txt=""
  c_lines_txt="$c_lines_txt
      met  C1  digests: $c_seen/$c_members claim-owning scripts re-hashed from the tree, all matching"
  c_lines_txt="$c_lines_txt
      met  C2  line ratchet: $c_lines_now <= baseline $c_baseline (direction: down; rises only by dated rebase)"
  c_lines_txt="$c_lines_txt
      met  C3  disposition: $c_rust rewritten-to-rust + $c_tcb tcb-declared = $c_members (Ring R2 admits no third state)"
  if [ "$c_undemo" -gt 0 ]; then
    c_owes=$((c_owes + 1))
    c_lines_txt="$c_lines_txt
      owes C4  $c_undemo of $c_members claim-owning scripts have NEITHER a demonstration nor a waiver in
               data/gate_registry.json ($c_undemo_st of them DO carry a --self-test entry point, which is a
               place a demonstration could run, not a demonstration). A gate nobody has seen refuse is an
               unearned claim, and declaring it TCB pins its bytes without earning its verdict."
  else
    c_lines_txt="$c_lines_txt
      met  C4  every claim-owning member is demonstrated or waived"
  fi
  if [ "$c_owes" -eq 0 ]; then
    earned=$((earned + 1))
    printf '[c] claim-owning script surface ..... EARNED           %d members, %d lines\n' "$c_members" "$c_lines_now"
  else
    refusals="$refusals c"
    printf '[c] claim-owning script surface ..... NOT-YET-EARNED   %d members, %d lines\n' "$c_members" "$c_lines_now"
  fi
  printf '%s\n' "$c_lines_txt"
  echo ""

  if [ "$earned" -eq 3 ]; then
    echo "VERDICT_GATE=ok earned=3/3"
    return 0
  fi
  echo "VERDICT_GATE=refuse earned=$earned/3 not-yet-earned=$(echo $refusals | tr ' ' ',')"
  echo "   Ring R2's gate is RED because Ring R2's work is not done. Nothing above is a gate defect:"
  echo "   every line is a named obligation with a named artifact behind it."
  return 1
}

# ---------------------------------------------------------------------------
# self-test: synthesized artifacts, one arm per refusal path plus a GREEN arm
# ---------------------------------------------------------------------------
self_test() {
  # NOT `local`: the EXIT trap fires after this function returns, and under
  # `set -u` a trap that dereferences an out-of-scope local aborts the shell.
  td="$(mktemp -d)"
  trap 'rm -rf "${td:-}"' EXIT
  local -i failures=0 passes=0
  mkdir -p "$td/data" "$td/scripts"
  printf '#!/bin/sh\nexit 0\n' > "$td/scripts/demo_gate.sh"
  printf '{"rows":[]}\n' > "$td/data/pinned_input.json"

  make_artifact() {
    # $1 out, $2 a_chained/a_members mode ("unmet"|"met")
    "$PYTHON_BIN" - "$td" "$1" "$2" <<'PY'
import hashlib, json, sys
td, out, mode = sys.argv[1], sys.argv[2], sys.argv[3]
def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()
gate = f"{td}/scripts/demo_gate.sh"
lines = len(open(gate).read().splitlines())
met = mode == "met"
doc = {
 "schema": "clean.verdict_set/v1",
 "derivation": {
   "input_pins": {"data/pinned_input.json": sha(f"{td}/data/pinned_input.json")},
   "closure_limit": "" if met else "reference closure, not a call closure",
 },
 "partitions": {
   "a_pure_rust": {"member_count": 2, "chained_count": 2 if met else 0, "members": []},
   "b_io_bearing": {"member_count": 1, "ledgered_count": 1 if met else 0,
                    "separated_count": 1 if met else 0,
                    "io_site_total": 0 if met else 7, "members": []},
   "c_script_surface": {
     "member_count": 1, "tcb_declared_count": 1, "rewritten_to_rust_count": 0,
     "undemonstrated_unwaived_count": 0 if met else 1,
     "line_ratchet": {"baseline_total_lines": lines, "measured_total_lines": lines},
     "members": [{"path": "scripts/demo_gate.sh", "sha256": sha(gate), "lines": lines,
                  "disposition": "tcb-declared"}],
   },
 },
 "evidence": {
   "artifacts_this_surface_depends_on": {
     "data/spine_set.json": met, "data/spine_assumption_ledger.json": met},
   "corrections": ([] if met else [{"id": "scope-gap", "owed": "a scope decision"}]),
 },
}
if met:
    doc["partitions"]["b_io_bearing"]["members"] = []
json.dump(doc, open(out, "w"), indent=1)
PY
  }

  # The IO contract model, synthesized to match a given verdict_set artifact.
  # `mode` met  -> one FULLY-checked contract, empty ledger (lane (b) earnable)
  #        unmet-> one unchecked contract, one probed ledger row
  make_io_artifact() {
    # $1 out, $2 mode, $3 the verdict_set artifact it claims to model
    "$PYTHON_BIN" - "$1" "$2" "$3" <<'PY'
import hashlib, json, sys
out, mode, src = sys.argv[1], sys.argv[2], sys.argv[3]
met = mode == "met"
sites = json.load(open(src))["partitions"]["b_io_bearing"]["io_site_total"]
doc = {
 "schema": "clean.verdict_io_contracts/v1",
 "derivation": {
   "source_artifact": src,
   "source_artifact_sha256": hashlib.sha256(open(src, "rb").read()).hexdigest(),
 },
 "classification": {
   "site_total": sites, "sites_issuing_io": sites, "sites_issuing_no_io": 0,
   "unclassified": 0,
   "by_dependence": {"content-bearing": sites} if sites else {},
   "declaration_only_members": {"count": 0},
 },
 "contracts": [{
   "id": "C-SYNTH", "title": "the bytes read are the bytes",
   "dependence": "content-bearing", "site_count": sites, "member_count": 1,
   "check_strength": "full" if met else "none",
   "checked_by": ([{"file": "x", "pattern": "y", "lines": [1], "what": "z"}] if met else []),
   "holes": ([] if met else [{"file": "x", "pattern": "y", "lines": [1], "what": "z"}]),
 }],
 "measured_absent": [{"id": "C-NET-DIRECT", "title": "no sockets", "measured_sites": 0}],
 "ledger": {
   "row_count": 0 if met else 1,
   "rows_by_contract": ({} if met else {"C-SYNTH": 1}),
   "row_ratchet": {"baseline_rows": 0 if met else 1, "measured_rows": 0 if met else 1},
   "rows": ([] if met else [{
     "id": "L-SYNTH", "contract": "C-SYNTH", "class": "content-bearing",
     "statement": "s", "probe": "p", "discharge": "d",
     "date": "2026-08-26", "owning_job": "R2b-SYNTH"}]),
 },
 "recommendations": [],
}
json.dump(doc, open(out, "w"), indent=1)
PY
  }

  arm() { # arm <name> <expect-rc> <expect-substring> <artifact> [io-artifact]
    local name="$1" want_rc="$2" want="$3" art="$4" io="${5:-$td/data/verdict_io_contracts.json}"
    local out rc
    out="$(gate_run "$art" "$td" "$io" 2>&1)"; rc=$?
    if [ "$rc" -ne "$want_rc" ]; then
      echo "  FAIL  $name: rc=$rc want=$want_rc" >&2; failures=$((failures + 1)); return
    fi
    case "$out" in
      *"$want"*) echo "  PASS  $name"; passes=$((passes + 1)) ;;
      *) echo "  FAIL  $name: output lacks '$want'" >&2
         printf '%s\n' "$out" | sed 's/^/        /' >&2
         failures=$((failures + 1)) ;;
    esac
  }

  arm "refusal: artifact absent" 1 "reason=artifact-absent" "$td/data/nope.json"
  printf 'not json at all\n' > "$td/data/bad.json"
  arm "refusal: artifact not JSON" 1 "reason=artifact-malformed" "$td/data/bad.json"
  printf '{"schema":"other/v1","partitions":{},"evidence":{},"derivation":{}}\n' > "$td/data/schema.json"
  arm "refusal: wrong schema" 1 "reason=schema-mismatch" "$td/data/schema.json"

  make_artifact "$td/data/unmet.json" unmet
  arm "refusal: unmet partitions name what they owe" 1 "owes A1" "$td/data/unmet.json"
  arm "refusal: an ABSENT contract model is an 'owes B1', not a crash" 1 "owes B1" \
      "$td/data/unmet.json" "$td/data/no-such-model.json"
  arm "refusal: the ledger names undemonstrated claim owners" 1 "owes C4" "$td/data/unmet.json"
  arm "refusal: partition (c)'s met sub-obligations still print" 1 "met  C1" "$td/data/unmet.json"

  # ---- the IO contract model: lane (b)'s refusal names CONTRACTS -------------
  make_io_artifact "$td/data/io_unmet.json" unmet "$td/data/unmet.json"
  arm "refusal: lane (b) names a CONTRACT, not a partition" 1 "owes B2.C-SYNTH" \
      "$td/data/unmet.json" "$td/data/io_unmet.json"
  arm "refusal: the contract line carries its probe command" 1 "verdict_io_contracts.py --sites C-SYNTH" \
      "$td/data/unmet.json" "$td/data/io_unmet.json"
  arm "refusal: the §3.6 ledger row count is named" 1 "owes B4" \
      "$td/data/unmet.json" "$td/data/io_unmet.json"
  arm "refusal: the missing program-wide §3.6 ledger is its own row" 1 "owes B5" \
      "$td/data/unmet.json" "$td/data/io_unmet.json"
  arm "refusal: a PRESENT model is a met sub-obligation inside a refusing partition" 1 "met  B1" \
      "$td/data/unmet.json" "$td/data/io_unmet.json"
  arm "refusal: a measured ABSENCE is stated, so silence cannot mean coverage" 1 "note C-NET-DIRECT" \
      "$td/data/unmet.json" "$td/data/io_unmet.json"

  printf 'not json at all\n' > "$td/data/io_bad.json"
  arm "refusal: the contract model is not JSON" 1 "reason=io-contracts-malformed" \
      "$td/data/unmet.json" "$td/data/io_bad.json"
  printf '{"schema":"other/v1"}\n' > "$td/data/io_schema.json"
  arm "refusal: the contract model has the wrong schema" 1 "reason=io-contracts-schema-mismatch" \
      "$td/data/unmet.json" "$td/data/io_schema.json"

  # minted against bytes that have since moved
  cp "$td/data/unmet.json" "$td/data/unmet_moved.json"
  printf '\n' >> "$td/data/unmet_moved.json"
  arm "refusal: the model was minted against other bytes" 1 "reason=io-contracts-stale" \
      "$td/data/unmet_moved.json" "$td/data/io_unmet.json"

  patch_io() { # patch_io <src> <dst> <python-expr over `doc`>
    "$PYTHON_BIN" - "$1" "$2" "$3" <<'PY'
import json, sys
doc = json.load(open(sys.argv[1]))
exec(sys.argv[3])  # noqa: S102 - self-test mutation arm, literal from this file
json.dump(doc, open(sys.argv[2], "w"), indent=1)
PY
  }
  patch_io "$td/data/io_unmet.json" "$td/data/io_denom.json" \
    'doc["classification"]["site_total"] += 1'
  arm "refusal: model and partition disagree on the site count" 1 "reason=io-contracts-denominator-drift" \
      "$td/data/unmet.json" "$td/data/io_denom.json"
  patch_io "$td/data/io_unmet.json" "$td/data/io_unclass.json" \
    'doc["classification"]["unclassified"] = 3'
  arm "refusal: a site with no effect class" 1 "reason=io-contracts-unclassified" \
      "$td/data/unmet.json" "$td/data/io_unclass.json"
  patch_io "$td/data/io_unmet.json" "$td/data/io_noprobe.json" \
    'doc["ledger"]["rows"][0].pop("probe")'
  arm "refusal: a §3.6 row without a probe" 1 "reason=io-contracts-row-incomplete" \
      "$td/data/unmet.json" "$td/data/io_noprobe.json"
  patch_io "$td/data/io_unmet.json" "$td/data/io_ratchet.json" \
    'doc["ledger"]["row_ratchet"]["baseline_rows"] = 0'
  arm "refusal: the assumption ledger GREW" 1 "reason=io-contracts-row-ratchet" \
      "$td/data/unmet.json" "$td/data/io_ratchet.json"

  # a pinned input that moved
  printf '{"rows":[1]}\n' > "$td/data/pinned_input.json"
  arm "refusal: a pinned derivation input moved" 1 "reason=pin-stale" "$td/data/unmet.json"
  printf '{"rows":[]}\n' > "$td/data/pinned_input.json"

  # a lane (c) script edited under the pin
  printf '#!/bin/sh\nexit 1\n' > "$td/scripts/demo_gate.sh"
  arm "refusal: a lane (c) script drifted from its digest" 1 "reason=lane-c-digest-drift" "$td/data/unmet.json"
  printf '#!/bin/sh\nexit 0\n' > "$td/scripts/demo_gate.sh"

  # the ratchet
  make_artifact "$td/data/ratchet.json" met
  printf '#!/bin/sh\necho a\necho b\necho c\nexit 0\n' > "$td/scripts/demo_gate.sh"
  "$PYTHON_BIN" - "$td" <<'PY'
import hashlib, json, sys
td = sys.argv[1]
p = f"{td}/data/ratchet.json"
doc = json.load(open(p))
gate = f"{td}/scripts/demo_gate.sh"
doc["partitions"]["c_script_surface"]["members"][0]["sha256"] = hashlib.sha256(open(gate, "rb").read()).hexdigest()
json.dump(doc, open(p, "w"), indent=1)
PY
  arm "refusal: the lane (c) line ratchet is exceeded" 1 "reason=lane-c-ratchet" "$td/data/ratchet.json"
  printf '#!/bin/sh\nexit 0\n' > "$td/scripts/demo_gate.sh"

  # a pinned member deleted
  make_artifact "$td/data/met.json" met
  make_io_artifact "$td/data/io_met.json" met "$td/data/met.json"
  mv "$td/scripts/demo_gate.sh" "$td/scripts/moved.sh"
  arm "refusal: a pinned claim-owning script vanished" 1 "reason=lane-c-member-absent" \
      "$td/data/met.json" "$td/data/io_met.json"
  mv "$td/scripts/moved.sh" "$td/scripts/demo_gate.sh"

  # a fully-discharged partition (a)+(c) but an UNEARNED contract in (b): the
  # gate must still refuse, and only lane (b) may appear in not-yet-earned.
  make_io_artifact "$td/data/io_met_unmet_b.json" unmet "$td/data/met.json"
  arm "refusal: one unearned contract alone keeps the gate red" 1 "not-yet-earned=b" \
      "$td/data/met.json" "$td/data/io_met_unmet_b.json"

  # THE GREEN ARM: the gate is not hardwired to refuse
  make_artifact "$td/data/met.json" met
  make_io_artifact "$td/data/io_met.json" met "$td/data/met.json"
  arm "green: a fully-discharged artifact EARNS 3/3 (rc=0)" 0 "VERDICT_GATE=ok earned=3/3" \
      "$td/data/met.json" "$td/data/io_met.json"

  if [ "$failures" -gt 0 ]; then
    echo "VERDICT_GATE self-test: $failures arm(s) RED" >&2
    return 1
  fi
  echo "VERDICT_GATE self-test: $passes arms, all green"
  return 0
}

if [ "$SELF_TEST" -eq 1 ]; then
  self_test
  exit $?
fi

gate_run "$ARTIFACT" "$ROOT" "$IO_ARTIFACT"
exit $?
