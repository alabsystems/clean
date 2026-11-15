#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Compare Clean's export of a module closure with lean4export's export of the
# same closure, pinned Lean's own exporter (self-proof unit Q1).
#
# WHAT IT DOES, in order, every step under scripts/heavy_gate.sh:
#   1. `clean_export_write` writes the cone of every loaded constant whose name
#      contains --containing (`clean-all.ndjson`): the selection the Q1 test
#      makes. It also supplies the full comparison against Lean in step 6.
#   2. The roots are the names that export declares which contain the text and
#      which lean4export's command line can name: a private name has a numeric
#      component no `--` argument can spell (lean_export_differential.py
#      `roots`). Both cones reach a private declaration a root uses.
#   3. `clean_export_write --target <root>...` writes the cone of exactly those
#      roots (`clean.ndjson`).
#   4. scripts/lean_export_mint.sh runs lean4export, built for --toolchain at
#      its pinned commit, over the same modules with --export-mdata and
#      `--decl <root>...` (`lean4export.ndjson`, with its sidecar).
#      --export-mdata keeps `mdata` nodes and each `letE`'s `nondep` as Lean
#      stores them; without it lean4export drops the nodes and writes every
#      `nondep` false, which Clean's writer, writing what the `.olean` holds,
#      does not.
#   5. scripts/lean_export_differential.py compares the two files, each read
#      on its own (no Clean code), and writes `verdict.json`.
#   6. scripts/lean_export_replay.sh --reader upstream --against <module>...
#      compares Clean's file with pinned Lean's own environment of the same
#      modules, constant by constant, the file parsed by lean4export's own
#      parser (`against-lean.json`). Step 5 cannot settle binder annotations
#      (lean4export writes a term equal to an earlier one up to annotations as
#      that earlier term; lean_export_differential.py's header); this step
#      can.
#
# Exit 0: both comparisons equal (step 5's normalization: binder names, mdata
# payloads, the `all` of a definition, a block's recursor order, indices and
# record order; step 6's: binder names and mdata payloads). Exit 1: a
# difference in either, listed in its verdict file (step 5 lists declarations
# that differ in binder annotations alone apart, and still exits 1), or a step
# failed (named on stderr). Exit 2: a usage error.
#
# USAGE
#   scripts/lean_export_differential.sh --toolchain v4.30.0-rc2 \
#       --writer <path to clean_export_write> --lean-path <dir>... \
#       --module <M>... --containing <text> --out-dir <dir> [--gate-gb <n>]
#   The first --lean-path entries hold the modules' .olean files; the pinned
#   toolchain's lib/lean must be among them (the writer loads `Init` from it).
#   --gate-gb sizes the lean4export mint (lean_export_mint.sh asks for it while
#   the module root's class is unmeasured).
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GATE="$HERE/heavy_gate.sh"
PY=(python3 -I "$HERE/lean_export_differential.py")
WRITE_GB=3

usage() { echo "lean_export_differential: $*" >&2; sed -n '/^# USAGE/,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d; s/^# \{0,1\}//' >&2; exit 2; }
fail() { echo "lean_export_differential: $*" >&2; exit 1; }

tc="" writer="" containing="" out="" gate_gb=""
modules=() lpath=()
while [ $# -gt 0 ]; do
  case "$1" in
    --toolchain|--writer|--lean-path|--module|--containing|--out-dir|--gate-gb)
      [ $# -ge 2 ] && [ -n "$2" ] || usage "$1 needs a value" ;;
  esac
  case "$1" in
    --toolchain) tc=$2; shift 2 ;;
    --writer) writer=$2; shift 2 ;;
    --lean-path) lpath+=("$2"); shift 2 ;;
    --module) modules+=("$2"); shift 2 ;;
    --containing) containing=$2; shift 2 ;;
    --out-dir) out=$2; shift 2 ;;
    --gate-gb) gate_gb=$2; shift 2 ;;
    -h|--help) usage "help" ;;
    *) usage "unknown argument '$1'" ;;
  esac
done
[ -n "$tc" ] || usage "--toolchain is required"
[ -x "$writer" ] || usage "--writer must name the clean_export_write binary"
[ "${#modules[@]}" -gt 0 ] || usage "at least one --module is required"
[ "${#lpath[@]}" -gt 0 ] || usage "at least one --lean-path is required"
[ -n "$containing" ] || usage "--containing is required"
[ -n "$out" ] || usage "--out-dir is required"
mkdir -p -- "$out"

lean="${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---$tc/bin/lean"
[ -x "$lean" ] || fail "no toolchain $tc at $lean"
version=$("$lean" --version | sed -n 's/^Lean (version \([^,]*\),.*/\1/p')
githash=$("$lean" --githash)
[ -n "$version" ] && [ -n "$githash" ] || fail "cannot read $lean's version and githash"

common=(--lean-version "$version" --lean-githash "$githash" --force)
for m in "${modules[@]}"; do common+=(--module "$m"); done
for p in "${lpath[@]}"; do common+=(--lean-path "$p"); done

# 1. every constant whose name contains the text, to list the roots
"$GATE" run "$WRITE_GB" lean-export-differential-write -- \
  "$writer" "${common[@]}" --targets-containing "$containing" --out "$out/clean-all.ndjson" \
  > "$out/clean-all.json" || fail "clean_export_write over --containing $containing failed (exit $?)"

# 2. the roots both command lines can name
"${PY[@]}" roots "$out/clean-all.ndjson" --containing "$containing" > "$out/roots.txt" \
  || fail "listing the roots failed (exit $?)"
"${PY[@]}" roots "$out/clean-all.ndjson" --containing "$containing" --quoted > "$out/roots-quoted.txt" \
  || fail "listing the quoted roots failed (exit $?)"
roots=() quoted=()
while IFS= read -r r; do roots+=("$r"); done < "$out/roots.txt"
while IFS= read -r r; do quoted+=("$r"); done < "$out/roots-quoted.txt"
[ "${#roots[@]}" -gt 0 ] || fail "no root: nothing nameable contains $containing"
[ "${#roots[@]}" -eq "${#quoted[@]}" ] || fail "the two root lists differ in length"

# 3. Clean's cone of exactly those roots
targets=()
for r in "${roots[@]}"; do targets+=(--target "$r"); done
"$GATE" run "$WRITE_GB" lean-export-differential-write -- \
  "$writer" "${common[@]}" "${targets[@]}" --out "$out/clean.ndjson" \
  > "$out/clean.json" || fail "clean_export_write over the roots failed (exit $?)"

# 4. lean4export's cone of the same roots
mint=(--toolchain "$tc" --export-mdata --out "$out/lean4export.ndjson" --force)
for m in "${modules[@]}"; do mint+=(--module "$m"); done
for p in "${lpath[@]}"; do mint+=(--lean-path "$p"); done
if [ -n "$gate_gb" ]; then mint+=(--gate-gb "$gate_gb"); fi
for r in "${quoted[@]}"; do mint+=(--decl "$r"); done
"$HERE/lean_export_mint.sh" "${mint[@]}" > "$out/mint.log" 2>&1 \
  || { tail -5 "$out/mint.log" >&2; fail "lean_export_mint.sh failed (see $out/mint.log)"; }

# 5. the comparison with lean4export
rc=0
"${PY[@]}" compare "$out/clean.ndjson" "$out/lean4export.ndjson" > "$out/verdict.json" || rc=$?
case "$rc" in
  0|1) ;;
  *) fail "the comparison could not read an export (exit $rc)" ;;
esac

# 6. the FULL export, including private names --decl cannot name, against Lean
against=(--toolchain "$tc" --reader upstream "$out/clean-all.ndjson")
for m in "${modules[@]}"; do against+=(--against "$m"); done
for p in "${lpath[@]}"; do against+=(--lean-path "$p"); done
if [ -n "$gate_gb" ]; then against+=(--gate-gb "$gate_gb"); fi
rc6=0
"$HERE/lean_export_replay.sh" "${against[@]}" > "$out/against-lean.out" 2> "$out/against-lean.err" || rc6=$?
case "$rc6" in
  0|1) tail -n 1 "$out/against-lean.out" > "$out/against-lean.json" ;;
  *) tail -5 "$out/against-lean.err" >&2; fail "the comparison with Lean's environment did not run (exit $rc6)" ;;
esac

python3 -I -c 'import json,sys
v=json.load(open(sys.argv[1]))
a=json.load(open(sys.argv[3]))
print(json.dumps({"verdict": v["verdict"], "roots": int(sys.argv[2]),
  "clean": {k: v["left"][k] for k in ("declarations","records","sha256","canonical_sha256")},
  "lean4export": {k: v["right"][k] for k in ("declarations","records","sha256","canonical_sha256")},
  "only_clean": v["only_left_count"], "only_lean4export": v["only_right_count"],
  "differing": v["differing_count"], "binder_info_only": v["binder_info_only_count"],
  "grouped_otherwise": v["grouped_otherwise_count"], "verdict_file": sys.argv[1],
  "against_lean": {k: a[k] for k in ("verdict","compared","equal","absent","differing_count","differing_by_field")},
  "against_lean_file": sys.argv[3]}))' "$out/verdict.json" "${#roots[@]}" "$out/against-lean.json"
[ "$rc" -eq 0 ] && [ "$rc6" -eq 0 ] || exit 1
exit 0
