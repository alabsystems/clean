#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Replay a lean4export NDJSON 3.1 export through a pinned Lean's own kernel.
#
# WHY. Unit Q1 of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md is done
# when Lean's kernel accepts an export Clean wrote
# (`clean_export_write`, crates/clean-olean/src/ndjson/write/). Toolchains
# before v4.35 ship no reader of the format. The default reader is
# scripts/lean_export_replay/Replay.lean, Clean's reading of the format written
# in Lean: it parses the records and hands the constants to
# `Lean.Environment.replay`, the engine of `leanchecker`, from an empty
# environment. `--reader upstream` parses with lean4export's own reader at the
# commit the mint script pins (below), so no step of the verdict is Clean's.
# Read each Lean file's header for what its verdict is and is not.
#
# WHAT IT DOES.
#   * The toolchain is the elan toolchain named like the tag; this lane never
#     installs one. Every Lean tool runs by absolute path under `env -i` with
#     PATH and LEAN_SYSROOT set to the toolchain (under aterm a bare `lean` is
#     Clean) and LEAN_ABORT_ON_PANIC=1.
#   * Replay.lean refuses an export whose `meta.lean` is not the Lean running
#     it (version and githash), exit 2: a verdict from another Lean's kernel
#     is not this export's.
#   * The run goes through scripts/heavy_gate.sh (label `lean-export-replay`,
#     2 GB by default: the 12.9 MB export of the theories/cic_l closure, 3856
#     declarations, peaked at 1.04 GB on 2026-11-12, and the gate raises a
#     weight under 1.3 x the label's recorded peak; --gate-gb for a larger
#     export), or runs directly under an enclosing reservation
#     (HEAVY_GATE_HELD).
#
#   * --reader upstream reads the export with lean4export's own parser
#     instead (`Export.parseStream`, lean4export `Export/Parse.lean`, through
#     scripts/lean_export_replay/Upstream.lean), so neither the parsing nor the
#     kernel is Clean's. The parser is taken from the lean4export checkout
#     scripts/lean_export_mint.sh builds for the toolchain (its cache,
#     `<cache>/lean4export/<tag>@<commit>`, or --upstream-checkout): the
#     checkout must pass the mint script's own `check_checkout` (the commit
#     it pins for the tag, no edit to a tracked file, the tag's
#     `lean-toolchain`), and its `Export/Parse.lean` is compiled by the
#     toolchain's own `lean -o` into a temporary directory for the run. No
#     checkout is fetched here; run the mint script once for the tag to make
#     one. The reader's commit and the sha256 of `Parse.lean` are printed on
#     stderr.
#
#   * --against <module> (repeatable; with --reader upstream, without
#     --permit) does not replay: scripts/lean_export_replay/Compare.lean
#     imports the modules with pinned Lean, from the --lean-path directories
#     (repeatable) and the toolchain's own library, and compares every
#     constant the export declares with Lean's own, field by field (that
#     file's header says what equal is). Exit 0 when all are present and
#     equal, 1 when one is absent or differs (listed in the JSON line).
#
# EXIT. 0 accepted (the last stdout line is one JSON object), 1 refused by the
# reader or by Lean's kernel or for an unpermitted axiom (with --against: a
# constant absent or different), 2 usage or an export this lane does not
# judge (or, with --reader upstream, no usable checkout), 75 the gate refused
# the reservation (not a verdict).
#
# USAGE
#   scripts/lean_export_replay.sh [--toolchain <v4.X.Y[-rcN]>] [--gate-gb <n>]
#       [--reader clean|upstream] [--upstream-checkout <dir>]
#       <export.ndjson> [--permit <axiom>]...
#   scripts/lean_export_replay.sh [--toolchain <tag>] [--gate-gb <n>]
#       --reader upstream [--upstream-checkout <dir>] <export.ndjson>
#       --against <module>... [--lean-path <dir>]...
# --toolchain defaults to the tag in theories/cic_l/lean-toolchain; --reader
# defaults to clean (Replay.lean).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"
REPLAYER="$SCRIPT_DIR/lean_export_replay/Replay.lean"

usage() {
  echo "usage: $0 [--toolchain <tag>] [--gate-gb <n>] [--reader clean|upstream] [--upstream-checkout <dir>] <export.ndjson> [--permit <axiom>]... | [--against <module>]... [--lean-path <dir>]..." >&2
  exit 2
}

toolchain=""
gate_gb=2
export_path=""
permits=()
reader=clean
checkout=""
against=()
lean_paths=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --toolchain) [ "$#" -ge 2 ] || usage; toolchain="$2"; shift 2 ;;
    --gate-gb) [ "$#" -ge 2 ] || usage; gate_gb="$2"; shift 2 ;;
    --permit) [ "$#" -ge 2 ] || usage; permits+=(--permit "$2"); shift 2 ;;
    --reader) [ "$#" -ge 2 ] || usage; reader="$2"; shift 2 ;;
    --upstream-checkout) [ "$#" -ge 2 ] || usage; checkout="$2"; shift 2 ;;
    --against) [ "$#" -ge 2 ] || usage; against+=("$2"); shift 2 ;;
    --lean-path) [ "$#" -ge 2 ] || usage; lean_paths+=("$2"); shift 2 ;;
    -h|--help) usage ;;
    -*) echo "lean_export_replay: unknown option $1" >&2; usage ;;
    *) [ -z "$export_path" ] || usage; export_path="$1"; shift ;;
  esac
done
[ -n "$export_path" ] || usage
case "$gate_gb" in ''|*[!0-9]*) echo "lean_export_replay: --gate-gb needs a number" >&2; exit 2 ;; esac
if [ ! -f "$export_path" ]; then
  echo "lean_export_replay: no export at $export_path" >&2
  exit 2
fi

if [ -z "$toolchain" ]; then
  pin="$(tr -d '[:space:]' < "$REPO_ROOT/theories/cic_l/lean-toolchain")"
  toolchain="${pin#leanprover/lean4:}"
fi
case "$toolchain" in
  v[0-9]*) ;;
  *) echo "lean_export_replay: --toolchain must be a tag like v4.30.0-rc2, got $toolchain" >&2; exit 2 ;;
esac
tcdir="${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---$toolchain"
if [ ! -x "$tcdir/bin/lean" ]; then
  echo "lean_export_replay: no executable $tcdir/bin/lean (this lane never installs a toolchain; use elan)" >&2
  exit 2
fi

case "$reader" in
  clean) [ -z "$checkout" ] || { echo "lean_export_replay: --upstream-checkout needs --reader upstream" >&2; exit 2; } ;;
  upstream) ;;
  *) echo "lean_export_replay: --reader must be clean or upstream, got $reader" >&2; exit 2 ;;
esac
if [ "${#against[@]}" -gt 0 ]; then
  [ "$reader" = upstream ] || { echo "lean_export_replay: --against needs --reader upstream" >&2; exit 2; }
  [ "${#permits[@]}" -eq 0 ] || { echo "lean_export_replay: --against compares, it does not judge axioms: no --permit" >&2; exit 2; }
fi
if [ "${#lean_paths[@]}" -gt 0 ] && [ "${#against[@]}" -eq 0 ]; then
  echo "lean_export_replay: --lean-path needs --against" >&2; exit 2
fi
search=""
for dir in ${lean_paths[@]+"${lean_paths[@]}"}; do
  [ -d "$dir" ] || { echo "lean_export_replay: --lean-path $dir is not a directory" >&2; exit 2; }
  search="$search:$(cd "$dir" && pwd -P)"
done

run=(env -i "PATH=$tcdir/bin:/usr/bin:/bin" "LEAN_SYSROOT=$tcdir" "HOME=${HOME:-/}"
  "TMPDIR=${TMPDIR:-/tmp}" LEAN_ABORT_ON_PANIC=1)

if [ "$reader" = clean ]; then
  run+=("$tcdir/bin/lean" --run "$REPLAYER" "$export_path" ${permits[@]+"${permits[@]}"})
  if [ -n "${HEAVY_GATE_HELD:-}" ]; then
    exec "${run[@]}"
  fi
  exec "$REPO_ROOT/scripts/heavy_gate.sh" run "$gate_gb" lean-export-replay -- "${run[@]}"
fi

# --reader upstream: lean4export's own parser, from the mint script's pinned
# checkout (header).
commit="$(LEAN_EXPORT_MINT_LIB=1 bash -c '. "$1"; pinned_commit "$2"' sh \
  "$SCRIPT_DIR/lean_export_mint.sh" "$toolchain")"
if [ -z "$commit" ]; then
  echo "lean_export_replay: scripts/lean_export_mint.sh pins no lean4export commit for $toolchain" >&2
  exit 2
fi
if [ -z "$checkout" ]; then
  cache="${LEAN_EXPORT_MINT_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/clean-lean-export-mint}"
  checkout="$cache/lean4export/$toolchain@$commit"
fi
if [ ! -f "$checkout/Export/Parse.lean" ]; then
  echo "lean_export_replay: no lean4export checkout with Export/Parse.lean at $checkout; run scripts/lean_export_mint.sh --toolchain $toolchain --module Init.Prelude once to build one" >&2
  exit 2
fi
# The mint script's own check of a cached checkout: the pinned commit, no edit
# to a tracked file (its build stamp and `.lake` are untracked) and the
# toolchain's `lean-toolchain`. A refusal is printed by it and is exit 2 here.
if ! LEAN_EXPORT_MINT_LIB=1 bash -c '. "$1"; check_checkout "$2" "$3" "$4"' sh \
    "$SCRIPT_DIR/lean_export_mint.sh" "$checkout" "$toolchain" "$commit"; then
  echo "lean_export_replay: $checkout is not the pinned lean4export checkout for $toolchain" >&2
  exit 2
fi
parser_sha="$(shasum -a 256 "$checkout/Export/Parse.lean" | awk '{ print $1 }')"
echo "lean_export_replay: reader lean4export@$commit Export/Parse.lean sha256=$parser_sha" >&2
olean_dir="$(mktemp -d "${TMPDIR:-/tmp}/lean_export_replay.upstream.XXXXXX")"
trap 'rm -rf -- "${olean_dir:?}"' EXIT
mkdir -p "$olean_dir/Export"
if [ "${#against[@]}" -gt 0 ]; then
  leanfile="$SCRIPT_DIR/lean_export_replay/Compare.lean"
  rest=("$export_path" "${against[@]}")
else
  leanfile="$SCRIPT_DIR/lean_export_replay/Upstream.lean"
  rest=("$export_path" ${permits[@]+"${permits[@]}"})
fi
run+=("LEAN_PATH=$olean_dir$search" /bin/sh -c 'cd "$1" && "$2" -o "$3/Export/Parse.olean" Export/Parse.lean >&2 || exit 2
  shift 3 && exec "$@"' sh "$checkout" "$tcdir/bin/lean" "$olean_dir"
  "$tcdir/bin/lean" --run "$leanfile" "${rest[@]}")
rc=0
if [ -n "${HEAVY_GATE_HELD:-}" ]; then
  "${run[@]}" || rc=$?
else
  "$REPO_ROOT/scripts/heavy_gate.sh" run "$gate_gb" lean-export-replay -- "${run[@]}" || rc=$?
fi
exit "$rc"
