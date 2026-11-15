#!/usr/bin/env bash
# Census of the build output directories under target/: entry counts per
# `deps` directory, and (with --du) sizes. NOT a gate — it never fails the
# tree; it exists because a bloated deps directory is invisible until every
# compile is slow.
#
# WHY. Measured 2026-09-07: `target/debug/deps` held 2,340,398 entries
# (285 GB). rustc enumerates every `-L dependency=` directory at startup
# (`rustc_session::search_paths::SearchPath::new` -> `std::fs::read_dir`), so
# EVERY compiler unit that targeted `target/debug` spent ~45 s in
# `__getdirentries64` before compiling a line — sampled with `sample <pid>`
# on a `trustc` sitting in I/O wait; a trivial `trustc` with no -L took 1.3 s.
# A `targo --unverified check --workspace` that crawled at ~2 units/min
# against that directory finished all 355 units in 5m28s against a fresh one.
# The shared directory grows because many lanes with different RUSTFLAGS /
# feature sets share it and nothing collects the stale hashes.
#
# WHAT THE ENTRIES WERE. Of the 2,340,398: 2,308,682 (98.6%) were `*.rcgu.o`
# codegen-unit objects, 13,039 `.d`, 12,087 `.rmeta`, 5,654 `.rlib`, 436
# `.dylib`, across 1,939 distinct crate/target stems (`clean_elab` alone
# 301,675). macOS's default dev profile passes `-C split-debuginfo=unpacked`,
# which keeps every CGU object beside each test/bin it links so lldb can find
# the DWARF; nothing ever collects them, so ~12k compiled units left ~190
# objects each. Deleting stale `.rcgu.o` files is safe: cargo's fingerprints do
# not depend on them and the linked binaries keep running — only debugging a
# binary older than the prune loses its DWARF. Stopping the retention at the
# source (`[profile.dev] split-debuginfo = "packed"` or `debug =
# "line-tables-only"`) is an OWNER decision: it changes every lane's
# fingerprints and debugging experience, so this script prunes instead.
#
# Usage:  scripts/target_census.sh                     # entry counts (fast: O(entries))
#         scripts/target_census.sh --du                # also sizes (slow on big trees)
#         scripts/target_census.sh --prune-objects 7   # delete deps/*.rcgu.o older than 7 days
#         TARGET_CENSUS_WARN=50000 scripts/target_census.sh
# --prune-objects refuses while any compiler is running (a unit could be
# linking against the objects it would delete) and never touches anything but
# `*.rcgu.o` directly inside a `deps` directory.
set -euo pipefail
root="${CARGO_TARGET_DIR:-$(cd "$(dirname "$0")/.." && pwd)/target}"
warn_at="${TARGET_CENSUS_WARN:-100000}"
do_du=0; prune_days=""
case "${1:-}" in
  --du) do_du=1 ;;
  --prune-objects) prune_days="${2:-}"; [[ "$prune_days" =~ ^[0-9]+$ ]] || { echo "target_census: --prune-objects needs a whole number of days" >&2; exit 2; } ;;
  "") ;;
  *) echo "target_census: unknown argument $1" >&2; exit 2 ;;
esac
[ -d "$root" ] || { echo "target_census: no $root"; exit 0; }
if [ -n "$prune_days" ]; then
  if pgrep -qf '(^|/)(rustc|trustc|cargo|targo)( |$)'; then
    echo "target_census: REFUSING to prune while a compiler or driver is running:" >&2
    pgrep -fl '(^|/)(rustc|trustc|cargo|targo)( |$)' | cut -c1-100 >&2
    exit 3
  fi
  total=0
  for deps in "$root"/*/deps/ "$root"/*/*/deps/; do
    [ -d "$deps" ] || continue
    n=$(find "$deps" -maxdepth 1 -name '*.rcgu.o' -mtime +"$prune_days" -print -delete | wc -l | tr -d ' ')
    printf '%-40s pruned %s stale .rcgu.o\n' "${deps#"$root"/}" "$n"
    total=$((total + n))
  done
  echo "target_census: pruned $total codegen-unit objects older than $prune_days days under $root"
  exit 0
fi
printf '%-40s %12s' "directory" "deps entries"; [ $do_du = 1 ] && printf ' %8s' "size"; printf '\n'
worst=0
for profile in "$root"/*/ "$root"/*/*/; do
  deps="$profile/deps"; [ -d "$deps" ] || continue
  rel="${profile#"$root"/}"; rel="${rel%/}"
  n=$(ls -f "$deps" | wc -l | tr -d ' ')
  printf '%-40s %12s' "$rel" "$n"
  if [ $do_du = 1 ]; then printf ' %8s' "$(du -sh "$profile" 2>/dev/null | cut -f1)"; fi
  if [ "$n" -gt "$warn_at" ]; then printf '   WARN: > %s entries — every unit pays a startup scan of this directory' "$warn_at"; fi
  printf '\n'
  [ "$n" -gt "$worst" ] && worst=$n
done
if [ "$worst" -gt "$warn_at" ]; then
  echo
  echo "target_census: a deps directory exceeds $warn_at entries. Give the lane its own"
  echo "  CARGO_TARGET_DIR (e.g. target/<lane>) or remove the profile directory when no"
  echo "  compiler is running (check scripts/heavy_gate.sh status first)."
fi
