#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Mint a lean4export NDJSON export with a pinned Lean toolchain, reproducibly.
#
# WHY. The NDJSON front door (`clean olean replay --from-export`,
# crates/clean-olean/src/ndjson/) and the plan items that feed it fixtures
# (plan item `checkers-export-minting-lane` in
# docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md) need exports that nothing here
# writes: the installed toolchains (v4.28.0..v4.33.1) ship no exporter, and the
# arena archive covers 193 files at 4.29.1. An export made by hand does not say
# which exporter commit, which Lean or which search path made it. This lane
# pins all three and records them beside the export.
#
# WHAT IT DOES.
#   * A toolchain mints only if the pin table below has a row for its tag, and
#     its `lean --githash` must be the lean4 commit that row records (upstream's
#     tag, from `git ls-remote`). A local or rebuilt Lean installed under an
#     upstream tag's name is refused, not recorded as that tag.
#   * Lean v4.35.0-rc1 and later ship the exporter as `<toolchain>/bin/leanexport`
#     (lean4 `src/LeanExport.lean`; `lake check` runs it). Measured 2026-10-28:
#     v4.34.0 has no `leanexport` CMake target, v4.35.0-rc1 has one.
#   * Earlier toolchains get github.com/leanprover/lean4export at the tag named
#     like the toolchain, fetched BY COMMIT from the pin table (never by a tag
#     that can move), checked (commit, clean tree, `lean-toolchain`) before and
#     after it is built with that toolchain's own `lake`, once per (tag,
#     commit), in a cache outside the repo (LEAN_EXPORT_MINT_CACHE, default
#     ~/.cache/clean-lean-export-mint). The finished build, its binary hashed
#     into a build stamp, is published into the cache by one rename(2), which
#     refuses a non-empty target, under an atomic mkdir lock (`<build>.lock`).
#   * Every Lean tool runs by absolute path under `env -i` with PATH and
#     LEAN_SYSROOT set to the toolchain: under aterm a bare `lean` is Clean, and
#     the exporter's `findSysroot` spawns `lean --print-prefix` unless
#     LEAN_SYSROOT is set. LEAN_ABORT_ON_PANIC=1, as `lake check` sets it: an
#     unknown declaration name is a `panic!` in the exporter's dumpConstant,
#     and without it the mint would exit 0 on a short export. --lean-path
#     reaches the exporter alone, never the cached exporter's build.
#   * --out is resolved and checked (neither it nor its sidecar a directory,
#     neither already there unless --force, its directory writable) before
#     anything is fetched or built, and the targets again under the publish
#     lock, just before the publish, whose link(2) refuses what appears after
#     that check (under --force the old export and sidecar are set aside first,
#     so nothing at --out is replaced by a rename).
#   * The exporter never writes the export. Its stdout goes to the python
#     half's `write`, which runs it, checks every write, the fsync and the
#     close, and refuses on any OSError: Lean's stdout is buffered, and a lost
#     tail (a full disk) still exits 0.
#   * The export is streamed, never loaded whole. Its first (meta) line is read
#     with the front door's shape rules (crates/clean-olean/src/ndjson/world.rs,
#     read_meta) and must state the requested Lean version, format 3.1.0,
#     exporter lean4export, and the toolchain's own `lean --githash`. Every
#     later line must end in a newline and be a record the front door's
#     dispatch reads (crates/clean-olean/src/ndjson/source.rs): a one-key
#     declaration (axiom, def, thm, opaque, quot, inductive) or a
#     Name/Level/Expr primitive (exactly one of in/il/ie, an index, plus one
#     known variant). The last record must be a declaration: lean4export
#     prints each constant after the primitives it uses, so a complete export
#     ends with one, and an export cut at a line boundary does not. Each
#     --decl must have a declaration record (an inductive's types,
#     constructors and recursors count): lean4export skips an unsafe constant
#     without --export-unsafe and still exits 0.
#   * `<out>.sidecar.json` records the toolchain and its pinned githash, the
#     exporter (repo URL it was fetched from, tag, commit, binary sha256), the
#     command, the environment the exporter ran under (read back from that
#     argv; the toolchain dir, HOME and TMPDIR as placeholders), the gate
#     (script and its sha256, label, weight, the GB heavy_gate reserved, an
#     enclosing reservation), the export's sha256, the meta line parsed, the
#     date and this script's sha256.
#
# REFUSALS exit 1 and print `LEAN_EXPORT_MINT=refused reason=<slug> ...` on
# stderr; a usage error exits 2. Nothing is written to <out> unless every check
# passes: the export is minted to a partial file and placed last, export first,
# each by one link(2), which refuses anything at the target, a directory
# included. Under --force the old export and sidecar are first set aside
# (link(2) to a partial name, then unlink(2); link(2) refuses a directory), so
# no cut leaves the new export beside the old sidecar, and a publish that fails
# puts the old pair back. One run at a time publishes to an <out>: the lock
# `<out>.lock` is held from the last check of the targets to the end of the
# run, and SIGINT, SIGTERM and SIGHUP are ignored while it is. A publish
# step that ends any other way (SIGKILL, a crash) is undone by the shell: what
# this run placed is removed, only while each target still holds it, the old
# pair is put back, and the refusal says what is left. The EXIT trap removes
# the partial files, the partial exporter checkout (kept only when its build
# failed, for inspection) and any lock this run holds. A lock is removed only
# when /bin/ps says its owner pid has no process; any other answer is waited
# for.
#
# MEMORY. The exporter build and every mint run under scripts/heavy_gate.sh
# (honouring an enclosing HEAVY_GATE_HELD reservation); a reservation the gate
# refuses (exit 75 on a small box) or fails before the job starts is
# `gate-refused` or `gate-failed`, never the job's failure. No peaks were
# recorded for either on 2026-10-28, so the classes start at reasoned
# fallbacks: the build (`lean-export-build`, 6 GB) elaborates three modules
# that import `Lean`, and a leanchecker run over modules peaked at 3.80 GB
# (`land-replaydiff-lean`, 2026-10-19), so a mint falls back to
# ceil(1.3 x 3.80) = 5 GB. Every module's root decides the mint's class
# (`lean-export-mint-<roots>`): the roots that are not Init, Std or Lean,
# sorted and joined by `-`, or the core roots when there are no others. The
# class is measured once heavy_gate's `weight auto:<class>:<n>` answers
# `class <class>: max peak ...` (a completed run is filed under it); any other
# answer reads as unmeasured. Before anything is fetched or built a mint asks
# that once, for one refusal: an unmeasured class with a non-core root needs
# --gate-gb (`gate-weight-unseen`), since the 5 GB bound is Lean core's. The
# reservation is settled later, just before the mint's own, from a second
# asking and the label's floor (`weight 0 <label>`; heavy_gate floors an
# explicit weight by the last 10 completed runs of the label class, and an
# `auto:` one by no run but those filed under the class), since another mint
# can complete under the class while this one fetches, builds and waits. While
# the class is unmeasured the mint reserves `auto:<class>:<n>`, which reserves
# <n> (or more, after a killed run) and files the run's peak under the class,
# so the run that measures the class is one `auto:` reads: <n> is --gate-gb, or
# 5 GB for a core class, raised to the label's floor. Once it is measured,
# --gate-gb is an explicit weight (the gate raises it to the floor), and a mint
# without it reserves the class's `auto:` weight, or the label's floor when
# that is higher. The gated job first reads what heavy_gate reserved
# (HEAVY_GATE_HELD, `<gb>:<label>`) and does not start under what the second
# asking settled (`gate-under-reserved`: only a run completing in between can
# cause it; run again); the sidecar records that reservation.
#
# USAGE
#   scripts/lean_export_mint.sh --toolchain v4.30.0-rc2 --module Init.Prelude
#   scripts/lean_export_mint.sh --toolchain <v4.X.Y[-rcN]> --module <M> [--module <M>]...
#       [--decl <Name>]... [--out <file.ndjson>] [--lean-path <dir>]...
#       [--export-unsafe] [--export-mdata] [--gate-gb <n>] [--force]
#   scripts/lean_export_mint.sh --selftest   # scripts/test_lean_export_mint.sh
# --out defaults to <cache>/exports/<toolchain>/<modules joined by +>.ndjson and
# is required with --decl. --lean-path dirs become the exporter's LEAN_PATH.
set -euo pipefail

SCRIPT_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
REPO_ROOT="$(cd "$(dirname "$SCRIPT_PATH")/.." && pwd -P)"
DEFAULT_EXPORTER_REPO="https://github.com/leanprover/lean4export"
# TEST SEAM (scripts/test_lean_export_mint.sh): where lean4export is fetched
# from. The commit pin still fixes what is built; the build stamp and the
# sidecar record the URL.
EXPORTER_REPO="${LEAN_EXPORT_MINT_EXPORTER_REPO:-$DEFAULT_EXPORTER_REPO}"
LEAN_REPO="https://github.com/leanprover/lean4"
WANT_FORMAT="3.1.0"
WANT_EXPORTER="lean4export"
BUNDLED_FROM_MINOR=35
BUILD_WEIGHT="auto:lean-export-build:6"
MINT_FALLBACK_GB=5
PYTHON="${LEAN_EXPORT_MINT_PYTHON:-python3}"
# TEST SEAM (scripts/test_lean_export_mint.sh): the gate script to wrap with,
# as check_gate_registry.py's CLEAN_GATE_HEAVY_GATE. Recorded in the sidecar.
GATE="${LEAN_EXPORT_MINT_HEAVY_GATE:-$REPO_ROOT/scripts/heavy_gate.sh}"
# How long to wait for another run's cache lock, in seconds.
LOCK_WAIT="${LEAN_EXPORT_MINT_LOCK_WAIT:-600}"
# The python half's exit status for "a refusal was printed" (EX_DATAERR): an
# interpreter that fails on its own exits 1, which must never read as one.
PY_REFUSED=65
PARTIAL="" LOCK_HELD="" WORK="" MARK=""

refuse() { local reason=$1; shift; echo "LEAN_EXPORT_MINT=refused reason=$reason $*" >&2; exit 1; }
usage_error() { echo "LEAN_EXPORT_MINT=usage $* (see --help)" >&2; exit 2; }

# The EXIT trap: the lock this run holds, its partial exporter checkout
# (WORK, cleared when the checkout is published or kept), every partial file
# (also the partial names a linked export and sidecar keep) and the gate's
# start marker.
cleanup() {
  if [ -n "${LOCK_HELD:-}" ]; then rm -rf -- "${LOCK_HELD:?}"; LOCK_HELD=""; fi
  if [ -n "${WORK:-}" ]; then rm -rf -- "${WORK:?}"; WORK=""; fi
  if [ -n "${PARTIAL:-}" ]; then rm -f -- "${PARTIAL:?}" "${PARTIAL:?}.sidecar"; fi
  if [ -n "${MARK:-}" ]; then rm -f -- "${MARK:?}"; fi
}

# One row per Lean tag this lane mints with: the tag, the lean4 commit its
# `lean --githash` must print, and the lean4export commit built for it (`-`
# from v4.35.0-rc1 on, where the toolchain bundles `leanexport`). Both shas are
# from `git ls-remote` of the upstream repos on 2026-10-28; every tag in both
# was lightweight (no `^{}` line), so a tag's sha is its commit. Each
# lean4export tag's `lean-toolchain` read `leanprover/lean4:<tag>` and its
# Export.lean wrote format 3.1.0 that day; the build re-checks the first.
# lean4export v4.28.0-rc1 (another format) is deliberately absent. A tag not
# here is refused; adding one is a reviewed edit of this table.
pin_row() {  # <tag> -> its row, or nothing
  awk -v t="$1" '$1 == t { print; exit }' <<'PINS'
v4.28.0     7e01a1bf5c70fc6167d49c345d3bf80596e9a79b d065b0009aed0520e9e99752847a33b337661690
v4.29.0-rc1 985f350dcd18fc7814dfa677cac09933f44f3215 ddeb0869b0b5679b0104e16291ffd929fbaa6a48
v4.29.0-rc2 83e54b65b65d1d3ce31d99d820a7bd5f3e219295 b9902a6449db212f0a3b95df1070072a62be97cd
v4.29.0-rc3 5d86aa4032284a5242470e95fbe25f1ff506763d cb4cd708e90f35252735c662bc97b55980d780a4
v4.29.0-rc4 95583d74bd14ff8cc2b789347d15dfdad1259f97 13905cda096b3e87b40e1f742355366c6bb39ff7
v4.29.0-rc6 00659f8e6071d7e46131ed643bf8003b99b044e9 71f41350675895dda791b8ff9c1dfb77d18b3585
v4.29.0-rc7 f5d7f18743eac341c4fa6e86abc5056d6ece40f4 20c548b7f4cbc93fd3f4d9c64ea346bd384209ea
v4.29.0-rc8 513160ea59dfd60defec325636bbc5215a8a6e7e bacf47c7e6881a17fa82d0d55c843bac24d27b6e
v4.29.0     98dc76e3c0a9b856c9b98726b713fb04fab16740 5a53b634f6a3e21e55b4852337c4fcf0781ad1aa
v4.29.1     f72c35b3f637c8c6571d353742168ab66cc22c00 6f4e21dd70c3c11d7fbd07d39e3192792c657448
v4.30.0-rc1 714601baf118066cbf3f282361339c6d06665b2a fb517af7d71065b28c256348afdf764308acc369
v4.30.0-rc2 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc 12581a6b680d8478175596338eb2d53383a323e3
v4.30.0     d024af099ca4bf2c86f649261ebf59565dc8c622 a3e35a584f59b390667db7269cd37fca8575e4bf
v4.31.0-rc1 fd009949156901e6cf15b6d9bf1122294b8e697a cd502a76e05515e7d3e09eaefee1dfd8349ca592
v4.31.0-rc2 5e44d5f905127c78a2da7a015fe7a47840c95eb1 b66b1cd7b8819db6059bc3d6093b22b0a380e793
v4.31.0     68218e876d2a38b1985b8590fff244a83c321783 8554815c2dc6b7abe99ec1f08849c9759ba77947
v4.32.0-rc1 b4812ae53eea93439ad5dce5a5c26591c31cb697 3de59f10bc4b4a0f2de698597aeb1246caa0df0a
v4.32.0     8c9756b28d64dab099da31a4c09229a9e6a2ef35 4e7915201d3f9f04470d9eae002fa695f7cdc589
v4.32.2     f3b06c705e6c85f5314019d5d3baab0fec5b580c 86e4a339507466921dc8c5417c8cb1de1ce7df60
v4.33.0-rc1 62eed1db4d67327ec8120be05f1a1b0847d74561 af5aa64bb914c3c2c781f378088dbd38acf4f804
v4.33.0-rc2 d8b18978322de05a8f3dba51ef03cf5461676c17 9fb131bb100eb32ccf6836f14e4f8328d13b6792
v4.33.0     d8b18978322de05a8f3dba51ef03cf5461676c17 15f6055e299ad5b89345e533cc2192f4cc00f659
v4.34.0-rc1 3447a668783dbce1a8fdb97101dd067687b2b418 b18d673bd29b476466a51a3be1012df2ed322b10
v4.34.0-rc2 6a10ac8c22beadecabdbb0919c2b50214762f91d cacf989bd75f608700820f6afc595f32e7a99a4d
v4.34.0     293d5d0c0c3f3dded4688b3ccd6a33939ac5102b 076e8e57707e813375e8f9da8bf989799ace9680
v4.35.0-rc1 86c6347c75e39ec18c40e25ed2143b71a6e04a0a -
v4.35.0-rc2 11acb17ec6b07a8f9e9173e6845197929540936b -
v4.35.0-rc3 470d5ce1400764999581fd26d5d72b00d990b0f4 -
v4.35.0-rc4 c29b6dda4f7c20e3eeaa717c4e565663c5cfa364 -
v4.35.0     eb6cafb7290e8bd5f2937522d8d804f58f02bafc -
v4.36.0-rc1 c9afcddf514a6772bd4d649f7cfc04eff0b9f15e -
v4.36.0-rc2 b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a -
PINS
}
pinned_githash() { pin_row "$1" | awk '{ print $2 }'; }               # <tag> -> lean4 commit
pinned_commit() { pin_row "$1" | awk '$3 != "-" { print $3 }'; }      # <tag> -> lean4export commit

toolchain_dir() { printf '%s/toolchains/leanprover--lean4---%s\n' "${ELAN_HOME:-$HOME/.elan}" "$1"; }

# TOOL_ENV: the argv prefix every Lean tool runs under -- nothing from the
# caller's environment but HOME and TMPDIR, the toolchain first on PATH and as
# LEAN_SYSROOT. An argv, not a function, so heavy_gate.sh can run it. The
# exporter's build runs under it: lake hands an inherited LEAN_PATH to the Lean
# processes it runs, and the build cache's key (tag@commit) records none.
# LEAN_ENV, the exporter's, adds --lean-path's LEAN_PATH.
set_lean_env() {  # <toolchain dir>
  TOOL_ENV=(env -i "HOME=$HOME" "TMPDIR=${TMPDIR:-/tmp}" "PATH=$1/bin:/usr/bin:/bin"
            "LEAN_SYSROOT=$1" "LEAN_ABORT_ON_PANIC=1")
  LEAN_ENV=("${TOOL_ENV[@]}")
  if [ -n "${MINT_LEAN_PATH:-}" ]; then LEAN_ENV+=("LEAN_PATH=$MINT_LEAN_PATH"); fi
}

# Runs <cmd> under its own reservation (or the enclosing HEAVY_GATE_HELD one)
# and returns its exit status. The command first writes the GB heavy_gate
# reserved for it (its HEAVY_GATE_HELD, `<gb>:<label>`) to MARK, so when
# heavy_gate fails before the command starts (exit 75: a small box refused the
# weight) GATE_FAILED is that status, and the command's own exit 75 never reads
# as the gate's. It does not start when that GB is unreadable or under <least>
# (GATE_FAILED unsaid or under). GATE_RESERVED is what MARK holds. gate_failed
# turns each into the refusal.
gate_run() {  # <weight> <least GB> <label> -- <cmd>...
  local weight=$1 least=$2 label=$3 rc=0; shift 3
  [ "${1:-}" = "--" ] && shift
  GATE_FAILED="" GATE_RESERVED=""
  if [ -n "${HEAVY_GATE_HELD:-}" ]; then "$@"; return; fi
  if [ -z "${MARK:-}" ]; then MARK=$(mktemp "${TMPDIR:-/tmp}/lean_export_mint.started.XXXXXX") || MARK=""; fi
  [ -n "$MARK" ] || refuse gate-failed "cannot make the gate's start marker in ${TMPDIR:-/tmp}"
  rm -f -- "${MARK:?}"
  bash "$GATE" run "$weight" "$label" -- /bin/sh -c 'gb=${HEAVY_GATE_HELD%%:*}
    printf "%s\n" "$gb" >"$1" || exit 1
    [ "$gb" -ge "$2" ] 2>/dev/null || exit 1   # fails on a gb that is no number, too
    shift 2 && exec "$@"' sh "$MARK" "$least" "$@" || rc=$?
  if [ ! -e "$MARK" ]; then
    [ "$rc" -eq 0 ] || GATE_FAILED=$rc
    return "$rc"
  fi
  GATE_RESERVED=$(cat -- "$MARK")
  case "$GATE_RESERVED" in
    ""|*[!0-9]*) GATE_FAILED=unsaid ;;
    *) [ "$GATE_RESERVED" -ge "$least" ] || GATE_FAILED=under ;;
  esac
  return "$rc"
}
# What heavy_gate would reserve for a weight right now, and why (`heavy_gate.sh
# weight`, read-only; with a label, an explicit weight raised to the label's
# floor as `run` raises it). Sets GATE_GB and GATE_BASIS, or refuses.
gate_weight() {  # <spec> [<label>]
  local answer
  answer=$(bash "$GATE" weight "$@" 2>/dev/null) || answer=""
  GATE_GB=${answer%%$'\t'*}; GATE_BASIS=${answer#*$'\t'}
  case "$GATE_GB" in
    ""|*[!0-9]*) refuse gate-weight-unknown "'$GATE weight $*' answered '$answer', not a weight" ;;
  esac
}
gate_failed() {  # <label> <weight> <least GB>: the refusal, if the job did not start
  case "${GATE_FAILED:-}" in
    "") ;;
    75) refuse gate-refused "heavy_gate refused $1 at $2 (exit 75: the job does not fit this box); run it on a bigger one" ;;
    under) refuse gate-under-reserved \
      "heavy_gate reserved $GATE_RESERVED GB for $1 at $2, under the $3 GB its answers settled just before (a run of the class or label completed in between); $1 did not start, run again" ;;
    unsaid) refuse gate-failed "heavy_gate did not say what it reserved for $1 (the <gb> of its HEAVY_GATE_HELD, <gb>:<label>, read '$GATE_RESERVED'); $1 did not start" ;;
    *) refuse gate-failed "heavy_gate exited $GATE_FAILED before $1 started" ;;
  esac
}

# The named toolchain is installed and IS that Lean: its banner names the
# version and its githash is readable. Sets TC_BANNER and TC_GITHASH.
check_toolchain() {  # <toolchain> <toolchain dir>
  local tc=$1 tcdir=$2
  set_lean_env "$tcdir"
  [ -x "$tcdir/bin/lean" ] || refuse toolchain-not-installed \
    "$tc: no executable $tcdir/bin/lean (this lane never installs a toolchain; use elan)"
  TC_BANNER=$("${TOOL_ENV[@]}" "$tcdir/bin/lean" --version 2>&1) \
    || refuse toolchain-not-installed "$tc: $tcdir/bin/lean --version failed: $TC_BANNER"
  case "$TC_BANNER" in
    *"(version ${tc#v},"*) ;;
    *) refuse toolchain-version-mismatch "$tc: $tcdir/bin/lean says '$TC_BANNER'" ;;
  esac
  TC_GITHASH=$("${TOOL_ENV[@]}" "$tcdir/bin/lean" --githash 2>/dev/null) || TC_GITHASH=""
  case "$TC_GITHASH" in
    ""|*[!0-9a-f]*) refuse toolchain-githash-unreadable "$tc: lean --githash gave '$TC_GITHASH'" ;;
  esac
}

# The toolchain is the upstream tag it is named after: its githash is the
# lean4 commit the pin table records for that tag.
check_lean_pin() {  # <toolchain>
  local tc=$1 want
  want=$(pinned_githash "$tc")
  [ -n "$want" ] || refuse no-pinned-lean-githash \
    "$tc has no row in the pin table (pin_row): a Lean whose commit nothing pins is never used"
  [ "$TC_GITHASH" = "$want" ] || refuse toolchain-githash-mismatch \
    "$tc: lean --githash is $TC_GITHASH, upstream's tag $tc is $want (a local or rebuilt Lean under the tag's name)"
}

# A checkout is the pinned commit, unmodified, built for this toolchain.
check_checkout() {  # <dir> <toolchain> <commit>
  local dir=$1 tc=$2 commit=$3 head dirty want got
  head=$(git --git-dir="$dir/.git" rev-parse --verify -q 'HEAD^{commit}' 2>/dev/null) || head=""
  [ "$head" = "$commit" ] || refuse exporter-commit-mismatch \
    "$dir is at '${head:-no git checkout}', the pin for $tc is $commit"
  dirty=$(git --git-dir="$dir/.git" --work-tree="$dir" status --porcelain --untracked-files=no 2>&1) \
    || refuse exporter-checkout-modified "$dir: git status failed: $dirty"
  [ -z "$dirty" ] || refuse exporter-checkout-modified "$dir has edits to tracked files: $dirty"
  want="leanprover/lean4:$tc"
  got=$(tr -d ' \t\r\n' <"$dir/lean-toolchain" 2>/dev/null) || got=""
  [ "$got" = "$want" ] || refuse exporter-toolchain-mismatch \
    "$dir/lean-toolchain is '${got:-absent}', not '$want'"
}

sha256_of() {  # <file>, streamed: an export can be gigabytes
  "$PYTHON" -I -c 'import hashlib,sys
h = hashlib.sha256()
with open(sys.argv[1], "rb") as f:
    for b in iter(lambda: f.read(1 << 20), b""): h.update(b)
print(h.hexdigest())' "$1"
}
is_sha256() { [[ "$1" =~ ^[0-9a-f]{64}$ ]]; }
# The exporter binary's sha256, or the refusal: an empty or garbled hash must
# never be written into a build stamp or compared with one.
binary_sha() {  # <file>
  local got
  got=$(sha256_of "$1") || refuse exporter-hash-failed "hashing $1 failed (exit $?)"
  is_sha256 "$got" || refuse exporter-hash-failed "hashing $1 gave '$got', not a sha256"
  printf '%s\n' "$got"
}

# A published build is intact: the pinned commit, unmodified, for this
# toolchain, and its binary the one its build stamp records. Sets EXPORTER, and
# EXPORTER_FROM to the repo URL the stamp says the build fetched from.
use_built() {  # <dir> <toolchain> <commit>
  local dir=$1 tc=$2 commit=$3 bin=".lake/build/bin/lean4export" stamp_sha got
  check_checkout "$dir" "$tc" "$commit"
  [ -x "$dir/$bin" ] && [ -f "$dir/.mint-built" ] || refuse cached-exporter-unbuilt \
    "$dir has no finished build; delete it and run again"
  stamp_sha=$(awk '$1 == "binary_sha256" { print $2 }' "$dir/.mint-built")
  is_sha256 "$stamp_sha" || refuse cached-exporter-stamp-malformed \
    "$dir/.mint-built records binary_sha256 '$stamp_sha', not one sha256; delete $dir and run again"
  got=$(binary_sha "$dir/$bin") || exit 1
  [ "$stamp_sha" = "$got" ] || refuse cached-exporter-tampered \
    "$dir/$bin is not the binary its build recorded ($stamp_sha); delete $dir and run again"
  EXPORTER_FROM=$(awk '$1 == "repo" { print $2 }' "$dir/.mint-built")
  EXPORTER_FROM=${EXPORTER_FROM:-$DEFAULT_EXPORTER_REPO}  # a stamp written before the repo line
  EXPORTER="$dir/$bin"
}

# What /bin/ps says of a lock owner's pid: `gone` only when it exits 1 having
# printed nothing (`-o pid=` prints no header), its answer for a pid no process
# has; `alive` when it prints that pid; `unknown` otherwise (an error, a ps that
# cannot run). /bin/ps, not PATH's; and not `kill -0`, which also fails on
# another user's live process (launchd's pid 1 among them).
ps_verdict() {  # <pid> <ps exit status> <ps output>
  if [ "$2" -eq 1 ] && [ -z "$3" ]; then echo gone
  elif [ "$2" -eq 0 ] && [ "$(printf '%s' "$3" | tr -d ' \t\n')" = "$1" ]; then echo alive
  else echo unknown; fi
}
owner_state() {  # <pid>
  local out rc=0
  out=$(/bin/ps -p "$1" -o pid= 2>&1) || rc=$?
  ps_verdict "$1" "$rc" "$out"
}

# An atomic mkdir, waited for up to LOCK_WAIT seconds. A lock whose owner pid
# no process has (a run killed with SIGKILL runs no EXIT trap) is removed and
# taken; a lock with no owner yet (its taker writes it just after the mkdir), a
# live one, or one whose owner ps cannot speak for is waited for, then refused
# as <slug>. Two runs can still both remove one stale lock; no file the locks
# order is placed over another by it (rename(2) refuses a non-empty build
# directory, link(2) anything at --out).
take_lock() {  # <lock dir> <refusal slug>
  local lock=$1 slug=$2 waited=0 owner
  until mkdir -- "$lock" 2>/dev/null; do
    owner=$(cat -- "$lock/owner" 2>/dev/null) || owner=""
    case "$owner" in
      ""|*[!0-9]*) ;;
      *) if [ "$(owner_state "$owner")" = gone ] && rm -rf -- "${lock:?}" 2>/dev/null; then
           echo "lean_export_mint: removed $lock, left by pid $owner, which is gone" >&2
           continue
         fi ;;
    esac
    if [ "$waited" -ge "$LOCK_WAIT" ]; then
      refuse "$slug" \
        "$lock is held (owner pid ${owner:-unknown}) after ${waited}s; if that process is gone, remove the lock by hand"
    fi
    sleep 1; waited=$((waited + 1))
  done
  LOCK_HELD=$lock
  printf '%s\n' "$$" >"$lock/owner"
}
drop_lock() { rm -rf -- "${LOCK_HELD:?}"; LOCK_HELD=""; }

# The lean4export binary for <toolchain> at <commit>: the cached build when it
# is intact, else fetched by commit, built under the gate and published.
# Sets EXPORTER and EXPORTER_FROM.
repo_exporter() {  # <toolchain> <toolchain dir> <commit>
  local tc=$1 tcdir=$2 commit=$3 dir work bin=".lake/build/bin/lean4export" lsr remote rc bsha placed
  dir="$CACHE/lean4export/$tc@$commit"
  if [ -d "$dir" ]; then use_built "$dir" "$tc" "$commit"; return 0; fi
  # Read peeled: an annotated tag names a tag object, and `^{}` its commit.
  lsr=$(git ls-remote "$EXPORTER_REPO" "refs/tags/$tc" "refs/tags/$tc^{}" 2>/dev/null) || lsr=""
  remote=$(printf '%s\n' "$lsr" | awk -v t="refs/tags/$tc" \
    '$2 == t "^{}" { p = $1 } $2 == t { l = $1 } END { print (p != "" ? p : l) }')
  [ -n "$remote" ] || refuse exporter-fetch-failed "git ls-remote $EXPORTER_REPO refs/tags/$tc gave nothing"
  [ "$remote" = "$commit" ] || refuse exporter-tag-moved \
    "$EXPORTER_REPO tag $tc is now $remote, the pin is $commit; review the move before re-pinning"
  mkdir -p -- "$CACHE/lean4export" 2>/dev/null \
    || refuse cache-unwritable "cannot create $CACHE/lean4export, the exporter build cache"
  work="$dir.partial.$$"
  rm -rf -- "${work:?}"
  mkdir -- "$work" 2>/dev/null || refuse cache-unwritable "cannot create $work in the exporter build cache"
  WORK=$work   # from here every refusal but a failed build's removes it (the EXIT trap)
  # No hook of the caller's git config runs in the checkout.
  if ! { git -C "$work" init -q \
         && git -C "$work" -c core.hooksPath=/dev/null fetch -q --depth 1 "$EXPORTER_REPO" "$commit" \
         && git -C "$work" -c core.hooksPath=/dev/null -c advice.detachedHead=false checkout -q FETCH_HEAD; }; then
    refuse exporter-fetch-failed "git fetch of $commit from $EXPORTER_REPO failed"
  fi
  check_checkout "$work" "$tc" "$commit"
  echo "lean_export_mint: building lean4export $tc@$commit with $tcdir/bin/lake" >&2
  if gate_run "$BUILD_WEIGHT" 0 lean-export-build -- \
       "${TOOL_ENV[@]}" /bin/sh -c 'cd "$1" && exec "$2" build lean4export' sh "$work" "$tcdir/bin/lake"
  then rc=0; else rc=$?; fi
  gate_failed lean-export-build "$BUILD_WEIGHT" 0
  if [ "$rc" -ne 0 ] || [ ! -x "$work/$bin" ]; then
    WORK=""   # kept for inspection
    refuse exporter-build-failed \
      "lake build in $work exited $rc$([ -x "$work/$bin" ] || printf ' and wrote no %s' "$bin") (the partial checkout is left for inspection)"
  fi
  check_checkout "$work" "$tc" "$commit"   # the build left every tracked file as fetched
  bsha=$(binary_sha "$work/$bin") || exit 1
  printf 'toolchain %s\ncommit %s\nrepo %s\nbinary_sha256 %s\nbuilt %s\n' "$tc" "$commit" "$EXPORTER_REPO" \
    "$bsha" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >"$work/.mint-built" \
    || refuse cache-unwritable "cannot write the build stamp $work/.mint-built"
  # Publish by one rename(2): it refuses a non-empty target, so two first
  # builds of one tag never nest one checkout inside the other, even when both
  # removed one stale lock. A run that finds anything there discards its own
  # and checks what is there.
  take_lock "$dir.lock" exporter-cache-locked
  if [ -e "$dir" ]; then placed=exists
  else
    placed=$(py rename "$work" "$dir") \
      || { rc=$?; [ "$rc" -eq "$PY_REFUSED" ] || refuse cache-publish-failed "the rename of $work to $dir exited $rc"; exit 1; }
  fi
  case "$placed" in
    placed) ;;
    exists) rm -rf -- "${work:?}" ;;
    *) refuse cache-publish-failed "the rename of $work to $dir answered '$placed'" ;;
  esac
  WORK=""
  drop_lock
  use_built "$dir" "$tc" "$commit"
}

# The python half: the exporter's writer, the export check, the sidecar, a path
# test. stdlib only, -I. A program in a variable, not a heredoc on stdin, so the
# writer can run under heavy_gate and read the exporter's stdout. A refusal
# exits PY_REFUSED (65) after printing its line; a crash exits 70.
IFS= read -r -d '' PY_SRC <<'PY' || :
import datetime, errno, hashlib, json, os, platform, subprocess, sys

# The record kinds the front door's dispatch reads (ndjson/source.rs `item`).
DECLS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
PRIMITIVES = {
    "in": ("str", "num"),
    "il": ("succ", "max", "imax", "param"),
    "ie": ("bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj",
           "natVal", "strVal", "mdata"),
}
REFUSED = 65  # PY_REFUSED in the shell half

def refuse(reason, detail):
    print(f"LEAN_EXPORT_MINT=refused reason={reason} {detail}", file=sys.stderr)
    sys.exit(REFUSED)

def bad(n, why):
    refuse("export-malformed", f"line {n} {why}")

class DuplicateKey(ValueError):
    pass

def no_duplicates(pairs):
    keys = [k for k, _ in pairs]
    if len(set(keys)) != len(keys):
        raise DuplicateKey(f"duplicate key in {keys}")
    return dict(pairs)

def fields(obj, what, names, strings=True):
    if not isinstance(obj, dict) or sorted(obj) != sorted(names):
        refuse("meta-malformed", f"{what} must be an object with exactly the fields {names}")
    if strings and not all(isinstance(obj[n], str) for n in names):
        refuse("meta-malformed", f"{what}.{names} must be strings")
    return obj

def index(v):
    return isinstance(v, int) and not isinstance(v, bool) and v >= 0

def name_parts(text):
    """A --decl as the exporter reads it (Syntax.decodeNameLit): dots part, «» quote."""
    parts, cur, quoted = [], "", False
    for ch in text:
        if ch == "«" and not quoted:
            quoted = True
        elif ch == "»" and quoted:
            quoted = False
        elif ch == "." and not quoted:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return tuple(parts)

def record(n, obj):
    """Line n's record kind: a declaration kind or a primitive table."""
    if not isinstance(obj, dict):
        bad(n, f"is a JSON {type(obj).__name__}, not an object")
    keys = list(obj)
    if len(keys) == 1:
        kind = keys[0]
        if kind not in DECLS:
            bad(n, f"has the one key {kind!r}, which is no declaration kind {list(DECLS)}")
        if not isinstance(obj[kind], dict):
            bad(n, f"is a {kind} record whose value is not an object")
        return kind
    if len(keys) == 2:
        tables = [k for k in keys if k in PRIMITIVES]
        if len(tables) != 1:
            bad(n, f"has the keys {keys}; a primitive has exactly one of {list(PRIMITIVES)}")
        table = tables[0]
        variant = keys[1] if keys[0] == table else keys[0]
        if not index(obj[table]):
            bad(n, f"has {table}={obj[table]!r}, which is not an index")
        if variant not in PRIMITIVES[table]:
            bad(n, f"is a {table!r} record of kind {variant!r}, not one of {list(PRIMITIVES[table])}")
        return table
    bad(n, f"has {len(keys)} keys {keys}; a record has one (a declaration) or two (a primitive)")

def declared(n, kind, data):
    """The name indices a declaration record declares."""
    entries = [data]
    if kind == "inductive":
        entries = []
        for part in ("types", "ctors", "recs"):
            got = data.get(part)
            if not isinstance(got, list) or not all(isinstance(x, dict) for x in got):
                bad(n, f"is an inductive record whose {part!r} is not a list of objects")
            entries += got
    for x in entries:
        if not index(x.get("name")):
            bad(n, f"is a {kind} record declaring the name {x.get('name')!r}, which is not an index")
    return [x["name"] for x in entries]

def meta(path, want_lean, want_format, want_githash, want_name, decls):
    wanted = {name_parts(d): d for d in decls}
    prefixes = {k[:i] for k in wanted for i in range(len(k) + 1)}
    names = {0: ()}  # name index -> parts, kept only for prefixes of a --decl
    found, records, n, last = set(), 0, 1, None
    with open(path, "rb") as fh:
        first = fh.readline()
        if not first.endswith(b"\n"):
            refuse("meta-malformed", "the export has no complete first line")
        try:
            top = json.loads(first, object_pairs_hook=no_duplicates)
        except ValueError as exc:
            refuse("meta-malformed", f"the first line does not parse: {exc}")
        m = fields(top, "the first line", ["meta"], strings=False)["meta"]
        fields(m, "meta", ["exporter", "lean", "format"], strings=False)
        exporter = fields(m["exporter"], "meta.exporter", ["name", "version"])
        lean = fields(m["lean"], "meta.lean", ["githash", "version"])
        fmt = fields(m["format"], "meta.format", ["version"])
        if exporter["name"] != want_name:
            refuse("meta-exporter-mismatch", f"meta.exporter.name is {exporter['name']!r}, not {want_name!r}")
        if fmt["version"] != want_format:
            refuse("meta-format-mismatch", f"meta.format.version is {fmt['version']!r}, not {want_format!r}")
        if lean["version"] != want_lean:
            refuse("meta-lean-version-mismatch", f"meta.lean.version is {lean['version']!r}, not {want_lean!r}")
        if lean["githash"] != want_githash:
            refuse("meta-githash-mismatch",
                   f"meta.lean.githash is {lean['githash']!r}, the toolchain's is {want_githash!r}")
        for raw in fh:
            n += 1
            if not raw.endswith(b"\n"):
                refuse("export-truncated",
                       f"line {n} ends without a newline: the export's tail was lost (a full disk, "
                       f"a failed write), and a cut export is not the whole export")
            try:
                obj = json.loads(raw, object_pairs_hook=no_duplicates)
            except ValueError as exc:
                bad(n, f"does not parse as JSON: {exc}")
            kind = record(n, obj)
            records += 1
            last = kind
            if kind in DECLS:
                for i in declared(n, kind, obj[kind]):
                    if names.get(i) in wanted:
                        found.add(names[i])
            elif kind == "in" and wanted:
                variant = next(k for k in obj if k != "in")
                data = obj[variant]
                if isinstance(data, dict) and index(data.get("pre")) and data["pre"] in names:
                    part = data.get("str") if variant == "str" else data.get("i")
                    if part is not None and names[data["pre"]] + (str(part),) in prefixes:
                        names[obj["in"]] = names[data["pre"]] + (str(part),)
    if records == 0:
        refuse("export-empty", "no record follows the meta line")
    if last not in DECLS:
        refuse("export-truncated",
               f"the last record (line {n}) is a {last!r} primitive, not a declaration: lean4export "
               f"prints each constant after the names, levels and expressions it uses, so a complete "
               f"export ends with a declaration, and this one was cut short at a line boundary")
    missing = [d for k, d in wanted.items() if k not in found]
    if missing:
        refuse("decl-not-exported",
               f"the export has no declaration record for {missing} (lean4export skips an "
               f"unsafe constant unless --export-unsafe is passed, and still exits 0)")
    print(json.dumps(top, separators=(",", ":"), sort_keys=True))

def file_sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def environment(argv, tcdir):
    """The environment an `env [-i] K=V...` argv sets, as the exporter saw it."""
    if not argv or argv[0] != "env":
        raise ValueError(f"the exporter's argv does not start with env: {argv[:2]}")
    flags = [a for a in argv[1:] if a.startswith("-")]
    pairs = [a.split("=", 1) for a in argv[1:] if not a.startswith("-")]
    def shown(k, v):
        if k == "HOME":
            return "<home>"
        if k == "TMPDIR":
            return "<tmpdir>"
        return v.replace(tcdir, "<toolchain dir>") if tcdir else v
    return "-i" in flags, {k: shown(k, v) for k, v in pairs}

def sidecar(export, out, rest):
    e = os.environ
    at = rest.index("--cmd")
    cleared, env = environment(rest[:at], e["MINT_TCDIR"])
    command = rest[at + 1:]
    digest, size, lines = hashlib.sha256(), 0, 0
    with open(export, "rb") as fh:
        first = fh.readline()
        fh.seek(0)
        for block in iter(lambda: fh.read(1 << 20), b""):
            digest.update(block); size += len(block); lines += block.count(b"\n")
    opts = [a for a in command[1:] if a.startswith("--") and len(a) >= 3]
    rest_args = [a for a in command[1:] if not (a.startswith("--") and len(a) >= 3)]
    modules = rest_args[:rest_args.index("--")] if "--" in rest_args else rest_args
    decls = rest_args[rest_args.index("--") + 1:] if "--" in rest_args else []
    gate_script = e.get("MINT_GATE_SCRIPT", "")
    root = os.path.realpath(e["MINT_REPO_ROOT"])
    def shown(p):
        rp = os.path.realpath(p)
        return os.path.relpath(rp, root) if rp.startswith(root + os.sep) else p
    doc = {
        "schema": "clean.lean_export_mint/1",
        "toolchain": e["MINT_TOOLCHAIN"],
        "lean_githash": e["MINT_GITHASH"],
        "lean_banner": e["MINT_BANNER"],
        "exporter": {"kind": e["MINT_KIND"], "repo": e["MINT_REPO"], "tag": e["MINT_TAG"],
                     "commit": e["MINT_COMMIT"], "binary_sha256": file_sha(command[0])},
        "command": [os.path.basename(command[0])] + command[1:],
        "modules": modules, "decls": decls, "options": opts,
        "environment": env, "environment_cleared": cleared,
        "export": {"file": e["MINT_OUT_NAME"], "sha256": digest.hexdigest(),
                   "bytes": size, "lines": lines},
        "meta_line": first.decode("utf-8").rstrip("\n"),
        "meta": json.loads(e["MINT_META"]),
        "gate": {"script": shown(gate_script) if gate_script else None,
                 "script_sha256": file_sha(gate_script) if gate_script else None,
                 "label": e["MINT_GATE_LABEL"], "weight": e["MINT_GATE_WEIGHT"],
                 "reserved_gb": int(e["MINT_GATE_RESERVED"]) if e.get("MINT_GATE_RESERVED") else None,
                 "held": e.get("HEAVY_GATE_HELD", "")},
        "generated": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "host": f"{platform.system()} {platform.machine()}",
        "minted_by": "scripts/lean_export_mint.sh",
        "script_sha256": file_sha(e["MINT_SCRIPT"]),
    }
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(doc, fh, indent=2, sort_keys=True)
        fh.write("\n")
    print(doc["export"]["sha256"])

def inside(path, root):
    p, r = os.path.realpath(path), os.path.realpath(root)
    print("yes" if p == r or p.startswith(r + os.sep) else "no")

def write(out, rest):
    """Run the exporter (`<env argv> --cmd <cmd>`) with its stdout copied to out.

    Lean buffers stdout and exits 0 when the last flush fails, so the exporter
    never writes the file: every write here is checked, and so are the fsync
    and the close. Either side's failure is a refusal of its own."""
    at = rest.index("--cmd")
    cmd = rest[at + 1:]
    what = " ".join([os.path.basename(cmd[0])] + cmd[1:])
    try:
        fd = os.open(out, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
    except OSError as exc:
        refuse("export-write-failed", f"cannot open {out}: {exc}")
    # `env` that cannot be started is this step's crash (exit 70), named by the shell half.
    proc = subprocess.Popen(rest[:at] + cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE)
    failed = None
    try:
        for block in iter(lambda: proc.stdout.read(1 << 20), b""):
            view = memoryview(block)
            while view:
                view = view[os.write(fd, view):]
        os.fsync(fd)
    except OSError as exc:
        failed = exc
        proc.kill()
    try:
        os.close(fd)
    except OSError as exc:
        failed = failed or exc
    proc.stdout.close()
    rc = proc.wait()
    if failed is not None:
        refuse("export-write-failed",
               f"writing {out} failed ({failed}): the file does not hold everything {what} printed")
    if rc != 0:
        refuse("exporter-failed", f"{what} " + (f"was killed by signal {-rc}" if rc < 0 else f"exited {rc}"))

def rename_build(src, dst):
    """Publish a finished exporter build by one rename(2). It refuses a target
    directory that is not empty (another run's build: `exists`), so src never
    lands inside one, and replaces an empty one."""
    try:
        os.rename(src, dst)
    except OSError as exc:
        if exc.errno in (errno.ENOTEMPTY, errno.EEXIST):
            print("exists")
            return
        refuse("cache-publish-failed", f"cannot rename {src} to {dst}: {exc}")
    print("placed")

def targets(partial, out):
    """(what, this run's partial file, its target, where --force sets the old one aside)"""
    return [("export", partial, out, partial + ".old"),
            ("sidecar", partial + ".sidecar", out + ".sidecar.json", partial + ".sidecar.old")]

def same(a, b):
    """a and b name one file, a symlink not followed (link(2) keeps a's name too)."""
    try:
        x, y = os.lstat(a), os.lstat(b)
    except FileNotFoundError:
        return False
    return (x.st_dev, x.st_ino) == (y.st_dev, y.st_ino)

def is_dir(path):
    return os.path.isdir(path) and not os.path.islink(path)

def undo(partial, out, placed=()):
    """Undo a publish and say what was done. What this run placed is removed only
    while its target still holds it: another run's file there is left alone (named
    when this run had placed one there, `placed`). The old pair --force set aside
    is put back, the old sidecar only beside its own export (or beside nothing,
    when it had none), so no undo leaves an export beside a sidecar that is not
    its own; what cannot go back stays at its aside name, which is said. A step
    cut inside `set_aside` left the old file at its target too: only the aside
    name goes."""
    said = []
    for what, src, dst, old in targets(partial, out):
        if same(src, dst):
            os.unlink(dst)
            said.append(f"the {what} this run placed was removed")
        elif what in placed:
            said.append(f"{dst} no longer holds the {what} this run placed (another run replaced it), "
                        f"so it is left as it is")
        if same(old, dst):
            os.unlink(old)
            said.append(f"the old {what} had not left {dst}")
    (_, _, _, old_export), (_, _, side, old_side) = targets(partial, out)
    export_back = False
    if os.path.lexists(old_export):
        try:
            os.link(old_export, out, follow_symlinks=False)
        except FileExistsError:
            said.append(f"{out} is taken, so the old export is kept at {old_export}")
        else:
            os.unlink(old_export)
            export_back = True
            said.append("the old export was put back")
    if os.path.lexists(old_side):
        if export_back or not (os.path.lexists(old_export) or os.path.lexists(out)):
            try:
                os.link(old_side, side, follow_symlinks=False)
            except FileExistsError:
                said.append(f"{side} is taken, so the old sidecar is kept at {old_side}")
            else:
                os.unlink(old_side)
                said.append("the old sidecar was put back")
        else:
            said.append(f"the old sidecar is kept at {old_side}, since its export is not back at {out}")
    return "; " + ", ".join(said) if said else "; nothing this run placed or set aside was left to undo"

def set_aside(cur, old):
    """--force: move the file at cur to old by link(2) and unlink(2), so that the
    new one is placed by a link like any other. link(2) refuses a directory."""
    try:
        os.link(cur, old, follow_symlinks=False)
    except FileNotFoundError:
        return
    os.unlink(cur)

def publish(partial, out, force):
    """Place the export, then its sidecar, each by one link(2), which refuses
    anything already at the target, a directory included: nothing is moved into a
    directory or written over, however late it appeared. Under --force the old
    export and sidecar are set aside first, so a cut at any point leaves at --out
    the old pair, nothing, or the new export alone, never the new export beside
    the old sidecar. A placement that fails undoes the publish (`undo`); the
    asides are removed once both files are placed."""
    placed = set()
    steps = targets(partial, out)
    def fail(reason, detail):
        try:
            done = undo(partial, out, placed)
        except OSError as exc:
            done = f"; and undoing the publish failed ({exc})"
        refuse(reason, detail + done)
    if force:
        for what, _, dst, old in steps:
            try:
                set_aside(dst, old)
            except OSError as exc:
                if is_dir(dst):
                    fail("out-is-directory", f"{dst} is a directory, not a file the mint can replace "
                         f"(it appeared during the mint; nothing was moved into it)")
                fail("out-publish-failed", f"cannot set the old {what} at {dst} aside ({exc})")
    for what, src, dst, _ in steps:
        try:
            os.link(src, dst)
        except OSError as exc:
            if is_dir(dst):
                fail("out-is-directory", f"{dst} is a directory, not a file the mint can replace "
                     f"(it appeared during the mint; nothing was moved into it)")
            if exc.errno == errno.EEXIST:
                fail("out-exists", f"{dst} appeared during the mint" + ("" if force else " (pass --force to replace it)"))
            fail("out-publish-failed", f"cannot place the {what} at {dst} ({exc})")
        placed.add(what)
    for _, _, _, old in steps:
        try:
            os.unlink(old)
        except OSError:
            pass  # no aside (none was set, or it is already gone): nothing to remove

def unpublish(partial, out):
    """The shell's undo of a publish step that ended other than by exiting 0 or
    REFUSED (SIGKILL, a crash): `undo`, printed for its refusal."""
    print(undo(partial, out))

verb, args = sys.argv[1], sys.argv[2:]
try:
    if verb == "meta":
        meta(*args[:5], args[5:])
    elif verb == "sidecar":
        sidecar(args[0], args[1], args[2:])
    elif verb == "inside":
        inside(*args)
    elif verb == "write":
        write(args[0], args[1:])
    elif verb == "rename":
        rename_build(*args)
    elif verb == "publish":
        publish(args[0], args[1], args[2] == "1")
    elif verb == "unpublish":
        unpublish(*args)
    else:
        raise ValueError(f"unknown verb {verb}")
except Exception as exc:  # a crash is no refusal: the shell half names the step
    print(f"lean_export_mint: the {verb} step crashed: {exc!r}", file=sys.stderr)
    sys.exit(70)
PY
py() { "$PYTHON" -I -c "$PY_SRC" "$@"; }

check_name() {  # <kind> <name>: a module or declaration name the exporter reads as one
  case "$2" in
    ""|-*|*[[:space:]]*) usage_error "bad $1 name '$2' (empty, starts with '-', or holds whitespace)" ;;
  esac
}

# Neither target is a directory, --force or not (the publish refuses one too,
# but this check refuses it before the mint and before the old export is
# replaced), and no export and no sidecar is there unless --force.
out_free() {  # <out> <force>
  local t
  for t in "$1" "$1.sidecar.json"; do
    [ ! -d "$t" ] || refuse out-is-directory "$t is a directory, not a file the mint can replace"
  done
  [ "$2" -eq 1 ] && return 0
  if [ -e "$1" ] || [ -e "$1.sidecar.json" ]; then
    refuse out-exists "$1 or its .sidecar.json exists (pass --force to replace them)"
  fi
}

# The mint's gate class, from EVERY module's root: the roots that are not Lean
# core's (Init, Std, Lean), or the core roots when every root is core; distinct,
# sorted and joined by `-` (a root, sanitised to [A-Za-z0-9_], holds none).
# Sets MINT_ROOTS, and MINT_CORE=1 when every root is core.
mint_class() {  # <module>...
  local m root core="" other=""
  for m in "$@"; do
    root=$(printf '%s' "${m%%.*}" | tr -c 'A-Za-z0-9_' '_')
    case "$root" in
      Init|Std|Lean) core="$core $root" ;;
      *) other="$other $root" ;;
    esac
  done
  MINT_CORE=0
  if [ -z "$other" ]; then MINT_CORE=1; other=$core; fi
  # The roots are [A-Za-z0-9_]+, so the unquoted split is the list.
  MINT_ROOTS=$(printf '%s\n' $other | LC_ALL=C sort -u | tr '\n' '-')
  MINT_ROOTS=${MINT_ROOTS%-}
}

# The mint's reservation (MEMORY, in the header), from what heavy_gate says of
# the class now. Refuses an unmeasured class with a non-core root and no
# --gate-gb. With `settle`, also asks the label's floor and sets MINT_WEIGHT (the
# spec to reserve) and MINT_LEAST (the GB heavy_gate's answers say it reserves).
mint_weight() {  # <label> <fallback GB> <--gate-gb, or empty> [settle]
  local label=$1 fb=$2 gb=$3 auto_gb floor unmeasured
  gate_weight "auto:$label:$fb"; auto_gb=$GATE_GB
  case "$GATE_BASIS" in
    "class $label: max peak "*) unmeasured=0 ;;  # heavy_gate_weights.sh _auto_weight's words for a measured class
    *) unmeasured=1 ;;                          # any other answer: unseen, killed runs only, or words it never wrote
  esac
  if [ "$unmeasured" -eq 1 ] && [ -z "$gb" ] && [ "$MINT_CORE" -eq 0 ]; then
    refuse gate-weight-unseen \
      "no $label mint has completed under its class (heavy_gate: '$GATE_BASIS'), and a closure rooted in $MINT_ROOTS is not bounded by Lean core's; pass --gate-gb <n> (that run's peak then sizes the next)"
  fi
  [ "${4:-}" = settle ] || return 0
  gate_weight 0 "$label"; floor=$GATE_GB   # 0 raised to the label class's floor
  if [ "$unmeasured" -eq 1 ]; then
    # Raise only on a comparison that succeeds: an unreadable operand keeps the
    # fallback (validated by the usage check) rather than taking the floor.
    if [ "$floor" -gt "$fb" ]; then fb=$floor; fi
    MINT_WEIGHT="auto:$label:$fb" MINT_LEAST=$fb   # reserves fb (more after a killed run), filed under the class
  elif [ -n "$gb" ]; then
    MINT_WEIGHT=$gb MINT_LEAST=$gb                 # explicit: the gate raises it to the label's floor itself
  elif [ "$floor" -gt "$auto_gb" ]; then
    MINT_WEIGHT=$floor MINT_LEAST=$floor           # explicit runs of the label peaked above what auto: reads
  else
    MINT_WEIGHT="auto:$label:$fb" MINT_LEAST=$auto_gb
  fi
}

main() {
  local tc="" out="" gate_gb="" force=0 a
  local modules=() decls=() opts=() lpath=()
  while [ $# -gt 0 ]; do
    a=$1
    case "$a" in
      --toolchain|--module|--decl|--out|--lean-path|--gate-gb)
        [ $# -ge 2 ] && [ -n "$2" ] || usage_error "$a needs a value" ;;
    esac
    case "$a" in
      --toolchain) tc=$2; shift 2 ;;
      --module) check_name module "$2"; modules+=("$2"); shift 2 ;;
      --decl) check_name declaration "$2"; decls+=("$2"); shift 2 ;;
      --out) out=$2; shift 2 ;;
      --lean-path) lpath+=("$2"); shift 2 ;;
      --export-unsafe|--export-mdata) opts+=("$a"); shift ;;
      --gate-gb) gate_gb=$2; shift 2
        case "$gate_gb" in
          *[!0-9]*) usage_error "--gate-gb needs a whole number of GB" ;;
          [1-9]|[1-9][0-9]|[1-9][0-9][0-9]|[1-9][0-9][0-9][0-9]) ;;
          [1-9]*) usage_error "--gate-gb '$gate_gb' is over 9999 GB: no box here has that, and past 2^63 the shell's comparisons stop reading it as a number" ;;
          *[1-9]*) usage_error "--gate-gb '$gate_gb' starts with 0: heavy_gate's shell arithmetic reads 010 as octal 8 and refuses 08" ;;
          *) usage_error "--gate-gb needs a whole number of GB above 0 (a 0 GB reservation reserves nothing)" ;;
        esac ;;
      --force) force=1; shift ;;
      --selftest) exec bash "$(dirname "$SCRIPT_PATH")/test_lean_export_mint.sh" ;;
      -h|--help) sed -n '2,/^set -euo/p' "$SCRIPT_PATH" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
      *) usage_error "unknown argument '$a'" ;;
    esac
  done
  [ -n "$tc" ] || usage_error "--toolchain is required"
  [ "${#modules[@]}" -gt 0 ] || usage_error "at least one --module is required"
  [[ "$tc" =~ ^v([0-9]+)\.([0-9]+)\.([0-9]+)(-rc[0-9]+)?$ ]] \
    || usage_error "toolchain '$tc' is not spelled v<major>.<minor>.<patch>[-rcN]"
  local major=${BASH_REMATCH[1]} minor=${BASH_REMATCH[2]}
  if [ "${#decls[@]}" -gt 0 ] && [ -z "$out" ]; then usage_error "--decl needs an explicit --out"; fi
  case "$LOCK_WAIT" in ""|*[!0-9]*) usage_error "LEAN_EXPORT_MINT_LOCK_WAIT must be a whole number of seconds" ;; esac
  command -v "$PYTHON" >/dev/null 2>&1 || refuse no-python "'$PYTHON' is not on PATH"
  trap cleanup EXIT

  CACHE="${LEAN_EXPORT_MINT_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/clean-lean-export-mint}"
  case "$CACHE" in /*) ;; *) CACHE="$PWD/$CACHE" ;; esac
  local inside
  inside=$(py inside "$CACHE" "$REPO_ROOT") || refuse cache-check-failed "the path check of $CACHE exited $?"
  [ "$inside" = "no" ] \
    || refuse cache-inside-repo "$CACHE is inside $REPO_ROOT; builds and exports stay out of the tree"

  # --out, resolved and checked before anything is fetched, built or minted.
  if [ -z "$out" ]; then
    local slug; slug=$(printf '%s+' "${modules[@]}"); slug=${slug%+}
    out="$CACHE/exports/$tc/$slug.ndjson"
  fi
  case "$out" in /*) ;; *) out="$PWD/$out" ;; esac
  case "$out" in */) usage_error "--out '$out' ends in '/': name the export file, not a directory" ;; esac
  [ ! -d "$out" ] || usage_error "--out '$out' is a directory: name the export file"
  out_free "$out" "$force"

  MINT_LEAN_PATH=""
  if [ "${#lpath[@]}" -gt 0 ]; then MINT_LEAN_PATH=$(IFS=:; printf '%s' "${lpath[*]}"); fi
  local tcdir; tcdir=$(toolchain_dir "$tc")
  check_toolchain "$tc" "$tcdir"

  local kind repo tag commit bundled=0
  if [ "$major" -gt 4 ] || { [ "$major" -eq 4 ] && [ "$minor" -ge "$BUNDLED_FROM_MINOR" ]; }; then bundled=1; fi
  if [ "$bundled" -eq 1 ]; then
    kind="bundled-leanexport"; repo="$LEAN_REPO"; tag="$tc"
    check_lean_pin "$tc"
    commit="$TC_GITHASH"
    EXPORTER="$tcdir/bin/leanexport"
    [ -x "$EXPORTER" ] || refuse bundled-exporter-missing \
      "$tc is v4.$BUNDLED_FROM_MINOR or later and has no executable $EXPORTER"
  else
    kind="lean4export-repo"; tag="$tc"
    commit=$(pinned_commit "$tc")
    [ -n "$commit" ] || refuse no-pinned-exporter-commit \
      "lean4export has no pinned tag $tc (pin_row); an exporter built for another Lean is never used"
    check_lean_pin "$tc"
  fi

  # The refusal an unmeasured class can draw, asked before any build is spent
  # on it; the reservation itself is settled just before the mint's (MEMORY, in
  # the header). Under an enclosing reservation the weight is only recorded.
  local label fb
  mint_class "${modules[@]}"
  label="lean-export-mint-$MINT_ROOTS"
  fb=${gate_gb:-$MINT_FALLBACK_GB}
  MINT_WEIGHT=${gate_gb:-"auto:$label:$fb"} MINT_LEAST=0
  if [ -z "${HEAVY_GATE_HELD:-}" ]; then mint_weight "$label" "$fb" "$gate_gb"; fi

  # The --out directory, made only once nothing before the fetch can refuse.
  local dir; dir=$(dirname "$out")
  mkdir -p -- "$dir" 2>/dev/null || refuse out-unwritable "cannot create $dir, the directory of --out"
  [ -w "$dir" ] || refuse out-unwritable "$dir, the directory of --out, is not writable"

  if [ "$bundled" -eq 0 ]; then
    repo_exporter "$tc" "$tcdir" "$commit"
    repo=$EXPORTER_FROM
  fi

  local cmd rc meta_json sha left gate_script=""
  cmd=("$EXPORTER" ${opts[@]+"${opts[@]}"} "${modules[@]}")
  if [ "${#decls[@]}" -gt 0 ]; then cmd+=(-- "${decls[@]}"); fi
  [ -n "${HEAVY_GATE_HELD:-}" ] || gate_script=$GATE
  PARTIAL="$out.partial.$$"
  # Asked again: another mint may have completed under the class since.
  if [ -z "${HEAVY_GATE_HELD:-}" ]; then mint_weight "$label" "$fb" "$gate_gb" settle; fi
  echo "lean_export_mint: minting ${modules[*]} with $kind $tag@$commit" >&2
  # The writer runs the exporter and refuses (exporter-failed,
  # export-write-failed) by itself; any other failure is its crash.
  if gate_run "$MINT_WEIGHT" "$MINT_LEAST" "$label" -- \
       "$PYTHON" -I -c "$PY_SRC" write "$PARTIAL" "${LEAN_ENV[@]}" --cmd "${cmd[@]}"
  then rc=0; else rc=$?; fi
  gate_failed "$label" "$MINT_WEIGHT" "$MINT_LEAST"
  if [ "$rc" -ne 0 ]; then
    [ "$rc" -eq "$PY_REFUSED" ] || refuse export-writer-failed "the writer of $PARTIAL exited $rc"
    exit 1
  fi

  if meta_json=$(py meta "$PARTIAL" "${tc#v}" "$WANT_FORMAT" "$TC_GITHASH" "$WANT_EXPORTER" ${decls[@]+"${decls[@]}"})
  then :; else
    rc=$?; [ "$rc" -eq "$PY_REFUSED" ] || refuse export-check-failed "the export check of $PARTIAL exited $rc"; exit 1
  fi
  sha=$(MINT_SCRIPT="$SCRIPT_PATH" MINT_REPO_ROOT="$REPO_ROOT" MINT_TOOLCHAIN="$tc" MINT_TCDIR="$tcdir" \
        MINT_GITHASH="$TC_GITHASH" MINT_BANNER="$TC_BANNER" MINT_KIND="$kind" MINT_REPO="$repo" \
        MINT_TAG="$tag" MINT_COMMIT="$commit" MINT_OUT_NAME="$(basename "$out")" MINT_META="$meta_json" \
        MINT_GATE_SCRIPT="$gate_script" MINT_GATE_LABEL="$label" MINT_GATE_WEIGHT="$MINT_WEIGHT" \
        MINT_GATE_RESERVED="$GATE_RESERVED" \
        py sidecar "$PARTIAL" "$PARTIAL.sidecar" "${LEAN_ENV[@]}" --cmd "${cmd[@]}") \
    || refuse sidecar-failed "writing the sidecar of $out failed (exit $?)"
  # One publisher per --out from the last check to the end of the run, whose
  # publish no SIGINT, SIGTERM or SIGHUP cuts (the python half inherits the ignore).
  take_lock "$out.lock" out-locked
  trap '' INT TERM HUP
  out_free "$out" "$force"   # again, before anything is replaced: nothing appeared there during the mint
  # The python half places both by link(2), after setting the old pair aside
  # under --force, and refuses (undoing the publish) by itself what appears at
  # either target after the check above. The EXIT trap removes the partial names.
  if py publish "$PARTIAL" "$out" "$force"; then rc=0; else rc=$?; fi
  if [ "$rc" -ne 0 ] && [ "$rc" -ne "$PY_REFUSED" ]; then
    left=$(py unpublish "$PARTIAL" "$out") || left="; undoing it failed too (exit $?): see $out and its .sidecar.json"
    refuse out-publish-failed "the publish of $out exited $rc$left"
  fi
  [ "$rc" -eq 0 ] || exit 1   # the EXIT trap drops --out's lock
  echo "LEAN_EXPORT_MINT=ok out=$out sidecar=$out.sidecar.json sha256=$sha lean=${tc#v} format=$WANT_FORMAT exporter=$kind@$commit"
}

# Sourced with LEAN_EXPORT_MINT_LIB=1 (the self-test), only the functions load.
if [ -z "${LEAN_EXPORT_MINT_LIB:-}" ]; then main "$@"; fi
