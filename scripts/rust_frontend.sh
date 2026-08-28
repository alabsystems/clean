#!/usr/bin/env bash
# Resolve the cargo-frontend subcommand binary for the TOOLCHAIN THAT IS PINNED,
# then exec the requested gate with it. Nothing here relaxes a check: the same
# `fmt --all --check` / `clippy ... -D warnings` runs, under whatever name the
# pinned toolchain ships it as.
#
# WHY THIS EXISTS. On 2026-08-18, `rust-toolchain.toml` moved from
# `channel = "stable"` to `channel = "trust"`. That file's own header lists, as
# explicitly UNKNOWN at the time, "whether the installed stage2 ships the
# components this repo's gates need: rustfmt (trustfmt) for
# `cargo fmt --all --check`, clippy (tippy) for the workspace `-D warnings`
# gate". Measured here on 2026-08-20, at fa691b5a9, the answer is: it ships
# them, under RENAMED binaries, and the stock spelling therefore cannot run.
#
#   $ cargo fmt --all --check
#   error: 'cargo-fmt' is not installed for the custom toolchain 'trust'.
#   $ cargo clippy --version
#   error: 'cargo-clippy' is not installed for the custom toolchain 'trust'.
#
# The stage2 bin holds `targo-fmt` and `targo-tippy` instead -- cargo resolves
# `cargo <sub>` by looking for a `cargo-<sub>` sibling, so the rename alone
# breaks both gates. Two further traps, both measured:
#
#   * `targo fmt` through the rustup shim (~/.cargo/bin/targo) is REFUSED:
#     "OS-reported Targo executable ... is not a plain regular file; protected
#     Targo frontends cannot be symlinks or reparse points".
#   * `targo fmt` through the rustup toolchain dir is ALSO refused:
#     "protected Trust toolchain directory `~/.rustup/toolchains/trust/bin`
#     traverses a symlink or non-canonical path". The linked toolchain is a
#     symlink into trust's build tree, so every path through rustup is
#     non-canonical by construction.
#
# `rustc --print sysroot` reports the resolved, canonical stage2 directory, and
# the frontend invoked from there authenticates. That is what this resolves.
#
# Usage:  scripts/rust_frontend.sh fmt --all --check
#         scripts/rust_frontend.sh clippy --locked --workspace --all-targets -- -D warnings
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: rust_frontend.sh <fmt|clippy> [args...]" >&2
  exit 2
fi

sub="$1"; shift

# ------------------------------------------------------------------ selftest
# THE RETRY HAS TO BE DEMONSTRABLE OR IT IS JUST A CLAIM. Three arms against a
# synthetic frontend, in a temp sysroot this script resolves exactly as it
# resolves the real one (a `rustc` shim on PATH answering `--print sysroot`):
#
#   A  a transient identity abort that HEALS      -> green, and SAYS it retried
#   B  an identity failure that NEVER heals       -> REFUSES, non-zero, the
#                                                    frontend's own status kept
#   C  a real `-D warnings` violation             -> fails on attempt 1, and is
#                                                    NOT retried
#
# B and C are the arms that matter. B is what makes this a retry rather than a
# suppression: a persistent guard failure -- which is what an actual tamper
# looks like -- still ends RED. C is what keeps it narrow: an ordinary lint
# failure is not in the transient class and never gets a second chance to be
# green.
if [ "$sub" = "--selftest" ]; then
  # PORTABLE TEMPLATE, not `-t <prefix>`. BSD/macOS mktemp treats the `-t`
  # argument as a bare PREFIX and appends its own suffix; GNU coreutils treats
  # it as a TEMPLATE and refuses anything without >= 3 trailing X's
  # ("mktemp: too few X's in template"). This script shipped the BSD spelling,
  # so on Linux BOTH mktemp calls in this file exited non-zero before doing any
  # work -- `--selftest` exited 2, and `run_frontend` (below) exited 2 for the
  # real clippy/fmt gates, which made `scripts/local_gate.sh` full mode
  # unrunnable on a GNU host (measured 2026-08-27, coreutils 9.4). An explicit
  # template under $TMPDIR is accepted verbatim by both implementations.
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/rust_frontend_selftest.XXXXXX")" || exit 2
  trap 'rm -rf "$tmp"' EXIT
  mkdir -p "$tmp/sysroot/bin" "$tmp/shim" "$tmp/repo/scripts"
  printf '#!/bin/bash\nexit 0\n' > "$tmp/sysroot/bin/trustc"
  printf '#!/bin/bash\nexec "$(dirname "$0")/targo-$1" "${@:2}"\n' > "$tmp/sysroot/bin/targo"
  cat > "$tmp/sysroot/bin/targo-tippy" <<'FAKE'
#!/bin/bash
n=$(cat "$FAKE_STATE" 2>/dev/null || echo 0); n=$((n+1)); echo "$n" > "$FAKE_STATE"
case "$FAKE_MODE" in
  heals)
    if [ "$n" -le 1 ]; then
      echo "error: invalid branded Tippy driver identity: selected Trust toolchain directory ancestor \`$HOME\` changed while it was opened" >&2
      exit 2
    fi
    echo "    Finished (fake) on attempt $n"; exit 0 ;;
  never)
    echo "error: branded Tippy driver identity changed: selected Trust toolchain directory ancestor \`$HOME\` changed identity or contents" >&2
    exit 2 ;;
  *)
    echo "error: unused variable \`x\`: \`-D warnings\` in effect" >&2
    exit 101 ;;
esac
FAKE
  chmod +x "$tmp/sysroot/bin/trustc" "$tmp/sysroot/bin/targo" "$tmp/sysroot/bin/targo-tippy"
  printf '#!/bin/bash\n[ "$1" = "--print" ] && [ "$2" = "sysroot" ] && { echo "%s/sysroot"; exit 0; }\nexit 0\n' "$tmp" > "$tmp/shim/rustc"
  chmod +x "$tmp/shim/rustc"
  printf '[toolchain]\nchannel = "trust"\n' > "$tmp/repo/rust-toolchain.toml"
  cp "$0" "$tmp/repo/scripts/rust_frontend.sh"
  export PATH="$tmp/shim:$PATH" CLEAN_FRONTEND_BACKOFF=1
  fe="$tmp/repo/scripts/rust_frontend.sh"
  fails=0
  _arm() {  # name mode attempts want_rc want_attempts needle
    local name="$1" mode="$2" att="$3" want="$4" wantn="$5" needle="$6" out rc n
    export FAKE_MODE="$mode" FAKE_STATE="$tmp/n"
    rm -f "$tmp/n"
    set +e
    out="$(CLEAN_FRONTEND_ATTEMPTS="$att" "$fe" clippy -- -D warnings 2>&1)"; rc=$?
    set -e
    n="$(cat "$tmp/n" 2>/dev/null || echo 0)"
    if [ "$rc" != "$want" ] || [ "$n" != "$wantn" ] || ! printf '%s' "$out" | grep -q "$needle"; then
      echo "  [FAIL] $name: rc=$rc (want $want), frontend ran $n time(s) (want $wantn), needle '$needle' $(printf '%s' "$out" | grep -q "$needle" && echo present || echo ABSENT)"
      fails=$((fails + 1))
    else
      echo "  [ok]   $name: rc=$rc after $n frontend invocation(s)"
    fi
  }
  _arm "A transient identity abort that heals -> green, and says so" \
       heals 4 0 2 "PASSED on attempt 2"
  _arm "B identity failure that never heals -> REFUSES, status kept" \
       never 3 2 3 "REFUSING after 3 attempts"
  _arm "C a real -D warnings violation -> fails at once, unretried" \
       warn 4 101 1 "D warnings"
  echo "RUST_FRONTEND_SELFTEST arms=3 failed=$fails"
  [ "$fails" -eq 0 ] || exit 1
  exit 0
fi

case "$sub" in
  fmt)    candidates=("fmt") ;;
  clippy) candidates=("clippy" "tippy") ;;
  *)      candidates=("$sub") ;;
esac

sysroot="$(rustc --print sysroot)"
# Canonicalise: a symlinked sysroot is what the Trust frontends refuse.
if command -v python3 >/dev/null 2>&1; then
  sysroot="$(python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "$sysroot")"
fi
bindir="$sysroot/bin"

# The pin must actually be the toolchain we resolved. `rust-toolchain.toml` names
# the channel, but `rustc` only honours it through the rustup shim: if that
# toolchain is not linked, or ~/.cargo/bin is not on PATH, `rustc` is some other
# installation and `$bindir/cargo-clippy` below exists — so the stock passthrough
# fires and the gate runs a DIFFERENT LINT SET under the same name. That is the
# one thing this script promises not to do ("Nothing here relaxes a check").
# Measured 2026-08-22: with no `trust` toolchain linked the workspace gate ran
# stock cargo-clippy and reported clean while `targo tippy` had six
# -D warnings violations on the same tree.
pinned_channel=""
repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
if [ -f "$repo_root/rust-toolchain.toml" ]; then
  pinned_channel="$(sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' \
    "$repo_root/rust-toolchain.toml" | head -n 1)"
fi
case "$pinned_channel" in
  ""|stable|beta|nightly|nightly-*|1.*) : ;;   # upstream channels: passthrough is correct
  *)
    if [ ! -x "$bindir/${pinned_channel}c" ] && [ ! -x "$bindir/$pinned_channel" ]; then
      echo "rust_frontend.sh: rust-toolchain.toml pins channel \"$pinned_channel\", but the" >&2
      echo "  resolved sysroot is not that toolchain:" >&2
      echo "    sysroot: $sysroot" >&2
      echo "  Running the gate here would silently use a different frontend and a" >&2
      echo "  different lint set. Refusing." >&2
      echo "  Fix: link the toolchain and put the rustup shim first on PATH, e.g." >&2
      echo "    rustup toolchain link $pinned_channel <path-to-stage1-or-stage2-sysroot>" >&2
      echo "    export PATH=\"\$HOME/.cargo/bin:\$PATH\"" >&2
      exit 2
    fi
    ;;
esac

# ---------------------------------------------------------------- transient
# THE ANCESTOR-CHURN ABORT, and why a retry here is not a suppression.
#
# MEASURED CAUSE (2026-08-25). The Trust frontends authenticate the selected
# toolchain directory AND every ancestor of it up to `/`. In the stage2 that is
# installed on this machine, an ancestor is compared by its FULL `PathSnapshot`
# -- `len`, `mtime` and `ctime` included:
#
#   $ git -C ~/trust show 10f221fbe:src/tools/tippy/src/path_identity.rs
#   523:            if snapshot != expected.snapshot {
#   525:                "selected Trust toolchain directory ancestor `{}` changed
#                       identity or contents",
#
# Those three fields move on a DIRECTORY whenever any unrelated entry is created
# or removed inside it, and the chain reaches `$HOME` and `/Users`. So a
# sibling lane writing any file under the home directory aborts an in-flight
# lint. Reproduced here at 100%: six `targo tippy` runs on a 3-line crate, with
# a loop creating and removing ONE dotfile in `$HOME`, failed 6 of 6,
# while the same run on a quiescent machine passed. That is the whole of the
# "clippy leg is chronically UNKNOWN" story -- three lanes in a row, and 3 of
# the 12 REDs the suite runner has ever recorded.
#
# THE REAL FIX IS UPSTREAM AND ALREADY WRITTEN. `trust` commit 2929e33df4
# (2026-08-08 17:09, "an ancestor directory is checked for authority, not for
# contents") holds an ancestor to identity plus permission bits only, and its
# message names this exact failure string and this exact directory. Two more
# followed: 9e3286f3ea (2026-08-11) keeps the rename-and-restore signature, and
# d2043ab6ee (2026-08-20) authenticates a rustup-linked toolchain instead of
# refusing it. The installed stage2 is built from `10f221fbe` (2026-08-08
# 07:23 -- `rustc -V` reports `1.99.0-dev (10f221fbe 2026-08-08)`), which is an
# ancestor of NONE of the three. The deployed binary predates its own fix by
# nine hours and fifty minutes. Landing that fix means rebuilding stage2, which
# is a driver-weight job and a lane of its own; until then this is what the
# gates on this machine actually face.
#
# WHY A BOUNDED RETRY IS SOUND. This guard is detect-then-reject, not
# stable-handle execution: it observes the world twice and refuses when the two
# observations differ. A genuine tamper -- a replaced toolchain directory, a
# redirected symlink, a swapped subcommand binary -- is PERSISTENT: it is still
# there on the next observation, and on the one after that, so it fails every
# attempt and the gate still refuses. Unrelated churn in a shared directory is
# not persistent; it is over in milliseconds. Retrying separates the two by the
# only property that distinguishes them, and it does not lower the bar for
# either: the last attempt's verdict is the verdict, and an exhausted retry
# budget exits with the frontend's own status and its own diagnostic.
#
# WHAT IS NOT DONE HERE. This does not suppress the check, does not pass a flag
# that turns it off, and does not treat the diagnostic as a pass. It also does
# not touch any other failure: a clippy `-D warnings` violation is not in this
# class and is returned on the first attempt, unretried.
#
# THE MATCH IS THE CLASS, NOT ONE STRING. The lane note that opened this named
# only "changed identity or contents". The six-run reproduction printed THREE
# distinct tails from the same cause -- "changed identity or contents",
# "changed while it was opened", and "changed while its identity was captured"
# -- so a filter keyed to the first would have missed two thirds of them.
TRANSIENT_RE='selected (protected Trust subcommand|Trust toolchain directory ancestor).*(changed identity or contents|changed while it was opened|changed while its identity was captured)'
FRONTEND_ATTEMPTS="${CLEAN_FRONTEND_ATTEMPTS:-4}"
# First backoff, seconds; tripled each attempt. Overridable so --selftest
# can exercise the real ladder without paying 5+15+45 s for it.
FRONTEND_BACKOFF="${CLEAN_FRONTEND_BACKOFF:-5}"

run_frontend() {
  # "$@" is the full command line. Streams output live AND keeps a copy, so a
  # retry decision can be made without swallowing what the user sees.
  local log rc attempt delay
  # Explicit template, for the portability reason documented at the --selftest
  # arm above: `mktemp -t rust_frontend` is a BSD-only spelling and GNU
  # coreutils refuses it outright, which took every clippy/fmt gate in this
  # repo out on a Linux host before the frontend was ever invoked.
  log="$(mktemp "${TMPDIR:-/tmp}/rust_frontend.XXXXXX")" || { echo "rust_frontend.sh: mktemp failed" >&2; exit 2; }
  # shellcheck disable=SC2064
  trap "rm -f '$log'" EXIT
  attempt=1
  delay="$FRONTEND_BACKOFF"
  while :; do
    set +e
    "$@" 2>&1 | tee "$log"
    rc="${PIPESTATUS[0]}"
    set -e
    if [ "$rc" -eq 0 ]; then
      if [ "$attempt" -gt 1 ]; then
        echo "rust_frontend.sh: attempts 1..$((attempt - 1)) aborted on the Trust" >&2
        echo "  ancestor-identity guard -- not on this tree. See the header of this" >&2
        echo "  script: the installed stage2 (trust 10f221fbe) predates trust" >&2
        echo "  2929e33df4, which is the fix." >&2
        # LAST line on purpose: scripts/verify_runner.py records the verbatim
        # FINAL line of a gate as its verdict, so a retried pass must not be
        # filed as though it had been a clean first pass.
        echo "rust_frontend.sh: PASSED on attempt $attempt of $FRONTEND_ATTEMPTS (not a first-pass green)." >&2
      fi
      return 0
    fi
    if [ "$attempt" -ge "$FRONTEND_ATTEMPTS" ] \
       || ! grep -Eq "$TRANSIENT_RE" "$log"; then
      if [ "$attempt" -gt 1 ]; then
        echo "rust_frontend.sh: every one of $attempt attempts hit the Trust" >&2
        echo "  ancestor-identity guard. A retry budget distinguishes churn (transient)" >&2
        echo "  from tampering (persistent); this did not heal." >&2
        echo "rust_frontend.sh: REFUSING after $attempt attempts -- the gate is RED." >&2
      fi
      return "$rc"
    fi
    echo "rust_frontend.sh: attempt $attempt of $FRONTEND_ATTEMPTS aborted on the Trust" >&2
    echo "  ancestor-identity guard (a sibling process wrote under an ancestor of the" >&2
    echo "  toolchain, most likely \$HOME). This is NOT a verdict on the tree and is" >&2
    echo "  NOT being treated as a pass -- retrying in ${delay}s. A real tamper is" >&2
    echo "  persistent and will still be here." >&2
    sleep "$delay"
    attempt=$((attempt + 1))
    delay=$((delay * 3))
  done
}

# Try, in order: the stock `cargo <sub>`, then every (driver, subcommand) pair
# the pinned sysroot actually ships. The stock spelling comes FIRST so that on
# an ordinary upstream toolchain this script is a no-op passthrough.
for name in "${candidates[@]}"; do
  if [ -x "$bindir/cargo-$name" ]; then
    run_frontend cargo "$name" "$@"
    exit $?
  fi
done

for driver in targo cargo; do
  [ -x "$bindir/$driver" ] || continue
  for name in "${candidates[@]}"; do
    if [ -x "$bindir/$driver-$name" ]; then
      run_frontend "$bindir/$driver" "$name" "$@"
      exit $?
    fi
  done
done

echo "rust_frontend.sh: no frontend for '$sub' in $bindir" >&2
echo "  looked for: cargo-<n> and <targo|cargo>-<n> with n in: ${candidates[*]}" >&2
exit 127
