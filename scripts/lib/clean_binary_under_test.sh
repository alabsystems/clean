# shellcheck shell=bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Resolve the `clean` binary a MEASURING gate is about to judge the tree with,
# and refuse one that cannot be shown to have been built from this checkout.
#
# WHY THIS EXISTS. A gate that stamps a soundness number is making a claim about
# a kernel. If it measures with whatever binary happens to be lying around, the
# number is about a DIFFERENT kernel and the gate's own ratchet records it as
# though it were this one. Two gates resolved a binary like this:
#
#     [ -z "$CLEAN_BIN" ] && [ -x target/release/clean ] && CLEAN_BIN=target/release/clean
#     [ -z "$CLEAN_BIN" ] && [ -x target/debug/clean ]   && CLEAN_BIN=target/debug/clean
#     [ -z "$CLEAN_BIN" ] && CLEAN_BIN="$(command -v clean 2>/dev/null || true)"
#
# with no freshness check of any kind. `scripts/kv_ratchet_gate.sh`'s own
# comment named the hazard verbatim -- "a stale PATH binary would re-stamp with
# the wrong kernel and yield a wrong count (false pass/fail)" -- and then did
# not guard it. `scripts/kv_invariance_gate.sh` carried the identical three
# lines, and ITS registry row claims soundness and is already demonstrated, so
# a signed-off row was resting on the same hazard.
#
# It was not hypothetical. Measured 2026-09-15: `target/release/clean` on this
# box was built 2026-08-27, carries a `CLEAN_BUILD_GIT_SHA` that resolves to no
# commit in this clone at all, and would have been picked silently by both
# gates.
#
# THE HOUSE PATTERN ALREADY EXISTED and these two were the outliers.
# `scripts/source_elab_gate.sh` says it plainly: "target/release/clean only -- a
# debug or stale PATH binary would measure the wrong elaborator and mint a wrong
# baseline. Never builds anything itself." This helper is that rule, plus the
# positive freshness check, in one place with both callers.
#
# HOW FRESHNESS IS DECIDED. `crates/clean-cli/build.rs` already embeds
# `CLEAN_BUILD_GIT_SHA` (a full `git rev-parse HEAD`) for exactly this purpose --
# its own doc comment cites "the incident where a chain script picked a 5-day-old
# binary via `ls | head -1`". Nothing outside the Isabelle doctor ever read it.
# So the check is: does the binary contain this checkout's HEAD sha as an
# embedded string? That is a positive test with no false positive -- a binary
# built at HEAD carries it -- and it needs no CLI verb, no build and no `git`
# call beyond `rev-parse`.
#
# WHAT IT DELIBERATELY DOES NOT DO. It never builds anything: a measuring gate
# that silently builds its own subject decides when to measure, and a caller
# that wanted a build would have to pay it under the memory gate anyway. It also
# does not treat an explicit `$CLEAN_BIN` as an exemption. That override exists
# for out-of-tree runs (a worktree whose target/ is redirected), which is a
# statement about WHERE the binary is, not about whether it may be stale.
#
# USAGE
#   source "$REPO_ROOT/scripts/lib/clean_binary_under_test.sh"
#   resolve_clean_binary_under_test || case $? in
#     2) skip no-binary "...";;      # nothing to measure with
#     3) fail stale-binary "$CLEAN_BIN_REASON";;   # a correctness refusal
#   esac
#   # on success $CLEAN_BIN_UNDER_TEST is set and verified
#
# RETURNS
#   0  $CLEAN_BIN_UNDER_TEST is set and carries this checkout's HEAD
#   2  ABSENT: no candidate binary exists (the caller decides skip vs fail)
#   3  UNVERIFIABLE: a binary exists but cannot be shown to be built from HEAD
# On 2 and 3, $CLEAN_BIN_REASON carries a one-line human explanation.
#
# A caller should map 2 to its own "nothing to measure" path and 3 to a hard
# FAILURE, and should place the call BEFORE any admission or deferral check. A
# correctness refusal outranks a deferral: a stale binary must not be able to
# arrive as a green "skipped:low-memory".

resolve_clean_binary_under_test() {
  CLEAN_BIN_UNDER_TEST=""
  CLEAN_BIN_REASON=""

  local candidate="${CLEAN_BIN:-}"
  local source_desc
  if [ -n "$candidate" ]; then
    source_desc="\$CLEAN_BIN"
    if [ ! -x "$candidate" ]; then
      CLEAN_BIN_REASON="\$CLEAN_BIN is set to '$candidate', which is not an executable file"
      return 3
    fi
  else
    # target/release ONLY. No debug build: a debug kernel is a different program
    # for anything timing- or optimisation-sensitive and is not what a released
    # measurement is about. No PATH lookup: `command -v clean` has resolved to
    # another user's home directory on this machine before.
    source_desc="target/release/clean"
    if [ -x target/release/clean ]; then
      candidate=target/release/clean
    else
      CLEAN_BIN_REASON="no target/release/clean (build it with: targo --unverified build --locked --release --bin clean)"
      return 2
    fi
  fi

  local head_sha
  head_sha="$(git rev-parse HEAD 2>/dev/null || true)"
  if [ -z "$head_sha" ]; then
    CLEAN_BIN_REASON="cannot read this checkout's HEAD, so '$candidate' cannot be shown to match it"
    return 3
  fi

  # `grep -a` treats the binary as text; the stamp is a plain &'static str in
  # rodata. Output is discarded -- only the match matters.
  if ! grep -a -q -- "$head_sha" "$candidate" 2>/dev/null; then
    CLEAN_BIN_REASON="$source_desc ('$candidate') does not carry this checkout's HEAD ($head_sha) in its embedded CLEAN_BUILD_GIT_SHA stamp, so it was built from different source; rebuild with: targo --unverified build --locked --release --bin clean"
    return 3
  fi

  CLEAN_BIN_UNDER_TEST="$candidate"
  return 0
}

# Self-test. Exercised by scripts/check_script_selftests.py through the callers,
# and runnable directly: `bash scripts/lib/clean_binary_under_test.sh --selftest`.
# Every arm is a REFUSAL arm plus one acceptance arm, because a resolver that
# accepts everything and a resolver that refuses everything are both useless and
# only the pair distinguishes them.
_clean_binary_under_test_selftest() {
  local tmp rc fails=0 arms=0 head_sha
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/cbut_selftest.XXXXXX")" || return 2
  ( cd "$tmp" && git init -q . && git -c user.email=t@t -c user.name=t commit -q --allow-empty -m x ) || {
    rm -rf "$tmp"; echo "  [RED] selftest could not create a git fixture" >&2; return 2; }
  head_sha="$(git -C "$tmp" rev-parse HEAD)"

  _arm() { # name expected_rc
    arms=$((arms + 1))
    if [ "$rc" != "$2" ]; then
      echo "  [RED] clean_binary_under_test arm $1: rc=$rc (want $2)" >&2
      fails=$((fails + 1))
    else
      echo "  self-test ARM ok: $1 -> rc=$rc"
    fi
  }

  ( cd "$tmp" || exit 2
    mkdir -p target/release

    # 1. nothing there at all -> ABSENT, not a refusal and not a pass
    CLEAN_BIN="" resolve_clean_binary_under_test; echo "$?" > rc1

    # 2. a binary that does NOT carry HEAD -> UNVERIFIABLE
    printf 'not the right sha: 0000000000000000000000000000000000000000\n' > target/release/clean
    chmod +x target/release/clean
    CLEAN_BIN="" resolve_clean_binary_under_test; echo "$?" > rc2

    # 3. a binary that DOES carry HEAD -> accepted (the acceptance control:
    #    without it, a resolver that refused everything would pass arms 1-2)
    printf 'stamped %s here\n' "$(git rev-parse HEAD)" > target/release/clean
    chmod +x target/release/clean
    CLEAN_BIN="" resolve_clean_binary_under_test; echo "$?" > rc3

    # 4. an explicit override is NOT an exemption: same stale binary, named
    #    directly, still refused
    printf 'not the right sha\n' > elsewhere; chmod +x elsewhere
    CLEAN_BIN=./elsewhere resolve_clean_binary_under_test; echo "$?" > rc4

    # 5. an explicit override pointing at nothing executable -> refusal, never
    #    a silent fall-through to target/release
    printf 'stamped %s here\n' "$(git rev-parse HEAD)" > target/release/clean
    CLEAN_BIN=./does_not_exist resolve_clean_binary_under_test; echo "$?" > rc5
  )

  rc="$(cat "$tmp/rc1" 2>/dev/null)"; _arm "no binary anywhere -> ABSENT" 2
  rc="$(cat "$tmp/rc2" 2>/dev/null)"; _arm "binary without HEAD's stamp -> UNVERIFIABLE" 3
  rc="$(cat "$tmp/rc3" 2>/dev/null)"; _arm "binary carrying HEAD's stamp -> accepted" 0
  rc="$(cat "$tmp/rc4" 2>/dev/null)"; _arm "explicit CLEAN_BIN is not an exemption" 3
  rc="$(cat "$tmp/rc5" 2>/dev/null)"; _arm "explicit CLEAN_BIN that is not executable -> refusal" 3
  rm -rf "$tmp"

  if [ "$fails" -ne 0 ]; then
    echo "clean_binary_under_test selftest: $fails of $arms arms misbehave" >&2
    return 1
  fi
  echo "clean_binary_under_test selftest: $arms/$arms arms behave"
  return 0
}

# Only when executed directly, never when sourced.
if [ "${BASH_SOURCE[0]}" = "${0}" ] && [ "${1:-}" = "--selftest" ]; then
  _clean_binary_under_test_selftest
  exit $?
fi
