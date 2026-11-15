#!/usr/bin/env bash
# Run a format/lint gate through the Trust toolchain's own frontend:
#
#   scripts/rust_frontend.sh fmt    <args>   ->  targo fmt   <args>
#   scripts/rust_frontend.sh clippy <args>   ->  targo tippy <args>
#   scripts/rust_frontend.sh --targo         ->  print the targo every gate runs
#
# Nothing here relaxes a check: the same `fmt --all --check` /
# `clippy ... -D warnings` runs, under the name Trust ships it as, and the
# frontend's exit status is the gate's.
#
# WHICH TARGO. This file is the ONE place a gate script resolves targo; the
# Python gates ask it (`--targo`) rather than spell the rule a second time.
#
#   1. `$TARGO`, when set: an explicit choice (a selftest's stub, or an
#      operator's). Relative paths are anchored to the caller's directory;
#      it must be a plain regular executable
#      file -- targo refuses to run as a symlink, so one is refused HERE, by
#      name, before anything runs.
#   2. When ATPKG_BIN is set, ask its managed `trustc --print sysroot` and
#      use that root's canonical bin/targo. A failed managed lookup refuses;
#      it does not fall through to another compiler installation.
#   3. Otherwise the canonical Trust targo, `$(rustc +trust --print sysroot)/bin/targo`
#      (CLAUDE.md, "Verifying changes"), with the sysroot's own directory
#      canonicalised and the same plain-regular-file requirement. `+trust` is
#      rustup's proxy syntax, so the sysroot is asked of rustup itself
#      (`rustup run trust rustc --print sysroot`; rustup from PATH, else
#      `$CARGO_HOME/bin`), and `rustc +trust` is the fallback only when no
#      rustup exists. A plain Trust `rustc` first on PATH -- the pre-push
#      hook puts the Trust sysroot's own `bin/` there (7a4cc03ea) -- reads
#      `+trust` as an input file and fails; measured 2026-09-29, the first
#      version of this rule refused inside the hook for exactly that reason.
#
# A targo on PATH is never a resolver input. Until 2026-09-29 this was
# "`$TARGO`, otherwise `targo` on PATH", and on this machine `~/.cargo/bin`
# sits ahead of the Trust sysroot on PATH while `~/.cargo/bin/targo` is a
# rustup symlink: targo refuses itself there ("OS-reported Targo executable
# ... is not a plain regular file"), so the `dep-boundary` and `lint-coverage`
# pre-push legs went RED on every tree, for every pusher whose PATH had that
# order, and GREEN for one whose PATH did not. A gate whose verdict depends on
# the pusher's PATH order is wrong in both directions, so the resolution no
# longer reads PATH at all. It fails closed (rc 127) with the reason when it
# cannot resolve; there is no stock fallback (owner directive 2026-09-28:
# ALab systems build with Trust), because a stock frontend is a different lint
# set under the same gate name.
#
# History: until 2026-09-28 this resolved the frontend through
# `rustc --print sysroot`, tried a stock `cargo <sub>` passthrough first, and
# retried a Trust ancestor-identity abort up to six times -- a workaround for
# stage 10f221fbe, whose fix (trust 2929e33df4) is an ancestor of the
# installed 321aaeda7. That text: `git show 7330fa6ce:scripts/rust_frontend.sh`.
#
# Usage:  scripts/rust_frontend.sh fmt --all --check
#         scripts/rust_frontend.sh clippy --locked --workspace --all-targets -- -D warnings
#         scripts/rust_frontend.sh --targo
#         scripts/rust_frontend.sh --selftest
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: rust_frontend.sh <fmt|clippy> [args...] | --targo | --selftest" >&2
  exit 2
fi

sub="$1"; shift

# A plain regular executable file, or the reason it is not one (on stderr).
_plain_executable() {  # <path> <what>
  if [ -L "$1" ]; then
    echo "$2 $1 is a symlink; targo refuses to run as one (\"not a plain regular file\")." >&2
    return 1
  fi
  if [ ! -f "$1" ] || [ ! -x "$1" ]; then
    echo "$2 $1 is not an executable regular file." >&2
    return 1
  fi
}

# Print the targo every gate runs, or explain on stderr why there is none.
resolve_targo() {
  local sysroot dir rustup
  if [ -n "${TARGO:-}" ]; then
    case "$TARGO" in
      *$'\n'*|*$'\r'*)
        echo '$TARGO pathname cannot contain line breaks.' >&2
        return 1 ;;
    esac
    _plain_executable "$TARGO" "\$TARGO names" || return 1
    case "$TARGO" in
      /*) printf '%s' "$TARGO" ;;
      *) dir="$(pwd -P && printf .)" || return 1
         dir="${dir%.}"
         dir="${dir%$'\n'}"
         case "$dir" in
           *$'\n'*|*$'\r'*)
             echo 'caller directory cannot contain line breaks.' >&2
             return 1 ;;
         esac
         printf '%s/%s' "$dir" "$TARGO" ;;
    esac
    return 0
  fi
  if [ -n "${ATPKG_BIN:-}" ]; then
    if ! sysroot="$("$ATPKG_BIN/trustc" --print sysroot 2>&1)" || [ -z "$sysroot" ]; then
      echo "managed Trust sysroot lookup failed: ${sysroot:-no output}" >&2
      return 1
    fi
  else
    rustup="$(command -v rustup 2>/dev/null)" \
      || rustup="${CARGO_HOME:-$HOME/.cargo}/bin/rustup"
    if [ -x "$rustup" ]; then
      if ! sysroot="$("$rustup" run trust rustc --print sysroot 2>&1)" || [ -z "$sysroot" ]; then
        echo "\`$rustup run trust rustc --print sysroot\` failed: ${sysroot:-no output}" >&2
        return 1
      fi
    elif ! sysroot="$(rustc +trust --print sysroot 2>&1)" || [ -z "$sysroot" ]; then
      echo "no rustup, and \`rustc +trust --print sysroot\` failed: ${sysroot:-no output}" >&2
      return 1
    fi
  fi
  sysroot="$(printf '%s\n' "$sysroot" | tail -n 1)"
  if ! dir="$(cd "$sysroot/bin" 2>/dev/null && pwd -P)"; then
    echo "the Trust sysroot lookup names ($sysroot) has no bin/ directory." >&2
    return 1
  fi
  _plain_executable "$dir/targo" "the Trust sysroot's targo" || return 1
  printf '%s' "$dir/targo"
}

_refuse_no_targo() {  # <frontend>
  echo "rust_frontend.sh: cannot resolve the Trust targo (reason above)." >&2
  echo "  Gates never take \`targo\` from PATH: set TARGO to a targo binary, or repair" >&2
  echo "  the \`trust\` toolchain (\`aterm pkg doctor\`, then \`aterm pkg repair\`)." >&2
  [ -n "$1" ] && echo "  The gate runs \`targo $1\` and has no stock fallback." >&2
  exit 127
}

# ------------------------------------------------------------------ selftest
# Arms against synthetic toolchains; none of them reaches a real one:
#
#   A  a passing frontend ($TARGO)      -> rc 0, and the frontend received
#                                          `tippy` plus the caller's args verbatim
#   B  a real `-D warnings` violation   -> the frontend's own rc (101), after
#                                          exactly ONE invocation
#   C  no $TARGO, no Trust sysroot      -> REFUSES rc 127 naming targo; a stock
#                                          `cargo` and a PATH `targo` never run
#   D  the canonical targo resolves     -> IT runs, and a `targo` FIRST on PATH
#                                          (a symlink, as ~/.cargo/bin's is) never
#                                          does: PATH order cannot choose the targo
#   E  $TARGO names a symlink           -> REFUSES rc 127 before anything runs
#   F  the sysroot's targo is a symlink -> REFUSES rc 127 before anything runs
#   G  `--targo`                        -> prints the canonical path, runs nothing
#   H  a plain Trust `rustc` FIRST on   -> still resolves the canonical targo
#      PATH (it reads `+trust` as a file)  through rustup (the pre-push hook's
#                                          PATH since 7a4cc03ea)
#   I  no rustup at all                 -> `rustc +trust` (a rustup-shaped rustc)
#   J  a stock `cargo` FIRST on PATH    -> the canonical targo runs, once; the
#      and the canonical targo resolves    stock one never does
#
# B is what keeps the gate honest (a failing lint is the gate's verdict); C
# keeps it Trust (no silent stock frontend under the same name); D is the
# 2026-09-29 defect -- with rule 2 reverted to "`targo` on PATH" it goes red,
# because the PATH decoy runs; E and F keep a refusal loud and early; H is the
# second 2026-09-29 defect -- with rule 2 asking `rustc +trust` whatever rustc
# PATH names, it refused inside the hook. J keeps it Trust when BOTH exist: C
# has a stock `cargo` but no targo, every other arm a targo but no stock
# `cargo`, so a dispatch that prefers stock whenever both exist passed A-I
# (measured on a mutated copy). Every arm runs with CARGO_HOME at an empty
# directory, so the machine's own rustup is never the one asked.
if [ "$sub" = "--selftest" ]; then
  # Explicit template: GNU mktemp refuses the BSD `-t <prefix>` spelling.
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/rust_frontend_selftest.XXXXXX")" || exit 2
  trap 'rm -rf "$tmp"' EXIT
  mkdir -p "$tmp/bin" "$tmp/stockonly" "$tmp/sysroot/bin" "$tmp/decoy" \
           "$tmp/badsys/sysroot/bin" "$tmp/rustc" "$tmp/badrustc" "$tmp/rustup" \
           "$tmp/badrustup" "$tmp/plainrustc" "$tmp/nocargohome"
  cat > "$tmp/bin/targo" <<'FAKE'
#!/bin/bash
echo "targo $*" >> "$FAKE_LOG"
case "$FAKE_MODE" in
  pass) echo "    Finished (fake)"; exit 0 ;;
  *) echo "error: unused variable \`x\`: \`-D warnings\` in effect" >&2; exit 101 ;;
esac
FAKE
  # The canonical one logs its own name, so D can tell WHICH targo ran.
  sed 's/echo "targo /echo "canonical-targo /' "$tmp/bin/targo" > "$tmp/sysroot/bin/targo"
  printf '#!/bin/bash\necho "DECOY PATH TARGO RAN $*" >> "$FAKE_LOG"\nexit 0\n' > "$tmp/decoy/decoy-targo"
  printf '#!/bin/bash\necho "STOCK CARGO RAN $*" >> "$FAKE_LOG"\nexit 0\n' > "$tmp/stockonly/cargo"
  # A rustup-shaped `rustc`: `+trust --print sysroot` names the fake sysroot.
  printf '#!/bin/bash\n[ "$*" = "+trust --print sysroot" ] || exit 2\necho "%s"\n' \
    "$tmp/sysroot" > "$tmp/rustc/rustc"
  printf '#!/bin/bash\n[ "$*" = "+trust --print sysroot" ] || exit 2\necho "%s"\n' \
    "$tmp/badsys/sysroot" > "$tmp/badrustc/rustc"
  # A rustup: `run trust rustc --print sysroot` names the fake sysroot.
  printf '#!/bin/bash\n[ "$*" = "run trust rustc --print sysroot" ] || exit 2\necho "%s"\n' \
    "$tmp/sysroot" > "$tmp/rustup/rustup"
  printf '#!/bin/bash\n[ "$*" = "run trust rustc --print sysroot" ] || exit 2\necho "%s"\n' \
    "$tmp/badsys/sysroot" > "$tmp/badrustup/rustup"
  # A Trust sysroot's own rustc: no rustup proxy, so `+trust` is an input file.
  printf '#!/bin/bash\necho "error: couldn'"'"'t read \`$1\`: No such file or directory" >&2\nexit 1\n' \
    > "$tmp/plainrustc/rustc"
  chmod +x "$tmp/bin/targo" "$tmp/sysroot/bin/targo" "$tmp/decoy/decoy-targo" \
    "$tmp/stockonly/cargo" "$tmp/rustc/rustc" "$tmp/badrustc/rustc" "$tmp/rustup/rustup" \
    "$tmp/badrustup/rustup" "$tmp/plainrustc/rustc"
  ln -s "$tmp/decoy/decoy-targo" "$tmp/decoy/targo"
  ln -s "$tmp/bin/targo" "$tmp/targo-link"
  ln -s "$tmp/bin/targo" "$tmp/badsys/sysroot/bin/targo"
  fe="$(cd "$(dirname "$0")" && pwd -P)/$(basename "$0")"
  fails=0
  FRONTEND_TEST_ATPKG_BIN=
  FRONTEND_TEST_CWD=
  # name mode TARGO-or-"" path want_rc want_invocations log_needle out_needle [args...]
  _arm() {
    local name="$1" mode="$2" targo="$3" path="$4" want="$5" wantn="$6" logneedle="$7" \
          outneedle="$8" out rc n
    shift 8
    [ "$#" -gt 0 ] || set -- clippy --locked --workspace -- -D warnings
    : > "$tmp/log"
    set +e
    if [ -n "$targo" ]; then
      out="$(cd "${FRONTEND_TEST_CWD:-$PWD}" && env TARGO="$targo" PATH="$path" CARGO_HOME="$tmp/nocargohome" FAKE_MODE="$mode" \
        ATPKG_BIN="${FRONTEND_TEST_ATPKG_BIN:-}" FAKE_LOG="$tmp/log" bash "$fe" "$@" 2>&1)"; rc=$?
    else
      out="$(cd "${FRONTEND_TEST_CWD:-$PWD}" && env -u TARGO PATH="$path" CARGO_HOME="$tmp/nocargohome" FAKE_MODE="$mode" \
        ATPKG_BIN="${FRONTEND_TEST_ATPKG_BIN:-}" FAKE_LOG="$tmp/log" bash "$fe" "$@" 2>&1)"; rc=$?
    fi
    set -e
    n="$(grep -c . "$tmp/log" || true)"
    local ok=1
    [ "$rc" = "$want" ] || ok=0
    [ "$n" = "$wantn" ] || ok=0
    if [ -n "$logneedle" ]; then grep -qF -- "$logneedle" "$tmp/log" || ok=0; fi
    printf '%s' "$out" | grep -qF -- "$outneedle" || ok=0
    if [ "$ok" -ne 1 ]; then
      echo "  [FAIL] $name: rc=$rc (want $want), invocations=$n (want $wantn), log: $(tr '\n' '|' < "$tmp/log") out: $(printf '%s' "$out" | tr '\n' '|')"
      fails=$((fails + 1))
    else
      echo "  [ok]   $name: rc=$rc after $n invocation(s)"
    fi
  }
  mkdir -p "$tmp/managed" "$tmp/managed root/bin" "$tmp/managedfail" \
    "$tmp/managedempty" "$tmp/managedlink" "$tmp/managedmissing"
  sed 's/echo "targo /echo "managed-targo /' "$tmp/bin/targo" > "$tmp/managed root/bin/targo"
  printf '#!/bin/bash\n[ "$*" = "--print sysroot" ] || exit 2\necho "%s"\n' \
    "$tmp/managed root" > "$tmp/managed/trustc"
  printf '#!/bin/bash\necho "managed lookup refused" >&2\nexit 51\n' > "$tmp/managedfail/trustc"
  printf '#!/bin/bash\nexit 0\n' > "$tmp/managedempty/trustc"
  printf '#!/bin/bash\necho "%s"\n' "$tmp/badsys/sysroot" > "$tmp/managedlink/trustc"
  printf '#!/bin/bash\necho "%s"\n' "$tmp/absent" > "$tmp/managedmissing/trustc"
  chmod +x "$tmp/managed root/bin/targo" "$tmp/managed/trustc" \
    "$tmp/managedfail/trustc" "$tmp/managedempty/trustc" \
    "$tmp/managedlink/trustc" "$tmp/managedmissing/trustc"
  _arm "A a passing frontend -> 0, args verbatim" \
       pass "$tmp/bin/targo" "/usr/bin:/bin" 0 1 "targo tippy --locked --workspace -- -D warnings" "Finished (fake)"
  _arm "B a real -D warnings violation -> the frontend's rc, once" \
       warn "$tmp/bin/targo" "/usr/bin:/bin" 101 1 "targo tippy" "D warnings"
  _arm "C no TARGO, no Trust sysroot -> refuses 127; stock cargo and a PATH targo never run" \
       pass "" "$tmp/decoy:$tmp/stockonly:/usr/bin:/bin" 127 0 "" "no stock fallback"
  _arm "D the canonical targo runs; a symlinked targo FIRST on PATH never does" \
       pass "" "$tmp/decoy:$tmp/rustup:/usr/bin:/bin" 0 1 "canonical-targo tippy --locked" "Finished (fake)"
  _arm "E TARGO names a symlink -> refused 127 before anything runs" \
       pass "$tmp/targo-link" "$tmp/decoy:/usr/bin:/bin" 127 0 "" "is a symlink"
  _arm "F the sysroot's targo is a symlink -> refused 127 before anything runs" \
       pass "" "$tmp/decoy:$tmp/badrustup:/usr/bin:/bin" 127 0 "" "is a symlink"
  _arm "G --targo prints the canonical path and runs nothing" \
       pass "" "$tmp/decoy:$tmp/rustup:/usr/bin:/bin" 0 0 "" "$(cd "$tmp/sysroot/bin" && pwd -P)/targo" --targo
  _arm "H a plain Trust rustc FIRST on PATH (the hook's PATH) still resolves through rustup" \
       pass "" "$tmp/decoy:$tmp/plainrustc:$tmp/rustup:/usr/bin:/bin" 0 1 "canonical-targo tippy --locked" "Finished (fake)"
  _arm "I no rustup at all: a rustup-shaped rustc answers +trust" \
       pass "" "$tmp/decoy:$tmp/rustc:/usr/bin:/bin" 0 1 "canonical-targo tippy --locked" "Finished (fake)"
  _arm "J a stock cargo FIRST on PATH with the canonical targo resolvable -> targo runs, stock never" \
       pass "" "$tmp/stockonly:$tmp/rustup:/usr/bin:/bin" 0 1 "canonical-targo tippy --locked --workspace -- -D warnings" "Finished (fake)"
  FRONTEND_TEST_ATPKG_BIN="$tmp/managed" _arm "K managed Trust wins over rustup and PATH decoys; spaces preserved" \
       pass "" "$tmp/decoy:$tmp/rustup:/usr/bin:/bin" 0 1 "managed-targo tippy --locked" "Finished (fake)"
  FRONTEND_TEST_ATPKG_BIN="$tmp/managed" _arm "L managed --targo prints the plain canonical path" \
       pass "" "$tmp/decoy:/usr/bin:/bin" 0 0 "" "$(cd "$tmp/managed root/bin" && pwd -P)/targo" --targo
  FRONTEND_TEST_ATPKG_BIN="$tmp/managedfail" _arm "M managed probe fails; no rustup or stock fallback" \
       pass "" "$tmp/decoy:$tmp/stockonly:$tmp/rustup:/usr/bin:/bin" 127 0 "" "managed Trust sysroot lookup failed"
  FRONTEND_TEST_ATPKG_BIN="$tmp/managedempty" _arm "N empty managed sysroot refuses" \
       pass "" "$tmp/rustup:/usr/bin:/bin" 127 0 "" "no output"
  FRONTEND_TEST_ATPKG_BIN="$tmp/managedlink" _arm "O managed targo symlink refuses before execution" \
       pass "" "$tmp/rustup:/usr/bin:/bin" 127 0 "" "is a symlink"
  FRONTEND_TEST_ATPKG_BIN="$tmp/managedfail" _arm "P explicit TARGO precedes managed lookup" \
       pass "$tmp/bin/targo" "/usr/bin:/bin" 0 1 "targo tippy" "Finished (fake)"
  FRONTEND_TEST_ATPKG_BIN="$tmp/managedmissing" _arm "Q absent managed sysroot refuses" \
       pass "" "$tmp/rustup:/usr/bin:/bin" 127 0 "" "has no bin/ directory"
  FRONTEND_TEST_ATPKG_BIN="$tmp/no-managed-tools" _arm "R missing managed trustc refuses; rustup does not rescue it" \
       pass "" "$tmp/rustup:/usr/bin:/bin" 127 0 "" "managed Trust sysroot lookup failed"
  FRONTEND_TEST_ATPKG_BIN="$tmp/managed" _arm "S managed lint failure preserves its status exactly once" \
       warn "" "$tmp/decoy:/usr/bin:/bin" 101 1 "managed-targo tippy" "D warnings"
  FRONTEND_TEST_CWD="$tmp/bin" _arm "T bare explicit filename executes the checked cwd file, never PATH" \
       pass targo "$tmp/decoy:/usr/bin:/bin" 0 1 "targo tippy --locked" "Finished (fake)"
  FRONTEND_TEST_CWD="$tmp/bin" _arm "U bare explicit --targo returns an anchored path" \
       pass targo "$tmp/decoy:/usr/bin:/bin" 0 0 "" "$(cd "$tmp/bin" && pwd -P)/targo" --targo
  FRONTEND_TEST_CWD="$tmp" _arm "V explicit relative path with spaces forwards the lint failure once" \
       warn "managed root/bin/targo" "$tmp/decoy:/usr/bin:/bin" 101 1 "managed-targo tippy" "D warnings"
  FRONTEND_TEST_CWD="$tmp" _arm "W relative explicit --targo is anchored before returning" \
       pass "managed root/bin/targo" "$tmp/decoy:/usr/bin:/bin" 0 0 "" "$(cd "$tmp" && pwd -P)/managed root/bin/targo" --targo
  cp "$tmp/bin/targo" "$tmp/bin/targo"$'\n'
  cp "$tmp/bin/targo" "$tmp/bin/targo"$'\r'
  _arm "X explicit trailing LF refuses before command substitution can select another file" \
       pass "$tmp/bin/targo"$'\n' "$tmp/decoy:/usr/bin:/bin" 127 0 "" "cannot contain line breaks"
  _arm "Y explicit CR refuses the ambiguous line output" \
       pass "$tmp/bin/targo"$'\r' "$tmp/decoy:/usr/bin:/bin" 127 0 "" "cannot contain line breaks"
  mkdir -p "$tmp/bin"$'\n' "$tmp/bin"$'\r'
  cp "$tmp/bin/targo" "$tmp/bin"$'\n'/targo
  cp "$tmp/bin/targo" "$tmp/bin"$'\r'/targo
  FRONTEND_TEST_CWD="$tmp/bin"$'\n' _arm "Z caller directory ending LF refuses without selecting its neighbor" \
       pass targo "$tmp/decoy:/usr/bin:/bin" 127 0 "" "caller directory cannot contain line breaks"
  FRONTEND_TEST_CWD="$tmp/bin"$'\r' _arm "AA caller directory containing CR refuses ambiguous line output" \
       pass targo "$tmp/decoy:/usr/bin:/bin" 127 0 "" "caller directory cannot contain line breaks"
  echo "RUST_FRONTEND_SELFTEST arms=27 failed=$fails"
  [ "$fails" -eq 0 ] || exit 1
  exit 0
fi

if [ "$sub" = "--targo" ]; then
  targo="$(resolve_targo)" || _refuse_no_targo ""
  printf '%s\n' "$targo"
  exit 0
fi

case "$sub" in
  fmt)    frontend="fmt" ;;
  clippy) frontend="tippy" ;;
  *)      frontend="$sub" ;;
esac

targo="$(resolve_targo)" || _refuse_no_targo "$frontend"

exec "$targo" "$frontend" "$@"
