#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Self-test for scripts/install-git-hooks.sh, run from a LINKED WORKTREE.
#
# Every arm runs in a throwaway repository (a main checkout plus one linked
# worktree) built from this tree's own hook files, so no arm can touch the
# git config of the clone it was started from. GIT_DIR and friends are
# scrubbed first: a pre-push hook run from a linked worktree exports an
# absolute GIT_DIR, and under it every `git config` below would land in the
# real repository.
#
# The defect these arms pin (measured 2026-09-24 in the same kind of sandbox):
# with core.hooksPath=.git/hooks -- git's default, spelled out -- an install
# from the main checkout took the setting over, and the identical install from
# the linked worktree REFUSED it as "holds a real hook", because a relative
# path was read against the linked worktree, where `.git` is a file.
#
# Run: bash scripts/test_install_git_hooks.sh
set -uo pipefail
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR

SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TD="$(mktemp -d "${TMPDIR:-/tmp}/install_git_hooks_test.XXXXXX")" || exit 1
trap 'rm -rf "$TD"' EXIT
fails=0
ok() { echo "  selftest ok: $1"; }
bad() { echo "  selftest FAILED: $1"; fails=$((fails + 1)); }

# A fresh main checkout + linked worktree carrying this tree's installer and
# pre-push hook. The coverage checker is a STUB that passes: these arms are
# about where the installer reads and writes core.hooksPath, and the real
# checker's verdict is a property of the tree (a leg awaiting its gate-legs.txt
# row turns it red) that check_hook_coverage.py's own gate row already owns --
# copying it here made every arm red whenever that one leg was.
fresh() {  # <name>  -> sets MAIN, LINKED
  MAIN="$TD/$1/main"; LINKED="$TD/$1/linked"
  mkdir -p "$MAIN/scripts/githooks" "$MAIN/data"
  local f
  for f in scripts/install-git-hooks.sh scripts/githooks/pre-push; do
    cp "$SRC/$f" "$MAIN/$f" || return 1
  done
  printf 'print("HOOK COVERAGE: stub (test_install_git_hooks.sh)")\n' >"$MAIN/scripts/check_hook_coverage.py"
  git -C "$MAIN" init -q -b main . || return 1
  git -C "$MAIN" add -A
  git -C "$MAIN" -c user.email=t@example.invalid -c user.name=t commit -qm sandbox || return 1
  git -C "$MAIN" worktree add -q "$LINKED" -b linked || return 1
}
install_from() { (cd "$1" && bash scripts/install-git-hooks.sh "${@:2}") >"$TD/out" 2>&1; }

# 1. Install from the LINKED worktree: the setting lands in the SHARED config,
#    both checkouts resolve the tracked hook dir, and the installer says where.
fresh a || { echo "sandbox setup failed"; exit 1; }
if install_from "$LINKED"; then
  shared="$(git -C "$MAIN" config --get core.hooksPath || true)"
  [ "$shared" = scripts/githooks ] && ok "install from a linked worktree writes the shared config" \
    || bad "shared core.hooksPath after a linked-worktree install is '$shared'"
  for wt in "$MAIN" "$LINKED"; do
    [ "$(git -C "$wt" rev-parse --git-path hooks)" = scripts/githooks ] \
      || bad "git resolves no tracked hook dir in $wt"
  done
  grep -q "run from a LINKED worktree" "$TD/out" && ok "the installer names the shared config it wrote" \
    || bad "a linked-worktree install did not say it changed the shared config"
else
  bad "install from a linked worktree exited non-zero: $(cat "$TD/out")"
fi
install_from "$LINKED" --check && ok "--check passes from the linked worktree once installed" \
  || bad "--check failed after install: $(cat "$TD/out")"

# 2. Fail closed: not installed is a red --check, from either checkout.
fresh b || exit 1
install_from "$LINKED" --check && bad "--check PASSED with no hook installed" \
  || ok "--check fails closed when nothing is installed"

# 3. The measured defect: a relative, samples-only `.git/hooks` is taken over
#    from the linked worktree exactly as it is from the main checkout.
fresh c || exit 1
git -C "$MAIN" config core.hooksPath .git/hooks
if install_from "$LINKED" && [ "$(git -C "$MAIN" config --get core.hooksPath)" = scripts/githooks ]; then
  ok "a relative samples-only hooksPath is taken over from a linked worktree"
else
  bad "linked-worktree install refused a samples-only relative hooksPath: $(cat "$TD/out")"
fi

# 4. ...but the safety half holds: a relative path that holds a REAL hook in
#    ANY worktree (here only the main checkout) is refused from the linked one.
fresh d || exit 1
mkdir -p "$MAIN/tools/hooks" && printf '#!/bin/sh\nexit 0\n' >"$MAIN/tools/hooks/pre-push"
git -C "$MAIN" config core.hooksPath tools/hooks
if install_from "$LINKED"; then
  bad "a hooksPath holding a real hook in the main checkout was TAKEN OVER from a linked worktree"
else
  [ "$(git -C "$MAIN" config --get core.hooksPath)" = tools/hooks ] \
    && ok "a real hook in another worktree still refuses the takeover" \
    || bad "the refused install changed core.hooksPath anyway"
fi

# 5. An absolute path to a directory that does not exist holds no hook.
fresh e || exit 1
git -C "$MAIN" config core.hooksPath "$TD/e/nowhere"
install_from "$LINKED" && [ "$(git -C "$MAIN" config --get core.hooksPath)" = scripts/githooks ] \
  && ok "an absent absolute hooksPath is taken over" \
  || bad "an absent absolute hooksPath was refused: $(cat "$TD/out")"

if [ "$fails" -gt 0 ]; then echo "INSTALL_GIT_HOOKS_SELFTEST=fail failed=$fails"; exit 1; fi
echo "INSTALL_GIT_HOOKS_SELFTEST=ok"
