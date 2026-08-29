#!/usr/bin/env bash
# Point this clone's git hooks at the tracked hooks in `scripts/hooks/`.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.
#
# WHY THIS SCRIPT REPLACED A ONE-LINE `just` RECIPE
# --------------------------------------------------
# The recipe was `git config core.hooksPath scripts/hooks`, and it was correct.
# It had also never been run: on 2026-08-23 this repo's `core.hooksPath` was
# `.git/hooks`, a directory of fourteen `.sample` files, while the tree carried
# a tracked `scripts/hooks/pre-push`, a `just install-hooks` recipe to install
# it, and prose in several places describing gates as "wired to local_gate".
# Mechanically they were wired to nothing. An install step that only exists is
# indistinguishable from no install step at all.
#
# So this script does three things the recipe could not:
#   * `--check` gives the wiring a FAIL-CLOSED test, which `scripts/local_gate.sh`
#     and `just ci` now run. Not installed is a red gate, loudly, in the thing
#     people already run before pushing.
#   * `--check` also runs `scripts/check_hook_coverage.py`, so "installed" means
#     installed AND still covering the gate -- an installed hook that has quietly
#     stopped running half the legs is the same bug one level down.
#   * install refuses to take over a foreign `core.hooksPath` rather than
#     silently clobbering another tool's hooks.
#
# WHY THE DIRECTORY IS `scripts/githooks` AND NOT `scripts/hooks`
# ----------------------------------------------------------------
# The directory name is the rollout boundary. Git resolves a RELATIVE
# `core.hooksPath` against the worktree the hook runs in, so each worktree runs
# the gate at ITS OWN sha -- correct, and also why the obvious install was an
# outage. Measured 2026-08-23: 59 of this repo's 61 worktrees are pinned below
# the commit that landed the new gate and still carry the old
# `scripts/hooks/pre-push`, which is `exec local_gate.sh --fast` and dies on
# `ModuleNotFoundError: No module named 'tomllib'` out of that gate's first leg.
# `core.hooksPath=scripts/hooks` would have refused all 59 with a traceback.
#
# A directory those 59 do not have makes the rollout monotone: they find no hook
# and stay exactly as ungated as they already are, while every worktree carrying
# the new commit is gated. `--status` prints that split so the coverage is a
# number somebody can watch converge, not a hope. `scripts/hooks/pre-push`
# survives as a redirect into here, and this script migrates a clone that was
# configured the old way.
#
# WHY `core.hooksPath` AND NOT A COPY INTO `.git/hooks`
# -----------------------------------------------------
# A copy is untracked, invisible to review, and outlives the tree it came from.
# Pointing at the tracked directory means a hook change lands with the commit
# that makes it, no clone can run a stale copy, and -- because git resolves a
# RELATIVE hooksPath against the root of the worktree the hook runs in -- each
# of this repo's ~50 linked worktrees runs the hook at ITS OWN checked-out sha.
# One `git config --local` therefore covers every worktree, and a worktree
# pinned to an old commit correctly runs that commit's gate.
#
# Usage:
#   bash scripts/install-git-hooks.sh             # install (idempotent)
#   bash scripts/install-git-hooks.sh --check     # fail-closed wiring test
#   bash scripts/install-git-hooks.sh --status    # same, but always exits 0
#   bash scripts/install-git-hooks.sh --uninstall # stop using the tracked hooks
#
# There is no environment-variable bypass. A leg that is legitimately red gets
# an owned, expiring `WAIVED` row in `scripts/githooks/gate-legs.txt` that the hook
# reads -- visible, reviewed, and self-retiring. The only way past the hook is
# `git push --no-verify`, which is git's own and shows up in the reflog rather
# than in a habit.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 1

HOOKS_DIR="scripts/githooks"
LEGACY_DIR="scripts/hooks"
HOOK="$HOOKS_DIR/pre-push"
COVERAGE="scripts/check_hook_coverage.py"

configured() { git config --local --get core.hooksPath 2>/dev/null || true; }

# Any python will do here: the coverage checker reads text files and json, and
# deliberately does not import tomllib (the hook's own interpreter probe is the
# place that requirement belongs).
pick_python() {
  local cand
  for cand in "${CLEAN_GATE_PYTHON:-}" python3 python3.14 python3.13 python3.12 python3.11; do
    [ -n "$cand" ] && command -v "$cand" >/dev/null 2>&1 && { printf '%s' "$cand"; return 0; }
  done
  return 1
}

check() {  # 0 = wired and current; 1 = not
  local current rc py
  rc=0
  current="$(configured)"
  if [ "$current" != "$HOOKS_DIR" ]; then
    echo "  x pre-push hook NOT INSTALLED (core.hooksPath = ${current:-<unset>}, want $HOOKS_DIR)" >&2
    echo "      Nothing runs the gate on push. Install it:" >&2
    echo "        bash scripts/install-git-hooks.sh" >&2
    rc=1
  fi
  if [ ! -f "$HOOK" ]; then
    echo "  x $HOOK is missing — core.hooksPath points at a directory with no pre-push hook" >&2
    rc=1
  elif [ ! -x "$HOOK" ]; then
    echo "  x $HOOK is not executable — git silently ignores a non-executable hook" >&2
    echo "      chmod +x $HOOK" >&2
    rc=1
  fi
  if [ ! -f "$COVERAGE" ]; then
    echo "  x $COVERAGE is missing — the hook can no longer prove it covers the gate" >&2
    rc=1
  else
    py="$(pick_python)" || { echo "  x no python3 on PATH to run $COVERAGE" >&2; return 1; }
    "$py" "$COVERAGE" || rc=1
  fi
  [ "$rc" -eq 0 ] && echo "  pre-push hook: INSTALLED and current (core.hooksPath = $HOOKS_DIR)"
  return "$rc"
}

# Rollout coverage. A relative hooksPath is per-worktree, so "installed" is not
# one bit -- it is a fraction, and the denominator is this repo's worktrees. A
# worktree without scripts/githooks/ finds no hook and pushes ungated, exactly as
# it did before this gate existed; it is not a regression, but it is also not
# covered, and nothing else in the tree would ever say so.
rollout() {
  local wt covered=0 uncovered=0
  while read -r wt; do
    [ -z "$wt" ] && continue
    if [ -f "$wt/$HOOKS_DIR/pre-push" ]; then
      covered=$((covered + 1))
    else
      uncovered=$((uncovered + 1))
      [ "${VERBOSE_ROLLOUT:-0}" = "1" ] && echo "      uncovered: $wt"
    fi
  done <<<"$(git worktree list --porcelain 2>/dev/null | awk '/^worktree /{print $2}')"
  echo "  rollout: $covered of $((covered + uncovered)) worktrees carry $HOOKS_DIR/pre-push"
  if [ "$uncovered" -gt 0 ]; then
    echo "      $uncovered are pinned below the commit that landed it and push UNGATED,"
    echo "      exactly as every worktree did before 2026-08-23. They become gated when"
    echo "      they include that commit; nothing here breaks them in the meantime."
    echo "      List them with: VERBOSE_ROLLOUT=1 bash scripts/install-git-hooks.sh --status"
  fi
}

action="${1:-install}"
case "$action" in
  --check|check)
    check
    rc=$?
    rollout
    exit $rc
    ;;
  --status|status)
    check || true
    rollout
    exit 0
    ;;
  --uninstall|uninstall)
    if [ "$(configured)" = "$HOOKS_DIR" ]; then
      git config --local --unset core.hooksPath
      echo "Clean git hooks: uninstalled. NOTHING now gates a push from this clone."
    else
      echo "Clean git hooks: nothing to uninstall (core.hooksPath is not ours)."
    fi
    exit 0
    ;;
  ""|install|--install) : ;;
  *)
    echo "usage: $0 [--check|--status|--uninstall]" >&2
    exit 2
    ;;
esac

if [ ! -f "$HOOK" ]; then
  echo "ERROR: $HOOK is missing; nothing to install." >&2
  exit 1
fi

current="$(configured)"
if [ "$current" = "$LEGACY_DIR" ]; then
  echo "Migrating core.hooksPath from $LEGACY_DIR to $HOOKS_DIR (the gate moved 2026-08-23)."
  current=""
fi

# A hooksPath that holds nothing but git's own `.sample` files is the default
# wearing a config entry, and taking it over loses nobody's hook. This repo was
# found on 2026-08-23 with an ABSOLUTE `core.hooksPath=$HOME/clean/.git/hooks`
# -- not merely unset, deliberately set, and set to a directory containing
# fourteen samples and no hook. That is strictly worse than leaving it unset,
# because an absolute path drags all ~60 linked worktrees to the MAIN repo's
# empty hook directory, so no worktree could ever have run its own tracked hook.
#
# Anything with a REAL hook in it is somebody else's tooling and is refused.
samples_only() {
  local dir="$1" f base
  [ -d "$dir" ] || return 1
  for f in "$dir"/*; do
    [ -e "$f" ] || continue
    base="${f##*/}"
    case "$base" in *.sample) continue ;; esac
    return 1
  done
  return 0
}
if [ -n "$current" ] && [ "$current" != "$HOOKS_DIR" ] && samples_only "$current"; then
  echo "Taking over core.hooksPath='$current': it contains only git's .sample"
  echo "  files, so it has never run a hook. (An absolute hooksPath also forces"
  echo "  every linked worktree to look in that one directory, which is why the"
  echo "  tracked hook in this tree could not fire even where it existed.)"
  current=""
fi

if [ -n "$current" ] && [ "$current" != "$HOOKS_DIR" ]; then
  echo "ERROR: core.hooksPath is already set to '$current', and it holds a real hook." >&2
  echo "       Refusing to take over another hook configuration. Clear it with:" >&2
  echo "         git config --local --unset core.hooksPath" >&2
  exit 1
fi

# A hook someone dropped into .git/hooks is dead weight once core.hooksPath
# moves: git stops reading it, but it stays on disk looking authoritative.
GIT_HOOK_DIR="$(git rev-parse --git-path hooks 2>/dev/null || echo "$REPO_ROOT/.git/hooks")"
if [ -f "$GIT_HOOK_DIR/pre-push" ]; then
  echo "NOTE: a hook remains at $GIT_HOOK_DIR/pre-push; core.hooksPath makes git" >&2
  echo "      ignore it. Chain it from $HOOK if you still want it." >&2
fi

for hook in "$HOOKS_DIR"/*; do
  [ -f "$hook" ] || continue
  case "$hook" in *.txt|*.md) continue ;; esac
  chmod +x "$hook"
done
[ -f "$LEGACY_DIR/pre-push" ] && chmod +x "$LEGACY_DIR/pre-push"

git config --local core.hooksPath "$HOOKS_DIR"
echo "Clean git hooks: installed (core.hooksPath = $HOOKS_DIR)"
echo "  pre-push runs the narrow gate (17.5-18.5 s measured, no cargo, no build): the fast legs of"
echo "  scripts/local_gate.sh that are cheap AND green. Which ones, and why the"
echo "  others are left out, is one reviewed row per leg in $HOOKS_DIR/gate-legs.txt."
echo "  The expensive legs still run, fail-closed, in scripts/local_gate.sh (full mode)."
echo
check
