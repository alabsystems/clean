#!/usr/bin/env bash
# Run the suite runner against a PINNED COMMIT in a detached git worktree.
#
# Why: several lanes commit to this repo at once, and a full pass over the
# clean-verify integration targets takes hours. Measured 2026-08-12, a green
# taken against the shared working tree went stale in under a minute, because
# another lane was editing crates/clean-verify while the pass ran. Results were
# correct and useless in the same breath.
#
# A worktree pinned to a commit cannot move underneath the run, so every result
# attributes cleanly to a sha and stays valid until you re-pin. The claim
# changes from "the working tree you happen to have" to "this commit" -- which
# is the more useful claim anyway.
#
#   scripts/verify_runner_pinned.sh status
#   scripts/verify_runner_pinned.sh run --jobs 4
#   COMMITISH=origin/main scripts/verify_runner_pinned.sh run
#
# Records land in the SHARED data/suite_state/ -- one artifact, whichever mode
# produced a row. Note that a row measured at a commit reads UNKNOWN from a
# dirty main tree, and GREEN from this pinned view. Both are correct: they are
# claims about different trees.
#
# This is a thin composition of VERIFY_RUNNER_STATE_DIR + VERIFY_RUNNER_TARGET_DIR
# over a worktree checkout. There is no separate code path to trust.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COMMITISH="${COMMITISH:-HEAD}"
PINNED_ROOT="${PINNED_ROOT:-$REPO_ROOT/target/verify-runner-pinned}"
WORKTREE="$PINNED_ROOT/worktree"

sha="$(git -C "$REPO_ROOT" rev-parse "$COMMITISH")"

# State and shard plans are shared with the main-tree runner; the build tree is
# not, because the two are checked out at different source states and would
# thrash one target dir.
#
# The plan directory must be shared for the same reason the state directory is:
# a plan left inside the throwaway worktree would vanish on the next re-pin, and
# the main tree would then read `clean-verify::lib` as unsharded and UNKNOWN
# while hundreds of measured shard records sat beside it.
export VERIFY_RUNNER_STATE_DIR="${VERIFY_RUNNER_STATE_DIR:-$REPO_ROOT/data/suite_state}"
export VERIFY_RUNNER_PLAN_DIR="${VERIFY_RUNNER_PLAN_DIR:-$REPO_ROOT/data/suite_plans}"
export VERIFY_RUNNER_TARGET_DIR="${VERIFY_RUNNER_TARGET_DIR:-$PINNED_ROOT/target}"

# A LIVE WORKER OWNS THIS WORKTREE. Refuse to re-pin underneath it.
#
# Measured 2026-08-13, the hard way: re-pinning 2241f47da -> 2821390fb while a
# worker was 18h into `clean-verify::lib` moved 24 files inside the input
# digest's scope (crates/clean-verify/**, Cargo.toml, Cargo.lock). The run
# itself survived -- its test binary was already built and executing -- but the
# runner re-digests at FINISH, so the row would have landed with
# `inputs_moved_during_run: true` and read UNKNOWN. An 18-hour measurement
# thrown away by a checkout in another terminal.
#
# The pristine-tree check above cannot catch this: the worktree IS pristine, it
# is simply in use. And this must be checked BEFORE the checkout, not after --
# the previous version re-pinned first and validated its arguments afterwards,
# so even a mistyped command mutated the tree.
WORKER_PIDFILE="$VERIFY_RUNNER_TARGET_DIR/suite-runner/worker.pid"
if [ -f "$WORKER_PIDFILE" ]; then
  worker_pid="$(cat "$WORKER_PIDFILE" 2>/dev/null || echo 0)"
  if [ -n "$worker_pid" ] && kill -0 "$worker_pid" 2>/dev/null; then
    current_head="$(git -C "$WORKTREE" rev-parse HEAD 2>/dev/null || echo none)"
    if [ "$current_head" != "$sha" ]; then
      echo "refusing to re-pin $WORKTREE: worker pid $worker_pid is running from it" >&2
      echo "  worktree is at ${current_head:0:9}, you asked for ${sha:0:9}" >&2
      echo "  re-pinning moves the input digest's own sources underneath an in-flight" >&2
      echo "  measurement, so its result records inputs_moved_during_run and reads" >&2
      echo "  UNKNOWN -- hours of work discarded." >&2
      echo "  Wait for it, or stop it first: scripts/verify_runner.sh stop" >&2
      exit 1
    fi
  fi
fi

if [ -d "$WORKTREE/.git" ] || [ -f "$WORKTREE/.git" ]; then
  current="$(git -C "$WORKTREE" rev-parse HEAD)"
  if [ "$current" != "$sha" ]; then
    if [ -n "$(git -C "$WORKTREE" status --porcelain)" ]; then
      echo "refusing to re-pin: $WORKTREE has local modifications" >&2
      echo "the pinned worktree must stay pristine or its results mean nothing" >&2
      exit 1
    fi
    echo "re-pinning $WORKTREE: ${current:0:9} -> ${sha:0:9}" >&2
    git -C "$WORKTREE" checkout -q --detach "$sha"
  fi
else
  mkdir -p "$PINNED_ROOT"
  echo "creating pinned worktree at $WORKTREE (${sha:0:9})" >&2
  git -C "$REPO_ROOT" worktree add --detach "$WORKTREE" "$sha" >/dev/null
fi

exec /usr/bin/env python3 "$WORKTREE/scripts/verify_runner.py" "${@:-status}"
