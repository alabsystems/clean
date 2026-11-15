#!/usr/bin/env bash
# Persistent, resumable, per-target test runner -- thin wrapper.
#
# The engine is scripts/verify_runner.py; read its module docstring for the
# exact definition of "inputs changed" and for what a GREEN does and does not
# claim. This wrapper exists so the entry point is discoverable next to the
# other gates in scripts/.
#
#   scripts/verify_runner.sh status              # is the suite green? (default)
#   scripts/verify_runner.sh status --json
#   scripts/verify_runner.sh status --shards     # expand the collapsed shard rows
#   scripts/verify_runner.sh inventory
#   scripts/verify_runner.sh policy              # the per-target timeout table
#   scripts/verify_runner.sh shards show         # the shard cut + its partition proof
#   scripts/verify_runner.sh shards plan         # recompute it (builds; slow)
#   scripts/verify_runner.sh run                 # detached; survives the reaper
#   scripts/verify_runner.sh stop
#   scripts/verify_runner.sh journal             # what has the working tree lost?
#   scripts/verify_runner.sh journal --apply     # re-project it
#
# EVERY VERDICT IS WRITTEN THROUGH AN APPEND-ONLY JOURNAL OUTSIDE THE WORKING
# TREE, and `data/suite_state/` is a PROJECTION of it. That directory is
# git-tracked and is also runner output that changes without a commit, so a
# `git checkout` over it silently reverts records with exit code 0 -- which is
# how a complete 14.33-hour sweep was destroyed once. A checkout can still
# revert the projection; it can no longer lose anything, because `status` heals
# from the journal before it derives, and says so. `docs/SUITE_STATE.md` has the
# four reconcile verdicts and why a record from another machine is never
# clobbered.
#
# A target too big to finish as one unit is SHARDED: each shard is a target in
# its own right with its own record, digest and budget, and the parent reports
# GREEN only when every shard is GREEN *and* the shards' measured test counts
# re-sum to the declared total. Any missing or unmeasured shard leaves the
# parent UNKNOWN -- it is never GREEN on a partial set. `shards plan` refuses to
# write a cut whose partition proof did not pass, because a scheme that silently
# drops tests is worse than the unmeasured target it replaces.
#
# Timeouts are PER-TARGET and derived from measured cost -- `policy` prints the
# budget each target would get and why. Do not reach for `run --timeout N`; that
# flag is a flat override of the policy for the whole queue, and a flat 25s is
# what threw away a 1761s target's result on 2026-08-12.
#
# Scope defaults to DEFAULT_PACKAGES in verify_runner.py -- clean-verify,
# clean-elab, clean-parser and clean-olean since 2026-09-24, clean-kernel and
# clean-ck0 since 2026-11-13 -- plus the
# workspace gates (WORKSPACE_GATES there; read both there rather than trusting
# a list here, which is how this line went stale twice).
# Widen with a COMMA-SEPARATED value before the subcommand:
#   scripts/verify_runner.sh --packages clean-verify,clean-mathverse status
# The space-separated `--packages a b -- status` form this line carried until
# 2026-09-16 is not a widening at all: argparse reads `b` as the subcommand and
# it exits `invalid choice`, so anyone following it measured nothing and was
# told so only by a usage error.
set -euo pipefail

# PYTHON >= 3.11, RESOLVED THE WAY scripts/local_gate.sh's `_gate_python` DOES.
#
# This line used to be `exec /usr/bin/env python3`, which on this machine is
# Apple's /usr/bin/python3 3.9.6, and the runner then imported
# scripts/check_test_target_coverage.py, which needs `tomllib` (3.11+). So the
# suite's own status oracle died at import with ModuleNotFoundError under the
# default PATH -- measured twice by the 2026-09-24 process audit -- and worked
# only for whoever happened to have Homebrew's python3 first on PATH.
#
# Since 2026-11-01 this runner imports scripts/rust_modules.py instead, which
# needs no tomllib: verify_runner.py runs, and `status` answers, on 3.9.6
# (measured in the 2026-11-01 review). The floor stays, for the pinned case
# below: scripts/verify_runner_pinned.sh runs an OLDER commit's runner through
# this wrapper, and every runner before that date imports the TOML-parsing
# checker.
#
# Same candidate order and the same override as local_gate.sh (and the pre-push
# hook's pick_python): CLEAN_GATE_PYTHON first, then python3 and its versioned
# names, then the two Homebrew locations. FAIL CLOSED when none imports
# tomllib: falling back to 3.9 would not produce a worse verdict, it would
# produce a traceback and no verdict.
_runner_python() {
  local cand
  for cand in "${CLEAN_GATE_PYTHON:-}" python3 python3.14 python3.13 python3.12 python3.11 \
              /opt/homebrew/bin/python3 /usr/local/bin/python3; do
    [[ -n "$cand" ]] || continue
    command -v "$cand" >/dev/null 2>&1 || continue
    if "$cand" -c 'import tomllib' >/dev/null 2>&1; then command -v "$cand"; return 0; fi
  done
  return 1
}
PY="$(_runner_python)" || {
  echo "verify_runner: no python3 with 'tomllib' (needs >= 3.11); a runner before 2026-11-01 (a pinned worktree's) imports a TOML-parsing checker and cannot run without it." >&2
  echo "  Set CLEAN_GATE_PYTHON=/path/to/python3 (3.11+), or install one (brew install python@3.14)." >&2
  exit 2
}
# VERIFY_RUNNER_SCRIPT names a DIFFERENT checkout's runner. It exists for
# scripts/verify_runner_pinned.sh, which measures a pinned worktree that may sit
# at a commit older than this resolver: running that commit's own wrapper would
# bring back the `/usr/bin/env python3` death for any pin that predates it, so
# the pinned script borrows THIS wrapper's interpreter choice instead.
exec "$PY" "${VERIFY_RUNNER_SCRIPT:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/verify_runner.py}" "${@:-status}"
