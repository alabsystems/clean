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
# Scope defaults to -p clean-verify plus the three workspace gates. Widen with:
#   scripts/verify_runner.sh --packages clean-verify clean-kernel -- status
set -euo pipefail
exec /usr/bin/env python3 "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/verify_runner.py" "${@:-status}"
