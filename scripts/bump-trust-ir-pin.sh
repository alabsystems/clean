#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# Move Clean's trust-ir pin TOGETHER with the trust-cg pin that co-owns it --
# atomically, or not at all.
#
# WHY THIS SCRIPT EXISTS (WS6.5)
# ------------------------------
# A trust-ir pin move here is a transaction over:
#
#   * nine `trust-ir.git` declarations in six manifests (the root
#     `trust-ir-contract` and test-only `trust-ir-semr`, clean-auto, clean-compiler x3, clean-reflect,
#     clean-verify, and the standalone crystal A2 producer);
#   * three `trust-cg.git` declarations in clean-auto, whose target commit must
#     itself pin the SAME trust-ir revision -- otherwise the root lock carries
#     two trust-ir graphs and clean-auto's tests hand a `ProofFormula` from one
#     to a lowering compiled against the other (measured 2026-09-14, recorded
#     in crates/clean-auto/Cargo.toml);
#   * TWO lockfiles: the root `Cargo.lock` and
#     `scripts/crystal_a2_project/Cargo.lock`, a separate `[workspace]` that no
#     `--workspace` command ever refreshes. `3e87b95ba` moved every manifest
#     and the root lock and left the crystal lock behind; the dep-boundary
#     hook leg then refused every push until `48ce23658` regenerated it.
#
# The legs are enumerated machine-readably in scripts/trust_ir_pin_legs.py;
# this script drives them as one transaction with an explicit rollback, so a
# half-applied bump is impossible rather than merely detectable. It is modelled
# on trust-ir's scripts/bump-dep-pin.sh.
#
#   scripts/bump-trust-ir-pin.sh <trust-ir-sha> <trust-cg-sha> [options]
#
# Phases: A preconditions (read-only) -> B stage -> C backup -> D install
#         -> E refresh both locks -> F verify -> G re-derive what the move
#         left stale. Any failure after D rolls the working tree back to
#         exactly what was found, including uncommitted work.
#
# PHASE G (2026-10-15). The move is not done when the legs agree: the root
# lock is pinned by data/vendor_manifest.json, the crystal manifest and lock
# are DERIVED inputs of check_lint_coverage's registry row (R7 refuses it until
# its arms replay over them), and re-pinning that row moves
# data/gate_registry.json, which the verdict set, the IO contracts, the
# assumption ledger and the scoreboard pin in turn. bb04555f8 and d95127f28
# each left the hook red until that walk was done by hand. Phase G runs
# scripts/rederive_chain.py inside this transaction: every stale node
# re-derived by its own documented mint, the registry row by `--repin` -- a
# green REPLAY of its arms, about an hour on a loaded box, which is what R7
# guarantees in the default diagnostic scope. If the replay or any mint refuses, the bump
# fails and rolls back. Phase A refuses a tree whose legs are coherent and
# whose derived artifacts are already red, so everything phase G re-derives is
# this move's. Over INCOHERENT legs (a split being repaired, a lock that
# disagrees with its manifests) the derived artifacts that read those legs are
# red because of them, and a check cannot tell that red from any other: it is
# reported, not refused, and phase G re-derives whatever is stale over the
# moved tree. Refusing it would leave no way out but a hand restore, since a
# replay over a split crystal leg cannot pass (`targo metadata --locked`
# refuses the stale lock in every arm's baseline). docs/DECISIONS.md R33.
#
# SOURCE PUBLICATION. --source-only selects phases A-F's dependency transaction
# without judging or minting the derived diagnostic artifacts. Revision/alias
# coherence, immutable CG authority, both lock refreshes, --locked acceptance,
# dependency-boundary verification and rollback remain mandatory. A source
# transaction grants no full-diagnostic verdict; affected consumers still need
# their own qualification. The default diagnostic transaction is unchanged.
#
# Exit codes: 0 success in the selected scope (or already at its target),
#             1 refusal/failure (working tree unchanged), 2 usage error.
#             `--dry-run` runs every phase-A precondition, the derived-artifact
#             check included, before it diffs.
#
# WHAT THIS DOES NOT DO. Beyond the check_lint_coverage replay (which runs the
# crystal projector's tests, lint and typed scan against the new trust-ir), it
# does not compile, test, or validate anything against the new trust-ir: a
# coherent pin is the precondition for that work, not a substitute for it. Run
# the consumer gates (clean-compiler with `trust-ir-backend`, clean-reflect,
# clean-verify, clean-auto) after it.
# trust-ir's own clean pin (the reverse edge) moves only through
# `trust-ir/scripts/bump-dep-pin.sh clean <sha>`, never from here.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

LEGS_PY="$ROOT/scripts/trust_ir_pin_legs.py"
BOUNDARY_PY="$ROOT/scripts/check_workspace_dependency_boundary.py"
REDERIVE_PY="$ROOT/scripts/rederive_chain.py"
TRUST_IR_REMOTE="https://github.com/alabsystems/trust-ir.git"
TRUST_CG_REMOTE="https://github.com/alabsystems/trust-cg.git"
TRUST_CG_OBJECT_REPO="${CLEAN_TRUST_CG_REPO:-$ROOT/../trust-cg}"

usage() {
    cat >&2 <<'USAGE'
usage: scripts/bump-trust-ir-pin.sh <trust-ir-sha> <trust-cg-sha> [options]

  <trust-ir-sha>    the immutable trust-ir commit to adopt (40 hex)
  <trust-cg-sha>    the immutable trust-cg commit whose Cargo.toml pins
                    exactly that trust-ir commit (40 hex)

  --targo <path>    the Targo frontend used by checks and both lock refreshes.
                    Default: $CLEAN_TARGO, then `targo` on PATH, then
                    `trustc --print sysroot`/bin/targo. Never stock cargo.
  --offline         skip the remote-existence probes; the trust-cg authority
                    manifest must then be readable from the local object
                    cache ($CLEAN_TRUST_CG_REPO, default ../trust-cg), and
                    phase G stages the vendor manifest from cargo's local
                    registry cache only
  --dry-run         run every precondition (the derived-artifact check
                    included: a tree with coherent legs and a red derived
                    artifact is refused here too), stage the edits and diff
                    them; change nothing
  --repair          a tree whose legs are SPLIT across revisions (a hand-edited
                    leg, a half-applied bump) is otherwise REFUSED with the
                    census naming the leg. With --repair every leg is rewritten
                    to the target and both locks refreshed. Explicit, because a
                    split is the failure this script exists to prevent and the
                    default must never launder one silently. A derived artifact
                    the split reddened is reported, not refused: phase G
                    re-derives it over the repaired legs. Manifests already
                    at the target with a lock that disagrees are a split too:
                    --repair refreshes both locks there.
  --no-boundary-check
                    skip scripts/check_workspace_dependency_boundary.py in
                    phase F (the pin coherence check itself still runs)
  --source-only      update the canonical dependency graph for ordinary source
                    publication. Keep phases A-F and rollback, but do not
                    judge/re-mint the full diagnostic's derived artifacts or
                    replay its hour-long phase G. Reports them NOT JUDGED;
                    does not claim compilation, consumer compatibility or a
                    green full diagnostic. The default remains the complete
                    diagnostic transaction.

  Phase G replays check_lint_coverage's arms (about an hour): run the bump as
  a heavy job, `build-slot -- scripts/bump-trust-ir-pin.sh ...`.

env:
  CLEAN_TRUST_CG_REPO   optional local trust-cg object cache. Only the target
                        COMMIT's Cargo.toml is read from it; its HEAD and
                        working tree are never inspected.
  CLEAN_TARGO           the Targo frontend, when --targo is not given.
USAGE
    exit 2
}

[[ $# -ge 2 ]] || usage
TRUST_IR_REV="$1"
TRUST_CG_REV="$2"
shift 2
TARGO=""
OFFLINE=0
DRY_RUN=0
REPAIR_OK=0
BOUNDARY_CHECK=1
SOURCE_ONLY=0
while [[ $# -gt 0 ]]; do
    case "$1" in
        --targo)
            [[ $# -ge 2 ]] || { printf '%s\n' 'missing value for --targo' >&2; usage; }
            TARGO="$2"
            shift
            ;;
        --offline) OFFLINE=1 ;;
        --dry-run) DRY_RUN=1 ;;
        --repair) REPAIR_OK=1 ;;
        --no-boundary-check) BOUNDARY_CHECK=0 ;;
        --source-only) SOURCE_ONLY=1 ;;
        -h|--help) usage ;;
        *) printf 'unknown option: %q\n' "$1" >&2; usage ;;
    esac
    shift
done

say() { printf '\n==> %s\n' "$*"; }
warn() { printf 'WARN: %s\n' "$*" >&2; }
die() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

if [[ $SOURCE_ONLY -eq 1 && $BOUNDARY_CHECK -eq 0 ]]; then
    printf 'FAIL: --source-only requires the dependency-boundary check; --no-boundary-check is incompatible.\n' >&2
    exit 2
fi

for REV in "$TRUST_IR_REV" "$TRUST_CG_REV"; do
    if [[ ! "$REV" =~ ^[0-9a-f]{40}$ ]]; then
        printf 'FAIL: %q is not a full 40-hex lowercase commit sha.\n' "$REV" >&2
        printf '      Abbreviated revisions cannot be written into a lockfile or\n' >&2
        printf '      compared against the coherence check.\n' >&2
        exit 1
    fi
done

# The leg module parses TOML with `tomllib` (3.11+). Resolve the interpreter
# once and loudly, the way the pre-push hook does, so a missing module never
# reads as a pin verdict.
pick_python() {
    local cand
    for cand in "${CLEAN_GATE_PYTHON:-}" python3 python3.14 python3.13 python3.12 python3.11 \
                /opt/homebrew/bin/python3 /usr/local/bin/python3; do
        [[ -z "$cand" ]] && continue
        command -v "$cand" >/dev/null 2>&1 || continue
        if "$cand" -c 'import tomllib' >/dev/null 2>&1 \
            || "$cand" -c 'import tomli' >/dev/null 2>&1; then
            printf '%s' "$cand"
            return 0
        fi
    done
    return 1
}
PY="$(pick_python)" || die "no python3 with tomllib (3.11+) or tomli on PATH; set CLEAN_GATE_PYTHON"
pin() { "$PY" -B "$LEGS_PY" "$@"; }

resolve_targo() {
    if [[ -n "$TARGO" ]]; then
        printf '%s' "$TARGO"
        return 0
    fi
    if [[ -n "${CLEAN_TARGO:-}" ]]; then
        printf '%s' "$CLEAN_TARGO"
        return 0
    fi
    if command -v targo >/dev/null 2>&1; then
        command -v targo
        return 0
    fi
    local sysroot
    if sysroot="$(trustc --print sysroot 2>/dev/null)" && [[ -x "$sysroot/bin/targo" ]]; then
        printf '%s' "$sysroot/bin/targo"
        return 0
    fi
    return 1
}

# Shared by an actual move and the source-scope already-coherent path. A
# no-op must not report success without the same locked/boundary acceptance.
verify_locked_graph_and_boundary() {
    # F.2 -- both locks are current: a lock the resolver would rewrite is not a
    # lock.
    "$TARGO" metadata --locked --format-version 1 --manifest-path "$ROOT/Cargo.toml" >/dev/null \
        || die "root Cargo.lock is not current under --locked after the refresh"
    "$TARGO" metadata --locked --format-version 1 --manifest-path "$ROOT/scripts/crystal_a2_project/Cargo.toml" >/dev/null \
        || die "scripts/crystal_a2_project/Cargo.lock is not current under --locked after the refresh"
    printf 'both lockfiles accepted under --locked\n'

    # F.3 -- the push-path gate itself, so the transaction ends exactly where the
    # hook would judge it.
    if [[ $BOUNDARY_CHECK -eq 1 ]]; then
        "$PY" -B "$BOUNDARY_PY" \
            || die "scripts/check_workspace_dependency_boundary.py FAILED after the bump"
    else
        printf 'VERIFY: dependency-boundary gate skipped (--no-boundary-check)\n'
    fi
}

# The transaction's scratch -- the BACKUP a rollback restores from -- lives in
# this checkout's git directory (as the pre-push hook's state does), never
# $TMPDIR: phase G keeps it open for an hour, and macOS's nightly cleaner
# deletes old-dated files in $TMPDIR (`cp -p` keeps each leg's old mtime). Not
# the working tree either, where the staged and backed-up manifests would sit
# beside the live ones for every tree walker the replay runs. BACKED_UP lists
# what phase C saved, so a backup that vanished anyway is a failed restore,
# never a skipped one.
GIT_DIR_ABS="$(git -C "$ROOT" rev-parse --absolute-git-dir 2>/dev/null)" \
    || die "$ROOT is not a git checkout; the transaction keeps its backup in its git directory"
TMP="$(mktemp -d "$GIT_DIR_ABS/bump-trust-ir-pin.XXXXXX")" \
    || die "cannot create the transaction's scratch directory under $GIT_DIR_ABS"
STAGE="$TMP/stage"
BACKUP="$TMP/backup"
BACKED_UP="$TMP/backed-up"
mkdir -p "$STAGE" "$BACKUP"
: >"$TMP/absent-before"
: >"$BACKED_UP"

INSTALLED=0
SUCCESS=0
ROLLED_BACK=0

rollback() {
    # Idempotent: a signal handler and the EXIT trap can both reach here, and a
    # second pass would run after `cleanup` has already removed the backup --
    # restoring nothing while printing success.
    if [[ $ROLLED_BACK -eq 1 ]]; then
        return 0
    fi
    ROLLED_BACK=1
    if [[ ! -d "$BACKUP" || ! -f "$BACKED_UP" ]]; then
        printf '\nROLLBACK IMPOSSIBLE -- the backup at %s is gone. The working tree may be PARTIALLY MODIFIED; inspect `git status` before doing anything else.\n' \
            "$BACKUP" >&2
        return 1
    fi
    local relative failed=0
    # Every file phase C SAVED, from its list -- not whatever the backup
    # directory still holds, which would skip a backup that vanished.
    while IFS= read -r relative; do
        [[ -n "$relative" ]] || continue
        # VERIFY the restore instead of asserting it: the success line below is
        # a factual claim about the tree, so every copy that fails must
        # downgrade it.
        if ! cp -p "$BACKUP/$relative" "$ROOT/$relative"; then
            printf 'ROLLBACK FAILED to restore %s\n' "$relative" >&2
            failed=1
        fi
    done <"$BACKED_UP"
    # A file the transaction may write that did not exist when it began.
    while IFS= read -r relative; do
        [[ -n "$relative" ]] || continue
        if ! rm -f "$ROOT/$relative"; then
            printf 'ROLLBACK FAILED to remove %s\n' "$relative" >&2
            failed=1
        fi
    done <"$TMP/absent-before"
    if [[ $failed -eq 1 ]]; then
        printf '\nROLLBACK INCOMPLETE -- the working tree is NOT guaranteed unchanged. Inspect `git status`/`git diff` before re-running.\n' >&2
        return 1
    fi
    printf '\nROLLED BACK -- working tree unchanged.\n' >&2
    return 0
}

cleanup() {
    if [[ $INSTALLED -eq 1 && $SUCCESS -ne 1 ]]; then
        rollback || true
    fi
    rm -rf "${TMP:?}"
}

# EXIT alone would let a signal fall through and resume the script body: the
# handler would roll back, `cleanup` would delete TMP, execution would continue
# to the next command, fail, and roll back a SECOND time against a deleted
# backup. Re-raise so the shell dies at the signal.
trap 'cleanup' EXIT
trap 'trap - EXIT; cleanup; trap - INT; kill -INT $$' INT
trap 'trap - EXIT; cleanup; trap - TERM; kill -TERM $$' TERM

# --- PHASE A: preconditions (read-only; nothing is written) ------------------
say "PHASE A -- preconditions for trust-ir -> $TRUST_IR_REV with trust-cg -> $TRUST_CG_REV"

# A transaction directory no trap removed: a bump killed outright (SIGKILL)
# during its hour-long phase G leaves its backup here, and nothing else would
# say so. Named, never consulted: which of its files still describe this tree
# is a judgement for whoever reads `git status`.
for LEFT in "$GIT_DIR_ABS"/bump-trust-ir-pin.*; do
    [[ -d "$LEFT" && "$LEFT" != "$TMP" ]] || continue
    warn "a bump's transaction directory survives at
        $LEFT
      left by a bump killed before it could roll back, unless another bump is
      running in this checkout now. Its backup/ holds the files that bump found
      (listed in its backed-up file). If \`git status\` shows a half-applied
      bump, restore them from there or re-run with --repair; then delete it."
done

CENSUS_OUT="$(pin census --root "$ROOT" 2>&1)"
CENSUS_CODE=$?
printf '%s\n' "$CENSUS_OUT"
# A `!!` row means a leg's DECLARATION drifted (a manifest was reformatted, a
# dependency key renamed, a new consumer crate added). The anchored rewrite
# would silently miss it, so refuse rather than half-apply.
if [[ $CENSUS_CODE -ge 2 ]] || grep -q '^!!' <<<"$CENSUS_OUT"; then
    die "a pin leg no longer matches its declared shape (the '!!' rows above).
      Update the leg table in scripts/trust_ir_pin_legs.py and the matching
      assertions in scripts/test_bump_trust_ir_pin.py together, then re-run."
fi

REPAIR=0
ALREADY_COHERENT=0
CURRENT_TRUST_IR=""
CURRENT_TRUST_CG=""
if [[ $CENSUS_CODE -ne 0 ]]; then
    # A pin is SPLIT across revisions -- i.e. someone hand-edited a subset of
    # the legs, or a previous bump was interrupted between install and
    # rollback. That is the recurring failure itself (the mutation control of
    # WS6.5), so by default it is a REFUSAL that names the leg: the split is
    # never taken as "the current revision", and it is never repaired without
    # being asked. `--repair` rewrites every leg to the target instead.
    if [[ $REPAIR_OK -ne 1 ]]; then
        die "a pin is SPLIT across revisions (the '<>' rows above name the legs).
      A hand-edited leg is refused, never adopted. Restore the edited leg (or
      re-run with --repair to move EVERY leg to the target and refresh both
      locks)."
    fi
    REPAIR=1
    printf '\nREPAIR MODE (--repair): a pin is currently SPLIT across revisions.\n'
    printf '             Every trust-ir leg moves to %s and every trust-cg leg to %s.\n' \
        "$TRUST_IR_REV" "$TRUST_CG_REV"
else
    CURRENT_TRUST_IR="$(pin current --root "$ROOT" --dep trust-ir)" \
        || die "cannot determine the current trust-ir revision"
    CURRENT_TRUST_CG="$(pin current --root "$ROOT" --dep trust-cg)" \
        || die "cannot determine the current trust-cg revision"
    if [[ "$CURRENT_TRUST_IR" == "$TRUST_IR_REV" && "$CURRENT_TRUST_CG" == "$TRUST_CG_REV" ]]; then
        # DEFERRED, NOT AN EARLY EXIT. Returning here would skip A.2 -- the
        # trust-cg authority leg and the lock coherence check -- and "already at
        # the target" must mean every precondition held, not only that the
        # manifests agree with each other.
        ALREADY_COHERENT=1
    else
        printf '\nmoving trust-ir: %s -> %s\n' "$CURRENT_TRUST_IR" "$TRUST_IR_REV"
        printf 'moving trust-cg: %s -> %s\n' "$CURRENT_TRUST_CG" "$TRUST_CG_REV"
    fi
fi

CONTROLLED_LEGS="$(pin legs --root "$ROOT")" || die "cannot enumerate the controlled legs"
# What phase G may write: the derived artifacts downstream of the legs.
DERIVED_OUTPUTS="$("$PY" -B "$REDERIVE_PY" --outputs)" \
    || die "cannot enumerate the derived artifacts ($REDERIVE_PY --outputs)"
DIRTY="$(git -C "$ROOT" status --porcelain -- $CONTROLLED_LEGS $DERIVED_OUTPUTS 2>/dev/null)"
if [[ -n "$DIRTY" ]]; then
    warn "pin legs have uncommitted changes:
$DIRTY
      Proceeding -- the backup is taken from the WORKING TREE, so a rollback
      restores these edits rather than discarding them."
fi

# A.2/A.3 -- fresh online Agh source authority precedes manifest parsing.
# Explicit offline preparation retains its existing local-object semantics;
# it grants no fresh remote authority or published-source qualification.
AUTHORITY_MANIFEST="$TMP/trust-cg-${TRUST_CG_REV}.toml"
if [[ $OFFLINE -eq 1 ]]; then
    [[ "$(git -C "$TRUST_CG_OBJECT_REPO" rev-parse --is-inside-work-tree 2>/dev/null)" == "true" ]] \
        && git -C "$TRUST_CG_OBJECT_REPO" cat-file -e "${TRUST_CG_REV}^{commit}" 2>/dev/null \
        || die "offline trust-cg authority check cannot find commit $TRUST_CG_REV in $TRUST_CG_OBJECT_REPO"
    git -C "$TRUST_CG_OBJECT_REPO" show "${TRUST_CG_REV}:Cargo.toml" >"$AUTHORITY_MANIFEST" \
        || die "offline trust-cg commit $TRUST_CG_REV has no readable Cargo.toml"
    warn "--offline: skipping fresh remote authority. Local-only revisions fail downstream; this is not published-source qualification."
else
    "$PY" -B "$ROOT/scripts/compiler_pin_authority.py" \
        --directory "$TMP/compiler-source-authority" --manifest "$AUTHORITY_MANIFEST" \
        --trust-ir "$TRUST_IR_REV" --trust-cg "$TRUST_CG_REV" \
        || die "native Agh compiler source authority refused; no direct Git fallback"
fi
pin trust-cg-authority --manifest "$AUTHORITY_MANIFEST" --trust-ir "$TRUST_IR_REV" \
    || die "trust-cg $TRUST_CG_REV does not co-own trust-ir $TRUST_IR_REV (see above).
      Move trust-cg to a commit that pins $TRUST_IR_REV first; adopting this
      pair would put two trust-ir graphs in Cargo.lock."

# A.4 -- one frontend for lock refreshes and every nested gate. Explicit
# choices apply to dry runs too: dev-alias reachability resolves with Targo
# before anything is staged. A dry run without an explicit choice can still
# inspect a fixture with no aliases without requiring a Rust toolchain.
if [[ $DRY_RUN -eq 0 || $SOURCE_ONLY -eq 1 || -n "$TARGO" || -n "${CLEAN_TARGO:-}" ]]; then
    TARGO="$(resolve_targo)" || die "no Targo frontend: pass --targo, set CLEAN_TARGO, or put targo on PATH.
      Stock cargo is never used here (owner ruling; see CLAUDE.md)."
    [[ -x "$TARGO" ]] || die "Targo frontend is not executable: $TARGO"
    export TARGO
    printf 'lock refresh frontend: %s\n' "$TARGO"
fi

# A.5 -- the derived artifacts must be green BEFORE the move, so that what
# phase G re-derives is exactly what this move left stale (and a tree that is
# already red is not discovered an hour into a replay). Read-only: every node's
# own leg check.
#
# A REFUSAL ONLY OVER COHERENT LEGS. The vendor manifest pins the root lock and
# check_lint_coverage's registry row pins the crystal manifest and lock, so legs
# that disagree (a split under --repair, a lock an interrupted bump or an
# incomplete rollback left behind) redden those nodes BY THEMSELVES, and the
# remedy a refusal would name cannot run: the replay's `targo metadata --locked`
# refuses a stale crystal lock in every arm's baseline. This transaction
# rewrites every leg and refreshes both locks, then phase G re-derives whatever
# is stale over them -- so there the check is reported, not refused.
pin check --root "$ROOT" >"$TMP/legs-before" 2>&1
LEGS_BEFORE_CODE=$?
if [[ $LEGS_BEFORE_CODE -ne 0 && $LEGS_BEFORE_CODE -ne 3 ]]; then
    die "cannot establish pre-bump pin coherence:
$(sed 's/^/        /' "$TMP/legs-before")
      A shape, policy or tooling failure is not evidence of a split."
elif [[ $SOURCE_ONLY -eq 1 ]]; then
    printf 'SOURCE SCOPE: derived diagnostic artifacts NOT JUDGED; no diagnostic mint or replay is performed in this scope.\n'
elif [[ $LEGS_BEFORE_CODE -eq 0 ]]; then
    "$PY" -B "$REDERIVE_PY" --check \
        || die "a derived artifact is already red before the bump (the RED rows above).
      Re-derive it first (python3 scripts/rederive_chain.py) or fix what it names;
      a pin bump re-derives only what it moves."
elif ! "$PY" -B "$REDERIVE_PY" --check; then
    warn "the legs disagree before the move:
$(sed 's/^/        /' "$TMP/legs-before")
      so the derived artifacts that read them are not judged against them: the
      RED rows above are reported, NOT refused. Every leg is rewritten and both
      locks refreshed, then phase G re-derives whatever is stale over the moved
      tree, these rows included whatever caused them. Review its diff."
fi

# The deferred no-op return (see PHASE A). Reached only after EVERY
# precondition above has passed, so "nothing to do" now means the manifests,
# the trust-cg authority commit, the remotes AND both lockfiles were all
# confirmed -- not merely that the manifest legs agree with each other.
if [[ $ALREADY_COHERENT -eq 1 ]]; then
    if [[ $LEGS_BEFORE_CODE -eq 0 ]]; then
        cat "$TMP/legs-before"
        if [[ $SOURCE_ONLY -eq 1 ]]; then
            verify_locked_graph_and_boundary
            printf '\nalready at trust-ir %s + trust-cg %s; canonical dependency graph is coherent. Full diagnostic NOT JUDGED.\n' \
                "$TRUST_IR_REV" "$TRUST_CG_REV"
        else
            printf '\nalready at trust-ir %s + trust-cg %s; all legs coherent and every precondition verified -- nothing to do.\n' \
                "$TRUST_IR_REV" "$TRUST_CG_REV"
        fi
        SUCCESS=1
        exit 0
    fi
    cat "$TMP/legs-before" >&2
    # The manifests agree on the target and a lock does not: a split the census
    # (manifests only) cannot see. Refused like any split; --repair refreshes
    # both locks at the target (phase B stages no manifest).
    [[ $REPAIR_OK -eq 1 ]] \
        || die "the manifests already read the target but a lockfile does not (see above).
      A lock left behind is a split: re-run with --repair to refresh both locks
      at the target."
    REPAIR=1
    printf '\nREPAIR MODE (--repair): the manifests read the target and a lockfile does not;\n'
    printf '             both locks are refreshed at trust-ir %s + trust-cg %s.\n' \
        "$TRUST_IR_REV" "$TRUST_CG_REV"
fi

# --- PHASE B: stage the rewrites (still nothing installed) -------------------
say "PHASE B -- staging rewrites under $STAGE"
STAGED="$(pin stage --root "$ROOT" --trust-ir-to "$TRUST_IR_REV" --trust-cg-to "$TRUST_CG_REV" \
    --stage-dir "$STAGE")" \
    || die "staging failed; the working tree was not touched"
printf '%s\n' "$STAGED"

if [[ $DRY_RUN -eq 1 ]]; then
    say "--dry-run -- staged vs working tree"
    while IFS= read -r relative; do
        [[ -n "$relative" ]] || continue
        diff -u "$ROOT/$relative" "$STAGE/$relative" \
            --label "a/$relative" --label "b/$relative"
    done <<<"$STAGED"
    printf '\nDRY RUN -- nothing installed, no locks refreshed.\n'
    SUCCESS=1
    exit 0
fi

# --- PHASE C: back up every file the transaction can touch -------------------
say "PHASE C -- backing up the legs, both lockfiles and the derived artifacts"
while IFS= read -r relative; do
    [[ -n "$relative" ]] || continue
    [[ -f "$ROOT/$relative" ]] || die "controlled leg is missing: $relative"
    mkdir -p "$BACKUP/$(dirname "$relative")"
    cp -p "$ROOT/$relative" "$BACKUP/$relative" \
        || die "cannot back up $relative; refusing to proceed"
    printf '%s\n' "$relative" >>"$BACKED_UP"
done <<<"$CONTROLLED_LEGS"
while IFS= read -r relative; do
    [[ -n "$relative" ]] || continue
    if [[ ! -e "$ROOT/$relative" ]]; then
        printf '%s\n' "$relative" >>"$TMP/absent-before"
        continue
    fi
    mkdir -p "$BACKUP/$(dirname "$relative")"
    cp -p "$ROOT/$relative" "$BACKUP/$relative" \
        || die "cannot back up $relative; refusing to proceed"
    printf '%s\n' "$relative" >>"$BACKED_UP"
done <<<"$DERIVED_OUTPUTS"

# --- PHASE D: install ---------------------------------------------------------
say "PHASE D -- installing the staged legs"
INSTALLED=1
while IFS= read -r relative; do
    [[ -n "$relative" ]] || continue
    cp "$STAGE/$relative" "$ROOT/$relative" \
        || die "cannot install $relative"
    printf 'installed %s\n' "$relative"
done <<<"$STAGED"

# --- PHASE E: refresh BOTH lockfiles -----------------------------------------
# `metadata` is a non-compiling subcommand: no `--unverified`, no proof claim.
# The root lock records the trust-ir and trust-cg graphs; the crystal lock is
# THE LEG THAT WAS MISSED -- a standalone workspace no `--workspace` command
# ever refreshes.
say "PHASE E -- refreshing lockfiles"
"$TARGO" metadata --format-version 1 --manifest-path "$ROOT/Cargo.toml" >/dev/null \
    || die "root lock refresh failed (Targo metadata)"
printf 'refreshed Cargo.lock\n'
"$TARGO" metadata --format-version 1 --manifest-path "$ROOT/scripts/crystal_a2_project/Cargo.toml" >/dev/null \
    || die "scripts/crystal_a2_project/Cargo.lock refresh failed (Targo metadata)"
printf 'refreshed scripts/crystal_a2_project/Cargo.lock\n'

# --- PHASE F: verify ----------------------------------------------------------
say "PHASE F -- verification"

# F.1 (MANDATORY, no Rust toolchain): every manifest leg and both lockfiles
# agree on the new revisions, the root lock records exactly one trust-cg graph,
# and trust-ir's clean.git pin resolved into THIS workspace (one clean-kernel
# row, no source) rather than dropping the root [patch].
pin check --root "$ROOT" \
    || die "post-bump pin coherence FAILED -- see above"

verify_locked_graph_and_boundary

if [[ $REPAIR -eq 0 ]]; then
    for OLD_NEW in "$CURRENT_TRUST_IR $TRUST_IR_REV" "$CURRENT_TRUST_CG $TRUST_CG_REV"; do
        read -r OLD_REV NEW_REV <<<"$OLD_NEW"
        [[ "$OLD_REV" == "$NEW_REV" ]] && continue
        STALE="$(git -C "$ROOT" grep -l -F -e "$OLD_REV" -- . ':!*.lock' \
            ':!scripts/trust_ir_pin_legs.py' ':!scripts/test_bump_trust_ir_pin.py' 2>/dev/null)"
        if [[ -n "$STALE" ]]; then
            warn "the previous revision $OLD_REV still appears in:
$(printf '        %s\n' $STALE)
      Those are not controlled pin legs (docs, ledgers, fixtures). Review
      whether any should move."
        fi
    done
fi

if [[ $SOURCE_ONLY -eq 1 ]]; then
    say "SOURCE TRANSACTION COMPLETE -- canonical legs and both lockfiles verified"
    printf 'Full diagnostic and its derived artifacts: NOT JUDGED (phase G not run).\n'
    printf 'Qualify affected consumers before ordinary source publication; this dependency transaction makes no compiler or proof claim.\n'
    printf 'A full diagnostic still requires scripts/rederive_chain.py and its complete recorded replay.\n'
    SUCCESS=1
    exit 0
fi

# --- PHASE G: re-derive what the move left stale -------------------------------
# Last, inside the transaction: a replay or a mint that refuses rolls the whole
# move back (see the header). The registry row's replay is the long step.
say "PHASE G -- re-deriving the artifacts this move left stale (scripts/rederive_chain.py)"
REDERIVE_ARGS=()
[[ $OFFLINE -eq 1 ]] && REDERIVE_ARGS+=(--offline)
"$PY" -B "$REDERIVE_PY" "${REDERIVE_ARGS[@]+"${REDERIVE_ARGS[@]}"}" \
    || die "re-deriving the artifacts the move left stale FAILED (above) -- the bump is not done"

say "DONE -- trust-ir pinned at $TRUST_IR_REV and trust-cg at $TRUST_CG_REV across every leg and both lockfiles"
printf 'Review with: git diff --stat\n'
printf 'The derived artifacts were re-derived over the new pin. Build and test the consumers before pushing.\n'
SUCCESS=1
