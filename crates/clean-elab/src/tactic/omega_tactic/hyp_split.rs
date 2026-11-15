// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! omega's propositional layer: conjunctions, disjunctions and the shapes
//! that become them, in hypothesis position (gap G26, ledger class 95).
//!
//! Lean 4.8's `omega` (`Lean/Elab/Tactic/Omega/Frontend.lean`) collects `∧`
//! hypotheses as both conjuncts, rewrites `≠`, `¬(p ∨ q)`, `p → q` and
//! `p ↔ q` into `∧`/`∨` facts, queues every `∨` fact, and splits a queued
//! disjunction only after the linear problem without it failed
//! (`omegaImpl` → `splitDisjunction` → `cases₂`). Clean's linear pipeline
//! dropped all of those hypotheses, so `(hc : c = 1 ∨ c = 2) ⊢ c ≤ 2` fell
//! through to the linarith delegate and failed.
//!
//! [`omega_with_hyp_splits`] wraps that pipeline (`core`) with the same lazy
//! discipline: run `core`; when it fails recoverably, destructure and rewrite
//! every hypothesis [`hyp_facts::classify`] reads (non-branching), retry, and
//! only then `cases` the first relevant disjunction and solve each branch the
//! same way. Every step is an ordinary proof-carrying tactic step — `cases`
//! (`Or.casesOn` / `And.casesOn`) and `replace_local_decl_with_cast` — and the
//! assembled term is strictly re-checked when the declaration is, so the
//! certificate is the per-branch omega certificates joined by eliminators: its
//! size is their sum, never a product.
//!
//! Every pipeline run inside the layer sees only what Lean's `omega` reads
//! (`hyp_view::restrict_to_facts`): a `Nat`/`Int` fact target or `False`,
//! and the linear facts in context, with `False`, opaque propositions and
//! anything multiplying two atoms cleared. A compound goal is negated only
//! when Lean would find it `Decidable`; otherwise it is dropped, as Lean's
//! `falseOrByContra (useClassical := false)` does.
//!
//! Bounded: at most [`MAX_HYP_CASE_SPLITS`] case splits per `omega` call;
//! reaching the cap refuses loudly, it never truncates the search silently.

use std::collections::{HashSet, VecDeque};

use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use clean_parser::SurfaceName;

use super::super::pattern::util::generate_fresh_hyp_name as fresh_hyp_name;
use super::super::proof_manipulation::cases_fvar;
use super::super::{by_contra, exfalso, is_false, match_and, match_or};
use super::hyp_facts::{classify, may_act, yields_fact, HypAction};
use super::hyp_tighten::tighten_leaf;
use super::hyp_view::{lean_decidable, restrict_to_facts};
use super::{Goal, ProofState, TacticError, TacticResult};

/// Case splits one `omega` call may perform (a full 2^7-leaf tree, or two
/// six-way disjunctions with room to spare). Lean has no cap; this one keeps a
/// context full of disjunctions from exhausting the box. A split costs one
/// pipeline run per branch and adds one eliminator to the term.
pub(super) const MAX_HYP_CASE_SPLITS: usize = 128;

/// Non-branching rewrites (destructures and casts) one `omega` call may make.
const MAX_HYP_REWRITES: usize = 256;

/// The search's remaining allowance and what it has spent.
struct Budget {
    splits_left: usize,
    rewrites_left: usize,
    splits_done: usize,
}

/// Where a goal sits in one `omega` call's case-split tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Node {
    /// The goal `omega` was called on.
    Root,
    /// A goal a case split produced.
    Branch,
}

/// A rollback point: goals, metavariables (an OWNED scope, so a callee cannot
/// consume it) and the fvar cursor, which `close_fvars` ties to binder depth.
struct Snapshot {
    goals: VecDeque<Goal>,
    next_fvar: u64,
    token: crate::unify::OwnedMetaScopeToken,
}

impl Snapshot {
    fn take(state: &mut ProofState) -> Self {
        Self {
            goals: state.goals.clone(),
            next_fvar: state.next_fvar,
            token: state.metas_mut().push_owned_scope(),
        }
    }

    /// Keep the work on `Ok`, roll it back on `Err`. A scope a callee tampered
    /// with is rolled back and reported, never committed.
    fn close(self, state: &mut ProofState, outcome: TacticResult) -> TacticResult {
        if outcome.is_ok()
            && state
                .metas_mut()
                .close_owned_scope(self.token, false)
                .is_ok()
        {
            return Ok(());
        }
        if outcome.is_ok() {
            state.invalidate_tc_cache();
            state.goals = self.goals;
            state.next_fvar = self.next_fvar;
            return Err(TacticError::ArithmeticFailed {
                tactic: "omega".into(),
                reason: "hypothesis case split: metavariable scope was disturbed; rolled back"
                    .into(),
            });
        }
        let _ = state.metas_mut().close_owned_scope(self.token, true);
        state.invalidate_tc_cache();
        state.goals = self.goals;
        state.next_fvar = self.next_fvar;
        outcome
    }
}

/// Run `core` on the current goal, splitting hypotheses as Lean's `omega`
/// does when `core` alone fails. Other goals are untouched.
///
/// ENSURES: on `Ok`, the current goal is closed by a term built only from
///   `core`'s own closings joined by `cases` / `replace_local_decl_with_cast`
///   steps; on `Err`, the goal list is as on entry.
pub(super) fn omega_with_hyp_splits(
    state: &mut ProofState,
    core: fn(&mut ProofState) -> TacticResult,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }
    let rest = state.goals.split_off(1);
    let mut budget = Budget {
        splits_left: MAX_HYP_CASE_SPLITS,
        rewrites_left: MAX_HYP_REWRITES,
        splits_done: 0,
    };
    let result = solve(state, core, &mut budget, Node::Root);
    state.goals.extend(rest);
    result.map_err(|err| annotate(err, budget.splits_done))
}

/// Name the splits in a failure so a refused goal says what was tried.
fn annotate(err: TacticError, splits: usize) -> TacticError {
    match err {
        TacticError::ArithmeticFailed { reason, .. } if splits > 0 => {
            TacticError::ArithmeticFailed {
                tactic: "omega".into(),
                reason: format!("{reason} (in a branch of {splits} hypothesis case split(s))"),
            }
        }
        other => other,
    }
}

/// `core` on the view of the current goal Lean's `omega` reads
/// ([`restrict_to_facts`]). Every pipeline run the layer makes goes through
/// here, under a rollback point; only the root goal's first run does not.
fn run_core(state: &mut ProofState, core: fn(&mut ProofState) -> TacticResult) -> TacticResult {
    restrict_to_facts(state)?;
    core(state)
}

/// `step` under a rollback point.
fn attempt(
    state: &mut ProofState,
    step: impl FnOnce(&mut ProofState) -> TacticResult,
) -> TacticResult {
    let snapshot = Snapshot::take(state);
    let outcome = step(state);
    snapshot.close(state, outcome)
}

/// A leaf's last try: restate its strict comparisons and equalities the way
/// Lean's `omega` reads them (`hyp_tighten`), then run `core` again, on the
/// goal and on `False`. Rolled back unless it closes the goal.
fn last_resort(state: &mut ProofState, core: fn(&mut ProofState) -> TacticResult) -> bool {
    let snapshot = Snapshot::take(state);
    let closed = tighten_leaf(state) > 0
        && (attempt(state, |s| run_core(s, core)).is_ok() || attempt_exfalso(state, core));
    let outcome = if closed {
        Ok(())
    } else {
        Err(TacticError::GoalMismatch(
            "omega: the restated leaf did not close".into(),
        ))
    };
    snapshot.close(state, outcome).is_ok()
}

/// `core` on `False` (`exfalso` first) when the goal is something else.
///
/// Lean's `omega` refutes its facts with the goal negated among them, so it
/// also closes a goal its hypotheses contradict on their own: a case-split
/// branch is mostly that (`0 < a, a < 1 ⊢ a ≥ 2`). The linear pipeline's
/// replay can refuse such a branch when the goal plays no part in the
/// refutation; on `False` it has no goal to fit.
fn attempt_exfalso(state: &mut ProofState, core: fn(&mut ProofState) -> TacticResult) -> bool {
    let Some(goal) = state.current_goal() else {
        return false;
    };
    if is_false(&state.metas.instantiate(&goal.target)) {
        return false;
    }
    attempt(state, |s| {
        exfalso(s)?;
        run_core(s, core)
    })
    .is_ok()
}

/// Close the single goal in `state`: `core` first, then the propositional
/// layer.
/// `node` says whether this goal is the call's own or a case-split branch.
fn solve(
    state: &mut ProofState,
    core: fn(&mut ProofState) -> TacticResult,
    budget: &mut Budget,
    node: Node,
) -> TacticResult {
    // The root goal's first run is the linear pipeline exactly as before this
    // layer existed; every goal the layer builds gets Lean's view of it.
    let first = match node {
        Node::Root => attempt(state, core),
        Node::Branch => attempt(state, |s| run_core(s, core)),
    };
    let base_err = match first {
        Ok(()) => return Ok(()),
        Err(err) if !err.is_recoverable_first_failure() => return Err(err),
        Err(err) => err,
    };
    let Some(goal) = state.current_goal().cloned() else {
        return Err(base_err);
    };
    let acts =
        compound_goal(state, &goal) || goal.local_ctx.iter().any(|d| may_act(state, &goal, d));
    // At the root, a goal the propositional layer has nothing to act on keeps
    // the linear pipeline's verdict and costs nothing more than before this
    // layer. A branch is where contradictory facts are the common case.
    if (acts || node == Node::Branch) && attempt_exfalso(state, core) {
        return Ok(());
    }
    if !acts {
        if node == Node::Branch && last_resort(state, core) {
            return Ok(());
        }
        return Err(base_err);
    }
    let snapshot = Snapshot::take(state);
    let outcome = split_and_solve(state, core, budget, base_err);
    snapshot.close(state, outcome)
}

fn split_and_solve(
    state: &mut ProofState,
    core: fn(&mut ProofState) -> TacticResult,
    budget: &mut Budget,
    base_err: TacticError,
) -> TacticResult {
    let goal = state.current_goal().cloned().ok_or(TacticError::NoGoals)?;
    if compound_goal(state, &goal) && negate_goal(state, &goal).is_err() {
        return Err(base_err);
    }
    if normalize(state, budget) > 0 {
        match attempt(state, |s| run_core(s, core)) {
            Ok(()) => return Ok(()),
            Err(err) if !err.is_recoverable_first_failure() => return Err(err),
            Err(_) => {}
        }
    }
    let goal = state.current_goal().cloned().ok_or(TacticError::NoGoals)?;
    let Some(split) = goal.local_ctx.iter().find_map(|d| {
        matches!(classify(state, &goal, d), Some(HypAction::Split)).then_some(d.fvar)
    }) else {
        if last_resort(state, core) {
            return Ok(());
        }
        return Err(base_err);
    };
    if budget.splits_left == 0 {
        return Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!(
                "hypothesis case-split budget of {MAX_HYP_CASE_SPLITS} exhausted; \
                 refusing to split further"
            ),
        });
    }
    budget.splits_left -= 1;
    budget.splits_done += 1;
    if cases_fvar(state, split).is_err() {
        return Err(base_err);
    }
    let branches: Vec<Goal> = state.goals.drain(..).collect();
    let mut cursor_high = state.next_fvar;
    for branch in branches {
        // Sibling branches number their binders from the same base (`cases`
        // does, #3528): `close_fvars` ties a tactic FVar's id to its binder
        // depth, so a local minted in this branch must not continue from the
        // cursor the previous branch advanced. `eval_induction_alts` resets
        // the same way before each alternative.
        state.next_fvar = state.goal_binder_base(&branch);
        state.goals.push_back(branch);
        solve(state, core, budget, Node::Branch)?;
        cursor_high = cursor_high.max(state.next_fvar);
        if !state.goals.is_empty() {
            return Err(TacticError::ArithmeticFailed {
                tactic: "omega".into(),
                reason: "hypothesis case split: a branch left goals open".into(),
            });
        }
    }
    state.next_fvar = cursor_high;
    Ok(())
}

/// Apply every non-branching step [`classify`] offers — destructure `∧`,
/// replace `≠` / `¬(p ∨ q)` / `→` / `↔` by the shape omega reads — until none
/// is left or the rewrite budget is spent. Returns the number applied.
fn normalize(state: &mut ProofState, budget: &mut Budget) -> usize {
    let mut applied = 0;
    let mut refused: HashSet<FVarId> = HashSet::new();
    while budget.rewrites_left > 0 {
        let Some(goal) = state.current_goal().cloned() else {
            break;
        };
        let next = goal
            .local_ctx
            .iter()
            .filter(|d| !refused.contains(&d.fvar))
            .find_map(|d| match classify(state, &goal, d) {
                Some(HypAction::Split) | None => None,
                Some(action) => Some((d.fvar, action)),
            });
        let Some((fvar, action)) = next else {
            break;
        };
        budget.rewrites_left -= 1;
        let snapshot = Snapshot::take(state);
        let outcome = match action {
            HypAction::Destructure => cases_fvar(state, fvar).and_then(|()| {
                if state.goals.len() == 1 {
                    Ok(())
                } else {
                    Err(TacticError::GoalMismatch(
                        "omega: destructuring a conjunction did not leave one goal".into(),
                    ))
                }
            }),
            HypAction::Replace { new_ty, cast } => {
                state.replace_local_decl_with_cast(fvar, new_ty, cast)
            }
            HypAction::Split => Ok(()),
        };
        if snapshot.close(state, outcome).is_ok() {
            applied += 1;
        } else {
            refused.insert(fvar);
        }
    }
    applied
}

/// Lean's `omega` opens with `falseOrByContra (useClassical := false)`: a
/// goal with a `Decidable` instance is negated into a hypothesis
/// (`Decidable.byContradiction`, then `intro`), which `addFact` / `pushNot`
/// read like any other; a goal without one is dropped (`False.elim`) and adds
/// no fact. The negation is introduced as `Not target`, the spelling `intro`
/// gives it, so it is read as a negation and not as an implication to `False`.
fn negate_goal(state: &mut ProofState, goal: &Goal) -> TacticResult {
    let target = state.metas.instantiate(&goal.target);
    if !lean_decidable(state, goal, &target) {
        return exfalso(state);
    }
    let name = fresh_hyp_name(&goal.local_ctx, &SurfaceName::component("h_omega", false));
    by_contra(state, &name)?;
    let negated = state
        .current_goal()
        .and_then(|g| g.local_ctx.last())
        .map(|d| d.fvar)
        .ok_or(TacticError::NoGoals)?;
    let not_target = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), target);
    state.replace_local_decl_type_validated(negated, not_target)
}

/// A `∧` / `∨` goal carrying a `Nat`/`Int` comparison: the shape Lean's
/// `omega` reads only after negating it into a hypothesis.
fn compound_goal(state: &ProofState, goal: &Goal) -> bool {
    let target = state.metas.instantiate(&goal.target);
    (match_or(&target).is_some() || match_and(&target).is_some()) && yields_fact(&target)
}
