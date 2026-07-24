// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term refinement, development, and closing tactics.
//!
//! This module contains tactics for refining goals with partial proof terms,
//! providing witnesses for existentials, deciding propositions by computation,
//! and closing goals through development aids or type changes.
//!
//! Tactics: `refine`, `use_`, `native_decide`, `dec_trivial`, `sorry`, `admit`,
//! `change`, `show`, `change_at`, `rfl_closure`, `norm_beta`, `assert_`,
//! `assert_after`.

mod refine;
mod refine_bridge;

#[cfg(test)]
pub(crate) use refine::count_placeholders;
#[cfg(test)]
pub(crate) use refine::refine_elaborated;
pub use refine::{refine, refine_placeholder};
pub(crate) use refine_bridge::{
    refine_elaborated_from_pending, refine_elaborated_from_pending_with_tags,
};

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::sorry::SorryKind;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::combinator::{trivial, try_tactic_preserving_state};
use super::connective::contradiction;
use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::decide_eq::decide_eq;
use super::existential::existsi;
use super::native_decide_eval::{execute_native_decide, NativeDecideExecOutcome};
use super::proof_term::{assumption, constructor, exact, rfl};
use super::smt::decide;

// ============================================================================
// use_ - Existential introduction (like existsi but more convenient)
// ============================================================================

/// Provide witnesses for an existential goal.
///
/// `use` is similar to `existsi` but more convenient for providing multiple
/// witnesses at once for nested existential quantifiers.
///
/// # Algorithm
/// 1. Check that the goal is an existential (∃ x, P x)
/// 2. Substitute the witness for the bound variable
/// 3. Continue with nested existentials if more witnesses provided
///
/// # Example
/// ```text
/// -- Goal: ∃ x y, x + y = 5
/// use 2, 3
/// -- Goal: 2 + 3 = 5
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `GoalMismatch` if goal is not an existential
///
/// # Contract
///
/// REQUIRES: `witnesses` is non-empty
/// REQUIRES: Applying `existsi` sequentially to the current goal is valid for each witness
/// ENSURES: On Ok, equivalent to `existsi(state, witness)` for each witness in order
/// ENSURES: On Err(MissingArgument) or Err(NoGoals) before iteration, state is unchanged
pub fn use_(state: &mut ProofState, witnesses: Vec<Expr>) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    if witnesses.is_empty() {
        return Err(TacticError::MissingArgument {
            tactic: "use".into(),
            expected: "at least one witness".into(),
        });
    }

    // Apply existsi for each witness
    for witness in witnesses {
        existsi(state, witness)?;
    }

    // Discharge a trivial residual side-goal, mirroring Lean/Mathlib `use`,
    // whose discharger is `try (with_reducible rfl); try trivial`. After the
    // witnesses are supplied the predicate often collapses to a reflexive
    // equality (e.g. `0 = 0`, `0 + 1 = 1`) or `True`, which the user should
    // not have to close by hand.
    //
    // SOUNDNESS / CONSERVATISM:
    //   * `rfl` and the `True.intro`-style closer produce real, kernel-checked
    //     proof terms (the whole proof is re-checked by `add_decl`); the
    //     discharger never drops or fabricates a goal.
    //   * Each branch runs under `try_tactic_preserving_state`, so a failed
    //     attempt fully restores the proof state — a genuinely non-trivial
    //     residual goal (e.g. `1 > 0`, `0 = 5`, `p 3`) is simply left open,
    //     exactly as Lean leaves it.
    //   * We deliberately do NOT run `assumption`, `decide`, or a general
    //     `trivial` here: those could close a goal the user meant to prove
    //     themselves (notably `p 3`, dischargeable by the in-context `h`, which
    //     must remain open for a following `exact h`).
    let _ = discharge_trivial_side_goal(state);

    Ok(())
}

/// Best-effort closer for the residual goal left by `use`, matching the
/// conservative half of Lean's `use` discharger (`with_reducible rfl`, then a
/// `trivial`-style no-argument constructor such as `True.intro`).
///
/// Returns `true` iff the current goal was actually closed. Never errors and
/// never leaves partial state: every attempt is wrapped so failure restores the
/// proof state. Intentionally excludes `assumption`/`decide` so it cannot
/// consume a goal the caller intends to discharge explicitly.
fn discharge_trivial_side_goal(state: &mut ProofState) -> bool {
    if state.goals.is_empty() {
        return false;
    }

    // 1. Reflexivity: closes `a = a` and reducible equalities like `0 + 1 = 1`.
    if try_tactic_preserving_state(state, rfl) {
        return true;
    }

    // 2. No-argument constructor (e.g. `⊢ True` via `True.intro`). Accept ONLY
    //    if the goal count strictly DECREASES — i.e. the goal was fully
    //    discharged, not split into fresh subgoals. Without this guard,
    //    `constructor` on `⊢ A ∧ B` would "succeed" while leaving `A`, `B` open.
    let goals_before = state.goals.len();
    if try_tactic_preserving_state(state, |s| {
        constructor(s)?;
        if s.goals.len() < goals_before {
            Ok(())
        } else {
            Err(TacticError::AllTacticsFailed {
                combinator: "use:discharge:constructor".into(),
            })
        }
    }) {
        return true;
    }

    false
}

/// Single witness version of use
///
/// REQUIRES: current goal is an existential goal compatible with `witness`
/// ENSURES: Equivalent to `use_(state, vec![witness])`
pub fn use_single(state: &mut ProofState, witness: Expr) -> TacticResult {
    use_(state, vec![witness])
}

// ============================================================================
// native_decide - Decide decidable propositions by computation
// ============================================================================

/// Decide a decidable proposition by computation.
///
/// `native_decide` is similar to `decide`, but first tries a native-Rust
/// execution path. If native compilation/execution is unavailable, it falls
/// back to the existing kernel-reduction path before giving up to `decide`.
///
/// # Algorithm
/// 1. Synthesize a kernel-reducible `Decidable` instance for the goal
/// 2. Try to compile a native `Bool` decision program for the proposition
/// 3. If native execution is unavailable, reduce the `Bool` in the kernel
/// 4. If the result is `isTrue h`, close the goal with `h`
/// 5. If both paths are unsupported, fall back to `decide`
///
/// # Example
/// ```text
/// -- Goal: 2 + 2 = 4
/// native_decide
/// -- Goal closed (evaluated to true)
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `Other` if the proposition is not decidable or evaluates to false
///
/// # Contract
///
/// REQUIRES: the current goal is decidable if this tactic is expected to succeed
/// ENSURES: On successful native or kernel reduction, closes the goal with the extracted proof payload
/// ENSURES: If both execution paths fail, falls back to `decide(state)`
pub fn native_decide(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    match execute_native_decide(state, &goal) {
        Ok(NativeDecideExecOutcome::Proved(proof)) => state.close_goal(&goal, proof),
        Ok(NativeDecideExecOutcome::Refuted) => Err(TacticError::InvalidTarget {
            tactic: "native_decide".into(),
            detail: "proposition evaluated to false".into(),
        }),
        Err(err) => {
            tracing::debug!(
                tactic = "native_decide",
                error = %err,
                "native_decide execution unavailable, falling back to decide"
            );
            decide(state)
        }
    }
}

// ============================================================================
// dec_trivial - discharge trivial decidable goals
// ============================================================================

/// Attempt to discharge a goal using decision procedures and trivial reasoning.
///
/// This tactic mirrors mathlib's `dec_trivial`: it tries to solve the goal
/// using decision procedures (`decide`, `native_decide`, `decide_eq`), falling
/// back to straightforward reasoning (`contradiction`, `trivial`).
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, one of the attempted tactics closed or transformed the current goal successfully
/// ENSURES: On Err(NoProgress), every attempted branch restored the original proof state
pub fn dec_trivial(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    if try_tactic_preserving_state(state, assumption) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, decide_eq) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, decide) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, native_decide) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, contradiction) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, trivial) {
        return Ok(());
    }

    Err(TacticError::NoProgress {
        tactic: "dec_trivial".into(),
    })
}

// ============================================================================
// Development Tactics
// ============================================================================

/// Mark the current goal as admitted (sorry).
///
/// This is a development aid that allows proceeding past unproven goals.
/// The resulting proof is NOT valid and should only be used during development.
///
/// # Tracking
///
/// This tactic uses a goal-context-aware explicit sorry builder which:
/// - Infers the universe level from the active goal context
/// - Increments `SORRY_COUNTER` for tracking how many sorries exist
/// - Respects `DENY_SORRY=1` environment variable (panics if set)
/// - Records caller location when location tracking is enabled
///
/// # Example
/// ```text
/// theorem foo : P := by
///   sorry  -- Goal marked as admitted
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed with a sorry axiom term that type-checks against the goal
/// ENSURES: The resulting proof is still intentionally unsound and therefore not fully verified
/// ENSURES: `SORRY_COUNTER` is incremented exactly once
/// ENSURES: On Err(NoGoals), state is unchanged
pub fn sorry(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    // Explicit sorry remains a trusted axiom, but the term still needs the
    // correct goal-context universe level so checked close_goal can validate it.
    let sorry_proof = state.build_goal_sorry_term(&goal, SorryKind::Explicit)?;
    state.close_goal(&goal, sorry_proof)?;
    state.record_sorry();
    Ok(())
}

/// Alias for `sorry`.
///
/// REQUIRES: same as `sorry`
/// ENSURES: Behavior is identical to `sorry(state)`
pub fn admit(state: &mut ProofState) -> TacticResult {
    sorry(state)
}

// =============================================================================
// Change/Show Tactics
// =============================================================================

/// Change the goal to a definitionally equal type.
///
/// This tactic changes the current goal to a new type that is
/// definitionally equal to the original goal type.
///
/// # Example
/// ```text
/// -- Goal: (fun x => x) n = n
/// change n = n
/// -- Goal: n = n
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `new_type` is definitionally equal to the current goal target
/// ENSURES: On Ok, only the current goal target changes to `new_type`
/// ENSURES: On Ok, TypeChecker cache is invalidated
pub fn change(state: &mut ProofState, new_type: Expr) -> TacticResult {
    // Delegate to replace_target_def_eq which checks def-eq, allocates a
    // fresh meta, closes the old goal, and pushes the new goal. This keeps
    // MetaId(0) connected through the proof chain. Part of #2477.
    state.replace_target_def_eq(new_type).map_err(|e| match e {
        TacticError::GoalMismatch(_) => TacticError::GoalMismatch(
            "change: new type is not definitionally equal to current target".to_string(),
        ),
        other => other,
    })
}

/// Alias for `change` - explicitly show what type we're proving.
///
/// REQUIRES: same as `change`
/// ENSURES: Behavior is identical to `change(state, ty)`
pub fn show(state: &mut ProofState, ty: Expr) -> TacticResult {
    change(state, ty)
}

/// Change the type of a hypothesis to a definitionally equal type.
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a hypothesis in the current goal context
/// REQUIRES: `new_type` is definitionally equal to the hypothesis's existing type
/// ENSURES: On Ok, only that hypothesis type is replaced with `new_type`
/// ENSURES: On Ok, TypeChecker cache is invalidated
pub fn change_at(state: &mut ProofState, hyp_name: &str, new_type: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Resolve the hypothesis name first so the shared proof-carry local
    // replacement helper can perform the actual rewrite.
    let hyp_fvar = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .map(|decl| decl.fvar)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    state
        .replace_local_decl_def_eq(hyp_fvar, new_type)
        .map_err(|err| match err {
            TacticError::GoalMismatch(_) => TacticError::GoalMismatch(format!(
                "change_at: new type is not definitionally equal to hypothesis '{hyp_name}' type"
            )),
            other => other,
        })
}

// =============================================================================
// Reflexive Closure and Utility Tactics
// =============================================================================

/// Try to close the goal using reflexivity of any relation.
///
/// Attempts `rfl` first, then tries other reflexive relations.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the goal was closed by `rfl`, `Iff.rfl`, or `HEq.rfl`
/// ENSURES: On Err(NoProgress), proof state is restored to its pre-call state
pub fn rfl_closure(state: &mut ProofState) -> TacticResult {
    // Try standard rfl first (wrapped to prevent state leak on failure)
    if try_tactic_preserving_state(state, rfl) {
        return Ok(());
    }

    // Try Iff.rfl for ↔ goals
    if try_tactic_preserving_state(state, |s| {
        let goal = s.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let target = s.whnf(&goal, &goal.target);
        if let ExprKind::App(f, _) = target.kind() {
            if let ExprKind::App(iff, _) = f.as_ref().kind() {
                if let ExprKind::Const(name, _) = iff.as_ref().kind() {
                    if name == &Name::from_string("Iff") {
                        let iff_rfl = Expr::const_(Name::from_string("Iff.rfl"), vec![]);
                        return exact(s, iff_rfl);
                    }
                }
            }
        }
        Err(TacticError::NoProgress {
            tactic: "rfl_closure/Iff".into(),
        })
    }) {
        return Ok(());
    }

    // Try HEq.rfl for heterogeneous equality
    if try_tactic_preserving_state(state, |s| {
        let goal = s.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let target = s.whnf(&goal, &goal.target);
        if let ExprKind::App(f, _) = target.kind() {
            if let ExprKind::App(heq, _) = f.as_ref().kind() {
                if let ExprKind::Const(name, _) = heq.as_ref().kind() {
                    if name == &Name::from_string("HEq") {
                        let heq_rfl = Expr::const_(
                            Name::from_string("HEq.rfl"),
                            vec![Level::param(Name::from_string("u"))],
                        );
                        return exact(s, heq_rfl);
                    }
                }
            }
        }
        Err(TacticError::NoProgress {
            tactic: "rfl_closure/HEq".into(),
        })
    }) {
        return Ok(());
    }

    Err(TacticError::NoProgress {
        tactic: "rfl_closure".into(),
    })
}

/// Normalize the goal by applying beta/eta reduction.
///
/// Reduces (λ x, e) y to e[x := y] and similar.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal target is replaced with its WHNF
/// ENSURES: On Ok, TypeChecker cache is invalidated
/// ENSURES: On Err(NoProgress), the target was already unchanged by WHNF reduction
pub fn norm_beta(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = &goal.target;

    // Apply WHNF which includes beta reduction
    let normalized = state.whnf(&goal, target);

    if normalized == *target {
        return Err(TacticError::NoProgress {
            tactic: "norm_beta".into(),
        });
    }

    // Part of #2477: use replace_target_def_eq instead of in-place mutation.
    // WHNF normalization is definitionally equal by construction.
    state.replace_target_def_eq(normalized)
}

/// Assert a proposition and add it as a hypothesis.
///
/// `assert name : type` creates two goals:
/// 1. Prove `type`
/// 2. Original goal with `name : type` added to context
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the original goal is replaced by two goals
/// ENSURES: On Ok, the first new goal proves `prop` in the original context
/// ENSURES: On Ok, the second new goal preserves the original target with `name : prop` appended
pub fn assert_(state: &mut ProofState, name: &str, prop: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Create metavariable for the proof of prop
    let proof_meta = state.fresh_meta(prop.clone());

    // Create new local decl for the hypothesis
    let hyp_fvar = state.fresh_fvar();
    let mut new_local_ctx = goal.local_ctx.clone();
    new_local_ctx.push(LocalDecl {
        fvar: hyp_fvar,
        name: name.to_string(),
        ty: prop.clone(),
        value: None,
    });

    // Create the continuation goal with the new hypothesis
    let cont_meta = state.fresh_meta_in_context(goal.target.clone(), &new_local_ctx);
    let cont_goal = Goal {
        meta_id: cont_meta,
        target: goal.target.clone(),
        local_ctx: new_local_ctx,
        tag: None,
    };

    // Create the proof goal for the assertion
    let proof_goal = Goal {
        meta_id: proof_meta,
        target: prop.clone(),
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };

    // Build the proof term: (λ (h : prop), ?cont) ?proof
    let proof = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            prop,
            Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(cont_meta))),
        ),
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(proof_meta))),
    );

    // Close the original goal with type-checked proof.
    // Part of #2154 Track 3 Option A: proof is App(Lam(Default, prop, FVar(cont)),
    // FVar(proof)) — simple beta redex, no missing implicits. infer_type resolves
    // meta-FVars via build_local_ctx. Ratchet 4→3.
    state.close_goal(&goal, proof)?;

    // Add both new goals (proof first, then continuation)
    state.goals.push_front(cont_goal);
    state.goals.push_front(proof_goal);

    Ok(())
}

/// Like `assert` but puts the proof goal second instead of first.
///
/// REQUIRES: same as `assert_`
/// ENSURES: On Ok, produces the same two goals as `assert_` but swaps their order
pub fn assert_after(state: &mut ProofState, name: &str, prop: Expr) -> TacticResult {
    assert_(state, name, prop)?;

    // Swap the two goals so proof is second
    if state.goals.len() >= 2 {
        state.invalidate_tc_cache();
        state.goals.swap(0, 1);
    }

    Ok(())
}
