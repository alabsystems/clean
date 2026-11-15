// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive type reasoning tactics: injection, discriminate, and rcases.
//!
//! These tactics work with equalities and hypotheses involving inductive type
//! constructors:
//!
//! - **injection**: Given `h : C a₁ ... aₙ = C b₁ ... bₙ`, derives equalities
//!   `a₁ = b₁`, ..., `aₙ = bₙ` (constructor injectivity).
//! - **discriminate**: Given `h : C₁ args = C₂ args` where `C₁ ≠ C₂`, closes
//!   the goal since different constructors are never equal (no confusion).
//! - **rcases**: Recursive case analysis that destructs nested inductive types.

use crate::stack_safe;
use clean_kernel::{Expr, ExprKind};

use super::core::{ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::noconfusion_app::{ctor_app, injection_core, InjectionOutcome};
use super::proof_manipulation::cases;

/// `injection h` on `h : C a₁ … aₙ = C b₁ … bₙ`: Lean's `injectionCore` +
/// `injectionIntro` (`Lean/Meta/Tactic/Injection.lean`).
///
/// The field equations are the premises of `C`'s `noConfusionType`, read off
/// the environment by [`super::noconfusion_app::injection_core`]: each carries
/// its field's own universe level, a field whose type depends on an earlier
/// field is related by `HEq` (turned into `Eq` once its two types are
/// definitionally equal, Lean's `heqToEq`), and `Prop` fields get none. `h` is
/// cleared when nothing else mentions it (Lean's `tryClear`).
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis of type `C a₁ ... aₙ = C b₁ ... bₙ`
/// ENSURES: On Ok, the field equations are added to the context as `h_inj…`
/// ENSURES: On Err(HypothesisNotFound), `hyp_name` is not in the local context
pub fn injection(state: &mut ProofState, hyp_name: &clean_parser::SurfaceName) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Check that the hypothesis is an equality
    let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
    let (eq_type, lhs, rhs, _eq_levels) = match_equality(&hyp_ty).map_err(|_| {
        TacticError::GoalMismatch(format!("injection: {hyp_name} is not an equality"))
    })?;
    let lhs = state.metas.instantiate(&lhs);
    let rhs = state.metas.instantiate(&rhs);

    let not_ctor = |which: &str| {
        TacticError::GoalMismatch(format!(
            "injection: {which}-hand side is not a constructor application"
        ))
    };
    let lhs_ctor = ctor_app(state, &goal, &lhs).ok_or_else(|| not_ctor("left"))?;
    let rhs_ctor = ctor_app(state, &goal, &rhs).ok_or_else(|| not_ctor("right"))?;
    // Lean's `injection` closes the goal on distinct constructors; Clean's has
    // always refused them (`discriminate` / `cases` close it) — a refusal,
    // never a widening.
    if lhs_ctor.ctor != rhs_ctor.ctor {
        return Err(TacticError::GoalMismatch(format!(
            "injection: constructors do not match ({} vs {})",
            lhs_ctor.ctor, rhs_ctor.ctor
        )));
    }
    if lhs_ctor.num_fields == 0 {
        return Err(TacticError::GoalMismatch(
            "injection: constructor has no fields to inject".to_string(),
        ));
    }

    let outcome = injection_core(
        state,
        &goal,
        &eq_type,
        (&lhs, &rhs),
        &Expr::fvar(hyp_decl.fvar),
        Some(hyp_decl.fvar),
    )?;
    let InjectionOutcome::Subgoal { num_eqs } = outcome else {
        return Ok(());
    };

    // `injectionIntro`: introduce each field equation, `HEq` → `Eq` when the
    // two types agree.
    for i in 0..num_eqs {
        let suffix = if num_eqs > 1 {
            format!("_inj_{}", i + 1)
        } else {
            "_inj".to_owned()
        };
        let base = super::pattern::names::generated_suffix(hyp_name, &suffix);
        let ctx = &state.current_goal().ok_or(TacticError::NoGoals)?.local_ctx;
        let inj_name = super::pattern::util::generate_fresh_hyp_name(ctx, &base);
        super::proof_term::intro(state, &inj_name)?;
        super::cases_unify_eqs::heq_local_to_eq(state, &inj_name)?;
    }

    // Mirror Lean 4's `injection`: after introducing the field equalities it
    // attempts to discharge the goal with them (via `assumption`, up to
    // definitional equality). Empirically confirmed against `lean`:
    //   - `h : C a = C b ⊢ a = b`  is closed by the derived `a = b`.
    //   - a goal that no derived equality matches (e.g. `⊢ b = a`, `⊢ b = a+1`,
    //     or a non-equality `⊢ True → …`) is left OPEN with the derived
    //     hypotheses in context — Lean reports `unsolved goals` there, and so
    //     do we. Crucially this is NOT symm-aware: `⊢ b = a` from `a = b` is
    //     NOT closed, matching Lean.
    // `assumption` builds a kernel-checked `exact` term, so soundness is never
    // widened: a false goal can never be closed by a hypothesis it does not
    // definitionally match. Only the "no matching hypothesis" case is swallowed
    // so the goal remains open (fail-open into an honest UnsolvedGoals); any
    // other tactic error propagates.
    //
    // This arm used to read `HypothesisNotFound(_)`, which is strictly wider
    // than the comment above it: that variant is a NAME failure ("you wrote `h`
    // and it is not here"), and swallowing one would hide a real bug. It caught
    // the intended case only because `assumption` was overloading it. With
    // `NoMatchingHypothesis` split out the arm finally says what it means, and
    // a genuine name failure now propagates.
    match super::proof_term::assumption(state) {
        Ok(()) => {}
        Err(TacticError::NoMatchingHypothesis { .. }) => {}
        Err(other) => return Err(other),
    }

    Ok(())
}

/// Discriminate tactic: given `h : C₁ args = C₂ args` where `C₁ ≠ C₂` are
/// constructors of the same inductive type, closes the goal (no confusion).
///
/// Errors: `HypothesisNotFound`, `GoalMismatch` (not equality, same ctor, different types).
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis equating two distinct constructors
/// ENSURES: On Ok, the current goal is closed (contradiction from distinct constructors)
/// ENSURES: On Err(GoalMismatch), the hypothesis is not an equality of distinct constructors
pub fn discriminate(state: &mut ProofState, hyp_name: &clean_parser::SurfaceName) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Check that the hypothesis is an equality
    let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
    let (eq_type, lhs, rhs, _eq_levels) = match_equality(&hyp_ty).map_err(|_| {
        TacticError::GoalMismatch(format!("discriminate: {hyp_name} is not an equality"))
    })?;

    // Get constructor applications from both sides
    let lhs_whnf = state.whnf(&goal, &lhs);
    let rhs_whnf = state.whnf(&goal, &rhs);

    let lhs_head = lhs_whnf.get_app_fn();
    let rhs_head = rhs_whnf.get_app_fn();

    // Check both sides are constructor applications
    let lhs_ctor_name = match lhs_head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "discriminate: left-hand side is not a constructor application".to_string(),
            ));
        }
    };

    let rhs_ctor_name = match rhs_head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "discriminate: right-hand side is not a constructor application".to_string(),
            ));
        }
    };

    // Verify the constructors are DIFFERENT
    if lhs_ctor_name == rhs_ctor_name {
        return Err(TacticError::GoalMismatch(
            "discriminate: constructors are the same (use injection instead)".to_string(),
        ));
    }

    // Verify both are constructors of the same inductive type
    let lhs_ctor_info = state
        .env
        .get_constructor(&lhs_ctor_name)
        .ok_or_else(|| {
            TacticError::GoalMismatch(format!(
                "discriminate: {lhs_ctor_name} is not a constructor"
            ))
        })?
        .clone();

    let rhs_ctor_info = state
        .env
        .get_constructor(&rhs_ctor_name)
        .ok_or_else(|| {
            TacticError::GoalMismatch(format!(
                "discriminate: {rhs_ctor_name} is not a constructor"
            ))
        })?
        .clone();

    if lhs_ctor_info.inductive_name != rhs_ctor_info.inductive_name {
        return Err(TacticError::GoalMismatch(format!(
            "discriminate: constructors are from different types ({} vs {})",
            lhs_ctor_info.inductive_name, rhs_ctor_info.inductive_name
        )));
    }

    // Build proof using noConfusion: when v1 and v2 are different
    // constructors, `T.noConfusionType P v1 v2` reduces to `P`, so
    // `T.noConfusion … h : goal.target`. The premises and universe levels are
    // read off `noConfusion`'s declared type — Lean 4.8's classic signature or
    // Lean 4.30's heterogeneous one, which a parameterized type such as `List`,
    // `Option` or `Except` has here — by the helper `injection` and `cases`'
    // equation unification share (round-5 lane B's class (81) finding: the
    // classic application this built by hand failed on those types; kept at
    // the round-6 integration on lane C's `mk_no_confusion`).
    let proof = super::noconfusion_app::mk_no_confusion(
        state,
        &goal,
        &goal.target,
        &eq_type,
        (&lhs_whnf, &rhs_whnf),
        &Expr::fvar(hyp_decl.fvar),
    )?;

    // Part of #2154: migrated to checked close_goal. The kernel's whnf reduces
    // noConfusionType P v1 v2 → P via delta+iota for different constructors.
    state.close_goal(&goal, proof)?;

    Ok(())
}

/// Recursive cases tactic: destructs nested inductive types up to `max_depth`.
///
/// # Errors
/// - Same as `cases` for the base case
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis whose type is an inductive type
/// ENSURES: On Ok, nested inductive types are destructed recursively up to `max_depth`
/// ENSURES: Recursion stops at `max_depth == 0` (returns Ok without further destruction)
pub fn rcases(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
    max_depth: usize,
) -> TacticResult {
    stack_safe(|| {
        if max_depth == 0 {
            return Ok(());
        }

        // First apply cases
        cases(state, hyp_name)?;

        // Then try to recursively apply rcases on any new hypotheses that are inductive types
        let mut goals_count = state.goals.len();
        let mut processed = 0;

        while processed < goals_count {
            // Get the current goal (we iterate through all goals created by cases)
            let goal_idx = processed;
            if goal_idx >= state.goals.len() {
                break;
            }

            let goal = state.goals[goal_idx].clone();
            processed += 1;

            // Find hypotheses in this goal's context that are inductive types
            // and could be further destructed
            for decl in &goal.local_ctx {
                let decl_ty = state.whnf(&goal, &decl.ty);
                let ty_head = decl_ty.get_app_fn();

                // Check if this is an inductive type
                if let ExprKind::Const(name, _) = ty_head.kind() {
                    if state.env.get_inductive(name).is_some() {
                        // This is an inductive type, try rcases
                        // But we need to be careful not to infinite loop
                        // So we only recurse if depth allows

                        // Part of #2232: use snapshot/restore for rollback.
                        // cases() irreversibly assigns the goal's meta via
                        // close_goal_unchecked, so pop_current_goal() cannot
                        // undo on failure. Use MetaState undo trail instead.
                        let goals_snapshot = state.goals.clone();
                        state.metas.push_scope();
                        let next_fvar_snapshot = state.next_fvar;

                        // Focus on this goal temporarily
                        state.invalidate_tc_cache();
                        let original_goal = state.goals.remove(goal_idx).expect("goal_idx valid");
                        state.goals.push_front(original_goal);

                        // Try to apply rcases (may fail if already destructed)
                        if rcases(state, &decl.name, max_depth - 1).is_ok() {
                            state.metas.commit();
                            processed = 0;
                            goals_count = state.goals.len(); // Update after goal structure change
                            break;
                        }

                        // Restore full state on failure
                        state.metas.pop_scope();
                        state.goals = goals_snapshot;
                        state.next_fvar = next_fvar_snapshot;
                        state.invalidate_tc_cache();
                    }
                }
            }
        }

        Ok(())
    })
}
