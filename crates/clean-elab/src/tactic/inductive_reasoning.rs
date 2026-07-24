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
use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::proof_manipulation::cases;

fn mk_noconfusion_const(
    state: &ProofState,
    goal: &Goal,
    no_confusion_name: &Name,
    ctor_head: &Expr,
) -> Result<Expr, TacticError> {
    let nc_level_count = state
        .env
        .get_const(no_confusion_name)
        .ok_or_else(|| TacticError::EnvironmentMissing {
            constant: no_confusion_name.to_string(),
        })?
        .level_params
        .len();
    let ind_levels = match ctor_head.kind() {
        ExprKind::Const(_, lvls) => lvls.to_vec(),
        _ => vec![],
    };
    let nc_levels = if nc_level_count > ind_levels.len() {
        let motive_level = state
            .infer_type(goal, &goal.target)
            .ok()
            .and_then(|ty| match ty.kind() {
                ExprKind::Sort(level) => Some(level.clone()),
                _ => None,
            })
            .unwrap_or_else(Level::zero);
        [vec![motive_level], ind_levels].concat()
    } else {
        ind_levels
    };
    Ok(Expr::const_(no_confusion_name.clone(), nc_levels))
}

/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis of type `C a₁ ... aₙ = C b₁ ... bₙ`
/// ENSURES: On Ok, new hypotheses `a₁ = b₁`, ..., `aₙ = bₙ` are added to the context
/// ENSURES: On Err(HypothesisNotFound), `hyp_name` is not in the local context
pub fn injection(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Check that the hypothesis is an equality
    let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
    let (eq_type, lhs, rhs, eq_levels) = match_equality(&hyp_ty).map_err(|_| {
        TacticError::GoalMismatch(format!("injection: {hyp_name} is not an equality"))
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
                "injection: left-hand side is not a constructor application".to_string(),
            ));
        }
    };

    let rhs_ctor_name = match rhs_head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "injection: right-hand side is not a constructor application".to_string(),
            ));
        }
    };

    // Verify the constructor names match
    if lhs_ctor_name != rhs_ctor_name {
        return Err(TacticError::GoalMismatch(format!(
            "injection: constructors do not match ({lhs_ctor_name} vs {rhs_ctor_name})"
        )));
    }

    // Look up constructor info
    let ctor_info = state
        .env
        .get_constructor(&lhs_ctor_name)
        .ok_or_else(|| {
            TacticError::GoalMismatch(format!("injection: {lhs_ctor_name} is not a constructor"))
        })?
        .clone();

    // Get the arguments from both sides
    let lhs_args = lhs_whnf.get_app_args();
    let rhs_args = rhs_whnf.get_app_args();

    // Skip parameters (first num_params args)
    let num_params = ctor_info.num_params as usize;
    let num_fields = ctor_info.num_fields as usize;

    if num_fields == 0 {
        return Err(TacticError::GoalMismatch(
            "injection: constructor has no fields to inject".to_string(),
        ));
    }

    // The field arguments start after the parameters
    let lhs_fields: Vec<&Expr> = lhs_args
        .iter()
        .skip(num_params)
        .take(num_fields)
        .copied()
        .collect();
    let rhs_fields: Vec<&Expr> = rhs_args
        .iter()
        .skip(num_params)
        .take(num_fields)
        .copied()
        .collect();

    if lhs_fields.len() != rhs_fields.len() || lhs_fields.len() != num_fields {
        return Err(TacticError::GoalMismatch(format!(
            "injection: argument count mismatch (expected {} fields, got lhs={}, rhs={})",
            num_fields,
            lhs_fields.len(),
            rhs_fields.len()
        )));
    }

    // Build new local context with injected equalities
    let mut new_ctx = goal.local_ctx.clone();

    // Parse constructor type to get field types
    let mut ctor_ty = ctor_info.type_.clone();

    // Skip parameters (instantiate them with actual values from the term)
    for i in 0..num_params {
        if let ExprKind::Pi(_, _, codomain) = ctor_ty.kind() {
            if i < lhs_args.len() {
                ctor_ty = codomain.instantiate(lhs_args[i]);
            } else {
                ctor_ty = codomain.instantiate(&Expr::from_kind(ExprKind::Sort(Level::zero())));
                // placeholder
            }
        }
    }

    // Collect field types
    let mut field_types: Vec<Expr> = Vec::with_capacity(num_fields);
    for i in 0..num_fields {
        if let ExprKind::Pi(_, domain, codomain) = ctor_ty.clone().kind() {
            field_types.push(domain.as_ref().clone());
            // Instantiate with lhs field for proper typing
            if i < lhs_fields.len() {
                ctor_ty = codomain.instantiate(lhs_fields[i]);
            }
        }
    }

    // Create equality hypotheses for each field pair.
    // Part of #2232: also collect eq types for the noConfusion lambda chain.
    let mut eq_types: Vec<Expr> = Vec::with_capacity(num_fields);
    for i in 0..num_fields {
        let lhs_field = lhs_fields[i];
        let rhs_field = rhs_fields[i];

        // Get the type for this field
        let field_ty = if i < field_types.len() {
            field_types[i].clone()
        } else {
            // Infer the type if we couldn't get it from constructor
            state
                .infer_type(&goal, lhs_field)
                .unwrap_or_else(|_| eq_type.clone())
        };

        // Build equality type: lhs_field = rhs_field
        let eq_hyp_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), eq_levels.clone()),
                    field_ty,
                ),
                lhs_field.clone(),
            ),
            rhs_field.clone(),
        );
        eq_types.push(eq_hyp_ty.clone());

        // Create fresh fvar for this hypothesis
        let inj_fvar = state.fresh_fvar();
        let inj_name = format!(
            "{}_inj{}",
            hyp_name,
            if num_fields > 1 {
                format!("_{}", i + 1)
            } else {
                String::new()
            }
        );

        new_ctx.push(LocalDecl {
            fvar: inj_fvar,
            name: inj_name,
            ty: eq_hyp_ty,
            value: None,
        });
    }

    // Part of #2232: build noConfusion composite proof instead of bare meta.
    //
    // Previously the proof was just `?new_meta`, leaving the injected equality
    // hypotheses as phantom FVars unconnected to any injectivity principle.
    // Now we build:
    //   @T.noConfusion {P} {v1} {v2} h (λ h1 ... hk => ?new_meta)
    //
    // noConfusion type for same constructor: (a1=b1 -> ... -> ak=bk -> P) -> P
    // We provide the lambda that takes the field equalities and returns ?new_meta.
    let ind_name = &ctor_info.inductive_name;
    let no_confusion_name = Name::from_string(&format!("{ind_name}.noConfusion"));
    // @T.noConfusion.{motive, ind_levels} {goal.target} {lhs_whnf} {rhs_whnf} h
    let nc = mk_noconfusion_const(state, &goal, &no_confusion_name, lhs_head)?;
    let mut nc_app = nc;
    nc_app = Expr::app(nc_app, goal.target.clone()); // {P} = goal target
    nc_app = Expr::app(nc_app, lhs_whnf.clone()); // {v1}
    nc_app = Expr::app(nc_app, rhs_whnf.clone()); // {v2}
    nc_app = Expr::app(nc_app, Expr::fvar(hyp_decl.fvar)); // h : v1 = v2

    // Create fresh meta for the new goal (inside the lambda chain)
    let new_meta_id = state.fresh_meta_in_context(goal.target.clone(), &new_ctx);
    let new_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));

    // Build nested lambda: λ h1 : eq1. λ h2 : eq2. ... λ hk : eqk. ?new_meta
    // Built inside-out (last field first wraps outermost)
    let mut lambda_body = new_meta_expr;
    for eq_ty in eq_types.iter().rev() {
        lambda_body = Expr::lam(
            clean_kernel::BinderInfo::Default,
            eq_ty.clone(),
            lambda_body,
        );
    }

    // Composite proof: @T.noConfusion {P} {v1} {v2} h (λ h1...hk => ?new_meta)
    let proof = Expr::app(nc_app, lambda_body);

    // The continuation meta is created at the ambient goal target, so the
    // lambda-introduced field equalities do not appear in its type. That keeps
    // the final noConfusion application checkable through close_goal. (#2154)
    state.close_goal(&goal, proof)?;

    // Add the new goal with injected equalities in context
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: goal.target.clone(),
        local_ctx: new_ctx,
        tag: None,
    };
    state.goals.push_front(new_goal);

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
    match super::proof_term::assumption(state) {
        Ok(()) => {}
        Err(TacticError::HypothesisNotFound(_)) => {}
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
pub fn discriminate(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Check that the hypothesis is an equality
    let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
    let (_eq_type, lhs, rhs, _eq_levels) = match_equality(&hyp_ty).map_err(|_| {
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

    // Build proof using noConfusion:
    //   T.noConfusion.{u} : {P : Sort u} → {v1 v2 : T} → v1 = v2 → T.noConfusionType P v1 v2
    //
    // When v1 and v2 are different constructors, noConfusionType P v1 v2 reduces to P.
    // So: T.noConfusion {goal.target} {lhs} {rhs} h : goal.target
    //
    // Part of #2232: previously passed only 1 arg (h) instead of 4 ({P}, {v1}, {v2}, h).
    // Also had a broken fallback with an orphaned False meta.
    let ind_name = &lhs_ctor_info.inductive_name;
    let no_confusion_name = Name::from_string(&format!("{ind_name}.noConfusion"));

    // Explicit universe levels: [motive_level] ++ ind_levels. mk_const's fresh
    // Level::Param cannot be unified by the kernel's infer_type. Part of #2154.
    let nc = mk_noconfusion_const(state, &goal, &no_confusion_name, lhs_head)?;
    let mut proof = nc;
    proof = Expr::app(proof, goal.target.clone()); // {P} = goal target
    proof = Expr::app(proof, lhs_whnf.clone()); // {v1}
    proof = Expr::app(proof, rhs_whnf.clone()); // {v2}
    proof = Expr::app(proof, Expr::fvar(hyp_decl.fvar)); // h : v1 = v2

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
pub fn rcases(state: &mut ProofState, hyp_name: &str, max_depth: usize) -> TacticResult {
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
