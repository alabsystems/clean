// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic proof term tactics: exact, intro, apply, assumption, constructor, rfl.
//!
//! These are the fundamental tactics that directly manipulate proof terms.
//! See `proof_term_cert` for certified variants that generate proof certificates.

use crate::stack_safe;
use crate::unify::{MetaState, Unifier, UnifyResult};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, ExprVisitor, FVarId};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::equality;
use super::tauto::fresh_hyp_name_typed;

/// Whether `expr` mentions the free variable `fvar` (including meta-encoded
/// FVars). Used by `apply`'s dependent-goal partition (B102).
fn expr_mentions_fvar(expr: &Expr, fvar: FVarId) -> bool {
    struct FVarFinder {
        target: FVarId,
        found: bool,
    }
    impl ExprVisitor for FVarFinder {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            if id == self.target {
                self.found = true;
            }
        }
    }
    let mut finder = FVarFinder {
        target: fvar,
        found: false,
    };
    finder.visit_expr(expr);
    finder.found
}

// =============================================================================
// Basic proof term tactics
// =============================================================================

/// Close the goal with an exact proof term
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `proof` has a type that unifies with the current goal target
/// ENSURES: On Ok, the current goal is closed via `close_goal` with type-checked proof
/// ENSURES: On Err(TypeMismatch), proof type does not unify with goal target; state is unchanged
pub fn exact(state: &mut ProofState, proof: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the type of the proof
    let proof_ty = state.infer_type(&goal, &proof)?;

    // Check that the proof has the right type (via unification to handle metas)
    let target = state.metas.instantiate(&goal.target);
    let ctx = state.build_local_ctx(&goal);

    // Scope the unification borrow
    let unify_result = {
        let (metas, env) = state.metas_and_env();
        Unifier::with_env(metas, env, ctx)
            .with_protected_heads()
            .unify(&proof_ty, &target)
    };

    match unify_result {
        UnifyResult::Success => {
            // Part of #2154: type-check exact proof before accepting
            state.close_goal(&goal, proof)?;
            Ok(())
        }
        UnifyResult::Failure(msg) => Err(TacticError::TypeMismatch {
            expected: format!("{target}"),
            actual: msg,
        }),
        UnifyResult::Stuck => Err(TacticError::UnificationFailed(
            "unification stuck".to_string(),
        )),
    }
}

/// Introduce a hypothesis or a local definition.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Current goal target is a Pi/forall type or an explicit let.
/// ENSURES: On Ok, the current goal is replaced by a new goal with the domain added to local context
/// ENSURES: On Ok, the new goal target is the codomain instantiated with a fresh FVar
/// ENSURES: On Err(GoalMismatch), target has neither binder; state is unchanged
pub fn intro(state: &mut ProofState, name: &clean_parser::SurfaceName) -> TacticResult {
    enum IntroBinder {
        Forall(clean_kernel::BinderData),
        Let {
            name: Name,
            value: Expr,
            non_dep: bool,
        },
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    // An explicit let must be introduced before WHNF zeta-reduces its value,
    // including when outer metadata hides the binder. In particular, a reverted
    // definition is not an arbitrary hypothesis. Inspect through metadata without
    // changing the stored goal or its checked continuation.
    let original = state.metas.instantiate(&goal.target);
    let exposed = original.strip_mdata();
    let target = if matches!(exposed.kind(), ExprKind::Let(..)) {
        exposed.clone()
    } else {
        state.whnf(&goal, &original)
    };
    let (binder, domain, codomain) = match target.kind() {
        ExprKind::Pi(info, domain, body) => {
            (IntroBinder::Forall(*info), domain.clone(), body.clone())
        }
        ExprKind::Let(name, ty, value, body, non_dep) => (
            IntroBinder::Let {
                name: name.clone(),
                value: value.as_ref().clone(),
                non_dep: *non_dep,
            },
            ty.clone(),
            body.clone(),
        ),
        _ => {
            return Err(TacticError::GoalMismatch(
                "intro requires a forall/arrow or let goal".to_string(),
            ))
        }
    };

    let name = fresh_hyp_name_typed(&goal.local_ctx, name);

    // Create a free variable for the introduced hypothesis from THIS
    // goal's own tactic-binder base rather than the monotonic global
    // `next_fvar` counter (#2533). `close_fvars` maps a tactic FVar `n`
    // to a BVar only when `n` lands in `[fvar_base, fvar_base + depth)`,
    // so a goal's first `intro` must get id `fvar_base` and each further
    // intro the next slot up. `goal_fvar_base` computes exactly that from
    // the goal's context, so it is depth-correct for BOTH sibling goals
    // (a fresh `;`-sequenced sibling has no tactic FVars → base ==
    // `fvar_base`, identical to the first sibling) AND single-goal
    // multi-intro (`intro a; intro b`: after `a` the max is `base`, so
    // `b` gets `base + 1`). Using the global counter instead let an
    // earlier sibling's advanced `next_fvar` leak into the next sibling's
    // first `intro`, producing a too-high id that `close_fvars` could not
    // convert → fail-closed `ProofNotProduced`.
    // `goal_binder_base`, not `goal_fvar_base`: a goal whose context was
    // narrowed by `clear` keeps the removed local in its meta scope and
    // under a live `lambda`, so the context alone would hand back an id
    // that is still bound (capture). Identical to `goal_fvar_base`
    // wherever nothing has narrowed, so the sibling invariant below holds
    // unchanged.
    let base = state.goal_binder_base(&goal);
    let fvar = FVarId::new(base);

    // Keep the global counter monotonic past this allocation so unrelated
    // global `fresh_fvar` calls never collide with `fvar`, and so
    // `closed_proof`'s `close_fvars_validated(.., base, limit=next_fvar)`
    // scan range still covers this FVar's id.
    state.next_fvar = state.next_fvar.max(base + 1);

    // Create the new local declaration
    // Lean's `introN` head-betas the binder's type: a `∀`-bodied
    // predicate instantiated at its argument (`(fun h => p h) w`)
    // is introduced as `p w`. The lambda below keeps the domain as
    // written; the two are definitionally equal.
    let local_decl = LocalDecl {
        binder_info: match &binder {
            IntroBinder::Forall(info) => *info,
            IntroBinder::Let { .. } => Default::default(),
        },
        fvar,
        name: name.clone(),
        ty: super::op_projection::head_beta(&domain),
        value: match &binder {
            IntroBinder::Forall(_) => None,
            IntroBinder::Let { value, .. } => Some(value.clone()),
        },
    };

    // Create new context with the hypothesis
    let mut new_ctx = goal.local_ctx.clone();
    new_ctx.push(local_decl);

    // Instantiate the codomain with the free variable
    let new_target = codomain.instantiate(&Expr::fvar(fvar));

    // The visible target retains the defined local. The continuation meta's
    // declared type substitutes its genuine value, so it can also be checked
    // under the original goal's scope while the let proof is assembled.
    // These targets are definitionally equal in new_ctx; no context is widened.
    let meta_target = match &binder {
        IntroBinder::Forall(_) => new_target.clone(),
        IntroBinder::Let { value, .. } => codomain.instantiate(value),
    };
    let new_meta_id = state.fresh_meta_in_context(meta_target, &new_ctx);

    // Keep the same binder in the proof: a lambda for a hypothesis, a let for a definition.
    let new_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));
    let proof_body = new_meta_expr.abstract_fvar(fvar);
    let proof = match binder {
        IntroBinder::Forall(info) => Expr::lam(info, domain.as_ref().clone(), proof_body),
        IntroBinder::Let {
            name,
            value,
            non_dep,
        } => Expr::let_named(name, domain.as_ref().clone(), value, proof_body, non_dep),
    };

    // Part of #2154: type-check intro proof. The tactic-level
    // infer_type now fixes leaked FVars in Pi types via
    // fix_pi_leaked_fvars (#2197), so close_goal works here.
    state.close_goal(&goal, proof)?;

    // Add the new goal
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: new_ctx,
        case_binders: goal.case_binders.clone(),
        tag: goal.tag.clone(),
    };

    state.goals.push_front(new_goal);
    Ok(())
}

/// Introduce multiple hypotheses
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Current goal target has at least `names.len()` nested Pi/forall binders
/// ENSURES: On Ok, `names.len()` hypotheses are introduced sequentially via `intro`
/// ENSURES: On Err, partial introductions may have been applied (not transactional)
pub fn intros(state: &mut ProofState, names: Vec<clean_parser::SurfaceName>) -> TacticResult {
    for name in &names {
        intro(state, name)?;
    }
    Ok(())
}

/// Apply a function/theorem to the goal
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed with `func` applied to metavariable arguments
/// ENSURES: On Ok, unsolved argument metavariables become new goals
/// ENSURES: On Err(TypeMismatch), the function's result type cannot unify with the goal target
pub fn apply(state: &mut ProofState, func: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the type of the function
    let func_ty = state.infer_type(&goal, &func)?;

    // Collect the arguments needed and check if result matches target
    apply_aux_acc(state, &goal, func, func_ty, Vec::new())
}

pub(super) fn apply_aux(
    state: &mut ProofState,
    goal: &Goal,
    func: Expr,
    func_ty: Expr,
) -> TacticResult {
    apply_aux_acc(state, goal, func, func_ty, Vec::new())
}

/// Recursive worker for `apply` that threads an accumulator of the argument
/// metavariables created so far (one per Pi-argument consumed).
///
/// Each recursion frame consumes one Pi-argument, creating a fresh
/// metavariable `arg_meta_id` whose domain type it records in `arg_metas`.
/// When the running result type finally unifies with the goal target, EVERY
/// accumulated argument metavariable that is still unassigned becomes a new
/// goal — not just the last one. Implicit arguments that unification solved
/// stay assigned and are therefore skipped, matching Lean 4's behavior where
/// `apply f` leaves one subgoal per unsolved explicit premise.
fn apply_aux_acc(
    state: &mut ProofState,
    goal: &Goal,
    func: Expr,
    func_ty: Expr,
    // (metavariable id, its domain type at creation time) in argument order.
    mut arg_metas: Vec<(crate::unify::MetaId, Expr)>,
) -> TacticResult {
    stack_safe(|| {
        let func_ty = state.whnf(goal, &func_ty);
        let target = state.metas.instantiate(&goal.target);

        match func_ty.kind() {
            ExprKind::Pi(_bi, domain, codomain) => {
                // Create a metavariable for this argument
                let arg_meta_id = state.fresh_meta((**domain).clone());
                let arg_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(arg_meta_id)));

                // Record this argument metavariable (in argument order) so that,
                // once the result type unifies, we can turn EVERY unassigned
                // argument meta into a goal — not just the last one (#apply-multigoal).
                arg_metas.push((arg_meta_id, (**domain).clone()));

                // Apply the function to the metavariable
                let applied = Expr::app(func.clone(), arg_meta.clone());

                // Instantiate the codomain
                let new_ty = codomain.instantiate(&arg_meta);

                // Try to unify the result with the target
                let ctx = state.build_local_ctx(goal);
                let unify_result = {
                    let (metas, env) = state.metas_and_env();
                    Unifier::with_env(metas, env, ctx)
                        .with_protected_heads()
                        .unify(&new_ty, &target)
                };
                match unify_result {
                    UnifyResult::Success => {
                        // Part of #2154: type-check apply proof before accepting.
                        // close_goal pops the current (front) goal.
                        state.close_goal(goal, applied)?;

                        // Create a new goal for EVERY argument metavariable that
                        // unification did NOT solve, mirroring Lean 4's
                        // `ApplyNewGoals.nonDependentFirst` ordering (B102):
                        // an unassigned arg meta that OCCURS in another
                        // unassigned arg meta's domain — e.g. the middle
                        // `?m : Nat` of `Nat.le_trans`, appearing in both
                        // premise types `a ≤ ?m` / `?m ≤ c` — is a DEPENDENT
                        // goal and goes LAST, so `exact hab` meets `a ≤ ?m`
                        // (solving `?m` by unification) instead of a bare
                        // `⊢ Nat`. Once solved, `prune_solved_goals` (run after
                        // each successful tactic) drops the trailing goal,
                        // matching Lean's pruning of assigned mvars; an
                        // UNSOLVED dependent meta still surfaces as a loud
                        // trailing goal. Within each class, argument order is
                        // preserved (`apply And.intro` still yields `⊢ p`
                        // before `⊢ q`). We push to the front in reverse so
                        // `state.goals` reads front-to-back as
                        // [non-dependent..., dependent...].
                        let unassigned: Vec<(crate::unify::MetaId, Expr)> = arg_metas
                            .into_iter()
                            .filter(|(meta_id, _)| !state.metas.is_assigned(*meta_id))
                            .map(|(meta_id, domain)| (meta_id, state.metas.instantiate(&domain)))
                            .collect();
                        let is_dependent = |meta_id: crate::unify::MetaId| {
                            let meta_fvar = MetaState::to_fvar(meta_id);
                            unassigned.iter().any(|(other, domain)| {
                                *other != meta_id && expr_mentions_fvar(domain, meta_fvar)
                            })
                        };
                        let (non_dependent, dependent): (Vec<_>, Vec<_>) = unassigned
                            .iter()
                            .cloned()
                            .partition(|(meta_id, _)| !is_dependent(*meta_id));
                        for (meta_id, target) in non_dependent.into_iter().chain(dependent).rev() {
                            let new_goal = Goal {
                                meta_id,
                                target,
                                local_ctx: goal.local_ctx.clone(),
                                case_binders: goal.case_binders.clone(),
                                tag: goal.tag.clone(),
                            };
                            state.goals.push_front(new_goal);
                        }

                        Ok(())
                    }
                    UnifyResult::Failure(_) | UnifyResult::Stuck => {
                        // Try applying with more arguments
                        apply_aux_acc(state, goal, applied, new_ty, arg_metas)
                    }
                }
            }
            _ => {
                // Not a function type anymore, try direct unification
                let ctx = state.build_local_ctx(goal);
                let unify_result = {
                    let (metas, env) = state.metas_and_env();
                    Unifier::with_env(metas, env, ctx)
                        .with_protected_heads()
                        .unify(&func_ty, &target)
                };
                match unify_result {
                    UnifyResult::Success => {
                        // Part of #2154: type-check apply proof before accepting
                        state.close_goal(goal, func)?;
                        Ok(())
                    }
                    UnifyResult::Failure(msg) => Err(TacticError::TypeMismatch {
                        expected: format!("{target}"),
                        actual: msg,
                    }),
                    UnifyResult::Stuck => Err(TacticError::UnificationFailed(
                        "apply: unification stuck".to_string(),
                    )),
                }
            }
        }
    })
}

/// Use a hypothesis from the context
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the newest local matching exact's unification policy closes the checked goal
/// ENSURES: On Err(NoMatchingHypothesis), speculative assignments and goals are unchanged
pub fn assumption(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let target_has_metas = crate::tactic::pattern::contains_unassigned_meta(&target);

    // Search newest first, but a kernel-transparent match is only an
    // eligibility check. The selected local must also match exact's
    // elaborator transparency and protected-head policy. Otherwise a newer
    // irreducible local can hide an older usable hypothesis.
    for decl in goal.local_ctx.iter().rev() {
        let hyp_ty = state.metas.instantiate(&decl.ty);
        if !state.is_def_eq(&goal, &hyp_ty, &target)
            && !target_has_metas
            && !crate::tactic::pattern::contains_unassigned_meta(&hyp_ty)
        {
            continue;
        }
        let ctx = state.build_local_ctx(&goal);
        state.metas.push_scope();
        let unified = {
            let (metas, env) = state.metas_and_env();
            matches!(
                Unifier::with_env(metas, env, ctx)
                    .with_protected_heads()
                    .unify(&hyp_ty, &target),
                UnifyResult::Success
            )
        };
        if unified {
            // Keep the existing checked assignment boundary; no candidate
            // assignments survive if that final check rejects the proof.
            match state.close_goal(&goal, Expr::fvar(decl.fvar)) {
                Ok(()) => {
                    state.metas.commit();
                    return Ok(());
                }
                Err(error) => {
                    state.metas.pop_scope();
                    state.invalidate_tc_cache();
                    return Err(error);
                }
            }
        }
        state.metas.pop_scope();
        state.invalidate_tc_cache();
    }

    Err(crate::tactic::display::no_matching_hypothesis(
        state,
        "assumption",
    ))
}

/// Constructor tactic for inductive types
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Goal target head (after WHNF) is a const referring to an inductive type
/// ENSURES: On Ok, the first constructor of the inductive type is applied via `apply`
/// ENSURES: On Err(GoalMismatch), target head is not an inductive type; state is unchanged
pub fn constructor(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);

    // Get the head constant of the target
    let head = target.get_app_fn();

    match head.kind() {
        // `split_` already builds and checks the connective-specific proof
        // terms, so reuse it instead of the generic `apply` path here.
        ExprKind::Const(name, _)
            if *name == Name::from_string("And") || *name == Name::from_string("Iff") =>
        {
            super::connective::split_(state)
        }
        ExprKind::Const(name, levels) => {
            // Look up the inductive type
            if let Some(ind_info) = state.env.get_inductive(name) {
                // Get the first constructor
                if let Some(ctor_name) = ind_info.constructor_names.first() {
                    let ctor = Expr::const_(ctor_name.clone(), levels.clone());
                    return apply(state, ctor);
                }
            }
            Err(TacticError::GoalMismatch(format!(
                "not an inductive type: {name}"
            )))
        }
        _ => Err(TacticError::GoalMismatch(
            "goal is not an application of a constant".to_string(),
        )),
    }
}

/// Reflexivity tactic (for goals of the form a = a)
///
/// Tries `Eq.refl` first (kernel-verified def-eq), then falls back to
/// `reduce_eq` which produces explicit proof terms via WHNF reduction.
/// This handles cases where the sides are computationally equal but require
/// multiple reduction steps the kernel's `apply Eq.refl` path doesn't resolve.
pub fn rfl(state: &mut ProofState) -> TacticResult {
    // Extract universe levels from the goal's Eq constant when possible.
    // When match_equality fails, fall back to mk_const_str which creates fresh
    // universe metavars resolved during apply/unification.
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = state.metas.instantiate(&goal.target);

    // Lean's `rfl` closes ANY reflexive relation registered `@[refl]`, not
    // only `Eq`: `Iff.refl` and `HEq.refl` are the two the core library
    // registers, and Lean core itself relies on the first — every structure
    // field declared `f : ∀ a b, a < b ↔ … := by intros; rfl`
    // (`Preorder.lt_iff_le_not_ge`, `LinearOrder.min_def`, …) is discharged
    // by `rfl` on an `Iff`. Until 2026-09-10 Clean's `rfl` applied `Eq.refl`
    // to that goal and reported `rigid head/arity mismatch: Eq vs Iff`, so
    // `Pi.preorder`'s autoParam script failed one step after it started
    // running (measured on `Mathlib/Order/Basic.lean`). The goal head decides
    // the constant; `apply` still unifies both sides, so a non-reflexive
    // `p ↔ q` fails here exactly as `Eq.refl` fails on `a = b`.
    if let ExprKind::Const(head, _) = target.get_app_fn().kind() {
        // Both spellings: the builtin prelude carries `Iff.rfl` but not
        // `Iff.refl`; a real `Init` import carries both.
        let refl_for: &[&str] = match head.to_string().as_str() {
            "Iff" => &["Iff.refl", "Iff.rfl"],
            "HEq" => &["HEq.refl", "HEq.rfl"],
            _ => &[],
        };
        if !refl_for.is_empty() {
            for candidate in refl_for {
                if state.env.get_const(&Name::from_string(candidate)).is_some() {
                    let refl = state.mk_const_str(candidate);
                    return apply(state, refl);
                }
            }
            return Err(TacticError::EnvironmentMissing {
                constant: refl_for[0].to_string(),
            });
        }
    }
    let extracted_levels = equality::match_equality(&target)
        .map(|(_ty, _lhs, _rhs, lvls)| lvls)
        .ok();

    // Look for Eq.refl or rfl in the environment
    let eq_refl = Name::from_string("Eq.refl");
    if state.env.get_const(&eq_refl).is_some() {
        let refl = match extracted_levels {
            Some(ref lvls) => Expr::const_(eq_refl, lvls.clone()),
            None => state.mk_const_str("Eq.refl"),
        };
        if apply(state, refl).is_ok() {
            return Ok(());
        }
        // Eq.refl failed (sides not syntactically def-eq) — try reduce_eq
        // which produces an explicit proof term via WHNF reduction. Part of #685.
        if reduce_eq(state).is_ok() {
            return Ok(());
        }
    }

    // Try rfl
    let rfl_name = Name::from_string("rfl");
    if state.env.get_const(&rfl_name).is_some() {
        let refl = match extracted_levels {
            Some(lvls) => Expr::const_(rfl_name, lvls),
            None => state.mk_const_str("rfl"),
        };
        return apply(state, refl);
    }

    Err(TacticError::EnvironmentMissing {
        constant: "rfl".to_string(),
    })
}

/// Prove an equality goal `a = b` by reducing both sides via WHNF.
///
/// Unlike `rfl` (which requires the kernel to verify definitional equality
/// internally), `reduce_eq` produces an explicit proof term that witnesses
/// each reduction step. This is useful when:
/// - The equality requires multiple reduction steps (delta + iota + beta)
/// - An explicit proof term is needed for self-verification
/// - `rfl` fails but both sides reduce to the same normal form
///
/// Part of #685.
pub fn reduce_eq(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    let (alpha, lhs, rhs, levels) = equality::match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("reduce_eq: goal is not an equality".into()))?;

    // Extract universe level from Eq's level parameters
    let u = levels
        .first()
        .cloned()
        .unwrap_or_else(|| Level::param(Name::from_string("u")));

    match state.prove_eq_by_reduction(&goal, &alpha, &lhs, &rhs, u) {
        Some(proof) => {
            state.close_goal(&goal, proof)?;
            Ok(())
        }
        None => Err(TacticError::no_progress("reduce_eq")),
    }
}
