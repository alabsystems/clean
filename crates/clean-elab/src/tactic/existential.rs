// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Existential and case analysis tactics: existsi, by_cases.
//!
//! These tactics work with existential quantifiers and classical case analysis.

use crate::unify::{MetaState, Unifier, UnifyResult};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::simp::beta_reduce;

/// The `existsi` tactic provides a witness for an existential goal.
///
/// For a goal `∃ x : α, P x`, `existsi w` reduces the goal to `P w`.
///
/// # Example
/// ```text
/// Goal: ∃ x : Nat, x > 0
/// existsi 1
/// Goal: 1 > 0
/// ```
///
/// The proof term is `Exists.intro {α} {P} w <proof of P w>`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Current goal target WHNF-reduces to `Exists {α} p`
/// REQUIRES: `Exists.intro` exists in the environment
/// REQUIRES: `witness` has type `α` (checked via `is_def_eq`)
/// ENSURES: On Ok, original goal closed with `Exists.intro` proof
/// ENSURES: On Ok, new goal `P witness` pushed (beta-reduced)
/// ENSURES: On Err(TypeMismatch), witness type does not match `α`
pub fn existsi(state: &mut ProofState, witness: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Check that Exists.intro exists
    let exists_intro_name = Name::from_string("Exists.intro");
    if state.env.get_const(&exists_intro_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Exists.intro".to_string(),
        });
    }

    // WHNF to expose the Exists application
    let target = state.whnf(&goal, &goal.target);

    // Parse Exists {α} p
    // Exists : {α : Sort u} → (α → Prop) → Prop
    let (alpha, pred) = match_exists(&target).ok_or_else(|| {
        TacticError::GoalMismatch(format!(
            "existsi: goal '{}' is not of the form '∃ x, P x'",
            crate::error_render::term(&target)
        ))
    })?;

    // Infer the type of the witness
    let witness_ty = state.infer_type(&goal, &witness)?;

    // Check that the witness has the right type (α)
    if !state.is_def_eq(&goal, &witness_ty, &alpha) {
        return Err(TacticError::TypeMismatch {
            expected: format!("{alpha}"),
            actual: format!("{witness_ty}"),
        });
    }

    // The new goal is: P witness (beta-reduced)
    // Without reduction, (λ x => x = 0) 0 would remain unreduced
    let new_target_unreduced = Expr::app(pred.clone(), witness.clone());
    let new_target = beta_reduce(&new_target_unreduced);
    let new_meta_id = state.fresh_meta(new_target.clone());

    // Infer universe level for α
    let alpha_ty = state.infer_type(&goal, &alpha)?;
    let level = match alpha_ty.kind() {
        ExprKind::Sort(l) => l.clone(),
        _ => Level::zero(), // Fallback
    };

    // The proof is: Exists.intro {α} {p} witness <new_meta>
    // Exists.intro : {α : Sort u} → {p : α → Prop} → (w : α) → p w → Exists p
    let exists_intro = Expr::const_(exists_intro_name, vec![level.clone()]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(exists_intro, alpha.clone()), pred.clone()),
            witness,
        ),
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id))),
    );

    // Solve any unassigned universe level metavariable left in the goal target
    // before closing. When the binder type is elided (`∃ n, p n`), elaboration
    // can leave the goal as `Exists.{?u} Nat pred` with `?u` an *unsolved* level
    // metavariable (a residual `Level::Param` head, e.g. `u_0`). The proof we
    // build above inhabits `Exists.{level} α pred` with `level` the *concrete*
    // level of `α` (e.g. `Succ Zero` for `Nat`). `close_goal` only runs the
    // kernel's read-only `is_def_eq`, which cannot *assign* `?u`, so the close —
    // and the later certificate check — fail on `Sort(?u)` vs `Sort(Succ Zero)`.
    //
    // Running the full unifier (which commits level constraints, unlike
    // `is_def_eq`) between the proof's result type `Exists.{level} α pred` and
    // the goal target drives `?u := level`, exactly as `exact` does for its
    // proof term. The constraint is recorded in the level union-find but is NOT
    // reflected by `instantiate` (which substitutes expr metavars only); we must
    // therefore apply `instantiate_levels` to the target/subgoal types below so
    // the now-solved `?u` is realized before `close_goal` re-checks def-eq.
    //
    // This only *solves* a level metavariable the goal already carries; the
    // resulting proof is still kernel-rechecked by `close_goal` and by
    // `add_decl`, so a wrong commitment fails downstream rather than slipping
    // through. Best-effort: a failed unify leaves the state untouched and we
    // fall through to the original `close_goal` (which then surfaces the real
    // mismatch).
    //
    // Exists.{level} α pred — the proposition the assembled proof inhabits.
    let result_ty = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![level]),
            alpha,
        ),
        pred,
    );
    {
        let target_inst = state.metas.instantiate(&goal.target);
        let ctx = state.build_local_ctx(&goal);
        let (metas, env) = state.metas_and_env();
        // Ignore the outcome: success commits the level constraint; failure
        // leaves the state unchanged for `close_goal` to report.
        let _: UnifyResult = Unifier::with_env(metas, env, ctx).unify(&result_ty, &target_inst);
    }

    // Realize any level constraint solved above into the goal target and the
    // pushed sub-goal target, so the proof's concrete levels match.
    let solved_target = state.metas.instantiate_levels(&goal.target);
    let solved_new_target = state.metas.instantiate_levels(&new_target);
    let goal_for_close = Goal {
        meta_id: goal.meta_id,
        target: solved_target,
        local_ctx: goal.local_ctx.clone(),
        case_binders: goal.case_binders.clone(),
        tag: goal.tag.clone(),
    };

    // Close the current goal — structural Exists.intro with meta sub-goal
    state.close_goal(&goal_for_close, proof)?;

    // Add the new goal
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: solved_new_target,
        local_ctx: goal.local_ctx.clone(),
        case_binders: goal.case_binders.clone(),
        tag: None,
    };
    state.goals.push_front(new_goal);

    Ok(())
}

/// Match an expression of the form `Exists {α} p` and extract α and p.
pub(crate) fn match_exists(expr: &Expr) -> Option<(Expr, Expr)> {
    // Exists {α} p is App(App(Const("Exists", _), α), p)
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    match head.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Exists" => {
            if args.len() == 2 {
                Some((args[0].clone(), args[1].clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The `by_cases` tactic performs case analysis on a decidable proposition.
///
/// For a goal `G` and a decidable proposition `P`, `by_cases h : P` creates two goals:
/// 1. `G` with hypothesis `h : P`
/// 2. `G` with hypothesis `h : ¬P`
///
/// A dependent conditional uses the decision available under `open Classical`.
///
/// # Example
/// ```text
/// Goal: Q
/// by_cases h : P
/// -- Case 1:
/// h : P
/// Goal: Q
/// -- Case 2:
/// h : ¬P
/// Goal: Q
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: a decision and `dite`, or the classical Prop eliminator in a partial prelude
/// REQUIRES: `prop` is Prop-valued (checked via `is_def_eq` with `Prop`)
/// ENSURES: On Ok, the selected eliminator connects the original goal to both branches
/// ENSURES: On Ok, two new goals pushed: positive (`h : P`) first, negative (`h : ¬P`) second
/// ENSURES: On Err(TypeMismatch), `prop` is not Prop-valued; state unchanged
pub fn by_cases(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
    prop: Expr,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Verify prop is a Prop
    let prop_ty = state.infer_type(&goal, &prop)?;
    let prop_sort = Expr::prop();
    if !state.is_def_eq(&goal, &prop_ty, &prop_sort) {
        return Err(TacticError::TypeMismatch {
            expected: "Prop".to_string(),
            actual: format!("{prop_ty}"),
        });
    }

    // `¬P`, spelled with the `Not` head as Lean's `by_cases` states it — not
    // the unfolded `P → False`. simp reads a negation off the `Not` head
    // only (`P = False`); a local `P → False` is the CONDITIONAL rule
    // `P → (False = True)`, so the arrow spelling left `by_cases h : P <;>
    // simp [h]` unable to decide `P` in the negative branch.
    let not_name = Name::from_string("Not");
    if state.env.get_const(&not_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Not".to_string(),
        });
    }
    let neg_prop = Expr::app(Expr::const_(not_name, vec![]), prop.clone());

    let (eliminator, major) = by_cases_eliminator(state, &goal, &prop, &neg_prop)?;

    // Fresh fvar for the hypothesis `h`. The positive and negative branches are
    // PARALLEL binders — each is its own `λ h => …` lambda directly under
    // the eliminator, both at the same binder depth. `close_fvars` (core/close_fvars.rs)
    // closes a tactic FVar `n` to a BVar only when `(n - base) < depth`, i.e. it
    // assumes FVar ids grow with binder *nesting* depth. Two distinct fvars for
    // the two branches would violate that: the second fvar would sit at offset 1
    // while its branch is only at depth 1, so it would never be closed (residual
    // FVar → close_fvars debug_assert panic). Because the branches are disjoint
    // scopes (a goal is solved before the next), both `h` binders can safely
    // share ONE fvar id; each branch body then references offset 0 at depth 1 and
    // closes cleanly. The assembled term is still kernel-rechecked by add_decl.
    // GOAL-DERIVED minting (the intro pattern, proof_term.rs): the scope
    // checker derives its binder base from the destination meta's captured
    // scope, so a cursor-minted id drifts out of the checked window whenever
    // ANYTHING minted between two splits (measured: sequential surface
    // `by_cases` steps with tauto in between — the second split's hypothesis
    // landed at id 8 where the checker expected 4). Minting from the goal's
    // own binder base is drift-immune by construction.
    let base = state.goal_binder_base(&goal);
    let fvar_h = FVarId::new(base);
    state.next_fvar = state.next_fvar.max(base + 1);
    let fvar_pos = fvar_h;
    let fvar_neg = fvar_h;

    // Context for positive case: h : P
    let mut ctx_pos = goal.local_ctx.clone();
    ctx_pos.push(LocalDecl {
        binder_info: Default::default(),
        fvar: fvar_pos,
        name: hyp_name.clone(),
        ty: prop.clone(),
        value: None,
    });

    // Context for negative case: h : ¬P
    let mut ctx_neg = goal.local_ctx.clone();
    ctx_neg.push(LocalDecl {
        binder_info: Default::default(),
        fvar: fvar_neg,
        name: hyp_name.clone(),
        ty: neg_prop.clone(),
        value: None,
    });

    // Create metavariables for the two cases
    let meta_pos = state.fresh_meta_in_context(goal.target.clone(), &ctx_pos);
    let meta_neg = state.fresh_meta_in_context(goal.target.clone(), &ctx_neg);

    let branch_pos = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(meta_pos))).abstract_fvar(fvar_pos),
    );

    let branch_neg = Expr::lam(
        BinderInfo::Default,
        neg_prop.clone(),
        Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(meta_neg))).abstract_fvar(fvar_neg),
    );

    let mut proof = Expr::apps(eliminator, [branch_pos, branch_neg]);
    if let Some(major) = major {
        proof = Expr::app(proof, major);
    }
    state.close_goal(&goal, proof)?;

    // Add the two new goals (positive case first)
    let goal_pos = Goal {
        meta_id: meta_pos,
        target: goal.target.clone(),
        local_ctx: ctx_pos,
        case_binders: goal.case_binders.clone(),
        tag: None,
    };
    let goal_neg = Goal {
        meta_id: meta_neg,
        target: goal.target,
        local_ctx: ctx_neg,
        case_binders: goal.case_binders.clone(),
        tag: None,
    };

    state.goals.push_front(goal_neg);
    state.goals.push_front(goal_pos);

    Ok(())
}

/// The eliminator ready for its two branch functions. Only `Or.rec` takes a
/// trailing major premise. Choose it before allocating either branch goal.
fn by_cases_eliminator(
    state: &ProofState,
    goal: &Goal,
    prop: &Expr,
    neg_prop: &Expr,
) -> Result<(Expr, Option<Expr>), TacticError> {
    let dite = Name::from_string("dite");
    let target_ty = state.infer_type(goal, &goal.target)?;
    let sort = state.whnf(goal, &target_ty);
    let ExprKind::Sort(level) = sort.strip_mdata().kind() else {
        return Err(TacticError::TypeCheckFailed(
            "by_cases target must be a type".into(),
        ));
    };
    if state.env.get_const(&dite).is_some() {
        let class_ty = Expr::app(
            Expr::const_(Name::from_string("Decidable"), vec![]),
            prop.clone(),
        );
        if let Some(instance) =
            state.synthesize_class_in_goal(goal, &class_ty, Some(&Name::from_string("Classical")))
        {
            let elim = Expr::apps(
                Expr::const_(dite, vec![level.clone()]),
                [goal.target.clone(), prop.clone(), instance],
            );
            return Ok((elim, None));
        }
        // The full prelude supplies this scoped instance. Honor a failed
        // search (including instance erasure) rather than overriding it with em.
        if !level.is_zero()
            || state
                .env
                .get_const(&Name::from_string("Classical.propDecidable"))
                .is_some()
        {
            return Err(TacticError::InstanceSynthesisFailed {
                class: "Decidable".into(),
                ty: crate::error_render::term(prop),
            });
        }
    }
    // Clean's partial classical prelude can supply excluded middle without
    // a scoped classical decision. Its Or recursor eliminates only into Prop.
    if !level.is_zero() {
        return Err(TacticError::EnvironmentMissing {
            constant: "dite".into(),
        });
    }
    for name in ["Classical.em", "Or.rec"] {
        if state.env.get_const(&Name::from_string(name)).is_none() {
            return Err(TacticError::EnvironmentMissing {
                constant: name.into(),
            });
        }
    }
    let disjunction = Expr::apps(
        Expr::const_(Name::from_string("Or"), vec![]),
        [prop.clone(), neg_prop.clone()],
    );
    let motive = Expr::lam(BinderInfo::Default, disjunction, goal.target.clone());
    let elim = Expr::apps(
        Expr::const_(Name::from_string("Or.rec"), vec![]),
        [prop.clone(), neg_prop.clone(), motive],
    );
    let em = Expr::app(
        Expr::const_(Name::from_string("Classical.em"), vec![]),
        prop.clone(),
    );
    Ok((elim, Some(em)))
}

/// The `classical` tactic makes classical reasoning available for the remainder
/// of the tactic block. It never changes the goal — it only enriches what is
/// derivable — so on success it leaves every goal untouched.
///
/// The surface tactic bridge scopes classical instance synthesis to the tactic
/// block. This primitive validates the classical foundation and leaves all
/// goals available to the following tactics.
/// # Contract
///
/// - REQUIRES: the classical foundation (`Classical.em`) is present in the
///   environment — otherwise classical reasoning cannot be made available and we
///   fail loudly with `EnvironmentMissing` rather than a vacuous success.
/// - ENSURES: on `Ok`, the goal list is unchanged (no goal closed or split).
/// - SOUNDNESS: this is a structural no-op — it introduces no proof term — so it
///   cannot affect the kernel-rechecked assembled proof. The final term produced
///   by the rest of the block is still verified by `add_decl`.
pub fn classical(state: &mut ProofState) -> TacticResult {
    // `classical` is legal even with no open goals (Lean permits it), but the
    // classical foundation it advertises must actually exist.
    let em_name = Name::from_string("Classical.em");
    if state.env.get_const(&em_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Classical.em".to_string(),
        });
    }
    // Goal(s) unchanged: classical only widens what is derivable.
    Ok(())
}
