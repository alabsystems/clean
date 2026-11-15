// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Substitution tactics: subst, subst_vars.
//!
//! These tactics eliminate equality hypotheses by substituting free variables.
//! Split from structural.rs for file size (#307).

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, Name};

use super::super::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::expr_utils::match_equality;
use crate::unify::MetaState;

/// Which side of `h : lhs = rhs` is the local being eliminated.
///
/// Lean's `substEq` (`Lean/Meta/Tactic/Subst.lean`) eliminates the RIGHT side
/// when it is a local variable and the left side otherwise; the direction is
/// observable (it decides which name survives), so it is mirrored exactly.
struct SubstPlan {
    /// The local variable being eliminated.
    var_id: FVarId,
    /// The other side of the equation — what `var_id` is replaced by.
    replacement: Expr,
    /// `h : replacement = var` (Lean `symm := true`) when `true`;
    /// `h : var = replacement` (`symm := false`) when `false`.
    var_is_rhs: bool,
    hyp_fvar: FVarId,
    /// `α` in `@Eq α lhs rhs`.
    eq_type: Expr,
    /// `u` in `@Eq.{u}`.
    eq_level_u: Level,
}

/// Whether `id` occurs free in `expr` (a specific-FVar occurrence check).
fn fvar_occurs_in(expr: &Expr, id: FVarId) -> bool {
    match expr.kind() {
        ExprKind::FVar(fid) => *fid == id,
        ExprKind::App(f, a) => fvar_occurs_in(f, id) || fvar_occurs_in(a, id),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            fvar_occurs_in(ty, id) || fvar_occurs_in(body, id)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            fvar_occurs_in(ty, id) || fvar_occurs_in(val, id) || fvar_occurs_in(body, id)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            fvar_occurs_in(inner, id)
        }
        _ => false,
    }
}

fn is_context_fvar(goal: &Goal, e: &Expr) -> Option<FVarId> {
    match e.kind() {
        ExprKind::FVar(id) if goal.local_ctx.iter().any(|d| d.fvar == *id) => Some(*id),
        _ => None,
    }
}

/// Choose the eliminated side the way Lean's `substEq` does: the RHS when it
/// is a local, else the LHS.
///
/// `forced` names the local to eliminate instead (it must be one side of the
/// equation): `cases`' equation unification picks the LATER-declared of two
/// locals, as Lean's `unifyEq?` does (`substEq (aDecl.index < bDecl.index)`).
fn plan_subst(
    goal: &Goal,
    hyp_fvar: FVarId,
    eq_type: Expr,
    eq_level_u: Level,
    lhs: &Expr,
    rhs: &Expr,
    forced: Option<FVarId>,
) -> Result<SubstPlan, TacticError> {
    let rhs_var = is_context_fvar(goal, rhs).filter(|r| forced.is_none_or(|f| f == *r));
    let lhs_var = is_context_fvar(goal, lhs).filter(|l| forced.is_none_or(|f| f == *l));
    let (var_id, replacement, var_is_rhs) = if let Some(r) = rhs_var {
        (r, lhs.clone(), true)
    } else if let Some(l) = lhs_var {
        (l, rhs.clone(), false)
    } else if forced.is_some() {
        return Err(TacticError::GoalMismatch(
            "subst: the variable to eliminate is not a side of the equality".to_string(),
        ));
    } else {
        return Err(TacticError::GoalMismatch(
            "subst: neither side of the equality is a free variable in the context".to_string(),
        ));
    };
    if fvar_occurs_in(&replacement, var_id) {
        return Err(TacticError::GoalMismatch(format!(
            "subst: the variable occurs in the other side of the equation: {}",
            crate::error_render::term(&replacement)
        )));
    }
    Ok(SubstPlan {
        var_id,
        replacement,
        var_is_rhs,
        hyp_fvar,
        eq_type,
        eq_level_u,
    })
}

/// The locals (other than the variable and the equation) whose TYPE depends —
/// transitively — on the eliminated variable or on the equation itself, in
/// context order. Lean's `substCore` reverts exactly these (`revert #[a, h]`
/// with `preserveOrder`) and re-introduces them after the `Eq.rec`; keeping
/// them in place would leave their kernel-visible types un-rewritten while the
/// new goal claims the substituted ones.
///
/// A local carrying a VALUE (a tactic `have`, which Clean records let-style)
/// is reverted as a plain binder and comes back value-less — exactly what a
/// Lean `have` is (opaque), and what `hfunext`'s `have this : β = β' := …;
/// subst this` needs when the FIRST `this` mentions a dependent
/// (`Mathlib/Logic/Function/Basic.lean`, measured 2026-09-11). Only the
/// local's type decides dependency: its value is not part of the goal's
/// kernel term.
fn dependent_locals(goal: &Goal, plan: &SubstPlan) -> Vec<LocalDecl> {
    let mut deps: Vec<LocalDecl> = Vec::new();
    for d in &goal.local_ctx {
        if d.fvar == plan.var_id || d.fvar == plan.hyp_fvar {
            continue;
        }
        let mentions = fvar_occurs_in(&d.ty, plan.var_id)
            || fvar_occurs_in(&d.ty, plan.hyp_fvar)
            || deps.iter().any(|dep| fvar_occurs_in(&d.ty, dep.fvar));
        if mentions {
            deps.push(LocalDecl {
                value: None,
                ..d.clone()
            });
        }
    }
    deps
}

/// `@Eq.{u} α a b`.
fn mk_eq(plan: &SubstPlan, a: &Expr, b: &Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![plan.eq_level_u.clone()]);
    Expr::app(
        Expr::app(Expr::app(eq, plan.eq_type.clone()), a.clone()),
        b.clone(),
    )
}

/// `@Eq.symm.{u} α a b h : b = a`.
fn mk_eq_symm(plan: &SubstPlan, a: &Expr, b: &Expr, h: Expr) -> Expr {
    let symm = Expr::const_(Name::from_string("Eq.symm"), vec![plan.eq_level_u.clone()]);
    let symm = Expr::app(symm, plan.eq_type.clone());
    let symm = Expr::app(symm, a.clone());
    let symm = Expr::app(symm, b.clone());
    Expr::app(symm, h)
}

/// `@Eq.refl.{u} α a`.
fn mk_eq_refl(plan: &SubstPlan, a: &Expr) -> Expr {
    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![plan.eq_level_u.clone()]);
    Expr::app(Expr::app(refl, plan.eq_type.clone()), a.clone())
}

/// The type of the goal left after the substitution:
/// `reverted[x := e, h := Eq.refl e]` (Lean's `newType` in `substCore`).
fn new_goal_type(plan: &SubstPlan, reverted: &Expr) -> Expr {
    reverted
        .subst_fvar(plan.var_id, &plan.replacement)
        .subst_fvar(plan.hyp_fvar, &mk_eq_refl(plan, &plan.replacement))
}

/// The eliminator application closing the goal `reverted` (the target with
/// every dependent local reverted into a `Π`) with `minor` as the new goal.
///
/// Port of the motive construction in Lean's `substCore`:
///
/// * `h : e = x` (the variable on the right, `symm := true`): major is `h`,
///   motive `fun z hz => reverted[x := z, h := hz]`;
/// * `h : x = e` (`symm := false`): major is `Eq.symm h : e = x`, and the
///   motive is `fun z hAux => reverted[x := z, h := Eq.symm hAux]` — `h` and
///   `Eq.symm hAux` are proofs of the same `Prop`, so the motive is type
///   correct by proof irrelevance while a bare `hz` in `h`'s place would not
///   be (it proves `z = e`, not `e = z`).
///
/// When the reverted target does not mention `h` at all, the motive drops the
/// equation and `Eq.ndrec` is used, exactly as Lean does.
fn build_elim(plan: &SubstPlan, reverted: &Expr, motive_level: Level, minor: Expr) -> Expr {
    let x = Expr::fvar(plan.var_id);
    let h = Expr::fvar(plan.hyp_fvar);
    let e = &plan.replacement;
    let dep_elim = fvar_occurs_in(reverted, plan.hyp_fvar);

    let major = if plan.var_is_rhs {
        h.clone()
    } else {
        mk_eq_symm(plan, &x, e, h.clone())
    };
    let (rec_name, motive) = if dep_elim {
        // `hAux : e = x` stands in for the abstracted equation; in the
        // `symm := false` case it is wrapped in `Eq.symm` where `h` occurred.
        let body = if plan.var_is_rhs {
            reverted.clone()
        } else {
            reverted.subst_fvar(plan.hyp_fvar, &mk_eq_symm(plan, e, &x, h.clone()))
        };
        let inner = Expr::lam(
            BinderInfo::Default,
            mk_eq(plan, e, &x),
            body.abstract_fvar(plan.hyp_fvar),
        );
        (
            "Eq.rec",
            Expr::lam(
                BinderInfo::Default,
                plan.eq_type.clone(),
                inner.abstract_fvar(plan.var_id),
            ),
        )
    } else {
        (
            "Eq.ndrec",
            Expr::lam(
                BinderInfo::Default,
                plan.eq_type.clone(),
                reverted.abstract_fvar(plan.var_id),
            ),
        )
    };

    let mut proof = Expr::const_(
        Name::from_string(rec_name),
        vec![motive_level, plan.eq_level_u.clone()],
    );
    proof = Expr::app(proof, plan.eq_type.clone());
    proof = Expr::app(proof, e.clone());
    proof = Expr::app(proof, motive);
    proof = Expr::app(proof, minor);
    proof = Expr::app(proof, x);
    Expr::app(proof, major)
}

/// The `subst` tactic substitutes an equality hypothesis into the goal and context.
///
/// Given a hypothesis `h : x = e` where `x` is a free variable, this tactic:
/// 1. Replaces all occurrences of `x` with `e` in the goal
/// 2. Replaces all occurrences of `x` with `e` in other hypotheses
/// 3. Removes the hypothesis `h` from the context
/// 4. Removes `x` from the context (since it's been substituted away)
///
/// The equation can point either way; as in Lean, the RIGHT side is the one
/// eliminated when it is a local variable (`h : e = x` replaces `x` by `e`),
/// and the left side otherwise (`h : x = e`).
///
/// Port of Lean's `substCore` (`Lean/Meta/Tactic/Subst.lean`): every local
/// whose type depends on `x` or on `h` is reverted into the target, the goal
/// is closed with `Eq.rec`/`Eq.ndrec` over a motive that abstracts `x` — and
/// `h` too when the target mentions it, which is what a `cases h`/`subst h`
/// on `h : α = β` under `cast h a`, `Eq.mp h` or `h ▸ x` needs — and the
/// reverted locals are re-introduced with their substituted types. Measured
/// on `Mathlib/Logic/Basic.lean` (`cast_heq_iff_heq`, `heq_cast_iff_heq`),
/// `Mathlib/Logic/Function/Basic.lean` (`eq_mp_bijective`,
/// `eq_mpr_bijective`, `cast_bijective`, `hfunext`) and
/// `Mathlib/Logic/Unique.lean` (`Unique.subtypeEq'`), 2026-09-11: the old
/// non-dependent motive kept `h : α = β` in a goal about `cast h a` at
/// `α = α`, failing the kernel check with `expected α = β, got α = ?z`.
///
/// # Errors
/// - `HypothesisNotFound` if the hypothesis doesn't exist
/// - `GoalMismatch` if the hypothesis is not an equality, if neither side is a
///   context variable, or if the variable occurs in the other side
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names an equality hypothesis in the local context
/// REQUIRES: One side of the equality is an FVar present in the local context
/// ENSURES: On Ok, original goal closed with an `Eq.rec`/`Eq.ndrec` proof (type-checked)
/// ENSURES: On Ok, new goal has `x` and `h` removed from context, `x` replaced by `e`
/// ENSURES: On Ok, every dependent hypothesis is re-introduced with the substituted type
/// ENSURES: On Err(GoalMismatch), state unchanged
pub fn subst(state: &mut ProofState, hyp_name: &clean_parser::SurfaceName) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // The MOST RECENT local of that name, as Lean resolves a shadowed name
    // (`have this : … ; have this : β = β' := …; subst this` in
    // `Function.hfunext` names the second `this`).
    let hyp_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();
    subst_decl(state, goal, &hyp_decl, None)
}

/// [`subst`] on the equation local `hyp_fvar`, eliminating exactly the local
/// `var` (one side of the equation) — the step `cases`' equation unification
/// (`crate::tactic::cases_unify_eqs`) takes, where Lean's `unifyEq?` chooses
/// the side itself.
///
/// ENSURES: what [`subst`] ensures, with `var` the eliminated local.
pub(crate) fn subst_eliminating(
    state: &mut ProofState,
    hyp_fvar: FVarId,
    var: FVarId,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.fvar == hyp_fvar)
        .ok_or_else(|| TacticError::HypothesisNotFound(format!("{hyp_fvar:?}")))?
        .clone();
    subst_decl(state, goal, &hyp_decl, Some(var))
}

fn subst_decl(
    state: &mut ProofState,
    goal: Goal,
    hyp_decl: &LocalDecl,
    forced: Option<FVarId>,
) -> TacticResult {
    let hyp_name = &hyp_decl.name;
    let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
    let (hyp_decl, eq_type, lhs, rhs, eq_levels, eliminate) = match match_equality(&hyp_ty) {
        Ok((eq_type, lhs, rhs, levels)) => (hyp_decl.clone(), eq_type, lhs, rhs, levels, None),
        // Lean's `subst x` with `x` a variable (`substVar`): the OLDEST
        // equation `x = e` or `e = x` whose other side does not mention `x`
        // eliminates `x` (block 13 of trust-ir's `PredLatticeProps.lean`:
        // `subst q` after `have hpq : p = q`).
        Err(_) => {
            let (eq_decl, eq_type, lhs, rhs, levels) =
                equation_for_variable(state, &goal, hyp_decl.fvar).ok_or_else(|| {
                    TacticError::GoalMismatch(format!(
                        "subst: {hyp_name} is not an equality, and no equation eliminates it \
                         (did not find equation for eliminating '{hyp_name}')"
                    ))
                })?;
            (eq_decl, eq_type, lhs, rhs, levels, Some(hyp_decl.fvar))
        }
    };
    let eq_level_u = eq_levels.into_iter().next().unwrap_or(Level::zero());
    let plan = plan_subst(
        &goal,
        hyp_decl.fvar,
        eq_type,
        eq_level_u,
        &lhs,
        &rhs,
        // `cases`' unification forces a side; `subst x` (lane B) names it.
        forced.or(eliminate),
    )?;
    let deps = dependent_locals(&goal, &plan);
    // Lean's `substCore` reverts the variable, the equation and these
    // dependents together, so a replacement that names a dependent cannot be
    // put back under them: "failed to create binder due to failure when
    // reverting variable dependencies" (pinned 4.8.0 and 4.30.0-rc2). Keeping
    // the dependent in place left the new goal naming a local it no longer
    // has (review r6, X5: `h : x = f y` with `y : Fin (x+1)`).
    if let Some(dep) = deps
        .iter()
        .find(|d| fvar_occurs_in(&plan.replacement, d.fvar))
    {
        return Err(TacticError::GoalMismatch(format!(
            "subst: failed to create binder due to failure when reverting variable \
             dependencies: '{}' depends on the eliminated variable and occurs in {}",
            dep.name,
            crate::error_render::term(&plan.replacement)
        )));
    }

    // Revert the dependents into the target (last first, so the binders come
    // out in context order), then read the motive's universe off it.
    let mut reverted = goal.target.clone();
    for d in deps.iter().rev() {
        reverted = Expr::pi(d.binder_info, d.ty.clone(), reverted.abstract_fvar(d.fvar));
    }
    let reverted_sort = state.infer_type(&goal, &reverted)?;
    let reverted_sort = state.whnf(&goal, &reverted_sort);
    let motive_level = match reverted_sort.kind() {
        ExprKind::Sort(l) => l.clone(),
        _ => {
            return Err(TacticError::GoalMismatch(format!(
                "subst: the goal is not a type: its sort reduced to {}",
                crate::error_render::term(&reverted_sort)
            )))
        }
    };

    // The binder base of the goal being closed fixes the ids of the
    // re-introduced dependents: `close_fvars` reads a tactic binder's depth
    // off its id, and the lambdas minted below sit exactly at this goal's
    // depth (the eliminator application adds none). Reading it off the
    // narrowed intermediate goals would hand back an id already bound by a
    // reverted local's live lambda (the `revert; intro` capture).
    let binder_base = state.goal_binder_base(&goal);

    let ctx_without: Vec<LocalDecl> = goal
        .local_ctx
        .iter()
        .filter(|d| {
            d.fvar != plan.var_id
                && d.fvar != plan.hyp_fvar
                && !deps.iter().any(|dep| dep.fvar == d.fvar)
        })
        .cloned()
        .collect();

    let new_type = new_goal_type(&plan, &reverted);
    // The parent's scope stays a superset (`fresh_case_meta`): the variable and
    // the equation leave the CONTEXT but their binders are still live, so the
    // next `intro` (G82's next equation) must not reuse their ids.
    let new_meta_id = state.fresh_case_meta(new_type.clone(), &goal, &ctx_without);
    let minor = Expr::fvar(MetaState::to_fvar(new_meta_id));
    // The eliminator proves the REVERTED target; applying it to the reverted
    // locals gives back the goal (the same `?new d₁ … dₙ` shape as `revert`).
    let mut proof = build_elim(&plan, &reverted, motive_level, minor);
    for d in &deps {
        proof = Expr::app(proof, Expr::fvar(d.fvar));
    }
    state.close_goal(&goal, proof)?;
    state.goals.push_front(Goal {
        meta_id: new_meta_id,
        target: new_type,
        local_ctx: ctx_without,
        case_binders: goal.case_binders.clone(),
        tag: None,
    });

    let mut case_binders = goal.case_binders.clone();
    // Re-introduce the reverted dependents with their substituted types,
    // one lambda per goal step exactly like `intro`, but at ids fixed by the
    // ORIGINAL goal's binder base (see above).
    for (k, dep) in deps.iter().enumerate() {
        let cur = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let target = state.whnf(&cur, &cur.target);
        let ExprKind::Pi(bi, domain, codomain) = target.kind() else {
            return Err(TacticError::GoalMismatch(format!(
                "subst: expected a reverted binder for `{}` in the new goal",
                dep.name
            )));
        };
        let fvar = FVarId::new(binder_base + k as u64);
        for field in &mut case_binders {
            if *field == dep.fvar {
                *field = fvar;
            }
        }
        state.next_fvar = state.next_fvar.max(binder_base + k as u64 + 1);
        let mut new_ctx = cur.local_ctx.clone();
        new_ctx.push(LocalDecl {
            binder_info: *bi,
            fvar,
            name: dep.name.clone(),
            ty: domain.as_ref().clone(),
            value: None,
        });
        let new_target = codomain.instantiate(&Expr::fvar(fvar));
        let new_meta_id = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
        let new_meta_expr = Expr::fvar(MetaState::to_fvar(new_meta_id));
        let lam = Expr::lam(
            *bi,
            domain.as_ref().clone(),
            new_meta_expr.abstract_fvar(fvar),
        );
        // The id is fixed by the ORIGINAL goal's depth (above), not by this
        // narrowed goal's scope, so it is declared to the assignment-scope
        // check explicitly: in scope from binder depth 1 (inside the lambda).
        state.close_goal_with_bound_locals(&cur, lam, &[(fvar, 1)])?;
        state.goals.push_front(Goal {
            meta_id: new_meta_id,
            target: new_target,
            local_ctx: new_ctx,
            tag: None,
            case_binders: case_binders.clone(),
        });
    }

    Ok(())
}

/// Whether a projection in `expr` hides `x`: `y.val` elaborates to the
/// primitive `Proj(Fin, 0, y)`, while Lean's `@Fin.val (n+1) y` spells the
/// structure's parameters, so its `substVar` search sees `n` in it and skips
/// that equation (review r6, X5). Read off the projected local's type.
fn projection_names(goal: &Goal, expr: &Expr, x: FVarId) -> bool {
    match expr.kind() {
        ExprKind::Proj(_, _, inner) => {
            let local_type_names = match inner.kind() {
                ExprKind::FVar(id) => goal
                    .local_ctx
                    .iter()
                    .find(|d| d.fvar == *id)
                    .is_some_and(|d| fvar_occurs_in(&d.ty, x)),
                _ => false,
            };
            local_type_names || projection_names(goal, inner, x)
        }
        ExprKind::App(f, a) => projection_names(goal, f, x) || projection_names(goal, a, x),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            projection_names(goal, ty, x) || projection_names(goal, body, x)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            projection_names(goal, ty, x)
                || projection_names(goal, val, x)
                || projection_names(goal, body, x)
        }
        ExprKind::MData(_, inner) => projection_names(goal, inner, x),
        _ => false,
    }
}

/// The oldest local of `goal` stating `x = e` or `e = x` with `e` not
/// mentioning `x` (Lean 4.8's `substVar` search), with its parts.
fn equation_for_variable(
    state: &ProofState,
    goal: &Goal,
    x: FVarId,
) -> Option<(LocalDecl, Expr, Expr, Expr, Vec<Level>)> {
    goal.local_ctx.iter().find_map(|decl| {
        if decl.fvar == x {
            return None;
        }
        let ty = state.whnf(goal, &decl.ty);
        let (eq_type, lhs, rhs, levels) = match_equality(&ty).ok()?;
        let names = |side: &Expr, other: &Expr| {
            matches!(side.kind(), ExprKind::FVar(id) if *id == x)
                && !fvar_occurs_in(other, x)
                && !projection_names(goal, other, x)
        };
        (names(&rhs, &lhs) || names(&lhs, &rhs)).then(|| (decl.clone(), eq_type, lhs, rhs, levels))
    })
}

/// The `subst_vars` tactic repeatedly applies `subst` to all equality hypotheses.
///
/// This finds all hypotheses of the form `h : x = e` or `h : e = x` where `x` is
/// a free variable and applies `subst` to eliminate them one by one.
///
/// # Example
/// ```text
/// x : Nat, y : Nat
/// h1 : x = 5
/// h2 : y = x + 1
/// goal : x + y = 11
///
/// subst_vars
///
/// goal : 5 + 6 = 11  (after substituting x=5, then y=6)
/// ```
pub fn subst_vars(state: &mut ProofState) -> TacticResult {
    let max_iterations = 100;
    for _ in 0..max_iterations {
        let goal = match state.current_goal() {
            Some(g) => g.clone(),
            None => return Ok(()),
        };

        let mut found = None;
        for decl in &goal.local_ctx {
            let hyp_ty = state.whnf(&goal, &decl.ty);
            if let Ok((_eq_type, lhs, rhs, _levels)) = match_equality(&hyp_ty) {
                let is_fvar_in_ctx = |e: &Expr| -> bool {
                    if let ExprKind::FVar(id) = e.kind() {
                        goal.local_ctx.iter().any(|d| d.fvar == *id)
                    } else {
                        false
                    }
                };

                if is_fvar_in_ctx(&lhs) || is_fvar_in_ctx(&rhs) {
                    found = Some(decl.name.clone());
                    break;
                }
            }
        }

        match found {
            Some(hyp_name) => {
                subst(state, &hyp_name)?;
            }
            None => return Ok(()),
        }
    }

    Ok(())
}
