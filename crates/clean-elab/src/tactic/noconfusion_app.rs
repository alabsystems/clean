// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `T.noConfusion` applications and the injection step built on them —
//! Lean 4.8.0's `mkNoConfusion` (`Lean/Meta/AppBuilder.lean`) and
//! `injectionCore` (`Lean/Meta/Tactic/Injection.lean`), shared by the
//! `injection` tactic and by `cases`' equation unification
//! ([`super::cases_unify_eqs`]).
//!
//! Two `noConfusion` signatures reach Clean, and both are read off the
//! constant's own type rather than assumed:
//!
//! * Lean 4.8.0's (the pinned oracle's `.olean`s):
//!   `@T.noConfusion.{u, us} params… indices… {P : Sort u} {v₁ v₂} (h : v₁ = v₂)`;
//! * Lean 4.30's heterogeneous one, which Clean's own inductive builder emits
//!   for a parameterized type and the repository's pinned v4.30 `.olean`s
//!   carry: `@T.noConfusion.{u, us} {P} params… {t} params'… {t'}
//!   (p₁ ~ p₁') … (HEq t t')`, applied here at `params' := params` with
//!   `Eq.refl` / `HEq.refl` for each parameter equation and `heq_of_eq h`.
//!
//! The field equations a same-constructor `noConfusion` offers are NEVER
//! rebuilt by hand: the type of the application is put in weak head normal
//! form, `(eq₁ → … → eqₖ → P) → P`, and its domain becomes the new goal, so
//! every equation carries exactly the universe level, the `Eq`/`HEq` choice and
//! the skipped `Prop` fields of the environment's `T.noConfusionType`.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId, Level, Literal, TypeChecker};

use super::core::{Goal, ProofState, TacticError};
use crate::unify::MetaState;

/// The result of [`injection_core`] (Lean's `InjectionResultCore`).
pub(crate) enum InjectionOutcome {
    /// The constructors differ: `noConfusion` closed the goal.
    Solved,
    /// The same constructor: the front goal is now `eq₁ → … → eqₖ → target`,
    /// with `num_eqs = k` (Lean's `numFields - numPropFields`).
    Subgoal { num_eqs: usize },
}

/// A side of an equation recognized as a constructor application.
pub(crate) struct CtorApp {
    pub(crate) ctor: Name,
    pub(crate) num_fields: u32,
}

fn tactic_err(detail: String) -> TacticError {
    TacticError::InvalidTarget {
        tactic: "injection".into(),
        detail,
    }
}

/// `Nat.zero` / `Nat.succ (n-1)` for a `Nat` literal — the `Nat` arm of
/// Lean's `litToCtor`, reading a raw literal and `@OfNat.ofNat Nat n _`.
fn lit_to_ctor(e: &Expr) -> Option<Expr> {
    let value = match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.clone(),
        _ => {
            let ExprKind::Const(head, _) = e.get_app_fn().kind() else {
                return None;
            };
            let args = e.get_app_args();
            if head != &Name::from_string("OfNat.ofNat") || args.len() != 3 {
                return None;
            }
            let is_nat =
                matches!(args[0].kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat"));
            match (is_nat, args[1].kind()) {
                (true, ExprKind::Lit(Literal::Nat(n))) => n.clone(),
                _ => return None,
            }
        }
    };
    Some(match value.pred() {
        None => Expr::const_(Name::from_string("Nat.zero"), vec![]),
        Some(pred) => Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::bignat_lit(pred),
        ),
    })
}

/// Lean's `isConstructorApp?`: `e` (no reduction, a `Nat` literal read as its
/// constructor) is a constructor applied to exactly its parameters and fields.
pub(crate) fn ctor_app_syntactic(state: &ProofState, e: &Expr) -> Option<CtorApp> {
    let e = state.metas.instantiate(e);
    let e = lit_to_ctor(&e).unwrap_or(e);
    let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
        return None;
    };
    let ctor = state.env.get_constructor(name)?;
    ((ctor.num_params + ctor.num_fields) as usize == e.get_app_num_args()).then(|| CtorApp {
        ctor: ctor.name.clone(),
        num_fields: ctor.num_fields,
    })
}

/// A checker at Lean's MetaM `.default` transparency: an `@[irreducible]`
/// definition stays folded (the unifier's B14 gate). The tactic layer's
/// `state.whnf` / `state.is_def_eq` are the transparency-blind kernel's; every
/// DECISION of `unifyEq?` / `injectionCore` (is a side a constructor
/// application, are the sides definitionally equal, did `whnf` change a side)
/// is taken here instead, so Clean never solves an equation Lean's `cases`
/// reports unsolvable by unfolding what Lean keeps folded.
fn meta_tc<'s>(state: &'s ProofState, goal: &Goal) -> TypeChecker<'s> {
    let tc = TypeChecker::with_context(&state.env, state.build_local_ctx(goal));
    tc.set_honor_reducibility(true);
    tc
}

/// `whnf` at Lean's `.default` transparency (see [`meta_tc`]).
pub(crate) fn meta_whnf(state: &ProofState, goal: &Goal, e: &Expr) -> Expr {
    meta_tc(state, goal).whnf(&state.instantiate_for_kernel(e))
}

/// Lean's `isConstructorApp'?`: [`ctor_app_syntactic`], else on the `whnf`.
pub(crate) fn ctor_app(state: &ProofState, goal: &Goal, e: &Expr) -> Option<CtorApp> {
    ctor_app_syntactic(state, e).or_else(|| ctor_app_syntactic(state, &meta_whnf(state, goal, e)))
}

/// The checker `cases`' equation decisions run in ([`super::cases_unify_eqs`]):
/// [`meta_tc`]'s transparency, with every `have` local bound WITHOUT its value.
///
/// Lean's `have` local has no value, so `unifyEq?` cannot see through it, while
/// a `let` local's value is unfolded. Clean keeps a tactic `have`'s proof as the
/// local's value, marked as a `have`'s (`core::have_value`, DECISIONS R127):
/// the shared goal context omits exactly the marked values
/// ([`ProofState::build_local_ctx`]). A `have b := a; cases (H b)`
/// equation Lean reports "dependent elimination failed" on was solved here by
/// unfolding `b` (review r6, X3; docs/DECISIONS.md R136); the `let` form, which
/// both Leans solve, is solved.
fn cases_tc<'s>(state: &'s ProofState, goal: &Goal) -> TypeChecker<'s> {
    let tc = TypeChecker::with_context(&state.env, state.build_local_ctx(goal));
    tc.set_honor_reducibility(true);
    tc
}

/// `whnf` for `cases`' decisions ([`cases_tc`]).
pub(crate) fn cases_whnf(state: &ProofState, goal: &Goal, e: &Expr) -> Expr {
    cases_tc(state, goal).whnf(&state.instantiate_for_kernel(e))
}

/// `isDefEq` for `cases`' decisions ([`cases_tc`]).
pub(crate) fn cases_is_def_eq(state: &ProofState, goal: &Goal, a: &Expr, b: &Expr) -> bool {
    cases_tc(state, goal).is_def_eq(
        &state.instantiate_for_kernel(a),
        &state.instantiate_for_kernel(b),
    )
}

/// [`ctor_app`] for `cases`' decisions ([`cases_tc`]).
pub(crate) fn cases_ctor_app(state: &ProofState, goal: &Goal, e: &Expr) -> Option<CtorApp> {
    ctor_app_syntactic(state, e).or_else(|| ctor_app_syntactic(state, &cases_whnf(state, goal, e)))
}

/// The number of leading `Π` binders of `ty` (syntactic, no reduction).
fn binder_count(ty: &Expr) -> usize {
    let mut n = 0;
    let mut cur = ty;
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        n += 1;
        cur = body.as_ref();
    }
    n
}

/// The refl proof a heterogeneous `noConfusion`'s parameter equation takes:
/// `@Eq.refl.{l} A x` for `@Eq.{l} A x x`, `@HEq.refl.{l} A x` for
/// `@HEq.{l} A x A x`.
fn param_refl(domain: &Expr, nc: &Name) -> Result<Expr, TacticError> {
    let args = domain.get_app_args();
    if let ExprKind::Const(head, lvls) = domain.get_app_fn().kind() {
        let refl = match (head.to_string().as_str(), args.len()) {
            ("Eq", 3) => Some("Eq.refl"),
            ("HEq", 4) => Some("HEq.refl"),
            _ => None,
        };
        if let Some(refl) = refl {
            return Ok(Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(refl), lvls.to_vec()),
                    args[0].clone(),
                ),
                args[1].clone(),
            ));
        }
    }
    Err(tactic_err(format!(
        "`{nc}`: a parameter equation of its heterogeneous signature is not `Eq`/`HEq`"
    )))
}

/// `@heq_of_eq.{l} T a b prf : HEq a b` for the final binder `@HEq.{l} T a T b`.
fn heq_of(domain: &Expr, prf: &Expr, nc: &Name) -> Result<Expr, TacticError> {
    let args = domain.get_app_args();
    match domain.get_app_fn().kind() {
        ExprKind::Const(head, lvls) if head == &Name::from_string("HEq") && args.len() == 4 => {
            let mut e = Expr::const_(Name::from_string("heq_of_eq"), lvls.to_vec());
            for arg in [args[0], args[1], args[3]] {
                e = Expr::app(e, arg.clone());
            }
            Ok(Expr::app(e, prf.clone()))
        }
        _ => Err(tactic_err(format!(
            "`{nc}`: the last binder of its heterogeneous signature is not `HEq t t'`"
        ))),
    }
}

/// Lean's `mkNoConfusion target prf` for `prf : a = b`, `a b : alpha`:
/// `T.noConfusion` applied so that its type is `T.noConfusionType target a b`.
///
/// Refuses (by name) an environment whose `T.noConfusion` has neither
/// signature, rather than guess an argument order.
pub(crate) fn mk_no_confusion(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
    alpha: &Expr,
    (a, b): (&Expr, &Expr),
    prf: &Expr,
) -> Result<Expr, TacticError> {
    let alpha = meta_whnf(state, goal, alpha);
    let ExprKind::Const(ind_name, us) = alpha.get_app_fn().kind() else {
        return Err(tactic_err(format!(
            "inductive type expected, got {}",
            crate::error_render::term(&alpha)
        )));
    };
    let ind = state
        .env
        .get_inductive(ind_name)
        .ok_or_else(|| tactic_err(format!("inductive type expected, got `{ind_name}`")))?;
    let (np, ni) = (ind.num_params as usize, ind.num_indices as usize);
    let ty_args: Vec<Expr> = alpha.get_app_args().into_iter().cloned().collect();
    if ty_args.len() != np + ni {
        return Err(tactic_err(format!(
            "`{ind_name}` is applied to {} arguments, not its {np} parameters and {ni} indices",
            ty_args.len()
        )));
    }
    let nc_name = ind_name.clone().str("noConfusion");
    let nc_info = state
        .env
        .get_const(&nc_name)
        .ok_or_else(|| TacticError::EnvironmentMissing {
            constant: nc_name.to_string(),
        })?;
    let target_sort = state.whnf(goal, &state.infer_type(goal, target)?);
    let ExprKind::Sort(u) = target_sort.kind() else {
        return Err(tactic_err("the goal is not a type".into()));
    };
    let mut levels = vec![u.clone()];
    levels.extend(us.iter().cloned());
    if levels.len() != nc_info.level_params.len() {
        return Err(tactic_err(format!(
            "`{nc_name}` takes {} universe levels, not the motive's and `{ind_name}`'s {}",
            nc_info.level_params.len(),
            levels.len()
        )));
    }
    // The position of the motive binder `{P : Sort u}` (u = the first level
    // parameter) tells the two signatures apart; with no parameters and no
    // indices they coincide.
    let motive_sort = Expr::sort(Level::param(nc_info.level_params[0].clone()));
    let mut p_pos = None;
    let mut cur = &nc_info.type_;
    let mut k = 0;
    while let ExprKind::Pi(_, dom, body) = cur.kind() {
        if p_pos.is_none() && **dom == motive_sort {
            p_pos = Some(k);
        }
        k += 1;
        cur = body.as_ref();
    }
    let total = binder_count(&nc_info.type_);
    let nc_ty = nc_info
        .type_
        .instantiate_level_params_direct(&nc_info.level_params, &levels);
    let nc_const = Expr::const_(nc_name.clone(), levels);
    let classic = p_pos == Some(np + ni) && total == np + ni + 4;
    let hetero = !classic && ni == 0 && p_pos == Some(0) && total == 3 * np + 4;
    let args: Vec<Expr> = if classic {
        let mut args = ty_args;
        args.extend([target.clone(), a.clone(), b.clone(), prf.clone()]);
        args
    } else if hetero {
        let params = &ty_args[..np];
        let mut args = vec![target.clone()];
        args.extend(params.iter().cloned());
        args.push(a.clone());
        args.extend(params.iter().cloned());
        args.push(b.clone());
        // Read each remaining binder's domain at the arguments so far.
        let mut ty = nc_ty.clone();
        for arg in &args {
            let ExprKind::Pi(_, _, body) = ty.kind() else {
                return Err(tactic_err(format!("`{nc_name}` has too few binders")));
            };
            ty = body.instantiate(arg);
        }
        for _ in 0..np {
            let ExprKind::Pi(_, dom, body) = ty.kind() else {
                return Err(tactic_err(format!("`{nc_name}` has too few binders")));
            };
            let refl = param_refl(dom, &nc_name)?;
            ty = body.instantiate(&refl);
            args.push(refl);
        }
        let ExprKind::Pi(_, dom, _) = ty.kind() else {
            return Err(tactic_err(format!("`{nc_name}` has too few binders")));
        };
        args.push(heq_of(dom, prf, &nc_name)?);
        args
    } else {
        return Err(tactic_err(format!(
            "`{nc_name}` has a signature that is neither Lean 4.8's \
             (`params… {{P}} {{v₁ v₂}} (v₁ = v₂)`) nor Lean 4.30's heterogeneous one"
        )));
    };
    Ok(args.into_iter().fold(nc_const, Expr::app))
}

/// [`mk_no_confusion`] with its type, read off `T.noConfusion`'s declared
/// type at the application's arguments rather than inferred, so `prf` may be
/// a loose bound variable (simp's constructor-injectivity lemma builds it
/// under the `fun h => …` binder that owns it, `simp/ctor_inj.rs`).
pub(crate) fn mk_no_confusion_typed(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
    alpha: &Expr,
    sides: (&Expr, &Expr),
    prf: &Expr,
) -> Result<(Expr, Expr), TacticError> {
    let app = mk_no_confusion(state, goal, target, alpha, sides, prf)?;
    let ExprKind::Const(nc_name, levels) = app.get_app_fn().kind() else {
        return Err(tactic_err("`noConfusion` application expected".into()));
    };
    let info = state
        .env
        .get_const(nc_name)
        .ok_or_else(|| TacticError::EnvironmentMissing {
            constant: nc_name.to_string(),
        })?;
    let mut ty = info
        .type_
        .instantiate_level_params_direct(&info.level_params, levels);
    for arg in app.get_app_args() {
        let ExprKind::Pi(_, _, body) = ty.kind() else {
            return Err(tactic_err(format!("`{nc_name}` has too few binders")));
        };
        ty = body.instantiate(arg);
    }
    Ok((app, ty))
}

/// How many leading binders of `domain` (= `eq₁ → … → eqₖ → target`) are
/// field equations: the first `k` whose remainder IS `target`. No shorter
/// remainder can equal `target`, since it would contain it as a proper part.
fn count_field_equations(domain: &Expr, target: &Expr) -> Option<usize> {
    let mut cur = domain;
    let mut k = 0;
    loop {
        if !cur.has_loose_bvars() && cur == target {
            return Some(k);
        }
        let ExprKind::Pi(_, dom, body) = cur.kind() else {
            return None;
        };
        let is_eq = matches!(dom.get_app_fn().kind(),
            ExprKind::Const(n, _) if n == &Name::from_string("Eq") || n == &Name::from_string("HEq"));
        if !is_eq {
            return None;
        }
        k += 1;
        cur = body.as_ref();
    }
}

/// Whether `fvar` occurs in `goal`'s target or in another local's type or value.
pub(crate) fn local_is_used(state: &ProofState, goal: &Goal, fvar: FVarId) -> bool {
    let mentions = |e: &Expr| {
        crate::tactic::hypothesis::collect_fvars(&state.metas.instantiate(e)).contains(&fvar)
    };
    mentions(&goal.target)
        || goal
            .local_ctx
            .iter()
            .filter(|d| d.fvar != fvar)
            .any(|d| mentions(&d.ty) || d.value.as_ref().is_some_and(mentions))
}

/// Lean's `injectionCore` on the equation `prf : a = b` (`a b : alpha`) in the
/// front goal `goal`.
///
/// Distinct constructors close the goal with `noConfusion` ([`InjectionOutcome::Solved`]).
/// The same constructor replaces the goal by `eq₁ → … → eqₖ → target` — the
/// domain of the `whnf` of `noConfusion`'s type — and drops `clear` (the local
/// holding the equation) from it when nothing else mentions it (Lean's
/// `tryClear`). The equations are NOT introduced.
///
/// # Errors
/// `GoalMismatch` when a side is not a constructor application; `InvalidTarget`
/// (a named refusal) for a `noConfusion` shape this does not support.
pub(crate) fn injection_core(
    state: &mut ProofState,
    goal: &Goal,
    alpha: &Expr,
    (a, b): (&Expr, &Expr),
    prf: &Expr,
    clear: Option<FVarId>,
) -> Result<InjectionOutcome, TacticError> {
    let (Some(ca), Some(cb)) = (ctor_app(state, goal, a), ctor_app(state, goal, b)) else {
        return Err(TacticError::GoalMismatch(
            "injection: equality of constructor applications expected".into(),
        ));
    };
    let target = state.instantiate_for_kernel(&goal.target);
    let nc = mk_no_confusion(state, goal, &target, alpha, (a, b), prf)?;
    if ca.ctor != cb.ctor {
        // `noConfusionType P (C₁ …) (C₂ …)` δι-reduces to `P`.
        state.close_goal(goal, nc)?;
        return Ok(InjectionOutcome::Solved);
    }
    let nc_ty = state.infer_type(goal, &nc)?;
    let nc_ty = state.whnf(goal, &nc_ty);
    let ExprKind::Pi(_, domain, _) = nc_ty.kind() else {
        return Err(tactic_err(format!(
            "`noConfusion` on `{}` did not reduce to `(… → P) → P`: {}",
            ca.ctor,
            crate::error_render::term(&nc_ty)
        )));
    };
    let new_target = super::op_projection::head_beta(domain);
    let num_eqs = count_field_equations(&new_target, &target).ok_or_else(|| {
        tactic_err(format!(
            "the `noConfusion` premise for `{}` is not a chain of field equations ending in the \
             goal: {}",
            ca.ctor,
            crate::error_render::term(&new_target)
        ))
    })?;
    debug_assert!(num_eqs <= ca.num_fields as usize);
    let ctx: Vec<_> = goal
        .local_ctx
        .iter()
        .filter(|d| Some(d.fvar) != clear || local_is_used(state, goal, d.fvar))
        .cloned()
        .collect();
    let new_meta = state.fresh_case_meta(new_target.clone(), goal, &ctx);
    let proof = Expr::app(nc, Expr::fvar(MetaState::to_fvar(new_meta)));
    state.close_goal(goal, proof)?;
    state.goals.push_front(Goal {
        meta_id: new_meta,
        target: new_target,
        local_ctx: ctx,
        tag: goal.tag.clone(),
        case_binders: goal.case_binders.clone(),
    });
    Ok(InjectionOutcome::Subgoal { num_eqs })
}
