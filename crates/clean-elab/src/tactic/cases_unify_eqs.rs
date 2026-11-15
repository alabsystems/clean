// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `cases h` on an equation `h : lhs = rhs` — Lean 4.8.0's `unifyEqs?` /
//! `unifyEq?` (`Lean/Meta/Tactic/UnifyEq.lean`, `Lean/Meta/Tactic/Cases.lean`).
//!
//! Lean's `cases` generalizes `Eq`'s index and so unifies the equation
//! `rhs = lhs`; each equation `a = b` it meets is solved in this order:
//!
//! 1. a heterogeneous `HEq a b` whose two types are definitionally equal is
//!    replaced by `a = b` (`heqToEq'`), which is solved next;
//! 2. a side that is a local variable is substituted away (`substEq`); of two
//!    locals the LATER-declared one is eliminated. When that fails (the
//!    variable occurs in the other side) the equation is cleared if `a` and
//!    `b` are definitionally equal; Lean would next try `acyclic`, which is
//!    not implemented here and is refused by name;
//! 3. otherwise an equation between definitionally equal sides is cleared;
//! 4. otherwise two constructor applications are split by `injectionCore`
//!    ([`super::noconfusion_app`]): distinct constructors close the goal,
//!    the same constructor queues the field equations `noConfusionType`
//!    states, in order;
//! 5. otherwise, when `whnf` changes a side, the reduced equation is queued;
//! 6. otherwise "dependent elimination failed".
//!
//! Queued equations are leading `Π` binders of the goal, introduced one at a
//! time, so every substitution also rewrites the equations still pending —
//! exactly Lean's `intro1`-driven loop.
//!
//! Lean finishes by substituting `h` itself by `Eq.refl` (the `HEq h h'`
//! index equation). Here `h` is consumed by its own first step instead: it is
//! substituted, cleared, or handed to `noConfusion` as `Eq.symm h`. When the
//! goal or another local MENTIONS `h` and the first step is not a
//! substitution, that is refused by name rather than approximated.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::SurfaceName;

use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::equality::match_equality;
// Every decision below reads locals without their values (`cases_tc`, review
// r6 X3): `cases_whnf` / `cases_is_def_eq` / `cases_ctor_app`.
use super::noconfusion_app::{
    cases_ctor_app as ctor_app, cases_is_def_eq as meta_is_def_eq, cases_whnf as meta_whnf,
    ctor_app_syntactic, injection_core, local_is_used, InjectionOutcome,
};

/// The numeric frame of clean-parser's `inaccessible_hypothesis` ("INAC"): a
/// name no identifier token can spell, as Lean's `intro1` names its locals.
const INACCESSIBLE_NAME_FRAME: u64 = 0x494E_4143;

/// Upper bound on unification steps for one `cases`; Lean has none, but a
/// `whnf` that keeps changing a side must not loop forever here.
const MAX_STEPS: usize = 10_000;

/// What one `unifyEq?` step left.
enum Step {
    /// The goal was closed (distinct constructors).
    Solved,
    /// The goal continues with this many NEW equations queued in front.
    Continue(usize),
}

/// The equation one step works on: the local `local` proves `a = b` — or,
/// for the hypothesis `cases` was given (`flipped`), `b = a`.
struct Equation {
    local: FVarId,
    alpha: Expr,
    a: Expr,
    b: Expr,
    level: Level,
    flipped: bool,
}

impl Equation {
    /// A proof of `a = b`.
    fn proof(&self) -> Expr {
        if !self.flipped {
            return Expr::fvar(self.local);
        }
        // `@Eq.symm.{u} α b a h : a = b` from `h : b = a`.
        let symm = [&self.alpha, &self.b, &self.a].into_iter().fold(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.level.clone()]),
            |f, arg| Expr::app(f, arg.clone()),
        );
        Expr::app(symm, Expr::fvar(self.local))
    }
}

fn dep_elim_message(state: &ProofState, eq: &Equation) -> String {
    format!(
        "dependent elimination failed, failed to solve equation {} = {}",
        crate::error_render::term(&state.metas.instantiate(&eq.a)),
        crate::error_render::term(&state.metas.instantiate(&eq.b)),
    )
}

fn dep_elim_failed(state: &ProofState, eq: &Equation) -> TacticError {
    TacticError::GoalMismatch(dep_elim_message(state, eq))
}

fn refused(detail: String) -> TacticError {
    TacticError::InvalidTarget {
        tactic: "cases".into(),
        detail,
    }
}

/// `cases h` for the local `hyp_fvar` whose type is (after `whnf`) an `Eq`.
///
/// ENSURES: On Ok, the equation is fully unified: the front goal is the one
/// continuation (or none, when distinct constructors closed it), every proof
/// step checked by `close_goal`.
pub(crate) fn cases_eq(state: &mut ProofState, hyp_fvar: FVarId) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let decl = goal
        .local_ctx
        .iter()
        .find(|d| d.fvar == hyp_fvar)
        .ok_or_else(|| TacticError::HypothesisNotFound(format!("{hyp_fvar:?}")))?
        .clone();
    let ty = meta_whnf(state, &goal, &decl.ty);
    let (alpha, lhs, rhs, levels) = match_equality(&ty)?;
    let eq = Equation {
        local: hyp_fvar,
        alpha,
        a: state.metas.instantiate(&rhs),
        b: state.metas.instantiate(&lhs),
        level: levels.into_iter().next().unwrap_or_else(Level::zero),
        flipped: true,
    };
    let open = match unify_eq(state, &goal, &eq, false)? {
        Step::Solved => false,
        Step::Continue(n) => unify_eqs(state, n)?,
    };
    if open {
        // Lean's `cases` names the goal it leaves `tag ++ refl` (`case refl`,
        // what `cases h with | refl => …` selects); every unification step
        // keeps that tag.
        let refl = SurfaceName::generated_path("refl");
        let tag = match &goal.tag {
            Some(parent) if !parent.is_anonymous() => parent.append(&refl),
            _ => refl,
        };
        if let Some(front) = state.current_goal_mut() {
            front.tag = Some(tag);
        }
    }
    Ok(())
}

/// Lean's `unifyEqs?`: introduce and solve `n` queued equations. Returns
/// whether the goal is still open (`false`: distinct constructors closed it).
pub(crate) fn unify_eqs(state: &mut ProofState, n: usize) -> Result<bool, TacticError> {
    unify_eqs_with_preference(state, n, false)
}

/// Index equations should retain constructor fields when either local side
/// can be substituted, so alternative binders continue to name those fields.
pub(crate) fn unify_index_eqs(state: &mut ProofState, n: usize) -> Result<bool, TacticError> {
    unify_eqs_with_preference(state, n, true)
}

fn unify_eqs_with_preference(
    state: &mut ProofState,
    mut n: usize,
    keep_case_fields: bool,
) -> Result<bool, TacticError> {
    let name = SurfaceName::from_name(Name::anon().num(INACCESSIBLE_NAME_FRAME).str("h✝"));
    let mut steps = 0;
    while n > 0 {
        steps += 1;
        if steps > MAX_STEPS {
            return Err(refused(format!(
                "equation unification did not finish within {MAX_STEPS} steps"
            )));
        }
        super::proof_term::intro(state, &name)?;
        let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let local = goal.local_ctx.last().ok_or(TacticError::NoGoals)?.clone();
        let ty = meta_whnf(state, &goal, &local.ty);
        let step = if let Some(heq) = as_heq(&ty) {
            heq_to_eq(state, &goal, local.fvar, heq)?
        } else {
            let (alpha, a, b, levels) = match_equality(&ty).map_err(|_| {
                TacticError::GoalMismatch(format!(
                    "cases: equality expected, got {}",
                    crate::error_render::term(&ty)
                ))
            })?;
            let eq = Equation {
                local: local.fvar,
                alpha,
                a: state.metas.instantiate(&a),
                b: state.metas.instantiate(&b),
                level: levels.into_iter().next().unwrap_or_else(Level::zero),
                flipped: false,
            };
            unify_eq(state, &goal, &eq, keep_case_fields)?
        };
        match step {
            Step::Solved => return Ok(false),
            Step::Continue(k) => n = n - 1 + k,
        }
    }
    Ok(true)
}

/// `(level, α, a, β, b)` of `@HEq.{level} α a β b`.
fn as_heq(ty: &Expr) -> Option<(Level, Expr, Expr, Expr, Expr)> {
    let ExprKind::Const(head, lvls) = ty.get_app_fn().kind() else {
        return None;
    };
    let args = ty.get_app_args();
    (head == &Name::from_string("HEq") && args.len() == 4).then(|| {
        (
            lvls.first().cloned().unwrap_or_else(Level::zero),
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
            args[3].clone(),
        )
    })
}

/// Lean's `heqToEq'`: `e : HEq a b` with `α ≡ β` becomes the queued `a = b`.
fn heq_to_eq(
    state: &mut ProofState,
    goal: &Goal,
    local: FVarId,
    (level, alpha, a, beta, b): (Level, Expr, Expr, Expr, Expr),
) -> Result<Step, TacticError> {
    if !meta_is_def_eq(state, goal, &alpha, &beta) {
        return Err(TacticError::GoalMismatch(format!(
            "dependent elimination failed: the heterogeneous equality's types {} and {} are \
             not definitionally equal",
            crate::error_render::term(&alpha),
            crate::error_render::term(&beta)
        )));
    }
    let eq_ty = [&alpha, &a, &b].into_iter().fold(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        |f, arg| Expr::app(f, arg.clone()),
    );
    let proof = [&alpha, &a, &b].into_iter().fold(
        Expr::const_(Name::from_string("eq_of_heq"), vec![level]),
        |f, arg| Expr::app(f, arg.clone()),
    );
    assert_front(
        state,
        goal,
        eq_ty,
        Expr::app(proof, Expr::fvar(local)),
        local,
    )?;
    Ok(Step::Continue(1))
}

/// Lean's `heqToEq` on the LAST local of the front goal (the `injection`
/// tactic's `injectionIntro`): when it is `HEq a b` with definitionally equal
/// types it becomes `name : a = b`; any other local is left as it is.
pub(crate) fn heq_local_to_eq(state: &mut ProofState, name: &SurfaceName) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let Some(local) = goal.local_ctx.last().cloned() else {
        return Ok(());
    };
    let ty = meta_whnf(state, &goal, &local.ty);
    let Some(heq) = as_heq(&ty) else {
        return Ok(());
    };
    if !meta_is_def_eq(state, &goal, &heq.1, &heq.3) {
        return Ok(());
    }
    heq_to_eq(state, &goal, local.fvar, heq)?;
    super::proof_term::intro(state, name)
}

/// Replace the front goal `goal` by `ty → target`, closing it with
/// `?new proof`; `drop` leaves the new goal's context when nothing mentions it.
fn assert_front(
    state: &mut ProofState,
    goal: &Goal,
    ty: Expr,
    proof: Expr,
    drop: FVarId,
) -> TacticResult {
    let target = state.metas.instantiate(&goal.target);
    let new_target = Expr::pi(BinderInfo::Default, ty, target);
    let ctx: Vec<_> = goal
        .local_ctx
        .iter()
        .filter(|d| d.fvar != drop || local_is_used(state, goal, d.fvar))
        .cloned()
        .collect();
    let new_meta = state.fresh_case_meta(new_target.clone(), goal, &ctx);
    let hole = Expr::fvar(crate::unify::MetaState::to_fvar(new_meta));
    state.close_goal(goal, Expr::app(hole, proof))?;
    state.goals.push_front(Goal {
        meta_id: new_meta,
        target: new_target,
        local_ctx: ctx,
        tag: goal.tag.clone(),
        case_binders: goal.case_binders.clone(),
    });
    Ok(())
}

/// Run `step`, keeping its work on `Ok` and rolling the goal list, the fvar
/// cursor and every metavariable assignment back on `Err` (the scope
/// discipline of omega's `Snapshot`; a full `ProofState` clone would copy
/// the environment on every step).
pub(crate) fn attempt(
    state: &mut ProofState,
    step: impl FnOnce(&mut ProofState) -> TacticResult,
) -> TacticResult {
    let goals = state.goals.clone();
    let next_fvar = state.next_fvar;
    let token = state.metas_mut().push_owned_scope();
    let outcome = step(state);
    if outcome.is_ok() {
        if state.metas_mut().close_owned_scope(token, false).is_ok() {
            return Ok(());
        }
    } else {
        let _ = state.metas_mut().close_owned_scope(token, true);
    }
    state.invalidate_tc_cache();
    state.goals = goals;
    state.next_fvar = next_fvar;
    outcome.and(Err(refused(
        "a substitution disturbed the metavariable scope; rolled back".into(),
    )))
}

/// The local `e` denotes in `goal`, when it is one.
fn context_fvar(goal: &Goal, e: &Expr) -> Option<(usize, FVarId)> {
    match e.kind() {
        ExprKind::FVar(id) => goal
            .local_ctx
            .iter()
            .position(|d| d.fvar == *id)
            .map(|pos| (pos, *id)),
        _ => None,
    }
}

/// Drop the equation local from the front goal (Lean's `clear`): refused by
/// name when the goal or another local mentions it.
fn clear_equation(state: &mut ProofState, goal: &Goal, eq: &Equation) -> Result<Step, TacticError> {
    if local_is_used(state, goal, eq.local) {
        return Err(refused(
            "the equation is mentioned by the goal or another hypothesis; Lean substitutes it \
             by `Eq.refl`, which is not implemented here"
                .into(),
        ));
    }
    let front = state.current_goal_mut().ok_or(TacticError::NoGoals)?;
    front.local_ctx.retain(|d| d.fvar != eq.local);
    Ok(Step::Continue(0))
}

/// Lean's `unifyEq?` on one equation (see the module doc for the order).
fn unify_eq(
    state: &mut ProofState,
    goal: &Goal,
    eq: &Equation,
    keep_case_fields: bool,
) -> Result<Step, TacticError> {
    // The local to eliminate and the side it is replaced by.
    let var = match (context_fvar(goal, &eq.a), context_fvar(goal, &eq.b)) {
        // `substEq (aDecl.index < bDecl.index)`: the later local goes.
        (Some((pa, xa)), Some((pb, xb))) => {
            let keep_a = keep_case_fields && goal.case_binders.contains(&xa);
            let keep_b = keep_case_fields && goal.case_binders.contains(&xb);
            Some(if keep_a != keep_b {
                if keep_a {
                    (xb, &eq.a)
                } else {
                    (xa, &eq.b)
                }
            } else if pa < pb {
                (xb, &eq.a)
            } else {
                (xa, &eq.b)
            })
        }
        (Some((_, x)), None) => Some((x, &eq.b)),
        (None, Some((_, x))) => Some((x, &eq.a)),
        (None, None) => None,
    };
    if let Some((var, other)) = var {
        // Lean's `observing? (substCore …)`: a failed substitution leaves no trace.
        let err = match attempt(state, |s| {
            super::equality::subst_eliminating(s, eq.local, var)
        }) {
            Ok(()) => return Ok(Step::Continue(0)),
            Err(err) => err,
        };
        if meta_is_def_eq(state, goal, &eq.a, &eq.b) {
            return clear_equation(state, goal, eq);
        }
        let occurs = crate::tactic::hypothesis::collect_fvars(other).contains(&var);
        if occurs && ctor_app(state, goal, other).is_some() {
            return Err(refused(format!(
                "the variable occurs in the constructor application {}; Lean closes such an \
                 equation by `acyclic`, which is not implemented here",
                crate::error_render::term(other)
            )));
        }
        return Err(match err {
            TacticError::GoalMismatch(msg) => {
                TacticError::GoalMismatch(format!("{}: {msg}", dep_elim_message(state, eq)))
            }
            e => e,
        });
    }
    if eq.flipped && local_is_used(state, goal, eq.local) {
        return Err(refused(
            "the hypothesis is mentioned by the goal or another hypothesis and neither side is a \
             local; Lean replaces it by `Eq.refl` after unifying, which is not implemented here"
                .into(),
        ));
    }
    if meta_is_def_eq(state, goal, &eq.a, &eq.b) {
        return clear_equation(state, goal, eq);
    }
    if ctor_app_syntactic(state, &eq.a).is_some() && ctor_app_syntactic(state, &eq.b).is_some() {
        let outcome = injection_core(
            state,
            goal,
            &eq.alpha,
            (&eq.a, &eq.b),
            &eq.proof(),
            Some(eq.local),
        )?;
        return Ok(match outcome {
            InjectionOutcome::Solved => Step::Solved,
            InjectionOutcome::Subgoal { num_eqs } => Step::Continue(num_eqs),
        });
    }
    let a_whnf = meta_whnf(state, goal, &eq.a);
    let b_whnf = meta_whnf(state, goal, &eq.b);
    if a_whnf == state.instantiate_for_kernel(&eq.a)
        && b_whnf == state.instantiate_for_kernel(&eq.b)
    {
        return Err(dep_elim_failed(state, eq));
    }
    let reduced = [&eq.alpha, &a_whnf, &b_whnf].into_iter().fold(
        Expr::const_(Name::from_string("Eq"), vec![eq.level.clone()]),
        |f, arg| Expr::app(f, arg.clone()),
    );
    assert_front(state, goal, reduced, eq.proof(), eq.local)?;
    Ok(Step::Continue(1))
}
