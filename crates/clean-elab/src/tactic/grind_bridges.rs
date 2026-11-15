// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! grind's BRIDGES: the speculative rewrites that turn a goal grind cannot
//! attack into one it can — `propext`, `funext`, extensionality at any
//! codomain, the `Eq`/`HEq` bridge, `exfalso` and the `Iff` split.
//!
//! Split out of `grind.rs` to keep that file under the paragon 1000-line
//! limit. Each is speculative: on failure the goal list and meta state roll
//! back, so a bridge can only ADD a route.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Name};

use super::combinator::try_tactic_preserving_state;
use super::connective::exfalso;
use super::grind::{
    grind_core, grind_no_progress, try_triggered_solve_by_elim, GrindConfig,
    GRIND_FUNEXT_NO_PROGRESS,
};
use super::grind_split::close_all_goals_recursive_with;
use super::proof_term::assumption;
use super::proof_term::{apply, constructor};
use super::solve_by_elim;
use super::{funext, match_iff, subst_vars, Goal, ProofState, TacticError, TacticResult};
use crate::stack_safe;
use crate::unify::MetaState;

/// Rewrite a `@Eq Prop p q` goal to `p ↔ q` via `propext`. No-op for any
/// other goal shape.
pub(super) fn try_propext_bridge(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let args = target.get_app_args();
    let head = target.get_app_fn();
    let is_eq_at_prop = matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Eq")
        && args.len() == 3
        && matches!(args[0].kind(), ExprKind::Sort(l) if l.is_zero());
    if !is_eq_at_prop {
        return Err(TacticError::no_progress("grind/propext"));
    }
    apply(state, Expr::const_(Name::from_string("propext"), vec![]))
}

/// Rewrite a `@Eq ((x₁ : α₁) → … → Prop) f g` goal to the pointwise
/// `f x₁ … xₙ ↔ g x₁ … xₙ` via one `funext` per binder followed by
/// [`try_propext_bridge`]. No-op for any other goal shape — in particular a
/// non-Prop-valued function equality is left untouched.
///
/// The Pi/Prop shape check runs BEFORE the first `funext`, so the chain never
/// starts on a goal it cannot finish with an `Iff`; each constituent step
/// type-checks through `close_goal`, and the whole chain is speculative — on
/// any failure the goal list and meta state roll back to the pre-bridge
/// snapshot.
pub(super) fn try_funext_propext_bridge(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let args = target.get_app_args();
    let head = target.get_app_fn();
    let is_eq =
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Eq") && args.len() == 3;
    if !is_eq {
        return Err(grind_no_progress(GRIND_FUNEXT_NO_PROGRESS));
    }
    let Some(arity) = pi_arity_into_prop(args[0]) else {
        return Err(grind_no_progress(GRIND_FUNEXT_NO_PROGRESS));
    };

    let saved_goals = state.goals.clone();
    state.metas_mut().push_scope();
    match funext_chain_then_propext(state, arity) {
        Ok(()) => {
            state.metas_mut().commit();
            Ok(())
        }
        Err(e) => {
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            state.metas_mut().pop_scope();
            Err(e)
        }
    }
}

/// One `funext` per leading Pi binder, then [`try_propext_bridge`] on the
/// pointwise `@Eq Prop` goal. Split out of [`try_funext_propext_bridge`] so
/// its speculative scope wraps the whole chain as one unit.
fn funext_chain_then_propext(state: &mut ProofState, arity: usize) -> TacticResult {
    // `funext` intros its own binder, so each iteration sees the remaining Pi
    // chain; per-depth names keep the generated binders distinct.
    for i in 0..arity {
        funext(
            state,
            &clean_parser::SurfaceName::from_name(Name::anon().str("x_grind_funext").num(i as u64)),
        )?;
    }
    try_propext_bridge(state)
}

/// Extensionality: rewrite a function equality at ANY codomain to its
/// pointwise form with one `funext` per leading binder, and run grind on the
/// result. Returns `true` only if the pointwise goal CLOSED.
///
/// Lean's grind instantiates registered extensionality theorems on any `Eq`
/// whose sides are functions (`instantiateExtTheorem`,
/// `Lean/Meta/Tactic/Grind/Ext.lean`); `funext` is one of them. Clean's only
/// `funext` was [`try_funext_propext_bridge`], gated on a `Prop` codomain
/// because its terminator is `propext` — so `⊢ f = f'` at `∀ a, β a`
/// (`Function.hfunext`, `Subtype.surjective_restrict`) was never touched.
///
/// Speculative and bounded: `grind_core` runs at `depth + 1`, so the recursion
/// is capped by `config.max_depth` exactly as a case split is, and a goal that
/// is not an `Eq` at a Pi type never enters. One pass per binder, not a
/// fixpoint — `pi_arity` counts the WHOLE leading chain, so the pointwise goal
/// is no longer an `Eq` at a Pi and cannot re-enter.
pub(super) fn try_ext_then_grind(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> bool {
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let target = state.metas.instantiate(&goal.target);
    let args = target.get_app_args();
    let head = target.get_app_fn();
    let is_eq =
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Eq") && args.len() == 3;
    if !is_eq {
        return false;
    }
    let Some(arity) = pi_arity(args[0]) else {
        return false;
    };

    let saved_goals = state.goals.clone();
    let saved_splits = *splits_remaining;
    state.metas_mut().push_scope();
    let outcome = ext_chain_then_grind(state, config, depth, splits_remaining, arity, case_hyps);
    if std::env::var_os("CLEAN_GRIND_TRACE").is_some() {
        match &outcome {
            Ok(()) => eprintln!("grind-trace: ext closed at arity={arity}"),
            Err(e) => eprintln!("grind-trace: ext arity={arity} failed: {e:?}"),
        }
    }
    if outcome.is_ok() {
        state.metas_mut().commit();
        return true;
    }
    state.invalidate_tc_cache();
    state.goals = saved_goals;
    *splits_remaining = saved_splits;
    state.metas_mut().pop_scope();
    false
}

/// One `funext` per leading binder, then the grind core on the pointwise goal.
/// Split out of [`try_ext_then_grind`] so its rollback wraps the chain whole.
fn ext_chain_then_grind(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    arity: usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> TacticResult {
    for i in 0..arity {
        funext(
            state,
            &clean_parser::SurfaceName::from_name(Name::anon().str("x_grind_ext").num(i as u64)),
        )?;
    }
    grind_core(state, config, depth + 1, splits_remaining, case_hyps)
}

/// Cross the `Eq`/`HEq` spelling when both type arguments are the SAME.
///
/// `HEq` appears nowhere in grind's closer fan or in `cc.rs`, so
/// `h : HEq a b ⊢ a = b` reported "no progress" with the proof one `eq_of_heq`
/// away (`Function.hfunext`, `Subtype.heq_iff_coe_eq`). Lean handles `HEq`
/// inside congruence closure itself, where a homogeneous `HEq` is an ordinary
/// merge.
///
/// SOUNDNESS: it never coerces across UNEQUAL types. `eq_of_heq` and
/// `heq_of_eq` are kernel constants, `apply` type-checks the term and
/// `close_goal` re-checks it, so a wrong bridge fails closed — but the
/// syntactic equal-types guard is what keeps the bridge from even being
/// attempted at `@HEq α a β b` with `α ≠ β`, which is the only shape where a
/// coercion would be a real mistake (`Subtype.heq_iff_coe_heq` is exactly that
/// shape, and stays open rather than being answered wrongly).
pub(super) fn try_heq_bridge(state: &mut ProofState, config: &GrindConfig) -> bool {
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let target = state.metas.instantiate(&goal.target);
    let Some(bridge) = heq_bridge_for(&target, context_mentions_heq(&goal, &state.metas)) else {
        return false;
    };
    if state.env.get_const(&Name::from_string(bridge)).is_none() {
        return false;
    }

    let saved_goals = state.goals.clone();
    state.metas_mut().push_scope();
    let bridge_term = state.mk_const_str(bridge);
    // A NARROW fan, not `try_closers`: the bridged goal is discharged by a
    // hypothesis (`exact eq_of_heq h`) or by instantiating a quantified one
    // (`this : ∀ a, HEq (f a) (f' a)`), and running the arithmetic closers on
    // it would pay `cert_mathverse`/`omega` twice per equality goal.
    let closed = apply(state, bridge_term).is_ok()
        && (try_tactic_preserving_state(state, assumption)
            || try_triggered_solve_by_elim(state, config.solve_by_elim_depth)
            || try_tactic_preserving_state(state, |s| {
                solve_by_elim(s, config.solve_by_elim_depth)
            }));
    // THIS goal closed, not the whole state. `state.is_complete()` means
    // `goals.is_empty()`, and every branch of a case split runs `grind_core`
    // with its sibling branch still on the list — so the completeness test
    // made the bridge unreachable everywhere except a single-goal top level,
    // which is exactly where `Function.hfunext`-shaped rows do NOT sit.
    // `apply` replaces the front goal with one subgoal and the closers below
    // close it, so a net decrease is precisely "the bridge discharged it".
    if closed && state.goals.len() < saved_goals.len() {
        state.metas_mut().commit();
        return true;
    }
    state.invalidate_tc_cache();
    state.goals = saved_goals;
    state.metas_mut().pop_scope();
    false
}

/// Replace a non-`False` goal with `False` when the context can reach one, and
/// run grind on it. Returns `true` only if `False` was actually derived.
///
/// Lean's grind is a refutation prover: `intro`
/// (`Lean/Meta/Tactic/Grind/Intro.lean`) applies `MVarId.byContra?` whenever
/// the target is not `False`, so every search runs against `⊢ False`. Clean's
/// grind had no step that changed the goal at all, and the decisive
/// measurement is a pair differing only in the goal: with `hpq : p → ¬q`,
/// `hp : p`, `hq : q` in context, grind CLOSES `⊢ False` and FAILS on `⊢ r`.
///
/// `exfalso`, not `Classical.byContradiction`. The diagnosis proposed the
/// latter; the correction measured that a contradictory context ALREADY closes
/// an arbitrary goal when the contradiction is syntactic (`contradiction`
/// handles `¬q` beside `q`), and what is missing is a TARGET for the backward
/// searchers when reaching it takes a modus ponens. `False.elim` supplies
/// exactly that and adds no classical axiom to the proof's closure, where
/// `Classical.byContradiction` would add `Classical.choice` to every grind
/// proof.
///
/// GUARDED on the context holding something that could produce `False` — a
/// hypothesis whose conclusion, under its leading binders, IS `False`. Without
/// that guard every failing goal in every grind call would pay a second full
/// search over `⊢ False`, which nothing in that context can close.
pub(super) fn try_exfalso_then_grind(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> bool {
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let target = state.metas.instantiate(&goal.target);
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    if target == false_c || !context_can_reach_false(&goal, &state.metas) {
        return false;
    }

    let saved_goals = state.goals.clone();
    let saved_splits = *splits_remaining;
    state.metas_mut().push_scope();
    let outcome = exfalso(state)
        .and_then(|()| grind_core(state, config, depth + 1, splits_remaining, case_hyps));
    if outcome.is_ok() {
        state.metas_mut().commit();
        return true;
    }
    state.invalidate_tc_cache();
    state.goals = saved_goals;
    *splits_remaining = saved_splits;
    state.metas_mut().pop_scope();
    false
}

/// Does the context hold a hypothesis that could PRODUCE `False` — one whose
/// conclusion, under its leading binders, is `False` or a negation?
///
/// The gate on [`try_exfalso_then_grind`]. It is about the CONCLUSION, not
/// about the hypothesis itself being a negation: `hpq : p → ¬q` is exactly the
/// shape `dite_dite_comm`'s branch needs, and reaching its `False` takes two
/// applications.
///
/// BOTH spellings of the negation count. `¬q` is definitionally `q → False`,
/// but which one a hypothesis carries is a matter of how it was written — a
/// `by_cases` branch gets the `Pi` form, a source `¬q` stays an application of
/// `Not`. Peeling binders and testing only for a literal `False` misses the
/// second, which is what `p → ¬q` is, and the gate then declined the one shape
/// the step exists for.
fn context_can_reach_false(goal: &Goal, metas: &MetaState) -> bool {
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    goal.local_ctx.iter().any(|decl| {
        let ty = metas.instantiate(&decl.ty);
        let mut cursor = &ty;
        while let ExprKind::Pi(_, _, body) = cursor.kind() {
            cursor = body.as_ref();
        }
        if *cursor == false_c {
            return true;
        }
        matches!(cursor.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "Not")
            && cursor.get_app_args().len() == 1
    })
}

/// Split an `Iff` goal with `Iff.intro` and run grind on both halves.
///
/// `tauto` closes a purely propositional `a ↔ b`, but an `Iff` whose halves are
/// EQUATIONS is beyond it while each half closes on its own — measured, the
/// hand route `constructor <;> grind` passes where bare `grind` does not. Lean
/// reaches the same place from the other side: its refutation mode puts the
/// negated `Iff` in the context, where `Grind/Cases.lean` splits it like any
/// other fact.
pub(super) fn try_iff_split_then_grind(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> bool {
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let target = state.metas.instantiate(&goal.target);
    if match_iff(&target).is_none() {
        return false;
    }

    let saved_goals = state.goals.clone();
    let saved_splits = *splits_remaining;
    state.metas_mut().push_scope();
    let outcome = constructor(state).and_then(|()| {
        close_all_goals_recursive_with(state, config, depth + 1, splits_remaining, case_hyps)
    });
    if outcome.is_ok() {
        state.metas_mut().commit();
        return true;
    }
    state.invalidate_tc_cache();
    state.goals = saved_goals;
    *splits_remaining = saved_splits;
    state.metas_mut().pop_scope();
    false
}

/// Which bridge constant, if any, crosses this target's `Eq`/`HEq` spelling?
///
/// Pure so the SOUNDNESS-relevant half — that `@HEq α a β b` with `α ≠ β` is
/// declined — is pinned by a test that needs no proof state. Syntactic
/// equality of the two type arguments is the guard; it is deliberately not a
/// `is_def_eq` call, because a bridge that has to REASON about the two types
/// being equal is exactly the one that should be left to a future increment
/// rather than guessed at here.
pub(crate) fn heq_bridge_for(target: &Expr, context_has_heq: bool) -> Option<&'static str> {
    let args = target.get_app_args();
    let ExprKind::Const(head_name, _) = target.get_app_fn().kind() else {
        return None;
    };
    match head_name.to_string().as_str() {
        // `⊢ a = b` from an `HEq` fact: `eq_of_heq : HEq a b → a = b`. Only
        // worth a try when the context HOLDS an `HEq` — otherwise every
        // failing equality goal in every grind call would pay for a second
        // closer pass over a goal nothing can discharge.
        "Eq" if args.len() == 3 && context_has_heq => Some("eq_of_heq"),
        // `⊢ HEq a b` at ONE type: `heq_of_eq : a = b → HEq a b`.
        "HEq" if args.len() == 4 && args[0] == args[2] => Some("heq_of_eq"),
        _ => None,
    }
}

/// Does any hypothesis of `goal` mention `HEq`, under leading binders or not?
///
/// The gate on the `Eq → HEq` direction of [`try_heq_bridge`]: without an
/// `HEq` fact in the context the bridged goal is unreachable, and attempting
/// it would cost a second closer pass on every equality goal grind fails on.
fn context_mentions_heq(goal: &Goal, metas: &MetaState) -> bool {
    goal.local_ctx
        .iter()
        .any(|decl| mentions_heq(&metas.instantiate(&decl.ty)))
}

fn mentions_heq(e: &Expr) -> bool {
    stack_safe(|| match e.kind() {
        ExprKind::Const(n, _) => n.to_string() == "HEq",
        ExprKind::App(f, a) => mentions_heq(f) || mentions_heq(a),
        ExprKind::Lam(_, d, b) | ExprKind::Pi(_, d, b) => mentions_heq(d) || mentions_heq(b),
        ExprKind::Let(_, t, v, b, _) => mentions_heq(t) || mentions_heq(v) || mentions_heq(b),
        ExprKind::MData(_, i) | ExprKind::Proj(_, _, i) => mentions_heq(i),
        _ => false,
    })
}

/// Number of leading Pi binders on a type, at ANY codomain. `None` for a type
/// that is not a function type, so a non-function equality never reaches
/// `funext`.
fn pi_arity(ty: &Expr) -> Option<usize> {
    let mut ty = ty;
    let mut arity = 0usize;
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        arity += 1;
        ty = body.as_ref();
    }
    (arity > 0).then_some(arity)
}

/// Number of leading Pi binders on a type whose codomain chain ends in
/// `Prop`. `Some(n ≥ 1)` only for that shape: bare `Prop` is `None` (that
/// goal belongs to [`try_propext_bridge`], which already ran), as is any
/// chain ending in a non-`Prop` codomain (`funext` alone would yield no
/// `Iff` for the closer fan — leave such goals to CC/rfl).
fn pi_arity_into_prop(ty: &Expr) -> Option<usize> {
    let mut ty = ty;
    let mut arity = 0usize;
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        arity += 1;
        ty = body.as_ref();
    }
    (arity > 0 && matches!(ty.kind(), ExprKind::Sort(l) if l.is_zero())).then_some(arity)
}

/// Normalize hypothesis equalities by substituting known variable equalities.
///
/// If the local context contains `h : x = 5`, replaces `x` throughout the goal.
/// Non-fatal — swallows errors since normalization is opportunistic.
pub(super) fn grind_normalize(state: &mut ProofState) {
    let _ = subst_vars(state);
}

#[cfg(test)]
#[path = "grind_funext_tests.rs"]
mod grind_funext_tests;
