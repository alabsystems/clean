// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit coverage for `assignment.rs`: the `ctxApprox` port and
//! `checkTypesAndAssign`, at the unifier. The end-to-end rows these ports
//! repair are pinned in `crate::tests_pkg4_unifier`.
//!
//! Root cause 1, unifier level: where `ctxApprox` must REFUSE. Each arm is a
//! place Lean's `checkMVar` throws (or where Clean's representation differs
//! from Lean's), and each must leave the constraint `Stuck` with NOTHING
//! narrowed — a narrowing that survived a refusal would forbid a metavariable a
//! solution nobody ruled out.

use crate::unify::{MetaId, MetaState, Unifier, UnifyResult};
use clean_kernel::name::Name;
use clean_kernel::{BinderData, Environment, Expr, FVarId, LocalContext};
use clean_parser::SurfaceName;

type Scope = Vec<(SurfaceName, FVarId, Expr)>;

fn local_name(text: &str) -> SurfaceName {
    SurfaceName::component(text, false)
}

fn meta(id: MetaId) -> Expr {
    Expr::fvar(MetaState::to_fvar(id))
}

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Locals `A : Type`, `P : A → Type`, `x : A`, in that order. Returns the
/// unifier context (with `x` LIVE when `x_live`), the outer scope `[A, P]`
/// and the inner scope `[A, P, x]`, plus `A` and `x`.
fn fixture(x_live: bool) -> (Environment, LocalContext, Scope, Scope, Expr, Expr) {
    let env = Environment::with_prelude();
    let mut ctx = LocalContext::new();
    let a = ctx.push(Name::from_string("A"), Expr::type_(), BinderData::default());
    let p_ty = Expr::pi(BinderData::default(), Expr::fvar(a), Expr::type_());
    let p = ctx.push(Name::from_string("P"), p_ty.clone(), BinderData::default());
    let x = if x_live {
        ctx.push(Name::from_string("x"), Expr::fvar(a), BinderData::default())
    } else {
        // A local that was abstracted out of the term again: it no longer
        // exists in the context the constraint is posed in.
        let mut scratch = ctx.clone();
        scratch.push(Name::from_string("x"), Expr::fvar(a), BinderData::default())
    };
    let outer = vec![
        (local_name("A"), a, Expr::type_()),
        (local_name("P"), p, p_ty),
    ];
    let mut inner = outer.clone();
    inner.push((local_name("x"), x, Expr::fvar(a)));
    (env, ctx, outer, inner, Expr::fvar(a), Expr::fvar(x))
}

fn scope_of(metas: &MetaState, id: MetaId) -> Vec<FVarId> {
    metas
        .get(id)
        .map(|m| m.locals.iter().map(|(_, fvar, _)| *fvar).collect())
        .unwrap_or_default()
}

/// The positive arm, at the unifier: `?m =?= (A → ?n)` with `?n` natural,
/// typed in `?m`'s context, and minted under the live binder `x`. `?m` is
/// solved and `?n` is narrowed to `?m`'s scope — not assigned.
#[test]
fn test_ctx_approx_natural_inner_meta_is_narrowed_and_outer_solved() {
    let (env, ctx, outer, inner, a, _x) = fixture(true);
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(Expr::type_(), outer.clone());
    let n = metas.fresh_natural_with_locals_at(Expr::type_(), inner, None);
    let rhs = Expr::pi(BinderData::default(), a, meta(n));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&meta(m), &rhs);
    assert!(
        matches!(result, UnifyResult::Success),
        "ctxApprox must solve `?m := A → ?n`: {result:?}"
    );
    assert!(metas.is_assigned(m), "`?m` must be assigned");
    assert!(!metas.is_assigned(n), "`?n` is narrowed, never assigned");
    let outer_ids: Vec<FVarId> = outer.iter().map(|(_, f, _)| *f).collect();
    assert_eq!(
        scope_of(&metas, n),
        outer_ids,
        "`?n` must be narrowed to exactly `?m`'s scope"
    );
}

/// Lean's `check mvarDecl.type`: `?k : P x` cannot live without `x`, so
/// `?m := Nat.succ ?k` is refused and `?k` keeps its scope.
#[test]
fn test_ctx_approx_inner_meta_whose_type_needs_the_local_stays_stuck() {
    let (env, ctx, outer, inner, _a, x) = fixture(true);
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(nat(), outer);
    let p = inner[1].1;
    let k_ty = Expr::app(Expr::fvar(p), x);
    let k = metas.fresh_natural_with_locals_at(k_ty, inner.clone(), None);
    let rhs = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), meta(k));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&meta(m), &rhs);
    assert!(
        !matches!(result, UnifyResult::Success),
        "a metavariable whose TYPE mentions the dropped local must not be narrowed: {result:?}"
    );
    assert!(!metas.is_assigned(m), "`?m` must stay unassigned");
    assert_eq!(
        scope_of(&metas, k).len(),
        inner.len(),
        "`?k` must keep its scope"
    );
}

/// Lean refuses a synthetic-opaque metavariable; Clean refuses every
/// metavariable not minted natural (a pending instance, a tactic goal).
#[test]
fn test_ctx_approx_opaque_inner_meta_stays_stuck() {
    let (env, ctx, outer, inner, a, _x) = fixture(true);
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(Expr::type_(), outer);
    let n = metas.fresh_with_locals(Expr::type_(), inner.clone());
    let rhs = Expr::pi(BinderData::default(), a, meta(n));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&meta(m), &rhs);
    assert!(
        matches!(result, UnifyResult::Stuck),
        "an OPAQUE inner metavariable must keep the constraint Stuck: {result:?}"
    );
    assert_eq!(
        scope_of(&metas, n).len(),
        inner.len(),
        "`?n` must keep its scope"
    );
}

/// The local `?n` would lose is not live — the shape `fun x => ?n` leaves
/// behind, which Lean never meets raw — so narrowing would forbid `?n` the
/// bound variable it may still need.
#[test]
fn test_ctx_approx_dead_extra_local_stays_stuck() {
    let (env, ctx, outer, inner, a, _x) = fixture(false);
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(Expr::type_(), outer);
    let n = metas.fresh_natural_with_locals_at(Expr::type_(), inner.clone(), None);
    let rhs = Expr::pi(BinderData::default(), a, meta(n));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&meta(m), &rhs);
    assert!(
        matches!(result, UnifyResult::Stuck),
        "a dead extra local must keep the constraint Stuck: {result:?}"
    );
    assert_eq!(
        scope_of(&metas, n).len(),
        inner.len(),
        "`?n` must keep its scope"
    );
}

/// Two widening metavariables, the first narrowable and the second not:
/// the refusal must roll the first narrowing back.
#[test]
fn test_ctx_approx_refusal_rolls_back_earlier_narrowing() {
    let (env, ctx, outer, inner, _a, _x) = fixture(true);
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(Expr::type_(), outer);
    let n1 = metas.fresh_natural_with_locals_at(Expr::type_(), inner.clone(), None);
    let n2 = metas.fresh_with_locals(Expr::type_(), inner.clone());
    let rhs = Expr::pi(BinderData::default(), meta(n1), meta(n2));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&meta(m), &rhs);
    assert!(
        matches!(result, UnifyResult::Stuck),
        "one refused metavariable keeps the whole constraint Stuck: {result:?}"
    );
    assert_eq!(
        scope_of(&metas, n1).len(),
        inner.len(),
        "the narrowing of `?n1` must be rolled back with the refusal"
    );
}

/// C2 at the unifier: `?f : ?α → Nat` assigned `f : Bool → Nat` solves
/// `?α := Bool` through the TYPES, the only place `?α` occurs.
#[test]
fn test_check_types_and_assign_solves_implicit_in_meta_type() {
    let env = Environment::with_prelude();
    let mut ctx = LocalContext::new();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let f_ty = Expr::pi(BinderData::default(), bool_ty.clone(), nat());
    let f = ctx.push(Name::from_string("f"), f_ty.clone(), BinderData::default());
    let scope = vec![(local_name("f"), f, f_ty)];
    let mut metas = MetaState::new();
    let alpha = metas.fresh_natural_with_locals_at(Expr::type_(), scope.clone(), None);
    let f_meta_ty = Expr::pi(BinderData::default(), meta(alpha), nat());
    let f_meta = metas.fresh_natural_with_locals_at(f_meta_ty, scope, None);
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&meta(f_meta), &Expr::fvar(f));
    assert!(
        matches!(result, UnifyResult::Success),
        "`?f := f`: {result:?}"
    );
    assert_eq!(
        metas.get_assignment(alpha),
        Some(&bool_ty),
        "`?α` must be solved from `?f`'s type"
    );
}

/// The undo record's real consumer. `approximate_context` COMMITS its own
/// scope when it succeeds, so the narrowing lands in whatever scope the CALLER
/// holds — a speculative elaboration (the no-expected-type lane of a body, an
/// unreduced-first attempt) that may still be rolled back. Popping that scope
/// must restore both halves: `?m` unassigned AND `?n` back at its wider scope.
/// A narrowing that outlived the rollback would forbid `?n` the bound `x` in
/// the lane that runs next, for an assignment that no longer exists.
#[test]
fn test_ctx_approx_committed_narrowing_is_undone_by_enclosing_rollback() {
    let (env, ctx, outer, inner, a, _x) = fixture(true);
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(Expr::type_(), outer);
    let n = metas.fresh_natural_with_locals_at(Expr::type_(), inner.clone(), None);
    let rhs = Expr::pi(BinderData::default(), a, meta(n));

    metas.push_scope();
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&meta(m), &rhs);
    assert!(
        matches!(result, UnifyResult::Success),
        "the speculative attempt itself must succeed: {result:?}"
    );
    assert_ne!(
        scope_of(&metas, n).len(),
        inner.len(),
        "the arm is vacuous unless the attempt really narrowed `?n`"
    );
    metas.pop_scope();

    assert!(!metas.is_assigned(m), "the rollback must unassign `?m`");
    let inner_ids: Vec<FVarId> = inner.iter().map(|(_, f, _)| *f).collect();
    assert_eq!(
        scope_of(&metas, n),
        inner_ids,
        "the rollback must restore `?n`'s full scope, bound `x` included"
    );
}
