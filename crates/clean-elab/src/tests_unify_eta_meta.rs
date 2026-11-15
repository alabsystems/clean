// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for eta unification when the lambda's body is headed by
//! an unsolved METAVARIABLE — `fun x => ?m x =?= t`.
//!
//! Queue-C brick 2 (`docs/plans/BRICK_QUEUE_2026-08-31-C.md` §7.2), the census
//! row `Subtype.coe_injective` at `Mathlib/Data/Subtype.lean:80`:
//!
//! ```text
//! Subtype.coe_injective: elaboration error at line 80: Type mismatch:
//!   expected Function.Injective (Subtype fvar#0 fvar#1) fvar#0
//!            (fun (x : Subtype fvar#0 fvar#1) => Subtype.val fvar#0 fvar#1 x),
//!   got (x : Subtype fvar#0 fvar#1) -> (x1 : Subtype fvar#0 fvar#1) ->
//!       Subtype.val fvar#0 (fun (x2 : fvar#0) => fvar#9223372036854775812 x2) x
//!     = Subtype.val fvar#0 (fun (x2 : fvar#0) => fvar#9223372036854775812 x2) x1
//!     -> x = x1
//! ```
//!
//! `fvar#9223372036854775812` is `2^63 + 4` — a metavariable, since metas are
//! bit-63 fvars. The queue read this row as "`Function.Injective` is not being
//! unfolded to its Pi form before comparison". That reading is REFUTED below:
//! the unfolding happens (the "got" side is already the Pi form). What never
//! happened is the eta step that solves `?p`.
//!
//! ## The mechanism
//!
//! `Subtype.ext`'s binders are spelled `{a1 a2 : {x // p x}}`, and `{x // p x}`
//! elaborates to `Subtype (fun x => p x)` — Lean's binder notation eta-expands
//! the predicate. Applying it where the argument's type is spelled `Subtype q`
//! therefore raises `Subtype α (fun x => ?p x) =?= Subtype α q`, i.e.
//! `fun x => ?p x =?= q`, whose only solution is `?p := q` by eta.
//!
//! `unify_core_inner` had no eta arm. A `Lam` against a non-`Lam` fell through
//! to `try_kernel_def_eq`, and the kernel's eta (`TypeChecker::
//! try_eta_expansion_impl`) cannot assign a metavariable — it compares
//! `?p x` against `q x` as two distinct fvars and says no. The verdict Clean
//! printed was the raw shape bail:
//!
//! ```text
//! cannot unify expressions of different shape: Discriminant(1) vs Discriminant(5)
//! ```
//!
//! (`Discriminant(1)` is `ExprKind::Lam`, `Discriminant(5)` is
//! `ExprKind::FVar`.)
//!
//! ## Ground truth, taken from the pinned toolchain
//!
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean` with
//! `set_option pp.parens true`, no Mathlib on `LEAN_PATH`:
//!
//! ```lean
//! axiom mkAny {α : Sort u} {p : α → Prop} (s : { x // p x }) : Nat
//! def t1 {α : Sort u} {q : α → Prop} (s : Subtype q) : Nat := mkAny s
//! #print t1
//! ```
//! ```text
//! def t1.{u} : {α : (Sort u)} → ({q : (α → Prop)} → ((Subtype q) → Nat)) :=
//! fun {α} {q} s => (mkAny s)
//! ```
//!
//! Lean accepts it and solves `?p := q`. Clean rejected it.
//!
//! ## Why the arms are shaped this way
//!
//! Eta needs a DOMAIN for the lambda it builds around the non-lambda side, and
//! there are two places to get one:
//!
//! * from the non-lambda side's own inferred type (what the kernel and
//!   `Lean.Meta.isDefEqEta` do), or
//! * from the lambda's binder — the convenient approximation, which needs no
//!   type inference at all and passes every positive arm.
//!
//! The approximation is wrong, and the last two arms below are what refuse it:
//! it eta-expands terms that are not functions and terms whose domain differs,
//! so `fun (x : Nat) => ?m x =?= (5 : Nat)` becomes `?m x =?= 5 x` and the
//! Miller solver *succeeds*, burying `?m := fun x => 5 x`. A unifier that
//! accepts an ill-typed pair does not become sound because the kernel rechecks
//! it later — it loses the metavariable to a junk solution first, and every
//! later constraint on `?m` then fails somewhere else entirely.
//!
//! | arm | must be | with the fix reverted | with the approximation |
//! |---|---|---|---|
//! | `fun x => f x =?= f` (no meta) | GREEN | stays GREEN | GREEN |
//! | `fun x => ?m x =?= q` | GREEN | **RED** | GREEN |
//! | `q =?= fun x => ?m x` (swapped) | GREEN | **RED** | GREEN |
//! | `fun x => ?m x =?= 5` (not a function) | RED | RED | **GREEN — wrongly** |
//! | `fun (x : Nat) => ?m x =?= (g : Bool → Nat)` | RED | RED | **GREEN — wrongly** |
//!
//! ## And the attempt is SPECULATIVE
//!
//! The last arm covers the second thing this brick got wrong on the first try.
//! An eta attempt that fails can still have assigned metavariables and level
//! parameters on the way down — the Lam/Lam arm unifies the domains before it
//! looks at the bodies — and keeping those decides later constraints from a
//! path that was abandoned. The unscoped first version passed every arm above
//! and reddened 41 `codata_cmd_tests` plus
//! `codata_seed::tests::test_codata_seed_injects_on_demand`, because the leaked
//! assignment there was a LEVEL: `Codata.ilabel_stable` became `cannot assign
//! rigid universe parameter u := 0` and took 21 of the 71 seed declarations
//! with it. `test_a_refused_eta_rolls_back_what_it_assigned` is the local
//! witness for that; the codata suite is the one that found it.

use clean_kernel::name::Name;
use clean_kernel::{BinderData, Environment, Expr, FVarId, LocalContext};
use clean_parser::SurfaceName;

/// `(env, ctx, f, g, scope)` — see [`fixture`].
type Fixture = (Environment, LocalContext, Expr, Expr, Scope);
/// The local scope a fixture metavariable is minted under.
type Scope = Vec<(SurfaceName, FVarId, Expr)>;

use crate::unify::{MetaId, MetaState, Unifier, UnifyResult};

/// `Nat`, the one concrete type every arm shares.
fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// `Bool`, used only by the domain-mismatch arm.
fn bool_ty() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

/// `Nat -> Nat`.
fn nat_to_nat() -> Expr {
    Expr::pi(BinderData::default(), nat(), nat())
}

/// `fun (x : dom) => body`, with `body` written in terms of `BVar(0)`.
fn lam(dom: Expr, body: Expr) -> Expr {
    Expr::lam(BinderData::default(), dom, body)
}

fn meta_expr(id: MetaId) -> Expr {
    Expr::fvar(MetaState::to_fvar(id))
}

fn is_success(r: &UnifyResult) -> bool {
    matches!(r, UnifyResult::Success)
}

/// The fixture world: a prelude environment plus a local context holding the
/// rigid terms the arms unify against. Returns the context and the ids pushed,
/// in the order `(f : Nat -> Nat, g : Bool -> Nat)`.
fn fixture() -> Fixture {
    let env = Environment::with_prelude();
    let mut ctx = LocalContext::new();
    let g_ty = Expr::pi(BinderData::default(), bool_ty(), nat());
    let f = ctx.push(Name::from_string("f"), nat_to_nat(), BinderData::default());
    let g = ctx.push(Name::from_string("g"), g_ty.clone(), BinderData::default());
    // Every metavariable in this file is minted under BOTH fixture locals.
    // Metavariables carry the local context they were created under and refuse
    // to capture anything outside it, so a meta minted with `MetaState::fresh`
    // (empty scope) cannot be assigned `f` at all — the arms would then be
    // measuring the scope check rather than eta.
    let scope = vec![
        (SurfaceName::generated_path("f"), f, nat_to_nat()),
        (SurfaceName::generated_path("g"), g, g_ty),
    ];
    (env, ctx, Expr::fvar(f), Expr::fvar(g), scope)
}

// ---------------------------------------------------------------------------
// CONTROL — green before the fix and green after it.
// ---------------------------------------------------------------------------

/// `fun (x : Nat) => f x  =?=  f`, with no metavariable anywhere.
///
/// This is plain eta and the KERNEL already decided it, through
/// `try_kernel_def_eq`. It is the control that proves the arms below are about
/// the metavariable and not about eta as such: if this one ever goes red the
/// whole comparison has broken, not just the meta path.
#[test]
fn test_eta_without_a_metavariable_was_already_accepted() {
    let (env, ctx, f, _g, _scope) = fixture();
    let mut metas = MetaState::new();
    let lhs = lam(nat(), Expr::app(f.lift(1), Expr::bvar(0)));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&lhs, &f);
    assert!(
        is_success(&result),
        "plain eta `fun x => f x =?= f` must hold: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// THE DEFECT — red before the fix, green after it.
// ---------------------------------------------------------------------------

/// `fun (x : Nat) => ?m x  =?=  f`, the `Subtype.coe_injective` shape.
///
/// The unique solution is `?m := f`, and the assertion checks the ASSIGNMENT,
/// not just the verdict: a unifier that answered `Success` while leaving `?m`
/// unsolved would leave the caller with an unsolved-metavariable error later,
/// which is the failure mode this row already had.
#[test]
fn test_meta_headed_eta_solves_the_metavariable() {
    let (env, ctx, f, _g, scope) = fixture();
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(nat_to_nat(), scope);
    let lhs = lam(nat(), Expr::app(meta_expr(m).lift(1), Expr::bvar(0)));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&lhs, &f);
    assert!(
        is_success(&result),
        "`fun x => ?m x =?= f` must hold by eta: {result:?}"
    );
    assert!(
        metas.is_assigned(m),
        "eta must SOLVE `?m := f`, not merely accept the pair"
    );
}

/// The same constraint with the sides swapped: `f =?= fun (x : Nat) => ?m x`.
///
/// Eta is symmetric, and the match arms that implement it are two separate
/// arms — one per side — so a fix that only wired up one direction passes the
/// previous arm and fails this one.
#[test]
fn test_meta_headed_eta_is_symmetric() {
    let (env, ctx, f, _g, scope) = fixture();
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(nat_to_nat(), scope);
    let rhs = lam(nat(), Expr::app(meta_expr(m).lift(1), Expr::bvar(0)));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&f, &rhs);
    assert!(
        is_success(&result),
        "`f =?= fun x => ?m x` must hold by eta: {result:?}"
    );
    assert!(
        metas.is_assigned(m),
        "eta must SOLVE `?m := f` in the swapped direction too"
    );
}

// ---------------------------------------------------------------------------
// THE CONVENIENT APPROXIMATION — these must stay RED. Taking the eta domain
// from the LAMBDA's binder instead of from the non-lambda side's inferred type
// turns both of them green.
// ---------------------------------------------------------------------------

/// `fun (x : Nat) => ?m x  =?=  (5 : Nat)`.
///
/// `5` is not a function, so there is no eta expansion of it and the pair has
/// no solution. Taking the domain from the lambda would build the ill-typed
/// `fun (x : Nat) => 5 x`, hand the Miller solver `?m x =?= 5 x`, and assign
/// the junk solution `?m := fun x => 5 x`.
#[test]
fn test_eta_refuses_a_non_function_and_leaves_the_meta_unsolved() {
    let (env, ctx, _f, _g, scope) = fixture();
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(nat_to_nat(), scope);
    let lhs = lam(nat(), Expr::app(meta_expr(m).lift(1), Expr::bvar(0)));
    let five = Expr::nat_lit(5);
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&lhs, &five);
    assert!(
        !is_success(&result),
        "`fun x => ?m x =?= 5` has no solution — 5 is not a function: {result:?}"
    );
    assert!(
        !metas.is_assigned(m),
        "a refused eta must not leave `?m` bound to a junk solution"
    );
}

/// `fun (x : Nat) => ?m x  =?=  (g : Bool -> Nat)`.
///
/// `g` IS a function, so the approximation's expansion is well-formed in shape
/// and only the domain is wrong — which is exactly why this arm is needed
/// beside the previous one. Inferring `g`'s type yields the domain `Bool`, the
/// Lam/Lam arm then compares `Nat =?= Bool`, and the pair is correctly refused.
#[test]
fn test_eta_refuses_a_function_with_the_wrong_domain() {
    let (env, ctx, _f, g, scope) = fixture();
    let mut metas = MetaState::new();
    let m = metas.fresh_with_locals(nat_to_nat(), scope);
    let lhs = lam(nat(), Expr::app(meta_expr(m).lift(1), Expr::bvar(0)));
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&lhs, &g);
    assert!(
        !is_success(&result),
        "`fun (x : Nat) => ?m x =?= (g : Bool -> Nat)` must be refused: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// ROLLBACK — a REFUSED eta attempt must leave no trace.
// ---------------------------------------------------------------------------

/// `fun (x : ?d) => Nat.zero  =?=  (g : Bool -> Nat)`.
///
/// The attempt gets far enough to assign before it fails: eta-expanding `g`
/// gives `fun (x : Bool) => g x`, the Lam/Lam arm unifies the DOMAINS first and
/// solves `?d := Bool`, and only then do the bodies (`Nat.zero` against `g x`)
/// disagree. Without the rollback scope that `?d := Bool` survives the
/// rejection and every later constraint on `?d` is decided by an abandoned
/// path.
///
/// This arm is the cheap, local witness. The expensive one is already in the
/// suite and is what found the defect: `codata_seed::tests::
/// test_codata_seed_injects_on_demand` and the 41 `codata_cmd_tests`, where the
/// leaked assignment was a LEVEL — an unscoped eta turned
/// `Codata.ilabel_stable` into `cannot assign rigid universe parameter u := 0`
/// and took 21 of the 71 seed declarations with it.
#[test]
fn test_a_refused_eta_rolls_back_what_it_assigned() {
    let (env, ctx, _f, g, scope) = fixture();
    let mut metas = MetaState::new();
    // `?d : Type` — the lambda's DOMAIN, not its body.
    let d = metas.fresh_with_locals(Expr::type_(), scope);
    let lhs = lam(
        meta_expr(d),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let result = Unifier::with_env(&mut metas, &env, ctx).unify(&lhs, &g);
    assert!(
        !is_success(&result),
        "`fun (x : ?d) => Nat.zero =?= (g : Bool -> Nat)` must be refused: {result:?}"
    );
    assert!(
        !metas.is_assigned(d),
        "a refused eta attempt must roll back the `?d := Bool` it made on the \
         way down; leaving it decides later constraints from an abandoned path"
    );
}
