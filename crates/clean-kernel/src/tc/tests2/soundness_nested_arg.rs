// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial soundness regression tests for the trusted kernel core.
//!
//! These tests reproduce confirmed soundness holes where the kernel accepted
//! proofs of `False` because subterm type-inference skipped nested argument
//! checks (App-arg, Let-value), a universe-depth fallback returned `Sort 0`
//! instead of erroring, and unsafe/partial constants slipped through in
//! argument position. Each `_rejects` test asserts `Err`; the brecOn/well-typed
//! tests assert `Ok` to guarantee the hardening did not over-reject valid
//! recursion terms.
//!
//! Holes closed (see commit body):
//!   (a) NESTED-APP False  — deep-check App argument in check mode
//!   (b) LET False         — deep-check Let value in check mode
//!   (c) DEPTH universe    — Pi-nesting > 64 hard-errors (no `Sort 0` fallback)
//!   (d) UNSAFE/PARTIAL     — whole-term unsafe/partial backstop in `add_decl`
//!   (e) brecOn regression — valid recursion terms still accepted

use super::*;
use crate::env::Declaration;
use crate::level::Level;

mod cert_path;

/// Build a minimal environment with True / False (and Eq, pulled in by
/// `init_true_false`). This gives us `True`, `True.intro`, `False`.
fn make_true_false_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false()
        .expect("invariant: True/False initialize");
    env
}

/// `myid : (A : Prop) -> A -> A := fun A x => x`
///
/// A polymorphic identity over `Prop`. When applied to `False` it yields
/// `False -> False`; applying it to a non-`False` proof is the adversarial
/// payload (the argument check is what must reject).
fn add_myid(env: &mut Environment) {
    let prop = Expr::prop();
    // type: (A : Prop) -> A -> A
    let ty = Expr::pi(
        BinderInfo::Implicit,
        prop.clone(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    // value: fun (A : Prop) (x : A) => x
    let val = Expr::lam(
        BinderInfo::Implicit,
        prop,
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myid"),
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .expect("myid is well-typed");
}

/// `gff : False -> False := fun x => x`
///
/// The identity on `False`. Used as the outer function so that the overall
/// theorem type is `False`; the unsoundness must come from the *argument*.
fn add_gff(env: &mut Environment) {
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let ty = Expr::arrow(false_const.clone(), false_const.clone());
    let val = Expr::lam(BinderInfo::Default, false_const, Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("gff"),
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .expect("gff is well-typed");
}

/// `myid False True.intro` — the ill-typed nested application.
///
/// `myid False : False -> False`, but `True.intro : True`, so feeding
/// `True.intro` as the `(x : False)` argument is a type error that the kernel
/// historically skipped because App-argument inference forced `infer_only=true`.
fn bad_inner_app() -> Expr {
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("myid"), vec![]), false_const),
        true_intro,
    )
}

// ===========================================================================
// (a) NESTED-APP False — must REJECT
// ===========================================================================

/// Exploit (a): `Theorem t : False := gff (myid False True.intro)`.
///
/// The outer `gff` expects a `False`; its argument `myid False True.intro`
/// *infers* to `False` (from `myid`'s result type) but is internally ill-typed
/// because `True.intro : True ≠ False`. Before the fix the nested argument
/// check was skipped, so the proof of `False` was accepted. It MUST now error.
#[test]
fn nested_app_false_rejects() {
    let mut env = make_true_false_env();
    add_myid(&mut env);
    add_gff(&mut env);

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let proof = Expr::app(
        Expr::const_(Name::from_string("gff"), vec![]),
        bad_inner_app(),
    );

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("exploit_nested_app"),
        level_params: vec![],
        type_: false_const,
        value: proof,
    });
    assert!(
        result.is_err(),
        "kernel accepted a proof of False via nested App argument: {result:?}"
    );
}

/// Direct `check_type` form of (a): checking `myid False True.intro : False`
/// must reject, because the nested argument `True.intro` does not have type
/// `False`.
#[test]
fn nested_app_false_check_type_rejects() {
    let mut env = make_true_false_env();
    add_myid(&mut env);

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let tc = TypeChecker::new(&env);
    let result = tc.check_type(&bad_inner_app(), &false_const);
    assert!(
        result.is_err(),
        "check_type accepted ill-typed nested App argument: {result:?}"
    );
}

// ===========================================================================
// (b) LET False — must REJECT
// ===========================================================================

/// Exploit (b): `Theorem t : False := let v : False := myid False True.intro; gff v`.
///
/// The let *value* `myid False True.intro` is annotated as `False` but is
/// internally ill-typed (same nested-arg payload as (a)). Before the fix the
/// let-value's nested App argument was inferred with `infer_only=true`, hiding
/// the mismatch. It MUST now error.
#[test]
fn let_false_rejects() {
    let mut env = make_true_false_env();
    add_myid(&mut env);
    add_gff(&mut env);

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    // body: gff v   (v = BVar(0), the let-bound variable)
    let body = Expr::app(
        Expr::const_(Name::from_string("gff"), vec![]),
        Expr::bvar(0),
    );
    let proof = Expr::let_named(
        Name::from_string("v"),
        false_const.clone(),
        bad_inner_app(),
        body,
        false,
    );

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("exploit_let"),
        level_params: vec![],
        type_: false_const,
        value: proof,
    });
    assert!(
        result.is_err(),
        "kernel accepted a proof of False via Let value: {result:?}"
    );
}

// ===========================================================================
// (c) DEPTH universe — must REJECT (not return Sort 0)
// ===========================================================================

/// (c) DEPTH universe: `infer_sort_inner` used to return `Ok(Level::zero())` past
/// `INFER_SORT_MAX_DEPTH` — an unsound collapse if ever reached. That fallback now
/// hard-errors (`SortDepthExceeded`) as defense in depth. The cap is unreachable
/// for ordinary terms, so a deeply-curried Pi type is sorted CORRECTLY, never
/// collapsed to `Sort 0`.
#[test]
fn deep_pi_type_sort_not_collapsed() {
    // A const whose *declared type* is a > 64-deep curried Pi. `infer_type(const)`
    // returns that type verbatim, so `infer_sort` must UNWIND it past the depth
    // cap (unlike a deep Pi *type expression*, whose sort `infer_type` computes
    // directly via imax). Before the fix the unwind silently returned `Sort 0`.
    let mut env = Environment::new();
    let prop = Expr::prop();
    let mut ty = prop.clone();
    for _ in 0..200 {
        ty = Expr::pi(BinderInfo::Default, prop.clone(), ty);
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("deep_f"),
        level_params: vec![],
        type_: ty,
    })
    .expect("the deep Pi type itself validates (its sort is computed directly)");

    let tc = TypeChecker::new(&env);
    let result = tc.infer_sort(&Expr::const_(Name::from_string("deep_f"), vec![]));
    // The deep Pi type's sort is computed correctly (Prop-impredicative ⇒ Sort 1),
    // never silently COLLAPSED to Sort 0. The unsound depth-cap `Sort 0` fallback
    // is unreachable for ordinary terms (infer_type yields a Pi body's sort
    // directly) and now hard-errors rather than collapsing, as defense in depth.
    match &result {
        Ok(lvl) => assert!(
            !lvl.is_zero(),
            "deep Pi type was unsoundly collapsed to Sort 0: {result:?}"
        ),
        Err(e) => panic!("infer_sort on a deep Pi-typed const should compute a sort: {e:?}"),
    }
}

// ===========================================================================
// (d) UNSAFE / PARTIAL const in argument position — must REJECT
// ===========================================================================

/// Exploit (d): a safe declaration referencing an `unsafe` constant buried in
/// argument position.
///
/// `evil` is declared then marked `unsafe`. A subsequent *safe* definition
/// `uses_unsafe := myid evil evil` (where `evil` appears in argument position)
/// must be rejected by the whole-term unsafe backstop in `add_decl`.
#[test]
fn unsafe_const_in_arg_rejects() {
    let mut env = make_true_false_env();
    add_myid(&mut env);

    // evil : Prop  (axiom), then marked unsafe.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("evil"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("evil axiom is well-typed before marking");
    env.mark_unsafe(Name::from_string("evil"));

    // uses_unsafe : Prop := myid evil evil
    //   `evil` rides in argument position of `myid`.
    let prop = Expr::prop();
    let evil = Expr::const_(Name::from_string("evil"), vec![]);
    let value = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("myid"), vec![]),
            evil.clone(),
        ),
        evil,
    );
    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("uses_unsafe"),
        level_params: vec![],
        type_: prop,
        value,
        is_reducible: false,
    });
    assert!(
        result.is_err(),
        "safe declaration referencing an unsafe const in argument position was accepted: {result:?}"
    );
}

/// (d') Partial-const variant: a safe declaration referencing a `partial`
/// constant in argument position must also be rejected by the backstop.
#[test]
fn partial_const_in_arg_rejects() {
    let mut env = make_true_false_env();
    add_myid(&mut env);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("loopy"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("loopy axiom is well-typed before marking");
    env.mark_partial(Name::from_string("loopy"));

    let prop = Expr::prop();
    let loopy = Expr::const_(Name::from_string("loopy"), vec![]);
    let value = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("myid"), vec![]),
            loopy.clone(),
        ),
        loopy,
    );
    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("uses_partial"),
        level_params: vec![],
        type_: prop,
        value,
        is_reducible: false,
    });
    assert!(
        result.is_err(),
        "safe declaration referencing a partial const in argument position was accepted: {result:?}"
    );
}

// ===========================================================================
// Positive controls — well-typed terms must still be ACCEPTED
// ===========================================================================

/// Positive control for (a): the *honest* version `gff (myid False h)` where
/// `h : False` (a hypothesis) must type-check. We model `h` via a lambda and
/// check `fun (h : False) => gff (myid False h)` against `False -> False`.
#[test]
fn well_typed_nested_app_accepts() {
    let mut env = make_true_false_env();
    add_myid(&mut env);
    add_gff(&mut env);

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    // fun (h : False) => gff (myid False h)
    let inner = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("myid"), vec![]),
            false_const.clone(),
        ),
        Expr::bvar(0),
    );
    let body = Expr::app(Expr::const_(Name::from_string("gff"), vec![]), inner);
    let lam = Expr::lam(BinderInfo::Default, false_const.clone(), body);
    let expected = Expr::arrow(false_const.clone(), false_const);

    let tc = TypeChecker::new(&env);
    let result = tc.check_type(&lam, &expected);
    assert!(
        result.is_ok(),
        "well-typed nested App was wrongly rejected: {result:?}"
    );
}

/// Positive control for (b): an honest let `let v : False := h; gff v` inside a
/// lambda binding `h : False` must type-check.
#[test]
fn well_typed_let_accepts() {
    let mut env = make_true_false_env();
    add_myid(&mut env);
    add_gff(&mut env);

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    // fun (h : False) => let v : False := h; gff v
    //   h = BVar(0) inside the lambda; inside the let body, v = BVar(0), h = BVar(1).
    let let_expr = Expr::let_named(
        Name::from_string("v"),
        false_const.clone(),
        Expr::bvar(0), // h
        Expr::app(
            Expr::const_(Name::from_string("gff"), vec![]),
            Expr::bvar(0),
        ), // gff v
        false,
    );
    let lam = Expr::lam(BinderInfo::Default, false_const.clone(), let_expr);
    let expected = Expr::arrow(false_const.clone(), false_const);

    let tc = TypeChecker::new(&env);
    let result = tc.check_type(&lam, &expected);
    assert!(
        result.is_ok(),
        "well-typed Let was wrongly rejected: {result:?}"
    );
}

/// Positive control for (c): a moderately deep Pi (well under the depth cap)
/// ending in a real `Sort` must still produce a level, not error.
#[test]
fn shallow_pi_universe_accepts() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let big_sort = Expr::sort(Level::succ(Level::succ(Level::zero())));
    let mut ty = big_sort.clone();
    for _ in 0..8 {
        ty = Expr::pi(BinderInfo::Default, big_sort.clone(), ty);
    }
    let result = tc.infer_sort(&ty);
    assert!(
        result.is_ok(),
        "shallow Pi (depth 8) was wrongly rejected by infer_sort: {result:?}"
    );
}

// ===========================================================================
// (e) brecOn / below regression — valid recursion must still type-check
// ===========================================================================

/// Positive control (e): the canonical `Nat.below` motive application that the
/// `#3134` infer_only wrapper was originally added to protect. With the deep
/// App-argument check restored, this valid term must still type-check.
///
/// We construct `fun (motive : Nat -> Prop) (n : Nat) => motive n` checked
/// against `(Nat -> Prop) -> Nat -> Prop`. The body is an App whose argument
/// `n : Nat` matches the motive's domain — a valid recursion-shaped App that
/// must not be falsely rejected by the deepened argument check.
#[test]
fn brecon_below_shaped_app_accepts() {
    let mut env = Environment::new();
    env.init_nat().expect("Nat initializes");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::prop();
    let motive_ty = Expr::arrow(nat.clone(), prop.clone());

    // fun (motive : Nat -> Prop) (n : Nat) => motive n
    let body = Expr::app(Expr::bvar(1), Expr::bvar(0));
    let lam = Expr::lam(
        BinderInfo::Default,
        motive_ty.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), body),
    );
    let expected = Expr::arrow(motive_ty, Expr::arrow(nat, prop));

    let tc = TypeChecker::new(&env);
    let result = tc.check_type(&lam, &expected);
    assert!(
        result.is_ok(),
        "valid recursion-shaped App was wrongly rejected: {result:?}"
    );
}
