// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for the **interval connections** (`∧`, `∨`, reversal
//! `~`), the **regular path inverse** `sym_neg`, and **path induction `J`** with
//! its computing β-rule (Rung-1 deliverables 1–3).
//!
//! All terms are built directly as kernel `Expr`s; the reserved Expr-encoding
//! (`I.min`/`I.max`/`I.neg`, plus `Cofib.*`/`System.*`) is registered as
//! interval-valued axioms via [`register_kan_system_axioms`], so the existing
//! inference / certificate machinery accepts the encoding unchanged.
//!
//! The key soundness facts all **compute** (they are not asserted):
//! * the De Morgan lattice laws on `I` (`I.neg i0 ≡ i1`, `I.min i1 r ≡ r`, …);
//! * `sym_neg (refl a) ≡ refl a` *definitionally* (the regularity law the
//!   hcomp-based `sym` left open);
//! * `J P d a (refl a) ≡ d` *by reduction* (the deep constant-family `coe` rule
//!   collapsing the i-degenerate motive line).

// `J`, `P`, `y` are the standard HoTT names for path induction / the motive /
// the endpoint; keep them verbatim in the test names.
#![allow(non_snake_case)]

use super::*;

use crate::env::Declaration;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{path_J, path_refl, path_sym_neg, register_kan_system_axioms};
use std::sync::Arc;

/// A nullary constant `name`.
fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::<crate::level::Level>::new())
}

/// The interval type `I`.
fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}
fn i0() -> Expr {
    Expr::from_kind(ExprKind::CubicalI0)
}
fn i1() -> Expr {
    Expr::from_kind(ExprKind::CubicalI1)
}

/// Path application `p @ r`.
fn path_app(p: Expr, r: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(p),
        arg: Arc::new(r),
    })
}

/// Interval connections as reserved-const applications.
fn i_neg(x: Expr) -> Expr {
    Expr::app(cst("I.neg"), x)
}
fn i_min(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("I.min"), [x, y])
}
fn i_max(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("I.max"), [x, y])
}

/// The constant path family `λ _ : I, A`.
fn fam_a() -> Expr {
    Expr::lam(BinderInfo::Default, interval(), cst("A"))
}

/// `Path (λ_.A) left right`.
fn path_ty(left: Expr, right: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(fam_a()),
        left: Arc::new(left),
        right: Arc::new(right),
    })
}

/// Cubical environment with the Kan system axioms (incl. the interval
/// connections) plus `A : Type`, `a b : A`, `iv jv : I`,
/// `p : Path (λ_.A) a b`, the motive `P : Π(y:A). Path (λ_.A) a y → Type`, and
/// the base case `d : P a (refl a)`.
fn cubical_j_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("register kan system axioms");

    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };

    axiom("A", Expr::type_());
    axiom("a", cst("A"));
    axiom("b", cst("A"));
    axiom("iv", interval());
    axiom("jv", interval());

    // p : Path (λ_.A) a b.
    axiom("p", path_ty(cst("a"), cst("b")));

    // P : Π (y:A). (Path (λ_.A) a y) → Type   (motive; y = BVar(0) in the codomain).
    let motive_ty = Expr::pi(
        BinderInfo::Default,
        cst("A"),
        Expr::pi(
            BinderInfo::Default,
            path_ty(cst("a"), Expr::bvar(0)),
            Expr::type_(),
        ),
    );
    axiom("P", motive_ty);

    // d : P a (refl a).
    let refl_a = path_refl(&cst("a"));
    axiom("d", Expr::apps(cst("P"), [cst("a"), refl_a]));

    env
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 1 — interval connection laws (the De Morgan lattice on I)
// ─────────────────────────────────────────────────────────────────────────────

/// Reversal: `I.neg i0 ≡ i1`, `I.neg i1 ≡ i0`, `I.neg (I.neg r) ≡ r` (involutive).
#[test]
fn test_interval_neg_laws() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    assert!(tc.is_def_eq(&i_neg(i0()), &i1()), "~i0 ≡ i1");
    assert!(tc.is_def_eq(&i_neg(i1()), &i0()), "~i1 ≡ i0");
    // Involutivity on a *neutral* interval variable `iv`.
    assert!(
        tc.is_def_eq(&i_neg(i_neg(cst("iv"))), &cst("iv")),
        "~(~iv) ≡ iv"
    );
    // And the literal forms reduce on the nose.
    assert!(matches!(tc.whnf(&i_neg(i0())).kind(), ExprKind::CubicalI1));
    assert!(matches!(tc.whnf(&i_neg(i1())).kind(), ExprKind::CubicalI0));
}

/// Meet / join: `I.min i0 r ≡ i0`, `I.min i1 r ≡ r`, `I.max i1 r ≡ i1`,
/// `I.max i0 r ≡ r` (and idempotency `I.min r r ≡ r`), with `r` neutral.
#[test]
fn test_interval_min_max_laws() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    assert!(tc.is_def_eq(&i_min(i0(), cst("iv")), &i0()), "i0 ∧ r ≡ i0");
    assert!(
        tc.is_def_eq(&i_min(i1(), cst("iv")), &cst("iv")),
        "i1 ∧ r ≡ r"
    );
    assert!(tc.is_def_eq(&i_min(cst("iv"), i0()), &i0()), "r ∧ i0 ≡ i0");
    assert!(
        tc.is_def_eq(&i_min(cst("iv"), i1()), &cst("iv")),
        "r ∧ i1 ≡ r"
    );

    assert!(tc.is_def_eq(&i_max(i1(), cst("iv")), &i1()), "i1 ∨ r ≡ i1");
    assert!(
        tc.is_def_eq(&i_max(i0(), cst("iv")), &cst("iv")),
        "i0 ∨ r ≡ r"
    );
    assert!(tc.is_def_eq(&i_max(cst("iv"), i1()), &i1()), "r ∨ i1 ≡ i1");
    assert!(
        tc.is_def_eq(&i_max(cst("iv"), i0()), &cst("iv")),
        "r ∨ i0 ≡ r"
    );

    // Idempotency: same neutral on both sides collapses.
    assert!(
        tc.is_def_eq(&i_min(cst("iv"), cst("iv")), &cst("iv")),
        "r ∧ r ≡ r"
    );
    assert!(
        tc.is_def_eq(&i_max(cst("iv"), cst("iv")), &cst("iv")),
        "r ∨ r ≡ r"
    );

    // On the nose for the absorbing forms.
    assert!(matches!(
        tc.whnf(&i_min(i0(), cst("iv"))).kind(),
        ExprKind::CubicalI0
    ));
    assert!(matches!(
        tc.whnf(&i_max(i1(), cst("iv"))).kind(),
        ExprKind::CubicalI1
    ));
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 4 — no over-fire / Cubical-mode gating (placed here so the negative
// behaviour is established before the connections are *relied on*)
// ─────────────────────────────────────────────────────────────────────────────

/// Fully-neutral connection redexes stay **stuck**: `I.min iv jv` (two distinct
/// neutral interval variables), `I.max iv jv`, and `I.neg iv` do not reduce.
#[test]
fn test_interval_neutral_stays_stuck() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let stuck_head = |e: &Expr, name: &str| matches!(tc.whnf(e).get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string(name));

    assert!(
        stuck_head(&i_min(cst("iv"), cst("jv")), "I.min"),
        "min of distinct neutrals is stuck"
    );
    assert!(
        stuck_head(&i_max(cst("iv"), cst("jv")), "I.max"),
        "max of distinct neutrals is stuck"
    );
    assert!(
        stuck_head(&i_neg(cst("iv")), "I.neg"),
        "neg of a neutral is stuck"
    );
}

/// The connection reductions are **gated on Cubical mode** — in a classical
/// environment even the always-firing `I.min i0 i0` stays a neutral application.
#[test]
fn test_interval_connection_inert_outside_cubical() {
    let env = Environment::new(); // default (classical) mode
    let tc = TypeChecker::new(&env);

    let term = i_min(i0(), i0());
    let r = tc.whnf(&term);
    assert!(
        matches!(r.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("I.min")),
        "interval connections must not reduce outside Cubical mode, got {r:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 2 — the *regular* `sym` via reversal (fixes the regularity gap)
// ─────────────────────────────────────────────────────────────────────────────

/// `sym_neg p` endpoints compute: `(sym_neg p) @ i0 ≡ b` (via path-beta,
/// `I.neg i0 ↝ i1`, neutral path-endpoint) and `(sym_neg p) @ i1 ≡ a`.
#[test]
fn test_sym_neg_endpoints_compute() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let sym = path_sym_neg(&cst("p"));
    let at_i0 = path_app(sym.clone(), i0());
    let at_i1 = path_app(sym, i1());

    assert!(tc.is_def_eq(&at_i0, &cst("b")), "(sym_neg p) @ i0 ≡ b");
    assert!(tc.is_def_eq(&at_i1, &cst("a")), "(sym_neg p) @ i1 ≡ a");
    assert!(
        !tc.is_def_eq(&cst("a"), &cst("b")),
        "a, b distinct ⇒ the endpoint checks are meaningful"
    );
}

/// `sym_neg p : Path (λ_.A) b a` (type preservation — the inferred path's
/// reversed endpoints reduce to `b`/`a`).
#[test]
fn test_sym_neg_type_is_path_b_a() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let sym = path_sym_neg(&cst("p"));
    let (inferred, _cert) = tc
        .infer_type_with_cert(&sym)
        .expect("sym_neg p should type-check");
    assert!(
        tc.is_def_eq(&inferred, &path_ty(cst("b"), cst("a"))),
        "sym_neg p must have type Path (λ_.A) b a; got {inferred:?}"
    );
}

/// **The regularity fix**: `sym_neg (refl a) ≡ refl a` *definitionally* — not
/// merely at the endpoints. Path-beta on the constant `refl a = <k> a` discards
/// the reversed argument, so `<i> (<k> a) @ (~i) ≡ <i> a = refl a`.
#[test]
fn test_sym_neg_refl_is_refl_definitionally() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let refl = path_refl(&cst("a"));
    let sym_refl = path_sym_neg(&refl);

    assert!(
        tc.is_def_eq(&sym_refl, &refl),
        "sym_neg (refl a) ≡ refl a must hold DEFINITIONALLY (the regularity law)"
    );

    // And it still type-checks at Path (λ_.A) a a.
    let (ty, _cert) = tc
        .infer_type_with_cert(&sym_refl)
        .expect("sym_neg (refl a) should type-check");
    assert!(
        tc.is_def_eq(&ty, &path_ty(cst("a"), cst("a"))),
        "sym_neg (refl a) : Path (λ_.A) a a; got {ty:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 3 — J (path induction) with its computing β-rule (THE headline)
// ─────────────────────────────────────────────────────────────────────────────

/// **The headline β-rule**: `J P d a (refl a) ≡ d`, by COMPUTATION. With
/// `p = refl a`, the motive line `λ i. P (p@i) (<j> p@(i∧j))` is i-degenerate
/// (≡ `λ i. P a (<j> a)`), so `coe` over it reduces to its base via the deep
/// constant-family rule.
#[test]
fn test_J_beta_rule_computes() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let refl_a = path_refl(&cst("a"));
    let j = path_J(&cst("P"), &cst("d"), &refl_a);

    // J P d a (refl a) head-reduces to the base `d`.
    let reduct = tc.whnf(&j);
    assert!(
        matches!(reduct.kind(), ExprKind::Const(n, _) if *n == Name::from_string("d")),
        "J P d a (refl a) must whnf to d, got {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&j, &cst("d")),
        "J P d a (refl a) ≡ d (the β-rule)"
    );
}

/// `J P d a p` type-checks at `P y p` for a general `p : Path A a y` (here
/// `y = b`). Relies on the `I.min` reductions (`i1 ∧ j ↝ j`, then path-eta) for
/// the result type, and (`i0 ∧ j ↝ i0`) for the base-case `coe` check.
#[test]
fn test_J_typechecks_at_P_y_p() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let j = path_J(&cst("P"), &cst("d"), &cst("p"));
    let (inferred, _cert) = tc
        .infer_type_with_cert(&j)
        .expect("J P d a p should type-check");

    // y = b (the right endpoint of p : Path A a b), so the result is `P b p`.
    let expected = Expr::apps(cst("P"), [cst("b"), cst("p")]);
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "J P d a p must have type P y p (= P b p); got {inferred:?}"
    );
}

/// β-rule type preservation: `infer(J P d a refl) ≡ infer(d) ≡ P a (refl a)`.
#[test]
fn test_J_beta_type_preservation() {
    let env = cubical_j_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let refl_a = path_refl(&cst("a"));
    let j = path_J(&cst("P"), &cst("d"), &refl_a);

    let (j_ty, _) = tc
        .infer_type_with_cert(&j)
        .expect("J P d a (refl a) should type-check");
    let (d_ty, _) = tc
        .infer_type_with_cert(&cst("d"))
        .expect("d should type-check");

    assert!(
        tc.is_def_eq(&j_ty, &d_ty),
        "β-rule must preserve type: infer(J P d a refl) ≡ infer(d)"
    );
    // And concretely it is `P a (refl a)`.
    let pa_refl = Expr::apps(cst("P"), [cst("a"), path_refl(&cst("a"))]);
    assert!(
        tc.is_def_eq(&j_ty, &pa_refl),
        "infer(J P d a refl) must be P a (refl a); got {j_ty:?}"
    );
}
