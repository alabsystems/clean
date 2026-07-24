// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for the cubical groupoid laws built on the
//! multi-branch `hcomp`: path inversion `sym p` and the reflexivity path
//! `refl a` (Rung-1 deliverable `sym`).
//!
//! All terms are built directly as kernel `Expr`s; the reserved Expr-encoding
//! (`Cofib.*`, `System.cons/nil`) is registered as interval-valued axioms via
//! [`register_kan_system_axioms`], so the existing inference / certificate
//! machinery accepts the encoding unchanged.
//!
//! The two key soundness facts both **compute** (they are not asserted):
//! * `(sym p) @ i0 ≡ b` and `(sym p) @ i1 ≡ a` — via the on-a-true-face `hcomp`
//!   rule followed by the neutral path-endpoint rule.
//! * `sym p : Path (λ_.A) b a` — the inferred path type's endpoints reduce to
//!   `b`/`a` by the same rules.

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{path_refl, path_sym, register_kan_system_axioms};

/// A nullary constant `name`.
fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::<Level>::new())
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
        path: std::sync::Arc::new(p),
        arg: std::sync::Arc::new(r),
    })
}

/// The level of `A : Type` (= `Sort 1`).
fn type_level() -> Level {
    Level::succ(Level::zero())
}

/// The constant path family `λ _ : I, A`.
fn fam_a() -> Expr {
    Expr::lam(BinderInfo::Default, interval(), cst("A"))
}

/// Cubical environment with the Kan system axioms plus
/// `A : Type`, `a b : A`, `iv : I`, `p : Path (λ_.A) a b`.
fn cubical_groupoid_env() -> Environment {
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

    let a_ty = cst("A");
    axiom("A", Expr::type_());
    axiom("a", a_ty.clone());
    axiom("b", a_ty.clone());
    axiom("iv", interval());

    // p : Path (λ_.A) a b
    axiom(
        "p",
        Expr::from_kind(ExprKind::CubicalPath {
            ty: std::sync::Arc::new(fam_a()),
            left: std::sync::Arc::new(cst("a")),
            right: std::sync::Arc::new(cst("b")),
        }),
    );
    env
}

/// The expected inverse type `Path (λ_.A) b a`.
fn path_b_a() -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: std::sync::Arc::new(fam_a()),
        left: std::sync::Arc::new(cst("b")),
        right: std::sync::Arc::new(cst("a")),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 1 — `sym p` infers to `Path (λ_.A) b a` (type preservation, deliverable 1/4)
// ─────────────────────────────────────────────────────────────────────────────

/// For `p : Path A a b`, the inverse `sym p` type-checks and its inferred type
/// is definitionally `Path (λ_.A) b a` (the inferred path's endpoints `b`/`a`
/// come out of the on-a-true-face `hcomp` rule).
#[test]
fn test_sym_type_is_path_b_a() {
    let env = cubical_groupoid_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let sym = path_sym(&cst("A"), type_level(), &cst("p"));

    let (inferred, _cert) = tc
        .infer_type_with_cert(&sym)
        .expect("sym p should type-check");
    assert!(
        tc.is_def_eq(&inferred, &path_b_a()),
        "sym p must have type Path (λ_.A) b a; got {inferred:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 2 — endpoints (THE key soundness test): (sym p)@i0 ≡ b, (sym p)@i1 ≡ a
// ─────────────────────────────────────────────────────────────────────────────

/// The boundary computation rules for `sym`: `(sym p) @ i0 ≡ b` (face `(i=0)`
/// total ⇒ lid `(λ j. p@j) i1 = p@i1 ≡ b`) and `(sym p) @ i1 ≡ a` (face `(i=1)`
/// total ⇒ lid `(λ j. a) i1 = a = p@i0 ≡ a`). Both fire through the existing
/// on-a-true-face `hcomp` rule + the neutral path-endpoint rule — nothing is
/// asserted.
#[test]
fn test_sym_endpoints_compute() {
    let env = cubical_groupoid_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let sym = path_sym(&cst("A"), type_level(), &cst("p"));

    let at_i0 = path_app(sym.clone(), i0());
    let at_i1 = path_app(sym, i1());

    assert!(
        tc.is_def_eq(&at_i0, &cst("b")),
        "(sym p) @ i0 must compute to b"
    );
    assert!(
        tc.is_def_eq(&at_i1, &cst("a")),
        "(sym p) @ i1 must compute to a"
    );

    // And the endpoints are NOT mixed up (a ≢ b, so this is a real check).
    assert!(
        !tc.is_def_eq(&cst("a"), &cst("b")),
        "a and b are distinct axioms, so the endpoint checks above are meaningful"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 3 — `sym refl` has constant value: sym (refl a) @ i0 ≡ a, @ i1 ≡ a
// ─────────────────────────────────────────────────────────────────────────────

/// Inverting the constant path `refl a` is a path `Path (λ_.A) a a` whose
/// endpoints both compute to `a`. (The *full* `sym (refl a) ≡ refl a` does not
/// hold definitionally — at a generic interior point the constant-system `hcomp`
/// is stuck, which is the standard no-regularity behaviour; the endpoints are
/// what the on-a-true-face rule discharges, exactly as for `path_compose`.)
#[test]
fn test_sym_refl_constant_value() {
    let env = cubical_groupoid_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // refl a : Path (λ_.A) a a.
    let refl = path_refl(&cst("a"));
    let refl_ty = Expr::from_kind(ExprKind::CubicalPath {
        ty: std::sync::Arc::new(fam_a()),
        left: std::sync::Arc::new(cst("a")),
        right: std::sync::Arc::new(cst("a")),
    });
    let (refl_inferred, _) = tc
        .infer_type_with_cert(&refl)
        .expect("refl a should type-check");
    assert!(
        tc.is_def_eq(&refl_inferred, &refl_ty),
        "refl a must have type Path (λ_.A) a a; got {refl_inferred:?}"
    );

    // sym (refl a) : Path (λ_.A) a a (both endpoints of refl a are a).
    let sym_refl = path_sym(&cst("A"), type_level(), &refl);
    let (sym_refl_ty, _) = tc
        .infer_type_with_cert(&sym_refl)
        .expect("sym (refl a) should type-check");
    assert!(
        tc.is_def_eq(&sym_refl_ty, &refl_ty),
        "sym (refl a) must have type Path (λ_.A) a a; got {sym_refl_ty:?}"
    );

    // Endpoints both reduce to the constant value a.
    let at_i0 = path_app(sym_refl.clone(), i0());
    let at_i1 = path_app(sym_refl, i1());
    assert!(
        tc.is_def_eq(&at_i0, &cst("a")),
        "sym (refl a) @ i0 must compute to a"
    );
    assert!(
        tc.is_def_eq(&at_i1, &cst("a")),
        "sym (refl a) @ i1 must compute to a"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 4 — type preservation of the hcomp reduction inside `sym`
// ─────────────────────────────────────────────────────────────────────────────

/// The `(sym p) @ i0` redex (a multi-branch `hcomp` whose `(i=0)` face is total)
/// reduces by the on-a-true-face rule, and the reduction preserves the inferred
/// type: `infer((sym p)@i0) ≡ infer(reduct) ≡ A`.
#[test]
fn test_sym_endpoint_hcomp_type_preservation() {
    let env = cubical_groupoid_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let sym = path_sym(&cst("A"), type_level(), &cst("p"));
    let at_i0 = path_app(sym, i0());

    // Type of the redex: (sym p) @ i0 : (λ_.A) i0 = A.
    let (redex_ty, _) = tc
        .infer_type_with_cert(&at_i0)
        .expect("(sym p) @ i0 should type-check");

    // Reduces (path-beta + on-a-true-face hcomp + path-endpoint) to b.
    let reduct = tc.whnf(&at_i0);
    assert!(
        tc.is_def_eq(&reduct, &cst("b")),
        "(sym p) @ i0 must reduce to b; got {reduct:?}"
    );

    // Type preservation: infer(redex) ≡ infer(reduct) ≡ A.
    let (reduct_ty, _) = tc
        .infer_type_with_cert(&reduct)
        .expect("reduct b should type-check");
    assert!(
        tc.is_def_eq(&redex_ty, &reduct_ty),
        "sym-endpoint reduction must preserve type"
    );
    assert!(
        tc.is_def_eq(&redex_ty, &cst("A")),
        "the redex type must be A; got {redex_ty:?}"
    );
}
