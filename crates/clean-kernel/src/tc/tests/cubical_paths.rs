// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for multi-branch cofibrations + partial-element
//! systems and path composition `p ∙ q` (Rung-1 hcomp deliverables A/B/C).
//!
//! All terms are built directly as kernel `Expr`s; the reserved Expr-encoding
//! (`Cofib.*`, `System.cons/nil`) is registered as interval-valued axioms via
//! [`register_kan_system_axioms`], so the existing inference / certificate
//! machinery accepts the encoding unchanged.

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::cofib::Cofib;
use crate::tc::reduction::kan::{path_compose, register_kan_system_axioms};

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

/// Atomic face `(r = 0)`.
fn face_eq0(r: Expr) -> Expr {
    Expr::app(cst("Cofib.eq0"), r)
}

/// Atomic face `(r = 1)`.
fn face_eq1(r: Expr) -> Expr {
    Expr::app(cst("Cofib.eq1"), r)
}

/// Disjunction `φ ∨ ψ`.
fn face_or(phi: Expr, psi: Expr) -> Expr {
    Expr::apps(cst("Cofib.or"), [phi, psi])
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

/// Build a 2-branch system `[φ₁ ↦ u₁, φ₂ ↦ u₂]` over type `a_ty : Sort u`.
fn system2(a_ty: &Expr, f1: Expr, u1: Expr, f2: Expr, u2: Expr) -> Expr {
    let cons_const = || Expr::const_(Name::from_string("System.cons"), vec![type_level()]);
    let nil = Expr::app(
        Expr::const_(Name::from_string("System.nil"), vec![type_level()]),
        a_ty.clone(),
    );
    let inner = Expr::apps(cons_const(), [a_ty.clone(), f2, u2, nil]);
    Expr::apps(cons_const(), [a_ty.clone(), f1, u1, inner])
}

/// Cubical environment with the Kan system axioms plus
/// `A : Type`, `a b c : A`, `iv : I`, `p : Path A a b`, `q : Path A b c`.
fn cubical_path_env() -> Environment {
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
    axiom("c", a_ty.clone());
    axiom("iv", interval());

    // Constant path family `λ _ : I, A`.
    let fam = Expr::lam(BinderInfo::Default, interval(), a_ty.clone());
    // p : Path (λ_.A) a b
    axiom(
        "p",
        Expr::from_kind(ExprKind::CubicalPath {
            ty: std::sync::Arc::new(fam.clone()),
            left: std::sync::Arc::new(cst("a")),
            right: std::sync::Arc::new(cst("b")),
        }),
    );
    // q : Path (λ_.A) b c
    axiom(
        "q",
        Expr::from_kind(ExprKind::CubicalPath {
            ty: std::sync::Arc::new(fam),
            left: std::sync::Arc::new(cst("b")),
            right: std::sync::Arc::new(cst("c")),
        }),
    );
    env
}

/// The expected composite type `Path (λ_.A) a c`.
fn path_a_c() -> Expr {
    let fam = Expr::lam(BinderInfo::Default, interval(), cst("A"));
    Expr::from_kind(ExprKind::CubicalPath {
        ty: std::sync::Arc::new(fam),
        left: std::sync::Arc::new(cst("a")),
        right: std::sync::Arc::new(cst("c")),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 1 — cofibration parse round-trip
// ─────────────────────────────────────────────────────────────────────────────

/// The Expr-encoding of `(iv=0) ∨ (iv=1)` parses to the right `Cofib`, and that
/// `Cofib` has the expected satisfaction behaviour (true at both endpoints of
/// `iv`, neither `⊤` nor `⊥`).
#[test]
fn test_cofib_parse_round_trip() {
    let env = cubical_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let encoded = face_or(face_eq0(cst("iv")), face_eq1(cst("iv")));
    let parsed = tc
        .parse_cofib_for_test(&encoded)
        .expect("(iv=0)∨(iv=1) should parse");

    // `iv` is the first (only) interned interval variable ⇒ id 0.
    let expected = Cofib::eq0(0).or(&Cofib::eq1(0));
    assert_eq!(
        parsed, expected,
        "parsed cofib must match the DNF algebra value"
    );

    // Satisfaction: true at iv↦0 and iv↦1, but it is a proper face (not ⊤/⊥).
    let at_0 = |v: u32| if v == 0 { Some(false) } else { None };
    let at_1 = |v: u32| if v == 0 { Some(true) } else { None };
    assert!(parsed.is_true(&at_0), "(iv=0)∨(iv=1) holds at iv↦0");
    assert!(parsed.is_true(&at_1), "(iv=0)∨(iv=1) holds at iv↦1");
    assert!(!parsed.is_top(), "the path boundary is not ⊤");
    assert!(!parsed.is_bot(), "the path boundary is not ⊥");

    // The legacy single-face encodings still parse: bare i1 ↦ ⊤, i0 ↦ ⊥.
    assert!(tc.parse_cofib_for_test(&i1()).expect("i1 parses").is_top());
    assert!(tc.parse_cofib_for_test(&i0()).expect("i0 parses").is_bot());
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 2 — system agreement on overlaps
// ─────────────────────────────────────────────────────────────────────────────

/// A consistent 2-branch system (disjoint faces) type-checks; an inconsistent one
/// (the SAME face mapped to definitionally-distinct values) is rejected.
#[test]
fn test_system_overlap_agreement() {
    let env = cubical_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let a_ty = cst("A");
    let lam_const = |v: &str| Expr::lam(BinderInfo::Default, interval(), cst(v));

    // Consistent: [(iv=0) ↦ λ_.a, (iv=1) ↦ λ_.a] — disjoint faces, overlap ⊥, and
    // both tubes cap onto the floor `a` (CAP/floor-agreement, now enforced). Each
    // tube's i0-end is `a` ≡ the floor on its face, so the system is well-formed.
    // (Using `λ_.b` for the (iv=1) tube — as a *previous* version of this test did —
    // is genuinely ill-formed: that tube caps onto `b` ≢ `a` = the floor, and is now
    // correctly REJECTED by the cap check; that behaviour is covered by
    // `cubical_int::test_hcomp_overlap_agreement_is_face_restricted`.)
    let good = Expr::from_kind(ExprKind::CubicalHComp {
        ty: std::sync::Arc::new(a_ty.clone()),
        phi: std::sync::Arc::new(face_or(face_eq0(cst("iv")), face_eq1(cst("iv")))),
        u: std::sync::Arc::new(system2(
            &a_ty,
            face_eq0(cst("iv")),
            lam_const("a"),
            face_eq1(cst("iv")),
            lam_const("a"),
        )),
        base: std::sync::Arc::new(cst("a")),
    });
    assert!(
        tc.infer_type_with_cert(&good).is_ok(),
        "a consistent (disjoint-face, cap-coherent) 2-branch system must type-check"
    );

    // Inconsistent: [(iv=0) ↦ λ_.a, (iv=0) ↦ λ_.b] — SAME face, a ≢ b.
    let bad = Expr::from_kind(ExprKind::CubicalHComp {
        ty: std::sync::Arc::new(a_ty.clone()),
        phi: std::sync::Arc::new(face_or(face_eq0(cst("iv")), face_eq0(cst("iv")))),
        u: std::sync::Arc::new(system2(
            &a_ty,
            face_eq0(cst("iv")),
            lam_const("a"),
            face_eq0(cst("iv")),
            lam_const("b"),
        )),
        base: std::sync::Arc::new(cst("a")),
    });
    let err = tc
        .infer_type_with_cert(&bad)
        .expect_err("an inconsistent system (overlapping faces, unequal tubes) must be rejected");
    assert!(
        matches!(err, TypeError::TypeMismatch { .. }),
        "expected TypeMismatch for inconsistent system, got {err:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 3 — path composition endpoints (the key soundness test)
// ─────────────────────────────────────────────────────────────────────────────

/// For `p : Path A a b`, `q : Path A b c`, the composite `p ∙ q` type-checks at
/// `Path A a c`, and `(p ∙ q) @ i0 ≡ a`, `(p ∙ q) @ i1 ≡ c`.
#[test]
fn test_path_composition_endpoints() {
    let env = cubical_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let comp = path_compose(&cst("A"), type_level(), &cst("p"), &cst("q"));

    // Type-checks at Path (λ_.A) a c.
    let (inferred, _cert) = tc
        .infer_type_with_cert(&comp)
        .expect("p ∙ q should type-check");
    assert!(
        tc.is_def_eq(&inferred, &path_a_c()),
        "p ∙ q must have type Path A a c; got {inferred:?}"
    );

    // Endpoint computation rules: (p∙q)@i0 ≡ a, (p∙q)@i1 ≡ c.
    let at_i0 = path_app(comp.clone(), i0());
    let at_i1 = path_app(comp, i1());
    assert!(
        tc.is_def_eq(&at_i0, &cst("a")),
        "(p ∙ q) @ i0 must compute to a"
    );
    assert!(
        tc.is_def_eq(&at_i1, &cst("c")),
        "(p ∙ q) @ i1 must compute to c"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 4 — type preservation of the multi-branch hcomp reduction
// ─────────────────────────────────────────────────────────────────────────────

/// A multi-branch `hcomp` whose first face is total reduces (on-a-true-face rule)
/// to that branch's `uᵢ i1`, and the reduction preserves the inferred type
/// (`infer(hcomp) ≡ infer(reduct)`).
#[test]
fn test_multibranch_hcomp_type_preservation() {
    let env = cubical_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let a_ty = cst("A");
    let lam_const = |v: &str| Expr::lam(BinderInfo::Default, interval(), cst(v));

    // hcomp {A} [(i0=0)↦λ_.a, (i0=1)↦λ_.b] a  — branch 1's face (i0=0) is ⊤.
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: std::sync::Arc::new(a_ty.clone()),
        phi: std::sync::Arc::new(face_or(face_eq0(i0()), face_eq1(i0()))),
        u: std::sync::Arc::new(system2(
            &a_ty,
            face_eq0(i0()),
            lam_const("a"),
            face_eq1(i0()),
            lam_const("b"),
        )),
        base: std::sync::Arc::new(cst("a")),
    });

    let (hcomp_ty, _) = tc
        .infer_type_with_cert(&hcomp)
        .expect("multi-branch hcomp should type-check");

    // Reduces to the total branch's lid (λ_.a) i1 ≡ a.
    let reduct = tc.whnf(&hcomp);
    assert!(
        tc.is_def_eq(&reduct, &cst("a")),
        "hcomp on a true face must reduce to that branch's u i1 (= a); got {reduct:?}"
    );

    // Type preservation: infer(hcomp) ≡ infer(reduct).
    let (reduct_ty, _) = tc
        .infer_type_with_cert(&reduct)
        .expect("reduct should type-check");
    assert!(
        tc.is_def_eq(&hcomp_ty, &reduct_ty),
        "hcomp reduction must preserve type"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 5 — parse_system round-trips a 2-branch system to its branch faces
// ─────────────────────────────────────────────────────────────────────────────

/// `parse_system` recovers exactly the two branch faces of a `System.cons`
/// encoding, with the shared interner giving `iv` a single id.
#[test]
fn test_parse_system_two_branches() {
    let env = cubical_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let a_ty = cst("A");
    let lam_const = |v: &str| Expr::lam(BinderInfo::Default, interval(), cst(v));

    let phi = face_or(face_eq0(cst("iv")), face_eq1(cst("iv")));
    let u = system2(
        &a_ty,
        face_eq0(cst("iv")),
        lam_const("a"),
        face_eq1(cst("iv")),
        lam_const("b"),
    );
    let branches = tc
        .parse_system_for_test(&phi, &u)
        .expect("system should parse");
    assert_eq!(branches.len(), 2, "two branches expected");
    assert_eq!(branches[0].0, Cofib::eq0(0), "branch 1 face is (iv=0)");
    assert_eq!(branches[1].0, Cofib::eq1(0), "branch 2 face is (iv=1)");
}
