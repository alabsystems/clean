// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung-1 **h-level library** — `isProp` / `isSet` and the foundational
//! implications `isContr→isProp`, `isProp→isSet`, built on the existing `isContr`
//! (Σ-encoded) and the cubical path/`hcomp` machinery.
//!
//! Encodings (plain `Const`/`App` over the reserved `Sigma.*` / Kan-system axioms):
//!
//! ```text
//! isProp A := (x y : A) → Path (λ_.A) x y
//! isSet  A := (x y : A) → isProp (Path (λ_.A) x y)
//! ```
//!
//! Every implication below is a genuine **proof term** discharged by a Kan square
//! (`hcomp`) — no `sorry`, no axiomatized h-level witness — and so is subject to the
//! enforced `validate_hcomp_cap` side condition (an ill-formed square is rejected).

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{
    is_contr_to_is_prop, is_contr_type, is_equiv_from_quasi_inv_on_set, is_equiv_type,
    is_prop_to_is_set, is_prop_to_path_p, is_prop_type, is_set_type, register_glue_axioms,
    register_kan_system_axioms, register_sigma_axioms, to_path_p,
};
use std::sync::Arc;

// ── Leaves ────────────────────────────────────────────────────────────────────

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::<Level>::new())
}
fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}
fn i0() -> Expr {
    Expr::from_kind(ExprKind::CubicalI0)
}
fn i1() -> Expr {
    Expr::from_kind(ExprKind::CubicalI1)
}
/// The level of `Type` (= `Sort 1`).
fn type_level() -> Level {
    Level::succ(Level::zero())
}
/// `Path (λ_:I. ty) left right` — homogeneous path.
fn path_homog(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::lam(BinderInfo::Default, interval(), ty)),
        left: Arc::new(left),
        right: Arc::new(right),
    })
}
/// `App(B, r)` for the opaque line `B : I → Type`.
fn b_at(r: Expr) -> Expr {
    Expr::app(cst("Bl"), r)
}

// ── Environment ─────────────────────────────────────────────────────────────────

/// Cubical env: Kan + Glue + Sigma axioms, plus an **opaque** `A : Type`. `A` being
/// an opaque axiom keeps every assertion non-vacuous.
fn hlevel_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("register kan system axioms");
    register_glue_axioms(&mut env).expect("register glue axioms");
    register_sigma_axioms(&mut env).expect("register sigma axioms");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("axiom A : Type should register");
    env
}

/// `hlevel_env` plus an **opaque line of propositions**: `Bl : I → Type`,
/// endpoints `bl0 : Bl i0` / `bl1 : Bl i1`, and `hBl : (i:I) → isProp (Bl i)`.
fn pathp_env() -> Environment {
    let mut env = hlevel_env();
    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };
    axiom(
        "Bl",
        Expr::pi(BinderInfo::Default, interval(), Expr::type_()),
    );
    axiom("bl0", b_at(i0()));
    axiom("bl1", b_at(i1()));
    // hBl : (i:I) → isProp (Bl i).   Under `Π i`: i = BVar0.
    axiom(
        "hBl",
        Expr::pi(
            BinderInfo::Default,
            interval(),
            is_prop_type(&b_at(Expr::bvar(0))),
        ),
    );
    env
}

fn infer_ty(tc: &TypeChecker<'_>, e: &Expr) -> Expr {
    tc.infer_type_with_cert(e)
        .unwrap_or_else(|err| panic!("infer failed for {e:?}: {err:?}"))
        .0
}

/// Assert `e : Sort level` (a type living at the given universe).
fn assert_is_sort(tc: &TypeChecker<'_>, e: &Expr, level: Level) {
    let ty = infer_ty(tc, e);
    assert!(
        tc.is_def_eq(&ty, &Expr::sort(level)),
        "expected a Sort; inferred {ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 1 — the definitions type-check at the right sorts
// ═════════════════════════════════════════════════════════════════════════════

/// `isProp A` and `isSet A` are both `Type` (`Sort 1`) for an opaque `A : Type`.
#[test]
fn test_hlevel_definitions_typecheck_at_right_sorts() {
    let env = hlevel_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let prop = is_prop_type(&cst("A"));
    assert_is_sort(&tc, &prop, type_level());

    let set = is_set_type(&cst("A"));
    assert_is_sort(&tc, &set, type_level());
}

// ═════════════════════════════════════════════════════════════════════════════
// 2 — isContr→isProp : a contractible type is a proposition (PROVED term)
// ═════════════════════════════════════════════════════════════════════════════

/// `isContr→isProp contr : isProp A` type-checks as a genuine proof term over an
/// **opaque** `contr : isContr A` (the center/contraction are projected by a single
/// `Sigma.elim`, the lid is a cap-coherent `hcomp` square).
#[test]
fn test_is_contr_to_is_prop_typechecks() {
    let mut env = hlevel_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("cA"),
        level_params: vec![],
        type_: is_contr_type(type_level(), &cst("A")),
    })
    .expect("opaque cA : isContr A registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proof = is_contr_to_is_prop(type_level(), &cst("A"), &cst("cA"));
    let ty = infer_ty(&tc, &proof);

    let expected = is_prop_type(&cst("A"));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "isContr→isProp cA : isProp A; got {ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 3 — isProp→isSet : a proposition is a set (PROVED term, the 4-face Kan square)
// ═════════════════════════════════════════════════════════════════════════════

/// `isProp→isSet hprop : isSet A` type-checks as a genuine proof term over an
/// **opaque** `hprop : isProp A`. This exercises the 2D / four-face cap-coherent
/// `hcomp` square (the crux of the h-level layer).
#[test]
fn test_is_prop_to_is_set_typechecks() {
    let mut env = hlevel_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hA"),
        level_params: vec![],
        type_: is_prop_type(&cst("A")),
    })
    .expect("opaque hA : isProp A registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proof = is_prop_to_is_set(type_level(), &cst("A"), &cst("hA"));
    let ty = infer_ty(&tc, &proof);

    let expected = is_set_type(&cst("A"));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "isProp→isSet hA : isSet A; got {ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 4 — isProp→PathP : a line of propositions has a PathP between any endpoints
//     (the heterogeneous-composition linchpin for the isEquiv upgrade)
// ═════════════════════════════════════════════════════════════════════════════

/// `toPathP q : PathP (λi.Bl i) bl0 bl1` type-checks, where
/// `q : coe Bl i0 i1 bl0 ≡ bl1` is synthesized from the line being propositional
/// (`hBl i1 …`). Exercises the `coe`-corrected single-wall homogeneous `hcomp`
/// that stands in for the heterogeneous CCHM `comp` (Clean lacks a `comp`
/// primitive; `System` tubes must be total).
#[test]
fn test_to_path_p_typechecks_opaque_line() {
    let env = pathp_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // q := hBl i1 (coe Bl i0 i1 bl0) bl1.
    let transported = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(cst("Bl")),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(cst("bl0")),
    });
    let q = Expr::apps(cst("hBl"), [i1(), transported, cst("bl1")]);
    let proof = to_path_p(type_level(), &cst("Bl"), &cst("bl0"), &cst("bl1"), &q);
    let ty = infer_ty(&tc, &proof);

    // Expected: PathP (λi. Bl i) bl0 bl1.
    let expected = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::lam(
            BinderInfo::Default,
            interval(),
            b_at(Expr::bvar(0)),
        )),
        left: Arc::new(cst("bl0")),
        right: Arc::new(cst("bl1")),
    });
    assert!(
        tc.is_def_eq(&ty, &expected),
        "toPathP q : PathP Bl bl0 bl1; got {ty:?}"
    );
}

/// `isProp→PathP hBl bl0 bl1 : PathP (λi.Bl i) bl0 bl1` — the packaged form.
#[test]
fn test_is_prop_to_path_p_typechecks_opaque_line() {
    let env = pathp_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proof = is_prop_to_path_p(
        type_level(),
        &cst("Bl"),
        &cst("hBl"),
        &cst("bl0"),
        &cst("bl1"),
    );
    let ty = infer_ty(&tc, &proof);

    let expected = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::lam(
            BinderInfo::Default,
            interval(),
            b_at(Expr::bvar(0)),
        )),
        left: Arc::new(cst("bl0")),
        right: Arc::new(cst("bl1")),
    });
    assert!(
        tc.is_def_eq(&ty, &expected),
        "isProp→PathP : PathP Bl bl0 bl1; got {ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 5 — biInvToIsEquivOnSet : isSet B → quasi-inverse → isEquiv f  (PROVED lemma)
//
// The general "B is a set ⟹ a quasi-inverse is an equivalence" upgrade, proved
// over an opaque quasi-inverse with `set_b : isSet B` a HYPOTHESIS (a function
// argument, NOT an axiom for the lemma). This is the engine that turns the kernel's
// `Equiv` (quasi-inverse) record into a genuine contractible-fibre `isEquiv`.
// ═════════════════════════════════════════════════════════════════════════════

/// Opaque quasi-inverse env: `A B : Type`, `f:A→B`, `g:B→A`, the homotopies
/// `eta : g∘f~id` / `eps : f∘g~id`, and `sB : isSet B`.
fn quasi_inv_env() -> Environment {
    let mut env = hlevel_env();
    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };
    axiom("B", Expr::type_());
    axiom("f", Expr::arrow(cst("A"), cst("B")));
    axiom("g", Expr::arrow(cst("B"), cst("A")));
    // eta : (x:A) → Path (λ_.A) (g (f x)) x.
    let g_f_x = Expr::app(cst("g"), Expr::app(cst("f"), Expr::bvar(0)));
    axiom(
        "eta",
        Expr::pi(
            BinderInfo::Default,
            cst("A"),
            path_homog(cst("A"), g_f_x, Expr::bvar(0)),
        ),
    );
    // eps : (y:B) → Path (λ_.B) (f (g y)) y.
    let f_g_y = Expr::app(cst("f"), Expr::app(cst("g"), Expr::bvar(0)));
    axiom(
        "eps",
        Expr::pi(
            BinderInfo::Default,
            cst("B"),
            path_homog(cst("B"), f_g_y, Expr::bvar(0)),
        ),
    );
    axiom("sB", is_set_type(&cst("B")));
    env
}

/// `biInvToIsEquivOnSet sB f g eta eps : isEquiv f` type-checks as a genuine proof
/// term over an opaque quasi-inverse — the upgrade engine. `sB : isSet B` is a
/// hypothesis (function argument), so the lemma itself is **axiom-free**.
#[test]
fn test_biinv_to_isequiv_on_set_typechecks() {
    let env = quasi_inv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proof = is_equiv_from_quasi_inv_on_set(
        type_level(),
        &cst("A"),
        &cst("B"),
        &cst("sB"),
        &cst("f"),
        &cst("g"),
        &cst("eta"),
        &cst("eps"),
    );
    let ty = infer_ty(&tc, &proof);

    let expected = is_equiv_type(type_level(), &cst("A"), &cst("B"), &cst("f"));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "biInvToIsEquivOnSet : isEquiv f; got {ty:?}"
    );
}

/// The lemma is **lift-correct in `set_b`**: abstracting the set hypothesis as a
/// genuine `λ (s : isSet B)` gives an axiom-free term
/// `(isSet B) → isEquiv f` — i.e. `set_b` may be a bound hypothesis, not only a
/// closed const. This is the exact shape `windingIsEquiv` needs (`isSet MyZ → isEquiv
/// winding`), so the upgrade is gated on *only* a proof term for `isSet B`.
#[test]
fn test_biinv_to_isequiv_on_set_abstracts_the_set_hypothesis() {
    let env = quasi_inv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // λ (s : isSet B). biInvToIsEquivOnSet s f g eta eps   — `set_b` = BVar 0.
    let body = is_equiv_from_quasi_inv_on_set(
        type_level(),
        &cst("A"),
        &cst("B"),
        &Expr::bvar(0), // the bound `s : isSet B`
        &cst("f"),
        &cst("g"),
        &cst("eta"),
        &cst("eps"),
    );
    let proof = Expr::lam(BinderInfo::Default, is_set_type(&cst("B")), body);
    let ty = infer_ty(&tc, &proof);

    // Expected: (isSet B) → isEquiv f.
    let expected = Expr::pi(
        BinderInfo::Default,
        is_set_type(&cst("B")),
        is_equiv_type(type_level(), &cst("A"), &cst("B"), &cst("f")),
    );
    assert!(
        tc.is_def_eq(&ty, &expected),
        "λ s. biInvToIsEquivOnSet s … : isSet B → isEquiv f; got {ty:?}"
    );
}
