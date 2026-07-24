// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for the **Kan-filling infrastructure** the cubical
//! `comp`-over-`hcomp` needs:
//!
//! * [`hfill`] — the **homogeneous filler**, defined as an `hcomp` over the
//!   `I.min` connection. Its two endpoints *compute* (they are not asserted):
//!   `hfill … i0 ≡ base` (the extra `(r=0)↦base` cell fires) and, on a total
//!   face, `hfill … i1 ≡ hcomp … ≡ u i1`.
//! * [`coe_equiv`] — **coercion along a line is an equivalence** (`isEquivTransport`/
//!   `transpEquiv`): the `e_T : L i1 ≃ L i0` whose round-trip coherences η/ε are
//!   built from the native coe-filler. Anchors: it type-checks as
//!   `Equiv (L i1) (L i0)`; `Equiv.fwd (coeEquiv L) x ≡ coe L i1 i0 x`; and for a
//!   constant line it degenerates to `Equiv.idEquiv`'s (identity) forward map.
//!
//! All terms are built directly as kernel `Expr`s over the reserved Kan/Glue
//! axioms ([`register_kan_system_axioms`] / [`register_glue_axioms`]) — plain
//! `Const`/`App` spines, no new `ExprKind` variant.

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{
    coe_equiv, hfill, register_glue_axioms, register_kan_system_axioms,
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
fn coe(line: Expr, r: Expr, s: Expr, base: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(r),
        s: Arc::new(s),
        base: Arc::new(base),
    })
}
fn cofib_top() -> Expr {
    cst("Cofib.top")
}
fn cofib_eq1(arg: Expr) -> Expr {
    Expr::app(cst("Cofib.eq1"), arg)
}

/// `System.cons.{ℓ} A φ head tail` and `System.nil.{ℓ} A`.
fn system_cons(level: Level, a: Expr, face: Expr, head: Expr, tail: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("System.cons"), vec![level]),
        [a, face, head, tail],
    )
}
fn system_nil(level: Level, a: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("System.nil"), vec![level]),
        a,
    )
}

/// `Equiv.fwd.{1} A B e [x]` — the (computing) forward-map projection, applied.
fn equiv_fwd_app(a: &Expr, b: &Expr, e: &Expr, x: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Equiv.fwd"), vec![type_level()]),
        [a.clone(), b.clone(), e.clone(), x.clone()],
    )
}

// ── Environment ───────────────────────────────────────────────────────────────

/// Cubical env: Kan + Glue axioms, plus
/// `A : Type`, `a0 : A`, `uA : I → A`, `iv jv : I` (neutral faces),
/// a line `L : I → Type` with a point `xL1 : L i1`.
fn hfill_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("register kan system axioms");
    register_glue_axioms(&mut env).expect("register glue axioms");

    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };

    axiom("A", Expr::type_());
    axiom("a0", cst("A"));
    axiom("uA", Expr::pi(BinderInfo::Default, interval(), cst("A"))); // uA : I → A
    axiom("iv", interval());
    axiom("jv", interval());

    // L : I → Type   (an opaque, genuinely interval-dependent line of types).
    axiom(
        "L",
        Expr::pi(BinderInfo::Default, interval(), Expr::type_()),
    );
    // xL1 : L i1.
    axiom("xL1", Expr::app(cst("L"), i1()));
    env
}

/// `App(L, r)` — the line `L` applied at the interval point `r`.
fn l_at(r: Expr) -> Expr {
    Expr::app(cst("L"), r)
}

fn infer_ty(tc: &TypeChecker<'_>, e: &Expr) -> Expr {
    tc.infer_type_with_cert(e)
        .unwrap_or_else(|err| panic!("infer failed for {e:?}: {err:?}"))
        .0
}

// ═════════════════════════════════════════════════════════════════════════════
// hfill — Deliverable 1
// ═════════════════════════════════════════════════════════════════════════════

/// **i0 endpoint** (the key fact): `hfill {A} [(jv=1)↦uA] a0 i0 ≡ a0`. At `r = i0`
/// the extra `(i0=0) ⇓ ⊤` cell fires the on-a-true-face `hcomp` rule, whose lid is
/// `(λ_. a0) i1 ≡ a0`. The user face `(jv=1)` is *neutral* (not total), so it does
/// not pre-empt the `(r=0)` cell — making the reduction to `a0` (and not `uA i0`)
/// meaningful.
#[test]
fn test_hfill_i0_endpoint_is_base() {
    let env = hfill_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let hf = hfill(
        &cst("A"),
        type_level(),
        &cofib_eq1(cst("jv")), // neutral face φ = (jv = 1)
        &cst("uA"),
        &cst("a0"),
        &i0(),
    );

    let reduct = tc.whnf(&hf);
    assert!(
        tc.is_def_eq(&reduct, &cst("a0")),
        "hfill … i0 must reduce to base a0; got {reduct:?}"
    );
    assert!(tc.is_def_eq(&hf, &cst("a0")), "hfill … i0 ≡ base a0");

    // Meaningful: a0 is NOT the φ-tube value uA i0 (so picking the (r=0) cell,
    // not the φ cell, is a real check).
    assert!(
        !tc.is_def_eq(&cst("a0"), &Expr::app(cst("uA"), i0())),
        "a0 ≢ uA i0, so the endpoint reduction is meaningful"
    );
}

/// **i1 endpoint = the full composite** (computable regime, total face): with
/// `φ = ⊤`, `hfill {A} [⊤↦uA] a0 i1 ≡ hcomp {A} [⊤↦uA] a0 ≡ uA i1`. At `r = i1`
/// the `(i1=0) ⇓ ⊥` cell drops out and `i1 ∧ j ↝ j` collapses the φ tube to `uA`,
/// so both sides agree.
#[test]
fn test_hfill_i1_endpoint_is_full_hcomp() {
    let env = hfill_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let hf = hfill(
        &cst("A"),
        type_level(),
        &cofib_top(), // φ = ⊤
        &cst("uA"),
        &cst("a0"),
        &i1(),
    );

    // The full homogeneous composite `hcomp {A} [⊤↦uA] a0`.
    let full = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(cst("A")),
        phi: Arc::new(cofib_top()),
        u: Arc::new(system_cons(
            type_level(),
            cst("A"),
            cofib_top(),
            cst("uA"),
            system_nil(type_level(), cst("A")),
        )),
        base: Arc::new(cst("a0")),
    });

    assert!(
        tc.is_def_eq(&hf, &full),
        "hfill [⊤↦uA] a0 i1 ≡ hcomp [⊤↦uA] a0"
    );
    // Both reduce to the lid `uA i1`.
    assert!(
        tc.is_def_eq(&hf, &Expr::app(cst("uA"), i1())),
        "hfill [⊤↦uA] a0 i1 ≡ uA i1"
    );
}

/// **Type preservation** of `hfill`: the filler infers to the element type `A`.
/// At `r = i1` the `(r=0)` cell's face is `⊥`, so the overlap check is vacuous and
/// `infer(hfill … i1) ≡ A`. With a *constant* tube `λ_. a0` (whose `(r=0)` overlap
/// genuinely agrees) the filler also type-checks at a **generic** `r = iv`.
#[test]
fn test_hfill_type_preservation() {
    let env = hfill_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // (a) Generic-tube filler at r = i1: the ⊥-overlap makes the OVERLAP check
    // vacuous, but the CAP/floor-agreement check (now enforced) genuinely REJECTS it
    // — the generic tube `uA` does not cap onto the floor `a0` on the face (jv=1)
    // (`uA i0 ≢ a0`), so this hfill is ill-formed. It type-checked before only
    // because the cap check was missing.
    let hf_i1 = hfill(
        &cst("A"),
        type_level(),
        &cofib_eq1(cst("jv")),
        &cst("uA"),
        &cst("a0"),
        &i1(),
    );
    assert!(
        tc.infer_type_with_cert(&hf_i1).is_err(),
        "a generic-tube hfill whose tube does not cap onto the floor must be REJECTED \
         (cap/floor-agreement)"
    );

    // (b) Constant tube `λ_. a0` at a GENERIC interval `r = iv`: the (r=0)/φ
    // overlap tubes are both `a0`, so the conservative overlap check passes.
    let const_u = Expr::lam(BinderInfo::Default, interval(), cst("a0")); // λ_:I. a0
    let hf_gen = hfill(
        &cst("A"),
        type_level(),
        &cofib_eq1(cst("jv")), // φ = (jv = 1)
        &const_u,
        &cst("a0"),
        &cst("iv"), // r = iv (neutral)
    );
    let ty_gen = infer_ty(&tc, &hf_gen);
    assert!(
        tc.is_def_eq(&ty_gen, &cst("A")),
        "hfill [const] a0 iv : A; got {ty_gen:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// coe_equiv — Deliverable 2
// ═════════════════════════════════════════════════════════════════════════════

/// **Anchor (a)**: `coeEquiv L` type-checks as `Equiv (L i1) (L i0)` — the η/ε
/// coherence fields really line up against `Equiv.mk`'s record type (the round-trip
/// homotopies, built from the coe-filler, have the demanded constant path family).
#[test]
fn test_coe_equiv_typechecks_as_equiv() {
    let env = hfill_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ce = coe_equiv(&cst("L"), type_level());
    let ty = infer_ty(&tc, &ce);

    let expected = Expr::apps(
        Expr::const_(Name::from_string("Equiv"), vec![type_level()]),
        [l_at(i1()), l_at(i0())],
    );
    assert!(
        tc.is_def_eq(&ty, &expected),
        "coeEquiv L : Equiv (L i1) (L i0); got {ty:?}"
    );
}

/// **Anchor (b)**: `Equiv.fwd (coeEquiv L) x ≡ coe L i1 i0 x` — the forward map is
/// the backward coercion. `Equiv.fwd (Equiv.mk … f …) ↝ f`, and `f x` β-reduces to
/// `coe L i1 i0 x` (which is genuinely *stuck* for the opaque line `L`, so this is
/// not vacuous).
#[test]
fn test_coe_equiv_fwd_is_coe_backward() {
    let env = hfill_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ce = coe_equiv(&cst("L"), type_level());
    let fwd = equiv_fwd_app(&l_at(i1()), &l_at(i0()), &ce, &cst("xL1"));
    let expected = coe(cst("L"), i1(), i0(), cst("xL1")); // coe L i1 i0 x

    let reduct = tc.whnf(&fwd);
    assert!(
        tc.is_def_eq(&reduct, &expected),
        "Equiv.fwd (coeEquiv L) x must reduce to coe L i1 i0 x; got {reduct:?}"
    );
    // Type preservation: both sides infer to `L i0`.
    let fwd_ty = infer_ty(&tc, &fwd);
    assert!(
        tc.is_def_eq(&fwd_ty, &l_at(i0())),
        "Equiv.fwd (coeEquiv L) x : L i0; got {fwd_ty:?}"
    );
}

/// **Anchor (c)** — the key sanity check: for a **constant** line `L = λ_. A`,
/// `coeEquiv L` degenerates to the identity equivalence. Its forward map reduces to
/// `id_A`, matching `Equiv.fwd (Equiv.idEquiv A)`:
/// `Equiv.fwd (coeEquiv (λ_.A)) x ≡ x ≡ Equiv.fwd (Equiv.idEquiv A) x`.
#[test]
fn test_coe_equiv_constant_line_is_id_equiv() {
    let mut env = hfill_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xa"),
        level_params: vec![],
        type_: cst("A"),
    })
    .expect("xa : A");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // L = λ_:I. A  (constant line).
    let const_line = Expr::lam(BinderInfo::Default, interval(), cst("A"));
    let ce = coe_equiv(&const_line, type_level());

    // It still type-checks (as Equiv ((λ_.A) i1) ((λ_.A) i0) ≡ Equiv A A).
    let ty = infer_ty(&tc, &ce);
    let expected_equiv = Expr::apps(
        Expr::const_(Name::from_string("Equiv"), vec![type_level()]),
        [cst("A"), cst("A")],
    );
    assert!(
        tc.is_def_eq(&ty, &expected_equiv),
        "coeEquiv (λ_.A) : Equiv A A; got {ty:?}"
    );

    // Forward map of coeEquiv (λ_.A) applied to xa ≡ xa (identity).
    let a_endpt = Expr::app(const_line.clone(), i1());
    let b_endpt = Expr::app(const_line, i0());
    let fwd_ce = equiv_fwd_app(&a_endpt, &b_endpt, &ce, &cst("xa"));
    assert!(
        tc.is_def_eq(&fwd_ce, &cst("xa")),
        "Equiv.fwd (coeEquiv (λ_.A)) xa ≡ xa (degenerates to the identity)"
    );

    // … and that is exactly Equiv.idEquiv's forward map.
    let id_equiv = Expr::app(
        Expr::const_(Name::from_string("Equiv.idEquiv"), vec![type_level()]),
        cst("A"),
    );
    let fwd_id = equiv_fwd_app(&cst("A"), &cst("A"), &id_equiv, &cst("xa"));
    assert!(
        tc.is_def_eq(&fwd_id, &cst("xa")),
        "Equiv.fwd (Equiv.idEquiv A) xa ≡ xa"
    );
    assert!(
        tc.is_def_eq(&fwd_ce, &fwd_id),
        "coeEquiv (λ_.A) and Equiv.idEquiv A have the same (identity) forward map"
    );
}

/// Soundness guard: for a *generic* (opaque) line the round-trip is genuinely a
/// non-trivial path — `coeEquiv L` does NOT collapse to `idEquiv`. The forward map
/// `coe L i1 i0` stays a **stuck** `coe` (it is not the identity `λx.x`).
#[test]
fn test_coe_equiv_generic_line_does_not_collapse() {
    let env = hfill_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ce = coe_equiv(&cst("L"), type_level());
    let fwd = equiv_fwd_app(&l_at(i1()), &l_at(i0()), &ce, &cst("xL1"));

    // The forward map applied to x is the stuck `coe L i1 i0 x`, NOT `x` — a
    // generic line is not (definitionally) the identity equivalence.
    let reduct = tc.whnf(&fwd);
    assert!(
        matches!(reduct.kind(), ExprKind::CubicalCoe { .. }),
        "Equiv.fwd (coeEquiv L) x must be a stuck coe for an opaque line; got {reduct:?}"
    );
    assert!(
        !tc.is_def_eq(&fwd, &cst("xL1")),
        "coeEquiv L must not collapse to the identity for a generic line"
    );
}
