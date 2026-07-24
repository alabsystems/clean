// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for the **`isEquiv` (contractible-fiber) layer** that the
//! CCHM `transp`-over-`Glue` correction needs (the kernel's `Equiv` is only a
//! quasi-inverse `(f,g,η,ε)`; the Glue `comp` consumes the equivalence's
//! `equivProof` / contractible-fiber structure).
//!
//! Encodings (plain `Const`/`App` over the reserved `Sigma.*` axioms — see
//! [`register_sigma_axioms`]):
//!
//! ```text
//! fiber f y   := Σ (x:A). Path (λ_.B) (f x) y
//! isContr F   := Σ (c:F). (x:F) → Path (λ_.F) c x
//! isEquiv f   := (y:B) → isContr (fiber f y)
//! ```
//!
//! The crux is [`is_equiv_coe`] (`isEquivTransport`): **coercion along a line has
//! contractible fibers**, proved as a genuine `coe` of [`id_is_equiv`] (the
//! identity's contractible fibers / co-singleton contractibility) — no `sorry`, no
//! axiomatized `isEquiv` witness.

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{
    coe_equiv_is_equiv, fiber_type, id_is_equiv, is_contr_type, is_equiv_coe, is_equiv_type,
    register_glue_axioms, register_kan_system_axioms, register_sigma_axioms,
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
/// `λ (z:A). z` — the identity on `A`.
fn id_on(a: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, a, Expr::bvar(0))
}
/// `App(L, r)`.
fn l_at(r: Expr) -> Expr {
    Expr::app(cst("L"), r)
}

// ── Environment ─────────────────────────────────────────────────────────────────

/// Cubical env: Kan + Glue + Sigma axioms, plus an **opaque** `A : Type` with a
/// point `ya : A`, and a genuinely interval-dependent line `L : I → Type`.
/// `A`/`L` being opaque axioms keeps every assertion non-vacuous.
fn isequiv_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("register kan system axioms");
    register_glue_axioms(&mut env).expect("register glue axioms");
    register_sigma_axioms(&mut env).expect("register sigma axioms");

    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };

    axiom("A", Expr::type_());
    axiom("ya", cst("A"));
    axiom(
        "L",
        Expr::pi(BinderInfo::Default, interval(), Expr::type_()),
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

/// `fiber`, `isContr`, `isEquiv` are all `Sort 1` (`Type`) for an opaque `A`.
#[test]
fn test_definitions_typecheck_at_right_sorts() {
    let env = isequiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // fiber (id_A) ya : Type.
    let fib = fiber_type(
        type_level(),
        &cst("A"),
        &cst("A"),
        &id_on(cst("A")),
        &cst("ya"),
    );
    assert_is_sort(&tc, &fib, type_level());

    // isContr (fiber id ya) : Type.
    let contr = is_contr_type(type_level(), &fib);
    assert_is_sort(&tc, &contr, type_level());

    // isEquiv (id_A) : Type.
    let ie = is_equiv_type(type_level(), &cst("A"), &cst("A"), &id_on(cst("A")));
    assert_is_sort(&tc, &ie, type_level());
}

/// `idIsEquiv A : isEquiv (λ x. x)` — the identity's contractible fibers
/// type-check as a **genuine proof term** (the co-singleton contraction is
/// discharged, not asserted).
#[test]
fn test_id_is_equiv_typechecks() {
    let env = isequiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proof = id_is_equiv(type_level(), &cst("A"));
    let ty = infer_ty(&tc, &proof);

    let expected = is_equiv_type(type_level(), &cst("A"), &cst("A"), &id_on(cst("A")));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "idIsEquiv A : isEquiv id; got {ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 2 — the crux: coe-along-a-line is an isEquiv (opaque line)
// ═════════════════════════════════════════════════════════════════════════════

/// **The crux**: `isEquivCoe L` type-checks as `isEquiv (λ x. coe L i1 i0 x)` for an
/// opaque line `L : I → Type`. The whole fiber contraction is carried by a genuine
/// `coe` of `idIsEquiv (L i1)` — this is the `equivProof` structure the Glue-`comp`
/// correction needs, beyond the kernel's quasi-inverse `Equiv`.
#[test]
fn test_is_equiv_coe_typechecks_opaque_line() {
    let env = isequiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proof = is_equiv_coe(type_level(), &cst("L"));
    let ty = infer_ty(&tc, &proof);

    // Expected: isEquiv (λ x. coe L i1 i0 x), i.e. (coe L i1 i0) has contractible fibers.
    let fwd = Expr::lam(
        BinderInfo::Default,
        l_at(i1()),
        coe(cst("L"), i1(), i0(), Expr::bvar(0)),
    );
    let expected = is_equiv_type(type_level(), &l_at(i1()), &l_at(i0()), &fwd);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "isEquivCoe L : isEquiv (coe L i1 i0); got {ty:?}"
    );
}

/// Non-vacuity guard: the expected `isEquiv (coe L i1 i0)` is NOT definitionally the
/// `isEquiv` of the identity on `L i1` — the opaque line's forward map is a genuinely
/// stuck `coe`, so the crux test above is meaningful (not trivially `isEquiv id`).
#[test]
fn test_is_equiv_coe_target_is_not_id_for_opaque_line() {
    let env = isequiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let fwd = Expr::lam(
        BinderInfo::Default,
        l_at(i1()),
        coe(cst("L"), i1(), i0(), Expr::bvar(0)),
    );
    let target = is_equiv_type(type_level(), &l_at(i1()), &l_at(i0()), &fwd);
    // isEquiv (id_{L i1}) — what it would be if the line collapsed.
    let id_ty = is_equiv_type(type_level(), &l_at(i1()), &l_at(i1()), &id_on(l_at(i1())));
    assert!(
        !tc.is_def_eq(&target, &id_ty),
        "an opaque line's coe-isEquiv must NOT collapse to isEquiv id"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 3 — constant-line sanity (regularity: coe over a constant line is the identity)
// ═════════════════════════════════════════════════════════════════════════════

/// **Constant-line sanity**: `isEquivCoe (λ_.A)` degenerates to the identity
/// equivalence's `isEquiv`. Its inferred type is `isEquiv (λ x. coe (λ_.A) i1 i0 x)`,
/// which — by the constant-line `coe` rule (`coe (λ_.A) i1 i0 x ≡ x`) — is
/// definitionally `isEquiv (λ x. x)`, matching `idIsEquiv A`'s type.
#[test]
fn test_is_equiv_coe_constant_line_degenerates_to_id() {
    let env = isequiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let const_line = Expr::lam(BinderInfo::Default, interval(), cst("A")); // λ_:I. A
    let proof = is_equiv_coe(type_level(), &const_line);
    let ty = infer_ty(&tc, &proof);

    // The type degenerates to isEquiv (id_A).
    let id_isequiv_ty = is_equiv_type(type_level(), &cst("A"), &cst("A"), &id_on(cst("A")));
    assert!(
        tc.is_def_eq(&ty, &id_isequiv_ty),
        "isEquivCoe (λ_.A) : isEquiv id (regularity); got {ty:?}"
    );

    // … and that is exactly idIsEquiv A's type.
    let id_ty = infer_ty(&tc, &id_is_equiv(type_level(), &cst("A")));
    assert!(
        tc.is_def_eq(&ty, &id_ty),
        "isEquivCoe (λ_.A) and idIsEquiv A inhabit the same (identity) isEquiv"
    );
}

/// **coe-over-Σ progress under `isEquivCoe`**: with the new coe-by-type-former
/// rules, `isEquivCoe L` applied to a point now reduces *through* its Pi line into
/// the inner `isContr` (a `Σ`) — `coe`-over-Pi peels the `(y:B)→…` binder, then
/// `coe`-over-Σ fires on the literal `idIsEquiv`-fiber pair — landing on a
/// `Sigma.mk` head rather than a stuck `coe`-over-`isContr`. This is the concrete
/// step toward the residual Glue `comp` (which consumes the contractible-fiber
/// `Σ`-record). The forward-map line `λ x. coe L i1 i x` is genuinely stuck, so
/// the progress is non-vacuous (not a constant-line collapse).
#[test]
fn test_is_equiv_coe_computes_through_sigma_layer() {
    let mut env = isequiv_env();
    // A point `yL0 : L i0` to feed the `isEquiv`'s `(y:B)→…` binder.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("yL0"),
        level_params: vec![],
        type_: l_at(i0()),
    })
    .expect("yL0 registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proof = is_equiv_coe(type_level(), &cst("L"));
    // `isEquivCoe L` itself reduces to a lambda (the Pi-coe already fired).
    let proof_whnf = tc.whnf(&proof);
    assert!(
        matches!(proof_whnf.kind(), ExprKind::Lam(..)),
        "isEquivCoe L should reduce to a λ (the Pi-coe); got {proof_whnf:?}"
    );
    // Applied to `yL0`, it computes *through* the inner `isContr` Σ: the result is
    // a literal `Sigma.mk` (the coerced contractible-fiber record), NOT a stuck
    // `coe`-over-`isContr`.
    let applied = Expr::app(proof, cst("yL0"));
    let r = tc.whnf(&applied);
    assert!(
        matches!(r.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Sigma.mk")),
        "isEquivCoe L yL0 should compute into a Sigma.mk (coe-over-Σ fired); got {r:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 4 — packaged contractible-fiber equivalence record (deliverable 3)
// ═════════════════════════════════════════════════════════════════════════════

/// `coeEquivIsEquiv L : Σ (f : L i1 → L i0). isEquiv f` — the forward coe map paired
/// with its contractible-fiber proof (the record a Glue-`comp` correction consumes).
#[test]
fn test_coe_equiv_is_equiv_packages_sigma_record() {
    let env = isequiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let record = coe_equiv_is_equiv(type_level(), &cst("L"));
    let ty = infer_ty(&tc, &record);

    // Expected: Σ (f : L i1 → L i0). isEquiv f.
    let fn_ty = Expr::arrow(l_at(i1()), l_at(i0()));
    let bfam = Expr::lam(
        BinderInfo::Default,
        fn_ty.clone(),
        is_equiv_type(type_level(), &l_at(i1()), &l_at(i0()), &Expr::bvar(0)),
    );
    let expected = Expr::apps(
        Expr::const_(Name::from_string("Sigma"), vec![type_level()]),
        [fn_ty, bfam],
    );
    assert!(
        tc.is_def_eq(&ty, &expected),
        "coeEquivIsEquiv L : Σ (f:L i1→L i0). isEquiv f; got {ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 5 — Σ-iota: the dependent-pair eliminator computation rule
//
//   Sigma.elim A B M m (Sigma.mk A B a b)  ↝  m a b
//
// Standard β for the dependent sum, type-preserving, Cubical-gated, fires ONLY on
// a literal `Sigma.mk` (a neutral Σ point stays stuck). This is what lets the
// `isContr` fiber **centre** be projected (`.fst` = `Sigma.elim … (λ c _. c) …`).
// ═════════════════════════════════════════════════════════════════════════════

/// `Sigma A (λ_.A)` — a *non-dependent* pair over the opaque `A` (second component
/// also `A`). The motive/minor pick out the first component.
fn sigma_aa() -> Expr {
    let bfam = Expr::lam(BinderInfo::Default, cst("A"), cst("A")); // λ_:A. A
    Expr::apps(
        Expr::const_(Name::from_string("Sigma"), vec![type_level()]),
        [cst("A"), bfam],
    )
}
/// `Sigma.mk.{1} A (λ_.A) fst snd`.
fn sigma_mk_aa(fst: Expr, snd: Expr) -> Expr {
    let bfam = Expr::lam(BinderInfo::Default, cst("A"), cst("A"));
    Expr::apps(
        Expr::const_(Name::from_string("Sigma.mk"), vec![type_level()]),
        [cst("A"), bfam, fst, snd],
    )
}
/// `Sigma.elim.{1} A (λ_.A) M m p`.
fn sigma_elim_aa(motive: Expr, minor: Expr, p: Expr) -> Expr {
    let bfam = Expr::lam(BinderInfo::Default, cst("A"), cst("A"));
    Expr::apps(
        Expr::const_(Name::from_string("Sigma.elim"), vec![type_level()]),
        [cst("A"), bfam, motive, minor, p],
    )
}
/// Motive `λ _:Sigma A (λ_.A). A` (a constant motive landing in `A : Type`).
fn const_a_motive() -> Expr {
    Expr::lam(BinderInfo::Default, sigma_aa(), cst("A"))
}
/// First-projection minor `λ (a:A). λ (b:A). a`.
fn fst_minor() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        cst("A"),
        Expr::lam(BinderInfo::Default, cst("A"), Expr::bvar(1)),
    )
}
/// Second-projection minor `λ (a:A). λ (b:A). b`.
fn snd_minor() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        cst("A"),
        Expr::lam(BinderInfo::Default, cst("A"), Expr::bvar(0)),
    )
}

/// `sigma_iota_env` = the `isEquiv` env plus a *second* opaque point `yb : A` (so
/// the two projections are genuinely distinguishable — the iota landing on the
/// wrong component would be caught).
fn sigma_iota_env() -> Environment {
    let mut env = isequiv_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("yb"),
        level_params: vec![],
        type_: cst("A"),
    })
    .expect("yb axiom registers");
    env
}

/// **Σ-iota fires** on a literal pair: `Sigma.elim … (λ a b. a) (Sigma.mk … ya yb)`
/// reduces (via the iota, then β) to the FIRST component `ya`; the second-projection
/// minor reduces to `yb`. Non-vacuous: `ya ≢ yb` (two distinct opaque points), so
/// landing on the wrong component would be observable.
#[test]
fn test_sigma_iota_fires_and_projects_correct_component() {
    let env = sigma_iota_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let pair = sigma_mk_aa(cst("ya"), cst("yb"));

    let fst = sigma_elim_aa(const_a_motive(), fst_minor(), pair.clone());
    let fst_r = tc.whnf(&fst);
    assert!(
        tc.is_def_eq(&fst_r, &cst("ya")),
        "Σ-iota + β must project the first component ya; got {fst_r:?}"
    );

    let snd = sigma_elim_aa(const_a_motive(), snd_minor(), pair);
    let snd_r = tc.whnf(&snd);
    assert!(
        tc.is_def_eq(&snd_r, &cst("yb")),
        "Σ-iota + β must project the second component yb; got {snd_r:?}"
    );

    // Non-vacuity: the two opaque points are genuinely distinct.
    assert!(
        !tc.is_def_eq(&cst("ya"), &cst("yb")),
        "ya ≡ yb — the projection test would be vacuous"
    );
    // The iota genuinely fired: the reduct is NOT a stuck `Sigma.elim` spine.
    assert!(
        !matches!(fst_r.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Sigma.elim")),
        "the iota must consume the Sigma.elim head; got {fst_r:?}"
    );
}

/// **Type preservation**: the redex `Sigma.elim A (λ_.A) M m (Sigma.mk …) : M p`
/// and its contractum `m a b` infer to the same type (`A`, the constant motive).
#[test]
fn test_sigma_iota_preserves_type() {
    let env = sigma_iota_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let pair = sigma_mk_aa(cst("ya"), cst("yb"));
    let redex = sigma_elim_aa(const_a_motive(), fst_minor(), pair);

    let redex_ty = infer_ty(&tc, &redex);
    let reduct = tc.whnf(&redex);
    let reduct_ty = infer_ty(&tc, &reduct);
    assert!(
        tc.is_def_eq(&redex_ty, &reduct_ty),
        "Σ-iota must preserve type: redex {redex_ty:?} vs reduct {reduct_ty:?}"
    );
    // The constant motive pins both at `A`.
    assert!(
        tc.is_def_eq(&redex_ty, &cst("A")),
        "the redex should infer to A; got {redex_ty:?}"
    );
}

/// **No over-fire on a neutral Σ**: `Sigma.elim … m p` for an *opaque* point
/// `p : Sigma A (λ_.A)` (not a literal `Sigma.mk`) stays STUCK — the WHNF is still
/// a `Sigma.elim`-headed spine.
#[test]
fn test_sigma_iota_does_not_fire_on_neutral_pair() {
    let mut env = sigma_iota_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pp"),
        level_params: vec![],
        type_: sigma_aa(),
    })
    .expect("opaque Σ point pp registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let stuck = sigma_elim_aa(const_a_motive(), fst_minor(), cst("pp"));
    let reduct = tc.whnf(&stuck);
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Sigma.elim")),
        "Σ-iota must stay stuck on a neutral pair; got {reduct:?}"
    );
    // Still well-typed (M pp = A) — the stuck eliminator is sound.
    let ty = infer_ty(&tc, &stuck);
    assert!(
        tc.is_def_eq(&ty, &cst("A")),
        "stuck Sigma.elim still infers to A; got {ty:?}"
    );
}

/// **Σ-iota is gated to Cubical mode** indirectly via the dispatch site: in a
/// non-cubical env the `Sigma.*` axioms are not even registered, so the rule has
/// nothing to fire on. Here we assert the rule does not interfere with a literal
/// pair whose components are themselves projected — i.e. nested iota composes
/// (`fst (mk (snd (mk ya yb)) ya) ↝ yb`).
#[test]
fn test_sigma_iota_composes_nested() {
    let env = sigma_iota_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // inner = snd (mk ya yb) ↝ yb
    let inner = sigma_elim_aa(
        const_a_motive(),
        snd_minor(),
        sigma_mk_aa(cst("ya"), cst("yb")),
    );
    // outer = fst (mk inner ya) ↝ inner ↝ yb
    let outer = sigma_elim_aa(const_a_motive(), fst_minor(), sigma_mk_aa(inner, cst("ya")));
    let reduct = tc.whnf(&outer);
    assert!(
        tc.is_def_eq(&reduct, &cst("yb")),
        "nested Σ-iota must compose to yb; got {reduct:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 6 — residual coe-over-Glue: the carried-isEquiv fibre CENTRE is value-correct
//
// The residual rule reads the cell's carried `isEquiv` and projects the fibre
// centre `(ie(s) a₁).fst.{fst,snd}`. These probes verify, on the opaque line `L`:
//   (P1) the centre POINT `(is_equiv_coe L ya).fst.fst` computes AND equals the
//        independently-known coherent inverse `coe L i0 i1 ya` (= Equiv.bwd of
//        coeEquiv L) — the value-correctness oracle for the centre;
//   (P2) the centre PATH `.fst.snd` reduces and has the fibre's right endpoint.
// ═════════════════════════════════════════════════════════════════════════════

/// WHNF `e`, assert it is a literal `Sigma.mk A B fst snd`, return `(fst, snd)`.
fn sigma_mk_proj(tc: &TypeChecker<'_>, e: &Expr) -> (Expr, Expr) {
    let w = tc.whnf(e);
    assert!(
        matches!(w.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Sigma.mk")),
        "expected a literal Sigma.mk; got {w:?}"
    );
    let args = w.get_app_args();
    assert_eq!(args.len(), 4, "Sigma.mk takes (A,B,fst,snd); got {w:?}");
    (args[2].clone(), args[3].clone())
}

/// (P1) `(is_equiv_coe L ya).fst.fst ≡ coe L i0 i1 ya` — the carried-isEquiv fibre
/// centre point is the genuine coherent inverse (the value the residual rule
/// glues). `ya : L i0` (the codomain of the forward map `coe L i1 i0`).
#[test]
fn test_residual_centre_point_is_coherent_inverse() {
    let mut env = isequiv_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("yL0"),
        level_params: vec![],
        type_: l_at(i0()),
    })
    .expect("yL0 registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // isContr (fiber (coe L i1 i0) yL0) = (is_equiv_coe L) applied at yL0.
    let ie_at = Expr::app(is_equiv_coe(type_level(), &cst("L")), cst("yL0"));
    // .fst = the fibre centre  (Σ (x:L i1). Path (L i0) (coe L i1 i0 x) yL0).
    let (centre, _contr) = sigma_mk_proj(&tc, &ie_at);
    // centre.fst = the point x₁ : L i1.
    let (x1, pth) = sigma_mk_proj(&tc, &centre);

    // The independently-known coherent inverse: coe L i0 i1 yL0 : L i1.
    let inverse = coe(cst("L"), i0(), i1(), cst("yL0"));
    assert!(
        tc.is_def_eq(&x1, &inverse),
        "residual centre point must be the coherent inverse coe L i0 i1 yL0; got {x1:?}"
    );

    // (P2) the centre path is a genuine Path whose right endpoint is yL0.
    let pty = tc
        .infer_type_with_cert(&pth)
        .expect("centre path should type-check")
        .0;
    let pty_w = tc.whnf(&pty);
    let ExprKind::CubicalPath { right, .. } = pty_w.kind() else {
        panic!("centre .snd must be a Path; got {pty_w:?}");
    };
    assert!(
        tc.is_def_eq(right, &cst("yL0")),
        "centre path right endpoint must be yL0; got {right:?}"
    );
}

/// Non-vacuity: the coherent inverse `coe L i0 i1 yL0` is a genuinely **stuck**
/// neutral coe for the opaque line (not collapsed), so (P1) is meaningful.
#[test]
fn test_residual_centre_inverse_is_nontrivial() {
    let mut env = isequiv_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("yL0"),
        level_params: vec![],
        type_: l_at(i0()),
    })
    .expect("yL0 registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let inverse = coe(cst("L"), i0(), i1(), cst("yL0"));
    // It must NOT be def-eq to yL0 itself (which would mean the line collapsed).
    assert!(
        !tc.is_def_eq(&inverse, &cst("yL0")),
        "coe L i0 i1 yL0 must be a non-trivial transport for the opaque line"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 7 — THE RESIDUAL coe-over-Glue rule: fires on a genuinely-neutral-φ Glue line
//
// Build a single-cell Glue line whose face is NEUTRAL at the target endpoint, by
// routing through the hcomp-in-universe rule (so the kernel itself builds the
// `coeEquiv`/`is_equiv_coe` cell witnesses under the opened fvar — no hand-built
// de-Bruijn):
//
//   line(i) := hcomp {Type} [(kv=1) ↦ (λ j. L (i ∧ j))] (L i0)
//            ↝ Glue (L i0) (kv=1) [(kv=1) ↦ (L i, coeEquiv …, is_equiv_coe …)]
//   coe line i0 i1 gbase   — at s=i1 the face (kv=1) is NEUTRAL ⇒ residual.
//
// The residual rule reads the carried `is_equiv_coe` witness, projects the fibre
// centre, builds the correction hcomp, and assembles a `glue`. Probes the Glue
// laws (a)/(b)/(e).
// ═════════════════════════════════════════════════════════════════════════════

fn i_min(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("I.min"), vec![]), [a, b])
}
fn cofib_eq1(r: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Cofib.eq1"), vec![]), r)
}

/// The residual Glue coercion line `λ i. hcomp {Type} [(kv=1)↦(λj. L(i∧j))] (L i0)`
/// (under `λ i`: i = BVar0; under the tube `λ j`: i = BVar1, j = BVar0).
fn residual_glue_coe(base: Expr) -> Expr {
    // tube = λ j:I. L (i ∧ j).
    let tube = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(cst("L"), i_min(Expr::bvar(1), Expr::bvar(0))),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(Expr::type_()),
        phi: Arc::new(cofib_eq1(cst("kv"))),
        u: Arc::new(tube),
        base: Arc::new(l_at(i0())), // floor A = L i0
    });
    let line = Expr::lam(BinderInfo::Default, interval(), hcomp);
    coe(line, i0(), i1(), base)
}

#[test]
fn test_residual_coe_glue_fires_and_obeys_laws() {
    let mut env = isequiv_env();
    // A neutral face variable `kv : I` and an opaque base `gbase` in the Glue at i0.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("kv"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("kv registers");
    // gbase : line(i0)  (the source Glue type — `(λi. hcomp …) i0`, β-reduces to the
    // Glue at i0). An opaque inhabitant suffices: `a0 = unglue@i0 gbase` stays neutral.
    let glue_at_i0 = {
        let l = residual_glue_coe(cst("kv")); // borrow the line shape
        let ExprKind::CubicalCoe { ty, .. } = l.kind() else {
            unreachable!()
        };
        Expr::app(ty.as_ref().clone(), i0())
    };
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gbase"),
        level_params: vec![],
        type_: glue_at_i0,
    })
    .expect("gbase registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let the_coe = residual_glue_coe(cst("gbase"));

    // (type preservation) the residual coe type-checks at line(i1) ≡ Glue (L i0) ….
    let coe_ty = tc
        .infer_type_with_cert(&the_coe)
        .expect("residual coe-over-Glue should type-check (type preservation)")
        .0;
    let coe_ty_w = tc.whnf(&coe_ty);
    assert!(
        matches!(coe_ty_w.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Glue")),
        "residual coe : Glue (L i0) (kv=1) […]; got {coe_ty_w:?}"
    );

    // (fires) whnf is a `glue` intro spine (NOT a stuck coe).
    let reduct = tc.whnf(&the_coe);
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("glue")),
        "the residual rule must fire, producing a `glue` intro; got {reduct:?}"
    );
    let gargs = reduct.get_app_args();
    assert_eq!(
        gargs.len(),
        7,
        "glue B T φ e ie t a — 7 args; got {reduct:?}"
    );

    // (cap discharges + type preservation) inferring the RESULT's type type-checks the
    // correction `hcomp` inside it (its `validate_hcomp_cap` side-condition must pass),
    // and the result inhabits the SAME Glue type as the coe (genuine type preservation).
    let reduct_ty = tc
        .infer_type_with_cert(&reduct)
        .expect("the residual `glue` result (incl. its correction hcomp) must type-check")
        .0;
    assert!(
        tc.is_def_eq(&reduct_ty, &coe_ty),
        "the residual result must inhabit the coe's type (preservation); got {reduct_ty:?}"
    );

    // (e: centre value-correct) the glued cell value t₁ (arg 5) is the coherent
    // inverse `coe L i0 i1 a₁`, a CONCRETE coe — not a stuck Sigma.elim projection.
    let t1 = gargs[5];
    let t1_w = tc.whnf(t1);
    assert!(
        !matches!(t1_w.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Sigma.elim")),
        "the glued cell value must have computed (not a stuck Sigma.elim); got {t1_w:?}"
    );
    // a₁ = coe (λ_.L i0) i0 i1 (unglue@i0 gbase) ≡ unglue@i0 gbase (constant base).
    // sys@i0: read it back from the produced Glue at i0 (same shape the rule used).
    let line_i0 = {
        let l = residual_glue_coe(cst("kv"));
        let ExprKind::CubicalCoe { ty, .. } = l.kind() else {
            unreachable!()
        };
        Expr::app(ty.as_ref().clone(), i0())
    };
    let g0 = tc.whnf(&line_i0);
    let sys_at_i0 = g0.get_app_args()[2].clone();
    let a0 = Expr::apps(
        Expr::const_(Name::from_string("unglue"), vec![type_level()]),
        [l_at(i0()), cofib_eq1(cst("kv")), sys_at_i0, cst("gbase")],
    );
    let expected_t1 = coe(cst("L"), i0(), i1(), a0);
    assert!(
        tc.is_def_eq(t1, &expected_t1),
        "glued cell value t₁ must be the coherent inverse coe L i0 i1 a₁;\n  t₁ = {t1:?}\n  exp = {expected_t1:?}"
    );

    // (a: unglue-β) `unglue (result) ↝ a₁''` — the correction hcomp (glue arg 6).
    let a1pp = gargs[6].clone();
    let ung = Expr::apps(
        Expr::const_(Name::from_string("unglue"), vec![type_level()]),
        [
            gargs[0].clone(),
            gargs[2].clone(),
            {
                // sys = Glue.Sys.cons B φ T e ie (nil B) — rebuild from the glue args.
                let cons = Expr::const_(Name::from_string("Glue.Sys.cons"), vec![type_level()]);
                let nil = Expr::app(
                    Expr::const_(Name::from_string("Glue.Sys.nil"), vec![type_level()]),
                    gargs[0].clone(),
                );
                Expr::apps(
                    cons,
                    [
                        gargs[0].clone(),
                        gargs[2].clone(),
                        gargs[1].clone(),
                        gargs[3].clone(),
                        gargs[4].clone(),
                        nil,
                    ],
                )
            },
            reduct.clone(),
        ],
    );
    let ung_r = tc.whnf(&ung);
    assert!(
        tc.is_def_eq(&ung_r, &a1pp),
        "unglue (residual result) must β-reduce to the correction hcomp a₁''; got {ung_r:?}"
    );
}

/// SOUNDNESS GUARD: a residual coe over a Glue line whose cell equivalence is
/// **opaque** (carried witness `Equiv.toIsEquiv`, the `ua`-cell shape) must stay
/// **STUCK** — the fibre centre never computes, so the rule returns `None` and the
/// coe is left as a neutral `CubicalCoe`, never a value-wrong glue. This is the
/// guard that the residual rule fires ONLY on coherent computing witnesses.
#[test]
fn test_residual_coe_glue_opaque_cell_stays_stuck() {
    let mut env = isequiv_env();
    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name}: {e:?}"));
    };
    axiom("kv", interval());
    axiom(
        "Ab",
        Expr::pi(BinderInfo::Default, interval(), Expr::type_()),
    ); // base line
    axiom("Tc", Expr::type_()); // cell type (constant)
                                // el : (i:I) → Equiv Tc (Ab i) — an OPAQUE per-i cell equivalence.
    axiom(
        "el",
        Expr::pi(
            BinderInfo::Default,
            interval(),
            Expr::apps(
                Expr::const_(Name::from_string("Equiv"), vec![type_level()]),
                [cst("Tc"), Expr::app(cst("Ab"), Expr::bvar(0))],
            ),
        ),
    );

    // line(i) = Glue (Ab i) (kv=1) [(kv=1) ↦ (Tc, el i, Equiv.toIsEquiv Tc (Ab i) (el i))].
    let ab_i = Expr::app(cst("Ab"), Expr::bvar(0));
    let el_i = Expr::app(cst("el"), Expr::bvar(0));
    let to_ie = Expr::apps(
        Expr::const_(Name::from_string("Equiv.toIsEquiv"), vec![type_level()]),
        [cst("Tc"), ab_i.clone(), el_i.clone()],
    );
    let nil = Expr::app(
        Expr::const_(Name::from_string("Glue.Sys.nil"), vec![type_level()]),
        ab_i.clone(),
    );
    let cell = Expr::apps(
        Expr::const_(Name::from_string("Glue.Sys.cons"), vec![type_level()]),
        [
            ab_i.clone(),
            cofib_eq1(cst("kv")),
            cst("Tc"),
            el_i,
            to_ie,
            nil,
        ],
    );
    let glue_i = Expr::apps(
        Expr::const_(Name::from_string("Glue"), vec![type_level()]),
        [ab_i, cofib_eq1(cst("kv")), cell],
    );
    let line = Expr::lam(BinderInfo::Default, interval(), glue_i);

    // gbase : line(i0).
    let glue_i0 = Expr::app(line.clone(), i0());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gbase2"),
        level_params: vec![],
        type_: glue_i0,
    })
    .expect("gbase2 registers");

    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let the_coe = coe(line, i0(), i1(), cst("gbase2"));
    let reduct = tc.whnf(&the_coe);
    assert!(
        matches!(reduct.kind(), ExprKind::CubicalCoe { .. }),
        "an opaque-cell residual coe must stay STUCK (never a value-wrong glue); got {reduct:?}"
    );
}
