// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for **Glue types** and **univalence (`ua`)** — Glue
//! Phases 0–2 (formation + boundary reduction + `unglue` β).
//!
//! All terms are built directly as kernel `Expr`s; `Glue`/`glue`/`unglue`/`Equiv`
//! and the Glue-system constructors are registered as interval/type-valued axioms
//! via [`register_glue_axioms`] (and the cofibration faces via
//! [`register_kan_system_axioms`]), so the existing inference / certificate
//! machinery accepts the encoding unchanged — they are plain `Const`/`App`
//! spines, no new `ExprKind` variant.
//!
//! The headline test is [`test_ua_typechecks`]: `ua e : A = B` type-checks, i.e.
//! `infer(ua e) ≡ Path (λ_.Type) A B`, driven entirely by the Glue boundary rule.

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::cofib::Cofib;
use crate::tc::reduction::kan::{glue_ua, register_glue_axioms, register_kan_system_axioms};
use std::sync::Arc;

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

/// The level of `A : Type` (= `Sort 1`).
fn type_level() -> Level {
    Level::succ(Level::zero())
}

/// `Equiv A B` at the type universe (`Equiv.{1} A B`).
fn equiv_ty(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Equiv"), vec![type_level()]),
        [a.clone(), b.clone()],
    )
}

/// `Equiv.toIsEquiv T B e : isEquiv (Equiv.fwd e)` — the opaque carried isEquiv
/// witness for a cell whose equivalence `e : Equiv T B` is opaque (the test `e`).
fn to_is_equiv(t: &Expr, b: &Expr, e: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Equiv.toIsEquiv"), vec![type_level()]),
        [t.clone(), b.clone(), e.clone()],
    )
}

/// A single-cell Glue system `[φ ↦ (T, e, ie)]` over `B`, i.e.
/// `Glue.Sys.cons B φ T e ie (Glue.Sys.nil B)` with `ie = Equiv.toIsEquiv T B e`.
fn glue_sys_one(b: &Expr, phi: Expr, t: &Expr, e: &Expr) -> Expr {
    let cons = Expr::const_(Name::from_string("Glue.Sys.cons"), vec![type_level()]);
    let nil = Expr::app(
        Expr::const_(Name::from_string("Glue.Sys.nil"), vec![type_level()]),
        b.clone(),
    );
    Expr::apps(
        cons,
        [
            b.clone(),
            phi,
            t.clone(),
            e.clone(),
            to_is_equiv(t, b, e),
            nil,
        ],
    )
}

/// `Glue B φ sys`.
fn glue_ty(b: &Expr, phi: Expr, sys: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Glue"), vec![type_level()]),
        [b.clone(), phi, sys],
    )
}

/// `glue B T φ e ie t a` with `ie = Equiv.toIsEquiv T B e`.
fn glue_intro(b: &Expr, t_ty: &Expr, phi: Expr, e: &Expr, t: &Expr, a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("glue"), vec![type_level()]),
        [
            b.clone(),
            t_ty.clone(),
            phi,
            e.clone(),
            to_is_equiv(t_ty, b, e),
            t.clone(),
            a.clone(),
        ],
    )
}

/// `unglue B φ sys g`.
fn unglue(b: &Expr, phi: Expr, sys: Expr, g: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("unglue"), vec![type_level()]),
        [b.clone(), phi, sys, g],
    )
}

/// The literal total cofibration `⊤` (`Cofib.top : I`).
fn top() -> Expr {
    cst("Cofib.top")
}

/// Cubical environment with the Kan + Glue axioms plus
/// `A B : Type`, `e : Equiv A B`, `ta : A`, `ab : B`.
fn glue_env() -> Environment {
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
    axiom("B", Expr::type_());
    axiom("e", equiv_ty(&cst("A"), &cst("B")));
    axiom("ta", cst("A")); // an element of A
    axiom("ab", cst("B")); // an element of B
    env
}

/// The expected univalence target type `Path (λ_.Type) A B` (= `A = B`).
fn path_a_b() -> Expr {
    let fam = Expr::lam(BinderInfo::Default, interval(), Expr::type_());
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(fam),
        left: Arc::new(cst("A")),
        right: Arc::new(cst("B")),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 1 — Glue boundary on a total face
// ─────────────────────────────────────────────────────────────────────────────

/// `Glue B [⊤ ↦ (A, e)] ≡ A` (def_eq), driven by the first-total-cell boundary
/// rule, and the term itself type-checks at `Sort 1` (= `Type`).
#[test]
fn test_glue_boundary_total_face() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let sys = glue_sys_one(&cst("B"), top(), &cst("A"), &cst("e"));
    let g = glue_ty(&cst("B"), top(), sys);

    // The Glue type-former application type-checks at Type.
    let (g_ty, _) = tc
        .infer_type_with_cert(&g)
        .expect("Glue B [⊤↦(A,e)] should type-check");
    assert!(
        tc.is_def_eq(&g_ty, &Expr::type_()),
        "Glue … : Type; got {g_ty:?}"
    );

    // Boundary rule: a total cell face reduces Glue to that cell's type.
    let reduct = tc.whnf(&g);
    assert!(
        tc.is_def_eq(&reduct, &cst("A")),
        "Glue B [⊤↦(A,e)] must reduce to A; got {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&g, &cst("A")),
        "Glue B [⊤↦(A,e)] ≡ A definitionally"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 2 — unglue β
// ─────────────────────────────────────────────────────────────────────────────

/// `unglue (glue t a) ≡ a` (def_eq), driven by the unglue-β projection rule.
#[test]
fn test_unglue_beta() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // g = glue B A ⊤ e ta ab  :  Glue B ⊤ [⊤↦(A,e)].
    let g = glue_intro(
        &cst("B"),
        &cst("A"),
        top(),
        &cst("e"),
        &cst("ta"),
        &cst("ab"),
    );
    let sys = glue_sys_one(&cst("B"), top(), &cst("A"), &cst("e"));
    let term = unglue(&cst("B"), top(), sys, g);

    // The full unglue application type-checks at B.
    let (term_ty, _) = tc
        .infer_type_with_cert(&term)
        .expect("unglue (glue …) should type-check");
    assert!(
        tc.is_def_eq(&term_ty, &cst("B")),
        "unglue … : B; got {term_ty:?}"
    );

    // β rule: unglue (glue B T φ e t a) ↝ a.
    let reduct = tc.whnf(&term);
    assert!(
        tc.is_def_eq(&reduct, &cst("ab")),
        "unglue (glue … a) must reduce to a (= ab); got {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&term, &cst("ab")),
        "unglue (glue … a) ≡ a definitionally"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 3 — `ua e : A = B` type-checks (THE soundness anchor)
// ─────────────────────────────────────────────────────────────────────────────

/// `infer(ua e) ≡ Path (λ_.Type) A B`, and the endpoints compute:
/// `(ua e) @ i0 ≡ A`, `(ua e) @ i1 ≡ B`. This works iff the Glue boundary rule
/// is correct (`body[i0] ↝ A`, `body[i1] ↝ B`).
#[test]
fn test_ua_typechecks() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ua = glue_ua(&cst("A"), &cst("B"), &cst("e"), type_level());

    // Headline: ua e : A = B.
    let (inferred, _cert) = tc
        .infer_type_with_cert(&ua)
        .expect("ua e should type-check");
    assert!(
        tc.is_def_eq(&inferred, &path_a_b()),
        "ua e must infer to Path (λ_.Type) A B; got {inferred:?}"
    );

    // Endpoint computation: (ua e) @ i0 ≡ A, (ua e) @ i1 ≡ B.
    let at_i0 = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(ua.clone()),
        arg: Arc::new(i0()),
    });
    let at_i1 = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(ua),
        arg: Arc::new(i1()),
    });
    assert!(
        tc.is_def_eq(&at_i0, &cst("A")),
        "(ua e) @ i0 must compute to A"
    );
    assert!(
        tc.is_def_eq(&at_i1, &cst("B")),
        "(ua e) @ i1 must compute to B"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 4 — type preservation of the Glue/unglue reductions
// ─────────────────────────────────────────────────────────────────────────────

/// Every Glue boundary / unglue-β reduction satisfies `infer(lhs) ≡ infer(reduct)`.
#[test]
fn test_glue_unglue_type_preservation() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // (a) Glue boundary: Glue B [⊤↦(A,e)]  ↝  A.
    let sys = glue_sys_one(&cst("B"), top(), &cst("A"), &cst("e"));
    let g = glue_ty(&cst("B"), top(), sys.clone());
    let (g_ty, _) = tc.infer_type_with_cert(&g).expect("Glue should type-check");
    let g_reduct = tc.whnf(&g);
    let (g_reduct_ty, _) = tc
        .infer_type_with_cert(&g_reduct)
        .expect("Glue reduct should type-check");
    assert!(
        tc.is_def_eq(&g_ty, &g_reduct_ty),
        "Glue boundary reduction must preserve type"
    );

    // (b) unglue β: unglue B ⊤ sys (glue B A ⊤ e ta ab)  ↝  ab.
    let intro = glue_intro(
        &cst("B"),
        &cst("A"),
        top(),
        &cst("e"),
        &cst("ta"),
        &cst("ab"),
    );
    let term = unglue(&cst("B"), top(), sys, intro);
    let (term_ty, _) = tc
        .infer_type_with_cert(&term)
        .expect("unglue should type-check");
    let term_reduct = tc.whnf(&term);
    let (term_reduct_ty, _) = tc
        .infer_type_with_cert(&term_reduct)
        .expect("unglue reduct should type-check");
    assert!(
        tc.is_def_eq(&term_ty, &term_reduct_ty),
        "unglue β reduction must preserve type"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 5 — parse_glue_system round-trips a two-cell system
// ─────────────────────────────────────────────────────────────────────────────

/// A two-cell Glue system parses to exactly its two faces (the `ua` shape):
/// `[(iv=0)↦(A,e), (iv=1)↦(B,id)]`.
#[test]
fn test_parse_glue_system_two_cells() {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("kan axioms");
    register_glue_axioms(&mut env).expect("glue axioms");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("A");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("B"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("B");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("e"),
        level_params: vec![],
        type_: equiv_ty(&cst("A"), &cst("B")),
    })
    .expect("e");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("iv"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("iv");

    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let face_eq0 = |r: Expr| Expr::app(cst("Cofib.eq0"), r);
    let face_eq1 = |r: Expr| Expr::app(cst("Cofib.eq1"), r);
    let id_b = Expr::app(
        Expr::const_(Name::from_string("Equiv.idEquiv"), vec![type_level()]),
        cst("B"),
    );

    // [(iv=0)↦(A,e), (iv=1)↦(B,id)]  (the ua system shape, with iv neutral).
    // Each cell carries its opaque `Equiv.toIsEquiv` isEquiv witness (arg 4).
    let cons = |b: &Expr, phi: Expr, t: &Expr, e: &Expr, tail: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Glue.Sys.cons"), vec![type_level()]),
            [
                b.clone(),
                phi,
                t.clone(),
                e.clone(),
                to_is_equiv(t, b, e),
                tail,
            ],
        )
    };
    let nil = Expr::app(
        Expr::const_(Name::from_string("Glue.Sys.nil"), vec![type_level()]),
        cst("B"),
    );
    let cell1 = cons(&cst("B"), face_eq1(cst("iv")), &cst("B"), &id_b, nil);
    let sys = cons(&cst("B"), face_eq0(cst("iv")), &cst("A"), &cst("e"), cell1);

    let cells = tc
        .parse_glue_system_for_test(&sys)
        .expect("two-cell glue system should parse");
    assert_eq!(cells.len(), 2, "two cells expected");
    assert_eq!(cells[0].0, Cofib::eq0(0), "cell 1 face is (iv=0)");
    assert_eq!(cells[1].0, Cofib::eq1(0), "cell 2 face is (iv=1)");
    assert!(tc.is_def_eq(&cells[0].1, &cst("A")), "cell 1 type is A");
    assert!(tc.is_def_eq(&cells[1].1, &cst("B")), "cell 2 type is B");
}

// ─────────────────────────────────────────────────────────────────────────────
// Univalence COMPUTATION rule — `transport (ua e) x ↝ Equiv.fwd e x`
// ─────────────────────────────────────────────────────────────────────────────

/// The `ua` coercion line `λ i. Glue B [(i=0)↦(A,e), (i=1)↦(B, Equiv.idEquiv B)]`
/// as an ordinary type-family line `I → Sort u` (the body of `glue_ua` rewrapped
/// from a path-lam into a `coe`-shaped lambda). `transport (ua e) x` is
/// `coe (ua-line) i0 i1 x`.
fn ua_line(a: &Expr, b: &Expr, e: &Expr, level: Level) -> Expr {
    let ua = glue_ua(a, b, e, level);
    let ExprKind::CubicalPathLam { body } = ua.kind() else {
        panic!("glue_ua must produce a CubicalPathLam");
    };
    Expr::lam(BinderInfo::Default, interval(), body.as_ref().clone())
}

/// A *single-cell* Glue line `λ i. Glue B [(i=0)↦(A,e)]` — deliberately NOT the
/// `ua` shape (it lacks the `(i=1)↦(B, idEquiv)` cell), used to confirm the
/// univalence rule does not over-fire.
fn single_cell_glue_line(a: &Expr, b: &Expr, e: &Expr) -> Expr {
    let cofib_eq0 = |arg: Expr| Expr::app(cst("Cofib.eq0"), arg);
    let glue = Expr::const_(Name::from_string("Glue"), vec![type_level()]);
    // i = BVar(0) under the line lambda.
    let sys = glue_sys_one(b, cofib_eq0(Expr::bvar(0)), a, e);
    let glue_ty = Expr::apps(glue, [b.clone(), cofib_eq0(Expr::bvar(0)), sys]);
    Expr::lam(BinderInfo::Default, interval(), glue_ty)
}

/// `Equiv.fwd.{1} A B e x` — the reduct of `transport (ua e) x`.
fn equiv_fwd(a: &Expr, b: &Expr, e: &Expr, x: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Equiv.fwd"), vec![type_level()]),
        [a.clone(), b.clone(), e.clone(), x.clone()],
    )
}

/// THE MILESTONE: `transport (ua e) x ↝ Equiv.fwd e x`, with full
/// type-preservation (`infer(transport (ua e) x) ≡ infer(Equiv.fwd e x) ≡ B`).
#[test]
fn test_transport_ua_computes() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // transport (ua e) x  ≡  coe (ua-line) i0 i1 x,  with x = ta : A.
    let line = ua_line(&cst("A"), &cst("B"), &cst("e"), type_level());
    let coe = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(cst("ta")),
    });

    // The forward map `Equiv.fwd e x`.
    let fwd = equiv_fwd(&cst("A"), &cst("B"), &cst("e"), &cst("ta"));

    // (1) Computation: transport (ua e) x ↝ Equiv.fwd e x.
    let reduct = tc.whnf(&coe);
    assert!(
        tc.is_def_eq(&reduct, &fwd),
        "transport (ua e) x must reduce to Equiv.fwd e x; got {reduct:?}"
    );

    // (2) Type preservation: infer(coe) ≡ infer(fwd) ≡ B.
    let (coe_ty, _) = tc
        .infer_type_with_cert(&coe)
        .expect("transport (ua e) x should type-check");
    let (fwd_ty, _) = tc
        .infer_type_with_cert(&fwd)
        .expect("Equiv.fwd e x should type-check");
    assert!(
        tc.is_def_eq(&coe_ty, &fwd_ty),
        "the ua rewrite must preserve type: coe : {coe_ty:?}, fwd : {fwd_ty:?}"
    );
    assert!(
        tc.is_def_eq(&coe_ty, &cst("B")),
        "transport (ua e) x : B; got {coe_ty:?}"
    );
}

/// `transp (ua e) i0 x ↝ Equiv.fwd e x` — `transp` normalizes to `coe^{i0→i1}`,
/// so the same univalence rule fires through the `transp` head.
#[test]
fn test_transp_ua_computes() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let line = ua_line(&cst("A"), &cst("B"), &cst("e"), type_level());
    let transp = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(line),
        phi: Arc::new(i0()),
        base: Arc::new(cst("ta")),
    });
    let fwd = equiv_fwd(&cst("A"), &cst("B"), &cst("e"), &cst("ta"));

    let reduct = tc.whnf(&transp);
    assert!(
        tc.is_def_eq(&reduct, &fwd),
        "transp (ua e) i0 x must reduce to Equiv.fwd e x; got {reduct:?}"
    );
}

/// No over-fire: coercion over a *non-`ua`* (genuinely residual) Glue line — one
/// with no `⊤` cell at the transport *target* — stays STUCK (never reduces to a
/// forward map). The complementary `ua` line, whose boundary has a `⊤` cell at BOTH
/// endpoints, computes in BOTH orientations (forward ↝ `Equiv.fwd e`, backward ↝
/// `Equiv.bwd e`); see part (b).
#[test]
fn test_coe_non_ua_glue_stays_stuck() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let fwd = equiv_fwd(&cst("A"), &cst("B"), &cst("e"), &cst("ta"));

    // (a) Single-cell Glue line (lacks the `(i=1)↦(B,id)` cell): coe i0 i1 stuck —
    // at the target `i1` the only cell `(i=0)` is `⊥`, so the Glue is residual there
    // and the rule (correctly) declines (the genuinely-general correction is not done).
    let single = single_cell_glue_line(&cst("A"), &cst("B"), &cst("e"));
    let coe_single = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(single),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(cst("ta")),
    });
    let r1 = tc.whnf(&coe_single);
    assert!(
        matches!(r1.kind(), ExprKind::CubicalCoe { .. }),
        "coe over a single-cell (residual) Glue line must stay stuck; got {r1:?}"
    );
    assert!(
        !tc.is_def_eq(&r1, &fwd),
        "coe over a residual Glue line must NOT reduce to the forward map"
    );

    // (b) The exact `ua` line with reversed endpoints (i1 → i0) IS a genuine
    // (inverse) transport — the `ua` boundary has a `⊤` cell at the target `i0`
    // (`(i=0)↦(A,e)`) and at the source `i1` (`(i=1)↦(B,id)`), so the symmetric rule
    // fires soundly: `coe (ua e) i1 i0 ab ↝ Equiv.bwd e ab : A`. The base inhabits
    // `(ua-line) i1 ≡ B`, so use `ab : B`.
    let line = ua_line(&cst("A"), &cst("B"), &cst("e"), type_level());
    let coe_rev = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i1()),
        s: Arc::new(i0()),
        base: Arc::new(cst("ab")),
    });
    let r2 = tc.whnf(&coe_rev);
    let expected_bwd = Expr::apps(
        Expr::const_(Name::from_string("Equiv.bwd"), vec![type_level()]),
        [cst("A"), cst("B"), cst("e"), cst("ab")],
    );
    assert!(
        tc.is_def_eq(&r2, &expected_bwd),
        "coe (ua e) i1 i0 ab must reduce to the inverse transport Equiv.bwd e ab; got {r2:?}"
    );
    // Type preservation: the inverse transport lands in A (= (ua-line) i0).
    let (rev_ty, _) = tc
        .infer_type_with_cert(&coe_rev)
        .expect("coe (ua e) i1 i0 ab should type-check");
    assert!(
        tc.is_def_eq(&rev_ty, &cst("A")),
        "coe (ua e) i1 i0 ab : A; got {rev_ty:?}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Equiv.bwd β + unglue total-face — the two primitives the general
// transp-over-Glue rule consumes (`Equiv.bwd` = the computable fiber-center point;
// `unglue` total-face = the base extraction at the degenerate i0 endpoint).
// ─────────────────────────────────────────────────────────────────────────────

/// `Equiv.bwd A A (Equiv.idEquiv A) x ↝ x` (the identity equivalence's backward map
/// is the identity), and `Equiv.bwd` of a *neutral* equivalence stays stuck.
#[test]
fn test_equiv_bwd_beta() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let bwd = |a: &Expr, b: &Expr, e: &Expr, x: &Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Equiv.bwd"), vec![type_level()]),
            [a.clone(), b.clone(), e.clone(), x.clone()],
        )
    };

    // Equiv.bwd A A (idEquiv A) ta ↝ ta.
    let id_a = Expr::app(
        Expr::const_(Name::from_string("Equiv.idEquiv"), vec![type_level()]),
        cst("A"),
    );
    let term = bwd(&cst("A"), &cst("A"), &id_a, &cst("ta"));
    let (ty, _) = tc
        .infer_type_with_cert(&term)
        .expect("Equiv.bwd (idEquiv A) ta should type-check");
    assert!(tc.is_def_eq(&ty, &cst("A")), "Equiv.bwd (idEquiv A) ta : A");
    assert!(
        tc.is_def_eq(&tc.whnf(&term), &cst("ta")),
        "Equiv.bwd (idEquiv A) ta must reduce to ta"
    );

    // Equiv.bwd A B e ab — e neutral ⇒ stuck (never over-fires).
    let neutral = bwd(&cst("A"), &cst("B"), &cst("e"), &cst("ab"));
    let r = tc.whnf(&neutral);
    assert!(
        matches!(r.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Equiv.bwd")),
        "Equiv.bwd on a neutral equivalence must stay stuck; got {r:?}"
    );
}

/// `unglue B ⊤ [⊤↦(A,e)] g ↝ Equiv.fwd e g` for a **non-`glue`-intro** `g` (the
/// total-face boundary rule), while `unglue (glue … a) ↝ a` (the β rule) still wins
/// when `g` *is* a literal `glue` intro (priority check — guards `test_unglue_beta`).
#[test]
fn test_unglue_total_face() {
    let env = glue_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // unglue B ⊤ [⊤↦(A,e)] ta  — ta : A is NOT a glue intro, so the total-face rule
    // fires: ↝ Equiv.fwd e ta (stuck, since e is neutral, but the rule has fired).
    let sys = glue_sys_one(&cst("B"), top(), &cst("A"), &cst("e"));
    let term = unglue(&cst("B"), top(), sys, cst("ta"));
    let (ty, _) = tc
        .infer_type_with_cert(&term)
        .expect("unglue B ⊤ [⊤↦(A,e)] ta should type-check");
    assert!(tc.is_def_eq(&ty, &cst("B")), "unglue … : B");
    let expected = Expr::apps(
        Expr::const_(Name::from_string("Equiv.fwd"), vec![type_level()]),
        [cst("A"), cst("B"), cst("e"), cst("ta")],
    );
    assert!(
        tc.is_def_eq(&tc.whnf(&term), &expected),
        "unglue B ⊤ [⊤↦(A,e)] ta must reduce to Equiv.fwd e ta"
    );

    // β still wins on a literal glue intro even on ⊤: unglue (glue B A ⊤ e ta ab) ↝ ab.
    let sys2 = glue_sys_one(&cst("B"), top(), &cst("A"), &cst("e"));
    let intro = glue_intro(
        &cst("B"),
        &cst("A"),
        top(),
        &cst("e"),
        &cst("ta"),
        &cst("ab"),
    );
    let term2 = unglue(&cst("B"), top(), sys2, intro);
    assert!(
        tc.is_def_eq(&tc.whnf(&term2), &cst("ab")),
        "unglue (glue … ab) must reduce to ab (β wins over total-face)"
    );
}
