// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the generalized coercion `coe^{r→s}` in Cubical mode.
//!
//! The decisive soundness anchor is **type preservation**: every coe reduction
//! must satisfy `infer(coe_term) ≡ infer(reduct)`. The Pi tests (d) check that on
//! non-trivial dependent lines — a buggy reduction surfaces as a type mismatch.

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{register_kan_system_axioms, register_sigma_axioms};
use std::sync::Arc;

fn i0() -> Expr {
    Expr::from_kind(ExprKind::CubicalI0)
}
fn i1() -> Expr {
    Expr::from_kind(ExprKind::CubicalI1)
}
fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}
fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn coe(ty: Expr, r: Expr, s: Expr, base: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(ty),
        r: Arc::new(r),
        s: Arc::new(s),
        base: Arc::new(base),
    })
}

/// Cubical env: `A : Type`, `a : A`, `B : Type`, `D : I → Type`, `d0 : D i0`,
/// `f : B → D i0`, `g : D i0 → B`.
fn coe_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    let axiom = |env: &mut Environment, name: &str, ty: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };

    axiom(&mut env, "A", Expr::type_());
    axiom(&mut env, "a", cst("A"));
    axiom(&mut env, "B", Expr::type_());
    // D : I → Type
    axiom(
        &mut env,
        "D",
        Expr::pi(BinderInfo::Default, interval(), Expr::type_()),
    );
    // d0 : D i0
    axiom(&mut env, "d0", Expr::app(cst("D"), i0()));
    // f : B → D i0   (Pi(B, D i0); codomain does not mention the binder)
    axiom(
        &mut env,
        "f",
        Expr::pi(BinderInfo::Default, cst("B"), Expr::app(cst("D"), i0())),
    );
    // g : D i0 → B
    axiom(
        &mut env,
        "g",
        Expr::pi(BinderInfo::Default, Expr::app(cst("D"), i0()), cst("B")),
    );
    env
}

fn infer(tc: &TypeChecker<'_>, e: &Expr) -> Expr {
    tc.infer_type_with_cert(e)
        .unwrap_or_else(|err| panic!("infer failed for {e:?}: {err:?}"))
        .0
}

// (a) infer(coe ty r s base) is `ty s` (App(ty, s)).
#[test]
fn test_cubical_coe_infers_ty_at_s() {
    let env = coe_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. D i   (a genuinely interval-dependent, neutral line)
    let d_line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(cst("D"), Expr::bvar(0)),
    );
    let term = coe(d_line.clone(), i0(), i1(), cst("d0"));

    let ty = infer(&tc, &term);
    // ty s = App(λ i. D i, i1)  ≡  D i1.
    let expected = Expr::app(d_line, i1());
    assert!(
        tc.is_def_eq(&ty, &expected),
        "infer(coe) should be `ty s`:\n  got:      {ty:?}\n  expected: {expected:?}"
    );
    assert!(
        tc.is_def_eq(&ty, &Expr::app(cst("D"), i1())),
        "infer(coe) should reduce to D i1, got {ty:?}"
    );
}

// (b) Degenerate r ≡ s: coe ty r r a ↝ a (whnf) and ≡ a (def_eq).
#[test]
fn test_cubical_coe_degenerate_reduces_to_base() {
    let env = coe_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Even over a non-constant, neutral line, r ≡ s makes coe the identity.
    let d_line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(cst("D"), Expr::bvar(0)),
    );
    let term = coe(d_line, i0(), i0(), cst("d0"));

    let r = tc.whnf(&term);
    assert!(
        matches!(r.kind(), ExprKind::Const(n, _) if *n == Name::from_string("d0")),
        "coe ty r r a must reduce to the base a, got {r:?}"
    );
    assert!(
        tc.is_def_eq(&term, &cst("d0")),
        "coe ty r r a must be def-eq to its base"
    );
}

// (c) Constant line: coe (λ_. A) r s a ↝ a.
#[test]
fn test_cubical_coe_constant_line_reduces_to_base() {
    let env = coe_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let const_line = Expr::lam(BinderInfo::Default, interval(), cst("A"));
    let term = coe(const_line, i0(), i1(), cst("a"));

    let r = tc.whnf(&term);
    assert!(
        matches!(r.kind(), ExprKind::Const(n, _) if *n == Name::from_string("a")),
        "coe over a constant line must reduce to the base, got {r:?}"
    );
    assert!(
        tc.is_def_eq(&term, &cst("a")),
        "coe over a constant line must be def-eq to its base"
    );
}

// (d.1) Pi, CONSTANT domain — type preservation.
// coe (λ i. (B → D i)) i0 i1 f  ↝  λ (x:B). coe (λ i. D i) i0 i1 (f (coe (λ j.B) i1 i0 x))
#[test]
fn test_cubical_coe_pi_constant_domain_preserves_type() {
    let env = coe_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. (B → D i)   [inside the Pi codomain, i is BVar(1)]
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::pi(
            BinderInfo::Default,
            cst("B"),
            Expr::app(cst("D"), Expr::bvar(1)),
        ),
    );
    let term = coe(line, i0(), i1(), cst("f"));

    let coe_ty = infer(&tc, &term);

    let r = tc.whnf(&term);
    assert!(
        matches!(r.kind(), ExprKind::Lam(..)),
        "coe over a constant-domain Pi should reduce to a lambda, got {r:?}"
    );

    // SOUNDNESS ANCHOR: infer(coe) ≡ infer(reduct), both `B → D i1`.
    let reduct_ty = infer(&tc, &r);
    assert!(
        tc.is_def_eq(&coe_ty, &reduct_ty),
        "Pi-coe (constant domain) must preserve type:\n  coe:    {coe_ty:?}\n  reduct: {reduct_ty:?}"
    );
    // And it is literally `B → D i1`.
    let expected_ty = Expr::pi(BinderInfo::Default, cst("B"), Expr::app(cst("D"), i1()));
    assert!(
        tc.is_def_eq(&coe_ty, &expected_ty),
        "coe type should be B → D i1, got {coe_ty:?}"
    );
}

// (d.2) Pi, VARYING domain (exercises the backward coercion) — type preservation.
// coe (λ i. (D i → B)) i0 i1 g
//   ↝ λ (x:D i1). coe (λ i. B) i0 i1 (g (coe (λ j. D j) i1 i0 x))
#[test]
fn test_cubical_coe_pi_varying_domain_preserves_type() {
    let env = coe_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. (D i → B)   [domain `D i`: i is BVar(0) directly under λ i]
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cst("D"), Expr::bvar(0)),
            cst("B"),
        ),
    );
    let term = coe(line, i0(), i1(), cst("g"));

    let coe_ty = infer(&tc, &term);

    let r = tc.whnf(&term);
    assert!(
        matches!(r.kind(), ExprKind::Lam(..)),
        "coe over a varying-domain Pi should reduce to a lambda, got {r:?}"
    );

    // SOUNDNESS ANCHOR: infer(coe) ≡ infer(reduct), both `D i1 → B`.
    let reduct_ty = infer(&tc, &r);
    assert!(
        tc.is_def_eq(&coe_ty, &reduct_ty),
        "Pi-coe (varying domain) must preserve type:\n  coe:    {coe_ty:?}\n  reduct: {reduct_ty:?}"
    );
    let expected_ty = Expr::pi(BinderInfo::Default, Expr::app(cst("D"), i1()), cst("B"));
    assert!(
        tc.is_def_eq(&coe_ty, &expected_ty),
        "coe type should be D i1 → B, got {coe_ty:?}"
    );
}

// (e) coe^{0→1} agrees with transp on lines where both reduce.
#[test]
fn test_cubical_coe_zero_to_one_agrees_with_transp() {
    let env = coe_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Constant line.
    let const_line = Expr::lam(BinderInfo::Default, interval(), cst("A"));
    let coe_term = coe(const_line.clone(), i0(), i1(), cst("a"));
    let transp_term = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(const_line),
        phi: Arc::new(i0()),
        base: Arc::new(cst("a")),
    });
    assert!(
        tc.is_def_eq(&coe_term, &transp_term),
        "coe (λ_.A) i0 i1 a must agree with transp (λ_.A) i0 a"
    );

    // Constant-domain Pi line: both reduce to the same lambda.
    let pi_line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::pi(
            BinderInfo::Default,
            cst("B"),
            Expr::app(cst("D"), Expr::bvar(1)),
        ),
    );
    let coe_pi = coe(pi_line.clone(), i0(), i1(), cst("f"));
    let transp_pi = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(pi_line),
        phi: Arc::new(i0()),
        base: Arc::new(cst("f")),
    });
    assert!(
        tc.is_def_eq(&coe_pi, &transp_pi),
        "coe^(0→1) and transp must agree on a constant-domain Pi line"
    );
}

// Sanity: a coe over a neutral (non-lambda) line stays stuck (sound).
#[test]
fn test_cubical_coe_neutral_line_stays_stuck() {
    let env = coe_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // `D` itself is a neutral line `I → Type` (not a literal λ).
    let term = coe(cst("D"), i0(), i1(), cst("d0"));
    let r = tc.whnf(&term);
    assert!(
        matches!(r.kind(), ExprKind::CubicalCoe { .. }),
        "coe over a neutral line must stay stuck, got {r:?}"
    );
}

// coe requires Cubical mode.
#[test]
fn test_cubical_coe_requires_cubical_mode() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let const_line = Expr::lam(BinderInfo::Default, interval(), Expr::prop());
    let term = coe(const_line, i0(), i1(), Expr::prop());
    let err = tc
        .infer_type_with_cert(&term)
        .expect_err("coe outside Cubical mode must fail");
    assert!(
        matches!(err, TypeError::ModeRequired { .. }),
        "expected ModeRequired, got {err:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// coe-over-Sigma and coe-over-Path (the CCHM comp-by-type-former rules)
// ═════════════════════════════════════════════════════════════════════════════

/// `Type` = `Sort 1`.
fn type_level() -> Level {
    Level::succ(Level::zero())
}
/// `λ i. D i` — the genuinely interval-dependent base line.
fn d_line() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(cst("D"), Expr::bvar(0)),
    )
}
/// `Sigma.{1} A B`.
fn sig(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Sigma"), vec![type_level()]),
        [a, b],
    )
}
/// `Sigma.mk.{1} A B fst snd`.
fn sig_mk(a: Expr, b: Expr, fst: Expr, snd: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Sigma.mk"), vec![type_level()]),
        [a, b, fst, snd],
    )
}
/// `Sigma.elim.{1} A B M m p`.
fn sig_elim(a: Expr, b: Expr, motive: Expr, minor: Expr, p: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Sigma.elim"), vec![type_level()]),
        [a, b, motive, minor, p],
    )
}
/// `CubicalPath { ty, left, right }`.
fn path_ty(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(ty),
        left: Arc::new(left),
        right: Arc::new(right),
    })
}
/// `p @ arg`.
fn path_app(p: Expr, arg: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(p),
        arg: Arc::new(arg),
    })
}

/// `coe_env` + Kan-system + Σ axioms, plus a second `B`-point `b0`, two endpoint
/// lines `pu`/`pv : (i:I) → D i`, and a homogeneous path `pp : Path (D i0) (pu i0)
/// (pv i0)` (so the coe-over-Path source `pp` is a genuine, non-vacuous point).
fn sigma_path_env() -> Environment {
    let mut env = coe_env();
    register_kan_system_axioms(&mut env).expect("kan system axioms");
    register_sigma_axioms(&mut env).expect("sigma axioms");
    let mut axiom = |name: &str, ty: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };
    // b0 : B.
    axiom("b0", cst("B"));
    // pu, pv : (i:I) → D i  (the two path-endpoint lines).
    let endpoint_ty = Expr::pi(
        BinderInfo::Default,
        interval(),
        Expr::app(cst("D"), Expr::bvar(0)),
    );
    axiom("pu", endpoint_ty.clone());
    axiom("pv", endpoint_ty);
    // pp : Path (λ_:I. D i0) (pu i0) (pv i0)  — a homogeneous path in `D i0`.
    axiom(
        "pp",
        path_ty(
            Expr::lam(BinderInfo::Default, interval(), Expr::app(cst("D"), i0())),
            Expr::app(cst("pu"), i0()),
            Expr::app(cst("pv"), i0()),
        ),
    );
    env
}

// ── coe-over-Sigma ──────────────────────────────────────────────────────────────

// (Σ-a) Constant Σ line ⇒ coe ↝ base (regularity / the constant-coe rule).
#[test]
fn test_coe_sigma_constant_line_reduces_to_base() {
    let env = sigma_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. Σ (x:A). A   (no interval dependence at all).
    let bfam = Expr::lam(BinderInfo::Default, cst("A"), cst("A")); // λ_:A. A
    let line = Expr::lam(BinderInfo::Default, interval(), sig(cst("A"), bfam.clone()));
    let base = sig_mk(cst("A"), bfam, cst("a"), cst("a"));
    let term = coe(line, i0(), i1(), base.clone());

    assert!(
        tc.is_def_eq(&term, &base),
        "coe over a constant Σ line must be def-eq to its base"
    );
    // And it genuinely reduces to the literal base pair (the constant rule fires).
    let r = tc.whnf(&term);
    assert!(
        tc.is_def_eq(&r, &base),
        "coe over a constant Σ line must reduce to base; got {r:?}"
    );
}

// (Σ-b/c) Concrete interval-dependent Σ line `λ i. Σ (D i) (λ_. B)`:
//   * type preservation (the soundness anchor),
//   * projection agreement — fst ≡ coe (λ i. D i) i0 i1 d0, snd ≡ b0,
//   * the reduct is the expected literal pair (non-vacuous: `D` is a real line).
#[test]
fn test_coe_sigma_concrete_line_projects_and_preserves_type() {
    let env = sigma_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. Σ (x : D i). B    (non-dependent second component `B`).
    // de Bruijn: under `λ i`, i = BVar0; the Σ family `λ (x:D i). B` keeps i = BVar0
    // at its domain (same binder level as the first Σ arg).
    let bfam_line = |di: Expr| Expr::lam(BinderInfo::Default, di, cst("B")); // λ _:D i. B
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        sig(
            Expr::app(cst("D"), Expr::bvar(0)),
            bfam_line(Expr::app(cst("D"), Expr::bvar(0))),
        ),
    );
    // base : Σ (D i0) (λ_.B) = Sigma.mk (D i0) (λ_:D i0.B) d0 b0.
    let base = sig_mk(
        Expr::app(cst("D"), i0()),
        bfam_line(Expr::app(cst("D"), i0())),
        cst("d0"),
        cst("b0"),
    );
    let term = coe(line, i0(), i1(), base);

    // (c) Type preservation: infer(coe) ≡ infer(reduct).
    let coe_ty = infer(&tc, &term);
    let reduct = tc.whnf(&term);
    let reduct_ty = infer(&tc, &reduct);
    assert!(
        tc.is_def_eq(&coe_ty, &reduct_ty),
        "coe-over-Σ must preserve type:\n  coe:    {coe_ty:?}\n  reduct: {reduct_ty:?}"
    );
    // …and it is literally `Σ (D i1) (λ_.B)`.
    let expected_ty = sig(
        Expr::app(cst("D"), i1()),
        bfam_line(Expr::app(cst("D"), i1())),
    );
    assert!(
        tc.is_def_eq(&coe_ty, &expected_ty),
        "coe-over-Σ type should be Σ (D i1) (λ_.B); got {coe_ty:?}"
    );

    // The reduct genuinely fired (a literal `Sigma.mk`, not a stuck `coe`).
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Sigma.mk")),
        "coe-over-Σ must reduce to a literal Sigma.mk; got {reduct:?}"
    );

    // (b) Projection agreement via the Σ-iota.
    //   fst (coe(Σ) …) ≡ coe (λ i. D i) i0 i1 d0.
    let a_s = Expr::app(cst("D"), i1());
    let b_s = bfam_line(Expr::app(cst("D"), i1()));
    let fst_motive = Expr::lam(
        BinderInfo::Default,
        sig(a_s.clone(), b_s.clone()),
        a_s.clone(),
    );
    let fst_minor = Expr::lam(
        BinderInfo::Default,
        a_s.clone(),
        Expr::lam(BinderInfo::Default, cst("B"), Expr::bvar(1)),
    );
    let fst = sig_elim(
        a_s.clone(),
        b_s.clone(),
        fst_motive,
        fst_minor,
        reduct.clone(),
    );
    let expected_fst = coe(d_line(), i0(), i1(), cst("d0"));
    assert!(
        tc.is_def_eq(&fst, &expected_fst),
        "fst (coe-over-Σ) ≡ coe (λ i. D i) i0 i1 d0; got fst whnf {:?}",
        tc.whnf(&fst)
    );

    //   snd (coe(Σ) …) ≡ b0   (the second component family is the constant `B`, so
    //   its coe degenerates to the identity).
    let snd_motive = Expr::lam(BinderInfo::Default, sig(a_s.clone(), b_s.clone()), cst("B"));
    let snd_minor = Expr::lam(
        BinderInfo::Default,
        a_s.clone(),
        Expr::lam(BinderInfo::Default, cst("B"), Expr::bvar(0)),
    );
    let snd = sig_elim(a_s, b_s, snd_motive, snd_minor, reduct);
    assert!(
        tc.is_def_eq(&snd, &cst("b0")),
        "snd (coe-over-Σ) ≡ b0; got snd whnf {:?}",
        tc.whnf(&snd)
    );
}

// (Σ-stuck) A neutral (non-`Sigma.mk`) base leaves coe-over-Σ stuck (sound).
#[test]
fn test_coe_sigma_neutral_base_stays_stuck() {
    let mut env = sigma_path_env();
    // pdep : Σ (D i0) (λ_.B) — an opaque Σ point (not a literal pair).
    let bfam_i0 = Expr::lam(BinderInfo::Default, Expr::app(cst("D"), i0()), cst("B"));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pdep"),
        level_params: vec![],
        type_: sig(Expr::app(cst("D"), i0()), bfam_i0.clone()),
    })
    .expect("pdep registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        sig(
            Expr::app(cst("D"), Expr::bvar(0)),
            Expr::lam(
                BinderInfo::Default,
                Expr::app(cst("D"), Expr::bvar(0)),
                cst("B"),
            ),
        ),
    );
    let term = coe(line, i0(), i1(), cst("pdep"));
    let r = tc.whnf(&term);
    assert!(
        matches!(r.kind(), ExprKind::CubicalCoe { .. }),
        "coe-over-Σ on a neutral base must stay stuck; got {r:?}"
    );
}

// ── coe-over-Path ───────────────────────────────────────────────────────────────

// (Path-a) Constant Path line ⇒ coe ↝ base (the constant-coe rule fires first).
#[test]
fn test_coe_path_constant_line_reduces_to_base() {
    let env = sigma_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. Path (λ_.A) a a   (no interval dependence).
    let const_path = path_ty(
        Expr::lam(BinderInfo::Default, interval(), cst("A")),
        cst("a"),
        cst("a"),
    );
    let line = Expr::lam(BinderInfo::Default, interval(), const_path);
    // base : Path (λ_.A) a a  = refl a.
    let base = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(cst("a")),
    });
    let term = coe(line, i0(), i1(), base.clone());
    assert!(
        tc.is_def_eq(&term, &base),
        "coe over a constant Path line must be def-eq to its base"
    );
}

// (Path-b/c) Concrete interval-dependent (non-dependent-in-its-own-interval) Path
// line `λ i. Path (D i) (pu i) (pv i)`:
//   * endpoints — (coe(Path) pp) @ i0 ≡ pu i1, @ i1 ≡ pv i1 (coerced endpoints),
//   * type preservation (the soundness anchor).
#[test]
fn test_coe_path_concrete_line_endpoints_and_preserves_type() {
    let env = sigma_path_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. Path (λ_:I. D i) (pu i) (pv i).
    // de Bruijn under `λ i` (i = BVar0): the Path family `λ_:I. D i` shifts i to
    // BVar1 inside its own binder; the endpoints `pu i`/`pv i` keep i = BVar0.
    let per_point = path_ty(
        Expr::lam(
            BinderInfo::Default,
            interval(),
            Expr::app(cst("D"), Expr::bvar(1)),
        ),
        Expr::app(cst("pu"), Expr::bvar(0)),
        Expr::app(cst("pv"), Expr::bvar(0)),
    );
    let line = Expr::lam(BinderInfo::Default, interval(), per_point);
    let term = coe(line, i0(), i1(), cst("pp"));

    // (c) Type preservation: infer(coe) ≡ infer(reduct).
    let coe_ty = infer(&tc, &term);
    let reduct = tc.whnf(&term);
    assert!(
        matches!(reduct.kind(), ExprKind::CubicalPathLam { .. }),
        "coe-over-Path must reduce to a path-lambda; got {reduct:?}"
    );
    let reduct_ty = infer(&tc, &reduct);
    assert!(
        tc.is_def_eq(&coe_ty, &reduct_ty),
        "coe-over-Path must preserve type:\n  coe:    {coe_ty:?}\n  reduct: {reduct_ty:?}"
    );
    // …and it is literally `Path (λ_.D i1) (pu i1) (pv i1)`.
    let expected_ty = path_ty(
        Expr::lam(BinderInfo::Default, interval(), Expr::app(cst("D"), i1())),
        Expr::app(cst("pu"), i1()),
        Expr::app(cst("pv"), i1()),
    );
    assert!(
        tc.is_def_eq(&coe_ty, &expected_ty),
        "coe-over-Path type should be Path (λ_.D i1) (pu i1) (pv i1); got {coe_ty:?}"
    );

    // (b) Endpoints: the reduct is a genuine path with the *coerced* endpoints.
    let at_i0 = path_app(reduct.clone(), i0());
    let at_i1 = path_app(reduct, i1());
    assert!(
        tc.is_def_eq(&at_i0, &Expr::app(cst("pu"), i1())),
        "(coe-over-Path pp) @ i0 ≡ pu i1; got {:?}",
        tc.whnf(&at_i0)
    );
    assert!(
        tc.is_def_eq(&at_i1, &Expr::app(cst("pv"), i1())),
        "(coe-over-Path pp) @ i1 ≡ pv i1; got {:?}",
        tc.whnf(&at_i1)
    );
}

// (Path-stuck) A genuinely *dependent* `PathP` line stays stuck (sound): its
// system tubes would only be well-typed on their faces, which the total
// `System.cons` tube typing cannot express — so the rule declines.
#[test]
fn test_coe_pathp_dependent_line_stays_stuck() {
    let mut env = sigma_path_env();
    // E : I → I → Type  (genuinely dependent in both arguments).
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("E"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            interval(),
            Expr::pi(BinderInfo::Default, interval(), Expr::type_()),
        ),
    })
    .expect("E registers");
    // qe : an opaque PathP point at i0 (its exact type is irrelevant to WHNF).
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("qe"),
        level_params: vec![],
        type_: cst("A"),
    })
    .expect("qe registers");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // line: λ i. PathP (λ j. E i j) (??) (??) — only the *family* matters for the
    // (sound) stuck check; build a dependent inner family `λ j. E i j`.
    // Under `λ i` (i=BVar0): inside the Path family `λ j` (j=BVar0), i = BVar1.
    let dependent_family = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::apps(cst("E"), [Expr::bvar(1), Expr::bvar(0)]),
    );
    let per_point = path_ty(dependent_family, cst("qe"), cst("qe"));
    let line = Expr::lam(BinderInfo::Default, interval(), per_point);
    let term = coe(line, i0(), i1(), cst("qe"));
    let r = tc.whnf(&term);
    assert!(
        matches!(r.kind(), ExprKind::CubicalCoe { .. }),
        "coe over a dependent PathP line must stay stuck; got {r:?}"
    );
}
