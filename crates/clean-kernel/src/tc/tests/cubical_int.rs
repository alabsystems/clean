// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A **real ℤ inductive with a PROVED successor-equivalence** — piece 1 of the
//! full `Ω S¹ ≃ ℤ` for the cubical `π₁` work.
//!
//! Unlike the opaque-`MyInt` winding tests in [`super::cubical_pi1`] (where
//! `MyInt`/`succ`/`pred`/the inverse laws are *axioms*), here **everything is
//! real**:
//!
//! * `MyZ` is a genuine **2-constructor** inductive
//!   `MyZ.ofNat : MyNat → MyZ | MyZ.negSucc : MyNat → MyZ` over a local
//!   `MyNat` (`zero`/`succ`). Two constructors ⇒ **no structure-η collapse**, so
//!   `ofNat 0`, `ofNat 1`, … are genuinely distinct (the winding vacuity guard).
//! * `succ`/`pred` are **computing DEFINED functions** built from the recursors
//!   (`MyZ.rec`/`MyNat.rec`), *not* axioms:
//!   `succ (ofNat n) = ofNat (Nat.succ n)`, `succ (negSucc 0) = ofNat 0`,
//!   `succ (negSucc (succ n)) = negSucc n`; and dually for `pred`. So
//!   `succ (ofNat 0)` genuinely *reduces* to constructor form `ofNat 1`.
//! * The inverse laws `predsucc`/`succpred` are **PROVED proof terms**
//!   (`MyZ.rec`/`MyNat.rec` with each case `= refl`): with the definitions above
//!   `pred (succ z)` and `succ (pred z)` reduce to `z` *definitionally* in each
//!   constructor case, so every minor is `<i> z`. **No new axioms** — the whole
//!   point is that `succ` is a *proved* equivalence.
//! * `sucEquiv := Equiv.mk MyZ MyZ succ pred predsucc succpred` therefore
//!   type-checks as a genuine `Equiv MyZ MyZ` (the η/ε fields line up against the
//!   record type), and the winding number
//!   `transport (ua sucEquiv) (ofNat 0) ↝ succ (ofNat 0) ↝ ofNat 1` computes to
//!   **constructor form**.
//!
//! These tests do **not** disturb the opaque-`MyInt` π₁ tests: a fresh `MyNat`
//! / `MyZ` / `MyZ.succ` / `MyZ.pred` namespace in its own environment.

use super::*;

use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{
    ap_cong, glue_ua, is_equiv_from_quasi_inv_on_set, is_equiv_type, is_prop_type,
    is_set_from_encode_decode, is_set_type, path_compose, path_refl, path_sym_neg,
    register_glue_axioms, register_kan_system_axioms, register_sigma_axioms,
};
use std::sync::Arc;

// ── Leaves ──────────────────────────────────────────────────────────────────

fn nm(s: &str) -> Name {
    Name::from_string(s)
}
fn cst(s: &str) -> Expr {
    Expr::const_(nm(s), Vec::<Level>::new())
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
fn bvar(i: u32) -> Expr {
    Expr::bvar(i)
}
/// `Sort 1`'s level — `MyZ`/`MyNat`/`S¹` and the `Path`s over them live here;
/// the recursors eliminate into `Sort 1` (`MyZ.rec.{1}` etc.).
fn lvl1() -> Level {
    Level::succ(Level::zero())
}
fn type_level() -> Level {
    Level::succ(Level::zero())
}
fn lam(dom: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, dom, body)
}
fn pi(dom: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, body)
}
/// `Path line left right` (cubical path type former).
fn path(line: Expr, left: Expr, right: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(left),
        right: Arc::new(right),
    })
}
/// The constant path line `λ_:I. ty` (for a `ty` closed in the interval).
fn const_line(ty: Expr) -> Expr {
    lam(interval(), ty)
}
/// `X.rec.{1}` — the (large-eliminating) recursor at motive-universe `Sort 1`.
fn rec(ind: &str) -> Expr {
    Expr::const_(nm(&format!("{ind}.rec")), vec![lvl1()])
}

// ── MyNat (a local zero/succ Nat) ─────────────────────────────────────────────

fn mynat() -> Expr {
    cst("MyNat")
}
fn mn_zero() -> Expr {
    cst("MyNat.zero")
}
fn mn_succ(n: Expr) -> Expr {
    Expr::app(cst("MyNat.succ"), n)
}

// ── MyZ = a real 2-constructor ℤ ──────────────────────────────────────────────

fn myz() -> Expr {
    cst("MyZ")
}
fn ofnat(n: Expr) -> Expr {
    Expr::app(cst("MyZ.ofNat"), n)
}
fn negsucc(n: Expr) -> Expr {
    Expr::app(cst("MyZ.negSucc"), n)
}
/// `succ z` / `pred z` — the DEFINED (computing) successor/predecessor on `MyZ`.
fn z_succ(z: Expr) -> Expr {
    Expr::app(cst("MyZ.succ"), z)
}
fn z_pred(z: Expr) -> Expr {
    Expr::app(cst("MyZ.pred"), z)
}

// ── succ / pred as recursor-built DEFINITIONS ─────────────────────────────────

/// `succ : MyZ → MyZ`, defined via the recursors:
/// ```text
/// succ (ofNat n)            = ofNat (MyNat.succ n)
/// succ (negSucc MyNat.zero) = ofNat MyNat.zero
/// succ (negSucc (succ n))   = negSucc n
/// ```
fn succ_value() -> Expr {
    let motive = lam(myz(), myz()); // λ _:MyZ. MyZ
    let cof = lam(mynat(), ofnat(mn_succ(bvar(0)))); // λ n. ofNat (succ n)
                                                     // λ m. MyNat.rec (λ_.MyZ) (ofNat 0) (λ k ih. negSucc k) m
    let inner = Expr::apps(
        rec("MyNat"),
        [
            lam(mynat(), myz()),                        // motive λ_:MyNat. MyZ
            ofnat(mn_zero()),                           // zero case: ofNat 0
            lam(mynat(), lam(myz(), negsucc(bvar(1)))), // succ case: λ k ih. negSucc k
            bvar(0),                                    // major: m
        ],
    );
    let cneg = lam(mynat(), inner);
    Expr::apps(rec("MyZ"), [motive, cof, cneg])
}

/// `pred : MyZ → MyZ`, defined via the recursors:
/// ```text
/// pred (ofNat MyNat.zero) = negSucc MyNat.zero
/// pred (ofNat (succ n))   = ofNat n
/// pred (negSucc n)        = negSucc (MyNat.succ n)
/// ```
fn pred_value() -> Expr {
    let motive = lam(myz(), myz());
    // λ n. MyNat.rec (λ_.MyZ) (negSucc 0) (λ k ih. ofNat k) n
    let inner_of = Expr::apps(
        rec("MyNat"),
        [
            lam(mynat(), myz()),
            negsucc(mn_zero()),                       // zero case: negSucc 0
            lam(mynat(), lam(myz(), ofnat(bvar(1)))), // succ case: λ k ih. ofNat k
            bvar(0),                                  // major: n
        ],
    );
    let cof = lam(mynat(), inner_of);
    let cneg = lam(mynat(), negsucc(mn_succ(bvar(0)))); // λ m. negSucc (succ m)
    Expr::apps(rec("MyZ"), [motive, cof, cneg])
}

// ── The PROVED inverse laws (refl-via-recursor) ───────────────────────────────

/// `predsucc : (z:MyZ) → Path (λ_:I.MyZ) (pred (succ z)) z`  (g∘f ~ id).
fn predsucc_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        myz(),
        path(const_line(myz()), z_pred(z_succ(bvar(0))), bvar(0)),
    )
}
/// `succpred : (z:MyZ) → Path (λ_:I.MyZ) (succ (pred z)) z`  (f∘g ~ id).
fn succpred_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        myz(),
        path(const_line(myz()), z_succ(z_pred(bvar(0))), bvar(0)),
    )
}

/// PROOF TERM of `predsucc`. Built as `MyZ.rec` with each case discharged by
/// `refl` (`<i> z`), because `pred (succ z) ≡ z` **definitionally** per case:
/// * `z = ofNat n`: direct (`pred (succ (ofNat n)) ↝ ofNat n`), minor `<i> ofNat n`.
/// * `z = negSucc m`: needs `MyNat.rec` on `m` (because `succ (negSucc m)` itself
///   case-splits on `m`); both sub-cases reduce to refl
///   (`pred (succ (negSucc 0)) ↝ negSucc 0`, `pred (succ (negSucc (succ k))) ↝ negSucc (succ k)`).
fn predsucc_value() -> Expr {
    // motive: λ z'. Path (λ_.MyZ) (pred (succ z')) z'
    let motive = lam(
        myz(),
        path(const_line(myz()), z_pred(z_succ(bvar(0))), bvar(0)),
    );
    // ofNat case: λ n. <i> ofNat n        (n = BVar 1 under the path-lam binder)
    let cof = lam(mynat(), path_refl(&ofnat(bvar(1))));
    // negSucc case: λ m. MyNat.rec C_in cz cs m
    //   C_in: λ m'. Path (λ_.MyZ) (pred (succ (negSucc m'))) (negSucc m')
    let c_in = lam(
        mynat(),
        path(
            const_line(myz()),
            z_pred(z_succ(negsucc(bvar(0)))),
            negsucc(bvar(0)),
        ),
    );
    let cz = path_refl(&negsucc(mn_zero())); // <i> negSucc 0
                                             // ih's type is `C_in k` (k = BVar 0 inside `λ k`).
    let ih_ty = path(
        const_line(myz()),
        z_pred(z_succ(negsucc(bvar(0)))),
        negsucc(bvar(0)),
    );
    // succ case: λ k ih. <i> negSucc (succ k)   (k = BVar 2 under [k, ih, i])
    let cs = lam(mynat(), lam(ih_ty, path_refl(&negsucc(mn_succ(bvar(2))))));
    let inner = Expr::apps(rec("MyNat"), [c_in, cz, cs, bvar(0)]);
    let cneg = lam(mynat(), inner);
    Expr::apps(rec("MyZ"), [motive, cof, cneg])
}

/// PROOF TERM of `succpred`. Dually: `z = negSucc m` is *direct* refl
/// (`succ (pred (negSucc m)) ↝ negSucc m`, reduces for symbolic `m`), while
/// `z = ofNat n` needs the `MyNat.rec` split on `n` (because `pred (ofNat n)`
/// case-splits on `n`).
fn succpred_value() -> Expr {
    // motive: λ z'. Path (λ_.MyZ) (succ (pred z')) z'
    let motive = lam(
        myz(),
        path(const_line(myz()), z_succ(z_pred(bvar(0))), bvar(0)),
    );
    // ofNat case: λ n. MyNat.rec C_in cz cs n
    let c_in = lam(
        mynat(),
        path(
            const_line(myz()),
            z_succ(z_pred(ofnat(bvar(0)))),
            ofnat(bvar(0)),
        ),
    );
    let cz = path_refl(&ofnat(mn_zero())); // <i> ofNat 0
    let ih_ty = path(
        const_line(myz()),
        z_succ(z_pred(ofnat(bvar(0)))),
        ofnat(bvar(0)),
    );
    let cs = lam(mynat(), lam(ih_ty, path_refl(&ofnat(mn_succ(bvar(2)))))); // <i> ofNat (succ k)
    let inner = Expr::apps(rec("MyNat"), [c_in, cz, cs, bvar(0)]);
    let cof = lam(mynat(), inner);
    // negSucc case: λ m. <i> negSucc m       (m = BVar 1 under the path-lam binder)
    let cneg = lam(mynat(), path_refl(&negsucc(bvar(1))));
    Expr::apps(rec("MyZ"), [motive, cof, cneg])
}

// ── sucEquiv / ua / winding ───────────────────────────────────────────────────

/// `sucEquiv := Equiv.mk.{1} MyZ MyZ succ pred predsucc succpred : Equiv MyZ MyZ`.
fn suc_equiv() -> Expr {
    Expr::apps(
        Expr::const_(nm("Equiv.mk"), vec![type_level()]),
        [
            myz(),
            myz(),
            cst("MyZ.succ"),
            cst("MyZ.pred"),
            cst("predsucc"),
            cst("succpred"),
        ],
    )
}

/// The `ua` coercion line `λ i. Glue B [(i=0)↦(A,e), (i=1)↦(B, idEquiv B)]`
/// (the body of `glue_ua e` rewrapped as a `coe`-shaped lambda).
fn ua_line(a: &Expr, b: &Expr, e: &Expr, level: Level) -> Expr {
    let ua = glue_ua(a, b, e, level);
    let ExprKind::CubicalPathLam { body } = ua.kind() else {
        panic!("glue_ua must produce a CubicalPathLam");
    };
    lam(interval(), body.as_ref().clone())
}

/// `transport (ua e) x` as the canonical `coe (ua-line) i0 i1 x`.
fn transport_ua(a: &Expr, b: &Expr, e: &Expr, x: &Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(ua_line(a, b, e, type_level())),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(x.clone()),
    })
}

/// `transport⁻¹ (ua e) x` as the BACKWARD `coe (ua-line) i1 i0 x` — the inverse
/// transport (`Equiv.bwd e x`). The orientation `decode`'s loop minor needs.
fn transport_ua_bwd(a: &Expr, b: &Expr, e: &Expr, x: &Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(ua_line(a, b, e, type_level())),
        r: Arc::new(i1()),
        s: Arc::new(i0()),
        base: Arc::new(x.clone()),
    })
}

// ── Environments ──────────────────────────────────────────────────────────────

/// Cubical env: Kan + Glue axioms, the `MyNat`/`MyZ` inductives, and the
/// recursor-built `succ`/`pred` plus the PROVED `predsucc`/`succpred`.
fn int_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("register kan system axioms");
    register_glue_axioms(&mut env).expect("register glue axioms");

    // MyNat — a local zero/succ Nat (generates MyNat.rec).
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("MyNat"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: nm("MyNat.zero"),
                    type_: mynat(),
                },
                Constructor {
                    name: nm("MyNat.succ"),
                    type_: Expr::arrow(mynat(), mynat()),
                },
            ],
        }],
    })
    .expect("MyNat inductive should register");

    // MyZ — a real 2-constructor ℤ over MyNat (generates MyZ.rec). Two ctors ⇒
    // NO structure-η collapse: ofNat 0, ofNat 1, … are genuinely distinct.
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("MyZ"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: nm("MyZ.ofNat"),
                    type_: Expr::arrow(mynat(), myz()),
                },
                Constructor {
                    name: nm("MyZ.negSucc"),
                    type_: Expr::arrow(mynat(), myz()),
                },
            ],
        }],
    })
    .expect("MyZ inductive should register");

    // Computing succ/pred (reducible ⇒ they unfold so the winding number lands in
    // constructor form).
    env.add_decl(Declaration::Definition {
        name: nm("MyZ.succ"),
        level_params: vec![],
        type_: Expr::arrow(myz(), myz()),
        value: succ_value(),
        is_reducible: true,
    })
    .expect("MyZ.succ should type-check and register");
    env.add_decl(Declaration::Definition {
        name: nm("MyZ.pred"),
        level_params: vec![],
        type_: Expr::arrow(myz(), myz()),
        value: pred_value(),
        is_reducible: true,
    })
    .expect("MyZ.pred should type-check and register");

    // The PROVED inverse laws — registration type-checks the recursor-with-refl
    // proof terms in Cubical mode. If a case did NOT reduce to refl definitionally,
    // these `add_decl`s would FAIL (we never axiomatize them).
    env.add_decl(Declaration::Definition {
        name: nm("predsucc"),
        level_params: vec![],
        type_: predsucc_ty(),
        value: predsucc_value(),
        is_reducible: false,
    })
    .expect("predsucc proof term should type-check (refl-via-recursor)");
    env.add_decl(Declaration::Definition {
        name: nm("succpred"),
        level_params: vec![],
        type_: succpred_ty(),
        value: succpred_value(),
        is_reducible: false,
    })
    .expect("succpred proof term should type-check (refl-via-recursor)");

    env
}

// ══════════════════════════════════════════════════════════════════════════════
// 1 — succ/pred are genuinely COMPUTING (reduce to constructor form)
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_succ_pred_compute_on_constructors() {
    let env = int_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // succ (ofNat 0) ↝ ofNat (succ 0)   ( = 1).
    assert!(
        tc.is_def_eq(&z_succ(ofnat(mn_zero())), &ofnat(mn_succ(mn_zero()))),
        "succ (ofNat 0) must reduce to ofNat (succ 0)"
    );
    // succ (negSucc 0) ↝ ofNat 0.
    assert!(
        tc.is_def_eq(&z_succ(negsucc(mn_zero())), &ofnat(mn_zero())),
        "succ (negSucc 0) must reduce to ofNat 0"
    );
    // succ (negSucc (succ 0)) ↝ negSucc 0.
    assert!(
        tc.is_def_eq(&z_succ(negsucc(mn_succ(mn_zero()))), &negsucc(mn_zero())),
        "succ (negSucc (succ 0)) must reduce to negSucc 0"
    );

    // pred (ofNat 0) ↝ negSucc 0.
    assert!(
        tc.is_def_eq(&z_pred(ofnat(mn_zero())), &negsucc(mn_zero())),
        "pred (ofNat 0) must reduce to negSucc 0"
    );
    // pred (ofNat (succ 0)) ↝ ofNat 0.
    assert!(
        tc.is_def_eq(&z_pred(ofnat(mn_succ(mn_zero()))), &ofnat(mn_zero())),
        "pred (ofNat (succ 0)) must reduce to ofNat 0"
    );
    // pred (negSucc 0) ↝ negSucc (succ 0).
    assert!(
        tc.is_def_eq(&z_pred(negsucc(mn_zero())), &negsucc(mn_succ(mn_zero()))),
        "pred (negSucc 0) must reduce to negSucc (succ 0)"
    );

    // The reduct really is constructor-headed (not a stuck recursor).
    let one = tc.whnf(&z_succ(ofnat(mn_zero())));
    assert!(
        matches!(one.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "succ (ofNat 0) must WHNF to an ofNat constructor application; got {one:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 2 — the inverse laws are PROVED (and well-typed)
// ══════════════════════════════════════════════════════════════════════════════

/// The crux: `predsucc`/`succpred` are real proof terms (recursor with refl
/// minors) and register WITHOUT any axiom. `int_env()` already type-checks them
/// at `add_decl`; here we re-confirm their inferred types are exactly the
/// inverse-law statements.
#[test]
fn test_predsucc_succpred_are_proved_inverse_laws() {
    let env = int_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (ps_ty, _) = tc
        .infer_type_with_cert(&cst("predsucc"))
        .expect("predsucc should type-check");
    assert!(
        tc.is_def_eq(&ps_ty, &predsucc_ty()),
        "predsucc : (z:MyZ) → Path (λ_.MyZ) (pred (succ z)) z; got {ps_ty:?}"
    );

    let (sp_ty, _) = tc
        .infer_type_with_cert(&cst("succpred"))
        .expect("succpred should type-check");
    assert!(
        tc.is_def_eq(&sp_ty, &succpred_ty()),
        "succpred : (z:MyZ) → Path (λ_.MyZ) (succ (pred z)) z; got {sp_ty:?}"
    );

    // Endpoint sanity on a concrete input: predsucc (ofNat 0) : Path (λ_.MyZ) _ _
    // with both endpoints `ofNat 0` (the law instance `pred (succ 0) = 0`).
    let app = Expr::app(cst("predsucc"), ofnat(mn_zero()));
    let (app_ty, _) = tc
        .infer_type_with_cert(&app)
        .expect("predsucc (ofNat 0) should type-check");
    let app_ty_whnf = tc.whnf(&app_ty);
    let ExprKind::CubicalPath { left, right, .. } = app_ty_whnf.kind() else {
        panic!("predsucc (ofNat 0) must infer to a Path; got {app_ty:?}");
    };
    assert!(
        tc.is_def_eq(left, &ofnat(mn_zero())) && tc.is_def_eq(right, &ofnat(mn_zero())),
        "predsucc (ofNat 0) : Path (λ_.MyZ) (ofNat 0) (ofNat 0); got {left:?} = {right:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 3 — sucEquiv : Equiv MyZ MyZ  (the η/ε fields line up against the record type)
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_sucequiv_is_an_equivalence() {
    let env = int_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (se_ty, _) = tc
        .infer_type_with_cert(&suc_equiv())
        .expect("sucEquiv should type-check");
    let expected = Expr::apps(
        Expr::const_(nm("Equiv"), vec![type_level()]),
        [myz(), myz()],
    );
    assert!(
        tc.is_def_eq(&se_ty, &expected),
        "sucEquiv : Equiv MyZ MyZ; got {se_ty:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 4 — THE MEANINGFUL WINDING + the vacuity guard
// ══════════════════════════════════════════════════════════════════════════════

/// VACUITY GUARD: `MyZ` must NOT η-collapse — `ofNat 0` and `ofNat 1` (and the
/// negSucc branch) must be DISTINCT. With a genuine 2-constructor `MyZ` over a
/// 2-constructor `MyNat` there is no structure-η, so the winding assertion below
/// is MEANINGFUL (not vacuously true).
#[test]
fn test_myz_integers_are_distinct_else_winding_is_vacuous() {
    let env = int_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    assert!(
        !tc.is_def_eq(&ofnat(mn_zero()), &ofnat(mn_succ(mn_zero()))),
        "ofNat 0 ≡ ofNat 1: MyZ η-collapsed — the winding test would be VACUOUS"
    );
    assert!(
        !tc.is_def_eq(&ofnat(mn_zero()), &negsucc(mn_zero())),
        "ofNat 0 ≡ negSucc 0: MyZ η-collapsed — VACUOUS"
    );
    assert!(
        !tc.is_def_eq(
            &ofnat(mn_succ(mn_zero())),
            &ofnat(mn_succ(mn_succ(mn_zero())))
        ),
        "ofNat 1 ≡ ofNat 2: MyZ/MyNat η-collapsed — VACUOUS"
    );
}

#[test]
fn test_winding_transport_sucequiv_zero_is_one() {
    let env = int_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // THE KEY COMPUTATION:
    //   transport (ua sucEquiv) (ofNat 0)
    //     ↝ Equiv.fwd sucEquiv (ofNat 0)   (univalence computation rule)
    //     ↝ succ (ofNat 0)                 (Equiv.fwd β on Equiv.mk)
    //     ↝ ofNat (succ 0)   (= 1).        (succ delta + MyZ.rec/MyNat.rec iota)
    let transport = transport_ua(&myz(), &myz(), &suc_equiv(), &ofnat(mn_zero()));
    let reduct = tc.whnf(&transport);
    let one = ofnat(mn_succ(mn_zero()));
    assert!(
        tc.is_def_eq(&reduct, &one),
        "transport (ua sucEquiv) (ofNat 0) must reduce to ofNat (succ 0) (= 1); got {reduct:?}"
    );
    // It really landed on a constructor (`ofNat _`), not a stuck spine.
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "the winding number must be in constructor form (ofNat _); got {reduct:?}"
    );

    // Type preservation: the winding number lives in MyZ.
    let (t_ty, _) = tc
        .infer_type_with_cert(&transport)
        .expect("transport (ua sucEquiv) (ofNat 0) should type-check");
    assert!(
        tc.is_def_eq(&t_ty, &myz()),
        "winding number : MyZ; got {t_ty:?}"
    );

    // Iterating the successor-transport once more gives 2 (the equivalence
    // composes). NOTE: iterated *single* transport, not winding (loop ∙ loop).
    let transport2 = transport_ua(&myz(), &myz(), &suc_equiv(), &reduct);
    let two = ofnat(mn_succ(mn_succ(mn_zero())));
    assert!(
        tc.is_def_eq(&tc.whnf(&transport2), &two),
        "transport (ua sucEquiv) (transport (ua sucEquiv) (ofNat 0)) must reduce to ofNat 2"
    );
}

/// THE BACKWARD WINDING (Deliverable 1 anchor over the real ℤ, on the bare `ua`
/// line): `coe (ua sucEquiv) i1 i0 (ofNat 1) ↝ Equiv.bwd sucEquiv (ofNat 1) ↝
/// pred (ofNat 1) ↝ ofNat 0`. Non-vacuous (genuine 2-ctor `MyZ`): `ofNat 0 ≢ ofNat 1`.
/// The mirror of the forward `coe (ua e) i0 i1 (ofNat 0) ↝ ofNat 1`.
#[test]
fn test_backward_transport_sucequiv_one_is_zero() {
    let env = int_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // coe (ua sucEquiv) i1 i0 (ofNat 1) ↝ ofNat 0  (the inverse / pred direction).
    let bwd = transport_ua_bwd(&myz(), &myz(), &suc_equiv(), &z1());
    let reduct = tc.whnf(&bwd);
    assert!(
        tc.is_def_eq(&reduct, &z0()),
        "coe (ua sucEquiv) i1 i0 (ofNat 1) must reduce to ofNat 0 (pred); got {reduct:?}"
    );
    // Constructor form, non-vacuously distinct from ofNat 1.
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "the inverse winding must be in constructor form (ofNat _); got {reduct:?}"
    );
    assert!(!tc.is_def_eq(&reduct, &z1()), "ofNat 0 ≡ ofNat 1 — VACUOUS");

    // Type preservation: the inverse winding lives in MyZ.
    let (t_ty, _) = tc
        .infer_type_with_cert(&bwd)
        .expect("coe (ua sucEquiv) i1 i0 (ofNat 1) should type-check");
    assert!(
        tc.is_def_eq(&t_ty, &myz()),
        "inverse winding : MyZ; got {t_ty:?}"
    );

    // FORWARD still green (no regression): coe (ua sucEquiv) i0 i1 (ofNat 0) ↝ ofNat 1.
    let fwd = transport_ua(&myz(), &myz(), &suc_equiv(), &z0());
    assert!(
        tc.is_def_eq(&tc.whnf(&fwd), &z1()),
        "forward transport must still compute (ofNat 0 ↦ ofNat 1)"
    );

    // Round-trip: bwd ∘ fwd = id. coe i1 i0 (coe i0 i1 (ofNat 0)) ↝ ofNat 0.
    let round = transport_ua_bwd(&myz(), &myz(), &suc_equiv(), &tc.whnf(&fwd));
    assert!(
        tc.is_def_eq(&tc.whnf(&round), &z0()),
        "backward ∘ forward must be the identity on ofNat 0"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 5 — `intLoop : MyZ → Ω S¹`, the decode map (type-checks)
// ══════════════════════════════════════════════════════════════════════════════

fn s1() -> Expr {
    cst("S1")
}
fn s1_base() -> Expr {
    cst("S1.base")
}
fn s1_loop() -> Expr {
    cst("S1.loop")
}
/// `Ω S¹ := Path (λ_:I. S¹) base base` — the loop space at `base`.
fn omega_s1() -> Expr {
    path(const_line(s1()), s1_base(), s1_base())
}

/// `path_compose` that tolerates **open** path arguments (used for the recursor
/// IH, a bound variable). Identical to [`crate::tc::reduction::kan::path_compose`]
/// except `p`/`q` are `lift`ed past the binders they are placed under (a no-op for
/// closed paths, so it agrees with the kernel helper on closed inputs):
/// `p` sits one binder deep in `base` (under `<i>`) and two deep in the tubes
/// (under `<i>` then `λ j`); likewise `q` in its tube.
fn path_compose_open(a_type: &Expr, level: Level, p: &Expr, q: &Expr) -> Expr {
    let eq0 = |arg: Expr| Expr::app(Expr::const_(nm("Cofib.eq0"), vec![]), arg);
    let eq1 = |arg: Expr| Expr::app(Expr::const_(nm("Cofib.eq1"), vec![]), arg);
    let papp = |path: Expr, arg: Expr| {
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(path),
            arg: Arc::new(arg),
        })
    };
    // φ = (i=0) ∨ (i=1), i = BVar 0 at the hcomp level.
    let phi = Expr::app(
        Expr::app(Expr::const_(nm("Cofib.or"), vec![]), eq0(bvar(0))),
        eq1(bvar(0)),
    );
    // Tubes (under `<i>` then `λ j`): p/q lifted by 2. Inside, i = BVar 1.
    let branch_i0 = lam(interval(), papp(p.lift(2), bvar(1)));
    let branch_i1 = lam(interval(), papp(q.lift(2), bvar(0)));
    let levels = vec![level];
    let sys_nil = Expr::app(
        Expr::const_(nm("System.nil"), levels.clone()),
        a_type.clone(),
    );
    let sys_cons = |face: Expr, head: Expr, tail: Expr| {
        Expr::apps(
            Expr::const_(nm("System.cons"), levels.clone()),
            [a_type.clone(), face, head, tail],
        )
    };
    let system = sys_cons(
        eq0(bvar(0)),
        branch_i0,
        sys_cons(eq1(bvar(0)), branch_i1, sys_nil),
    );
    // base (under `<i>`): p lifted by 1.
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(a_type.clone()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(papp(p.lift(1), bvar(0))),
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(hcomp),
    })
}

/// `intLoop : MyZ → Ω S¹`, the decode map:
/// ```text
/// intLoop (ofNat 0)          = refl base
/// intLoop (ofNat (succ n))   = intLoop (ofNat n) ∙ loop
/// intLoop (negSucc 0)        = loop⁻¹
/// intLoop (negSucc (succ n)) = intLoop (negSucc n) ∙ loop⁻¹
/// ```
/// (`ofNat n` ↦ `loopⁿ`, `negSucc n` ↦ `(loop⁻¹)ⁿ⁺¹`.) The recursor IH is the
/// `intLoop`-of-predecessor path, composed with one more (inverse) `loop`.
///
/// The inverse `loop⁻¹` is the **regular** `sym_neg` (`<i> loop @ (~i)`), *not*
/// the hcomp-based `sym`: the regular inverse winds back through the *same* `ua`
/// Glue line (read at the reversed interval), so `winding (q ∙ loop⁻¹) ↝ pred
/// (winding q)` **computes** — exactly the negSucc analogue of the forward
/// `winding (q ∙ loop) ↝ succ (winding q)`. With the hcomp-based `sym` the
/// backward `coe`-over-`Glue` stays stuck (the transp-over-Glue rule is the
/// forward, `i1`-total orientation), so `encodeDecode`'s negSucc minors would not
/// close. Both choices have the same type (`Path (λ_.S¹) base base`), so this is a
/// drop-in change to the decode map.
fn intloop_value() -> Expr {
    let loop_inv = || path_sym_neg(&s1_loop());
    // ofNat case: λ n. MyNat.rec (λ_.Ω) (refl base) (λ k ih. ih ∙ loop) n
    let cof = {
        let c_in = lam(mynat(), omega_s1());
        let cz = path_refl(&s1_base());
        let cs = lam(
            mynat(),
            lam(
                omega_s1(),
                path_compose_open(&s1(), lvl1(), &bvar(0), &s1_loop()),
            ),
        );
        lam(mynat(), Expr::apps(rec("MyNat"), [c_in, cz, cs, bvar(0)]))
    };
    // negSucc case: λ m. MyNat.rec (λ_.Ω) (loop⁻¹) (λ k ih. ih ∙ loop⁻¹) m
    let cneg = {
        let c_in = lam(mynat(), omega_s1());
        let cz = loop_inv();
        let cs = lam(
            mynat(),
            lam(
                omega_s1(),
                path_compose_open(&s1(), lvl1(), &bvar(0), &loop_inv()),
            ),
        );
        lam(mynat(), Expr::apps(rec("MyNat"), [c_in, cz, cs, bvar(0)]))
    };
    let motive = lam(myz(), omega_s1());
    Expr::apps(rec("MyZ"), [motive, cof, cneg])
}

/// `int_env()` plus the circle `S¹` (`base`/`loop`) and the registered `intLoop`.
fn int_env_with_s1() -> Environment {
    let mut env = int_env();
    let loop_ty = path(const_line(s1()), s1_base(), s1_base());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("S1"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: nm("S1.base"),
                    type_: s1(),
                },
                Constructor {
                    name: nm("S1.loop"),
                    type_: loop_ty,
                },
            ],
        }],
    })
    .expect("S¹ should declare without error");
    env.add_decl(Declaration::Definition {
        name: nm("intLoop"),
        level_params: vec![],
        type_: Expr::arrow(myz(), omega_s1()),
        value: intloop_value(),
        is_reducible: false,
    })
    .expect("intLoop (the decode map) should type-check and register");
    env
}

#[test]
fn test_intloop_typechecks_as_decode_map() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // intLoop : MyZ → Ω S¹.
    let (il_ty, _) = tc
        .infer_type_with_cert(&cst("intLoop"))
        .expect("intLoop should type-check");
    assert!(
        tc.is_def_eq(&il_ty, &Expr::arrow(myz(), omega_s1())),
        "intLoop : MyZ → Path (λ_.S¹) base base; got {il_ty:?}"
    );

    // Applied to a concrete integer it is a genuine loop `Path S¹ base base`.
    let il_one = Expr::app(cst("intLoop"), ofnat(mn_succ(mn_zero())));
    let (il_one_ty, _) = tc
        .infer_type_with_cert(&il_one)
        .expect("intLoop (ofNat 1) should type-check");
    let il_one_ty_whnf = tc.whnf(&il_one_ty);
    let ExprKind::CubicalPath { left, right, .. } = il_one_ty_whnf.kind() else {
        panic!("intLoop (ofNat 1) must infer to a Path; got {il_one_ty:?}");
    };
    assert!(
        tc.is_def_eq(left, &s1_base()) && tc.is_def_eq(right, &s1_base()),
        "intLoop (ofNat 1) : Path (λ_.S¹) base base; got {left:?} = {right:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 6 — `hcomp` commutes with a SINGLE NON-RECURSIVE field constructor (`ofNat`)
//
// This is the "`hcomp` on a discrete set (ℤ) collapses via the constructors"
// piece — the *tail* of the `winding(loop²) ↝ 2` chain. It pushes a stuck
// `hcomp {MyZ} [φ↦u] (ofNat n)` down to `ofNat (hcomp {MyNat} [φ↦ proj u] n)`,
// re-typing the System from `MyZ` to the field type `MyNat`, and then the inner
// `hcomp {MyNat}` collapses through `MyNat`'s own (succ/zero) Kan rules. The
// `MyZ`/`MyNat` types here are GENUINE 2-/2-constructor inductives (no η-collapse),
// so `ofNat 2 ≢ ofNat 0` and the value assertions are MEANINGFUL.
// ══════════════════════════════════════════════════════════════════════════════

/// A neutral interval `j : I` (so faces `(j=1)` are neither ⊤ nor ⊥ ⇒ the
/// genuinely-new constructor-commutation rule fires, not the on-a-face rule).
fn ji() -> Expr {
    cst("jI")
}
fn face_eq1(r: Expr) -> Expr {
    Expr::app(cst("Cofib.eq1"), r)
}
fn cofib_top() -> Expr {
    cst("Cofib.top")
}
/// `λ _:I. value : I → A` — a constant interval tube.
fn const_tube(value: Expr) -> Expr {
    lam(interval(), value)
}
/// `hcomp {ty} [phi ↦ u] base`.
fn hcomp(ty: Expr, phi: Expr, u: Expr, base: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(ty),
        phi: Arc::new(phi),
        u: Arc::new(u),
        base: Arc::new(base),
    })
}
/// `System.cons.{1} A φ head tail` / `System.nil.{1} A` (multi-branch encoding).
fn sys_cons(a: Expr, face: Expr, head: Expr, tail: Expr) -> Expr {
    Expr::apps(
        Expr::const_(nm("System.cons"), vec![lvl1()]),
        [a, face, head, tail],
    )
}
fn sys_nil(a: Expr) -> Expr {
    Expr::app(Expr::const_(nm("System.nil"), vec![lvl1()]), a)
}

/// `int_env()` plus a neutral interval `jI : I` and a neutral `aN : MyNat`.
fn int_env_with_j() -> Environment {
    let mut env = int_env();
    env.add_decl(Declaration::Axiom {
        name: nm("jI"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("neutral interval jI registers");
    env.add_decl(Declaration::Axiom {
        name: nm("aN"),
        level_params: vec![],
        type_: mynat(),
    })
    .expect("neutral MyNat aN registers");
    env
}

/// Convenience: the integer literals `0`, `1`, `2` as `MyZ` constructor terms.
fn z0() -> Expr {
    ofnat(mn_zero())
}
fn z1() -> Expr {
    ofnat(mn_succ(mn_zero()))
}
fn z2() -> Expr {
    ofnat(mn_succ(mn_succ(mn_zero())))
}

/// The projection `MyZ.ofNat`-field extractor `proj : MyZ → MyNat` reduces
/// `proj (ofNat n) ↝ n` (the only behaviour the `hcomp` rule's soundness uses),
/// and is a well-typed total `MyZ → MyNat`.
#[test]
fn test_single_field_projection_extracts_ofnat_field() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let proj = tc
        .build_single_field_projection_for_test(&nm("MyZ"), &nm("MyZ.ofNat"), &mynat(), &lvl1())
        .expect("MyZ.ofNat single-field projection builds");

    // proj (ofNat 0) ↝ 0 ; proj (ofNat 2) ↝ 2.
    assert!(
        tc.is_def_eq(&tc.whnf(&Expr::app(proj.clone(), z0())), &mn_zero()),
        "proj (ofNat 0) should be 0"
    );
    assert!(
        tc.is_def_eq(
            &tc.whnf(&Expr::app(proj.clone(), z2())),
            &mn_succ(mn_succ(mn_zero()))
        ),
        "proj (ofNat 2) should be 2"
    );
    // Also extracts the negSucc field (irrelevant off-face, but total & typed).
    assert!(
        tc.is_def_eq(
            &tc.whnf(&Expr::app(proj.clone(), negsucc(mn_zero()))),
            &mn_zero()
        ),
        "proj (negSucc 0) should be 0 (the negSucc field)"
    );
    // Well-typed total `MyZ → MyNat`.
    let proj_ty = tc.infer_type(&proj).expect("proj type-checks");
    assert!(
        tc.is_def_eq(&proj_ty, &Expr::arrow(myz(), mynat())),
        "proj : MyZ → MyNat; got {proj_ty:?}"
    );
}

/// The rule FIRES on a neutral face and lands on the `ofNat` constructor.
#[test]
fn test_hcomp_over_ofnat_neutral_face_pushes_through() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // hcomp {MyZ} [(jI=1) ↦ λ_. ofNat 0] (ofNat 0).  (jI neutral ⇒ new rule.)
    let h = hcomp(myz(), face_eq1(ji()), const_tube(z0()), z0());
    let reduct = tc.whnf(&h);

    // It genuinely reduced (not a stuck CubicalHComp), and is `ofNat _`-headed.
    assert!(
        !matches!(reduct.kind(), ExprKind::CubicalHComp { .. }),
        "the ofNat rule must fire on a neutral face, but hcomp stayed stuck: {reduct:?}"
    );
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "reduct must be ofNat-headed; got {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&reduct, &z0()),
        "hcomp [(jI=1)↦ofNat 0] (ofNat 0) should collapse to ofNat 0; got {reduct:?}"
    );
}

/// THE TAIL of `winding(loop²) ↝ 2`: a stuck `hcomp` correction over `MyZ`
/// (a discrete set) collapses to the base integer — `hcomp [φ↦…2] (ofNat 2) ↝
/// ofNat 2`. Guarded by non-vacuity (`ofNat 2 ≢ ofNat 0`, `≢ ofNat 1`).
#[test]
fn test_hcomp_over_ofnat_collapses_to_two() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // hcomp {MyZ} [(jI=1) ↦ λ_. ofNat 2] (ofNat 2)
    //   ↝ ofNat (hcomp {MyNat} [(jI=1) ↦ λj. proj(ofNat 2)] 2)
    //   ↝ ofNat 2                          (inner MyNat hcomp collapses via succ/zero)
    let h = hcomp(myz(), face_eq1(ji()), const_tube(z2()), z2());
    let reduct = tc.whnf(&h);
    assert!(
        tc.is_def_eq(&reduct, &z2()),
        "hcomp [(jI=1)↦ofNat 2] (ofNat 2) must collapse to ofNat 2; got {reduct:?}"
    );

    // NON-VACUITY: the result is genuinely 2, distinct from 0 and 1.
    assert!(
        !tc.is_def_eq(&reduct, &z0()),
        "ofNat 2 ≡ ofNat 0 — MyZ η-collapsed, the test is VACUOUS"
    );
    assert!(
        !tc.is_def_eq(&reduct, &z1()),
        "ofNat 2 ≡ ofNat 1 — MyZ η-collapsed, the test is VACUOUS"
    );

    // Same for 3 (`loop³` tail).
    let z3 = ofnat(mn_succ(mn_succ(mn_succ(mn_zero()))));
    let h3 = hcomp(myz(), face_eq1(ji()), const_tube(z3.clone()), z3.clone());
    assert!(
        tc.is_def_eq(&tc.whnf(&h3), &z3),
        "hcomp [(jI=1)↦ofNat 3] (ofNat 3) must collapse to ofNat 3"
    );
}

/// The rule also fires on the **other** single-non-recursive-field constructor
/// `negSucc` (both `MyZ` constructors are single-`MyNat`-field).
#[test]
fn test_hcomp_over_negsucc_collapses() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ns0 = negsucc(mn_zero());
    let h = hcomp(myz(), face_eq1(ji()), const_tube(ns0.clone()), ns0.clone());
    let reduct = tc.whnf(&h);
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.negSucc")),
        "reduct must be negSucc-headed; got {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&reduct, &ns0),
        "hcomp [(jI=1)↦negSucc 0] (negSucc 0) must collapse to negSucc 0; got {reduct:?}"
    );
}

/// TYPE PRESERVATION + the System is genuinely **re-typed** from `MyZ` to the
/// field type `MyNat`: on a NEUTRAL floor field `ofNat aN` (`aN : MyNat`) the
/// inner `hcomp` stays stuck, so we can inspect that it runs at `MyNat` and that
/// both redex and reduct infer to `MyZ`.
#[test]
fn test_hcomp_over_ofnat_type_preservation_and_retype() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Multi-branch System.cons encoding over MyZ, neutral floor `ofNat aN`.
    let floor = ofnat(cst("aN"));
    let system = sys_cons(
        myz(),
        face_eq1(ji()),
        const_tube(floor.clone()),
        sys_nil(myz()),
    );
    let h = hcomp(myz(), face_eq1(ji()), system, floor.clone());

    let h_ty = tc.infer_type(&h).expect("hcomp over ofNat type-checks");
    let reduct = tc.whnf(&h);

    // reduct = ofNat (inner), inner a stuck `hcomp {MyNat}` (neutral floor `aN`).
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "reduct must be ofNat-headed; got {reduct:?}"
    );
    let inner = &reduct.get_app_args()[0];
    let ExprKind::CubicalHComp { ty: inner_ty, .. } = inner.kind() else {
        panic!("the inner hcomp (over the field type) must survive; got {inner:?}");
    };
    assert!(
        tc.is_def_eq(inner_ty, &mynat()),
        "the inner hcomp must be RE-TYPED to the field type MyNat; got {inner_ty:?}"
    );

    // Type preservation: infer(redex) ≡ infer(reduct) ≡ MyZ.
    let r_ty = tc
        .infer_type(&reduct)
        .expect("the reduct (ofNat of a re-typed hcomp) type-checks");
    assert!(tc.is_def_eq(&h_ty, &myz()), "hcomp over ofNat : MyZ");
    assert!(tc.is_def_eq(&r_ty, &myz()), "reduct : MyZ");
    assert!(tc.is_def_eq(&h_ty, &r_ty), "type preserved");
}

/// BOUNDARY COHERENCE: on a TRUE face ⊤ the on-a-face rule gives `u i1`; the
/// constructor-commutation route (neutral face, same constant tube) gives the
/// same value — both `ofNat 2`.
#[test]
fn test_hcomp_over_ofnat_boundary_coherence() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let tube = const_tube(z2());
    let on_true = hcomp(myz(), cofib_top(), tube.clone(), z2());
    let true_route = tc.whnf(&on_true);
    assert!(
        tc.is_def_eq(&true_route, &Expr::app(tube.clone(), i1())),
        "⊤-face route must be exactly `u i1`"
    );

    let on_neutral = hcomp(myz(), face_eq1(ji()), tube, z2());
    let new_route = tc.whnf(&on_neutral);
    assert!(
        tc.is_def_eq(&true_route, &new_route),
        "⊤-route and constructor-rule route must agree (both ofNat 2)"
    );
    assert!(
        tc.is_def_eq(&new_route, &z2()),
        "both routes must be ofNat 2; got {new_route:?}"
    );
}

/// DETERMINISM: WHNF of the redex is reproducible (one canonical reduct).
#[test]
fn test_hcomp_over_ofnat_determinism() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let h = hcomp(myz(), face_eq1(ji()), const_tube(z2()), z2());
    let r1 = tc.whnf(&h);
    let r2 = tc.whnf(&h);
    assert!(
        tc.is_def_eq(&r1, &r2),
        "WHNF must be deterministic on the ofNat redex"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 7 — `hcomp` in the UNIVERSE: total-face boundary (`hcomp {U} [⊤↦T] A ≡ T i1`)
//
// Sanity that the universe-level `hcomp` boundary is the lid `T i1` — the boundary
// any sound "hcomp-in-U ↝ Glue" rule must agree with. (This holds via the existing
// on-a-true-face `hcomp` rule, which is type-agnostic; no Glue rule is required.)
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_hcomp_in_universe_total_face_is_lid() {
    let env = int_env_with_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // hcomp {Type} [⊤ ↦ λ_:I. MyZ] MyNat  ↝  (λ_:I. MyZ) i1 ≡ MyZ.
    let tube = const_tube(myz());
    let h = hcomp(Expr::type_(), cofib_top(), tube.clone(), mynat());
    let reduct = tc.whnf(&h);
    assert!(
        tc.is_def_eq(&reduct, &myz()),
        "hcomp {{U}} [⊤↦λ_.MyZ] MyNat must reduce to the lid MyZ; got {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&reduct, &Expr::app(tube, i1())),
        "the universe-hcomp total-face boundary must be exactly `T i1`"
    );
    // The boundary value is a genuine type (`MyZ : Type`).
    let r_ty = tc.infer_type(&reduct).expect("the lid type-checks");
    assert!(
        tc.is_def_eq(&r_ty, &Expr::type_()),
        "the lid MyZ : Type; got {r_ty:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 8 — `winding (loop ∙ loop)` over the REAL ℤ — Deliverable A progress + the
//      Deliverable B blocker, as a durable soundness anchor.
//
// `winding(loop²) := coe (λ i. helix ((loop∙loop)@i)) i0 i1 (ofNat 0)` with
// `helix := S¹.rec.{2} (λ_:S¹. Type) MyZ (ua sucEquiv)`. The reduction chain:
//   1. recursor-over-`hcomp` pushes `helix` through the `loop∙loop` `hcomp{S¹}`,
//   2. the loop β-rule turns each tube/base into `(ua sucEquiv)@·`, giving a
//      `hcomp{Type}` of types — i.e. exactly `(ua e)∙(ua e)` as a type line,
//   3. **Deliverable A** reduces that `hcomp{Type}` to an explicit `Glue` line,
//   4. the outer `coe` over that **Glue line** is the genuinely-general CCHM
//      transp-over-`Glue` (i-dependent faces (i=0)/(i=1)) — **Deliverable B**,
//      which is NOT implemented (it requires the equivalence's contractible-fiber
//      structure our quasi-inverse `Equiv` lacks; see the report). So the outer
//      `coe` stays **stuck** rather than guess the unsound correction.
//
// These tests assert the DURABLE facts: (a) step 3 fires — the line body is now an
// explicit `Glue` (Deliverable A on the real winding shape, over a genuine 2-ctor
// `MyZ` so it is non-vacuous); (b) the winding number is NEVER a *wrong* integer
// (stuck now, must be `ofNat 2` once B lands — never 0/1/3); (c) `winding loop ↝ 1`
// still computes (regression).
// ══════════════════════════════════════════════════════════════════════════════

/// `helix major := S¹.rec.{2} (λ_:S¹. Type) MyZ (ua sucEquiv) major` over real ℤ.
fn helix_applied_myz(major: Expr) -> Expr {
    let motive = lam(s1(), Expr::type_()); // λ_:S¹. Type
    let u2 = Level::succ(Level::succ(Level::zero())); // motive lands in Sort 2
    let rec = Expr::const_(nm("S1.rec"), vec![u2]);
    let ua = glue_ua(&myz(), &myz(), &suc_equiv(), type_level()); // ua sucEquiv : MyZ = MyZ
    Expr::apps(rec, [motive, myz(), ua, major])
}

/// `int_env_with_s1()` plus a neutral interval `jI : I` (so the universe `hcomp`
/// faces `(jI=0)`/`(jI=1)` are neutral and Deliverable A fires).
fn int_env_with_s1_and_j() -> Environment {
    let mut env = int_env_with_s1();
    env.add_decl(Declaration::Axiom {
        name: nm("jI"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("neutral interval jI registers");
    env
}

/// (a) **Deliverable A on the real winding shape**: the `helix(loop²@i)` line body
/// at a neutral interval point reduces to an explicit `Glue` line over real ℤ.
#[test]
fn test_winding_loop_squared_body_is_glue_line_over_real_z() {
    let env = int_env_with_s1_and_j();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // helix ((loop∙loop) @ jI), with jI : I neutral.
    let loop_sq = path_compose(&s1(), lvl1(), &s1_loop(), &s1_loop());
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(loop_sq),
        arg: Arc::new(cst("jI")),
    });
    let body = helix_applied_myz(major);

    let reduct = tc.whnf(&body);
    // Step 1–3: recursor-over-hcomp + loop β + Deliverable A ⇒ an explicit `Glue`.
    assert!(
        !matches!(reduct.kind(), ExprKind::CubicalHComp { .. }),
        "the universe→Glue rule must fire on the real winding line; stayed an hcomp: {reduct:?}"
    );
    let ExprKind::Const(head, _) = reduct.get_app_fn().kind() else {
        panic!("helix(loop²@jI) must reduce to a Glue-headed type; got {reduct:?}");
    };
    assert_eq!(
        *head,
        nm("Glue"),
        "helix(loop²@jI) must reduce to an explicit Glue line; got head {head:?}"
    );
    // Two cells (faces (jI=0) and (jI=1)) — the composed-ua shape.
    let cells = tc
        .parse_glue_system_for_test(reduct.get_app_args()[2])
        .expect("the produced Glue system parses");
    assert_eq!(
        cells.len(),
        2,
        "loop² ⇒ a two-cell Glue; got {}",
        cells.len()
    );
}

/// (b) **Durable soundness guard**: `winding(loop²)` is NEVER a wrong integer —
/// never `ofNat 0`, `ofNat 1`, or `ofNat 3`. With Deliverable B (the general
/// transp-over-`Glue` rule) landed it computes to exactly `ofNat 2`. Non-vacuous:
/// `MyZ` is a genuine 2-constructor ℤ (no η-collapse), so those integers are all
/// distinct.
#[test]
fn test_winding_loop_squared_is_never_a_wrong_integer() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // winding(loop²) := coe (λ i. helix ((loop∙loop)@i)) i0 i1 (ofNat 0).
    let loop_sq = path_compose(&s1(), lvl1(), &s1_loop(), &s1_loop());
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(loop_sq),
        arg: Arc::new(bvar(0)), // i = BVar(0) under the coe line λ i.
    });
    let line = lam(interval(), helix_applied_myz(major));
    let winding = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(z0()),
    });

    // The coe itself type-checks (it is a genuine transport over a type line : ℤ).
    let (w_ty, _) = tc
        .infer_type_with_cert(&winding)
        .expect("winding(loop²) should type-check as a transport");
    assert!(tc.is_def_eq(&w_ty, &myz()), "winding(loop²) : MyZ");

    let reduct = tc.whnf(&winding);
    let z3 = ofnat(mn_succ(mn_succ(mn_succ(mn_zero()))));

    // SOUNDNESS GUARD (durable): never a *wrong* integer.
    assert!(
        !tc.is_def_eq(&reduct, &z0()),
        "winding(loop²) must NEVER reduce to ofNat 0; got {reduct:?}"
    );
    assert!(
        !tc.is_def_eq(&reduct, &z1()),
        "winding(loop²) must NEVER reduce to ofNat 1; got {reduct:?}"
    );
    assert!(
        !tc.is_def_eq(&reduct, &z3),
        "winding(loop²) must NEVER reduce to ofNat 3; got {reduct:?}"
    );

    // Deliverable B landed: the value is exactly ofNat 2.
    assert!(
        tc.is_def_eq(&reduct, &z2()),
        "winding(loop²) must compute to ofNat 2; got {reduct:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 9 — THE HEADLINE: `winding (loop ∙ loop) ↝ ofNat 2` (π₁(S¹)=ℤ computational core)
//
// The full chain over the REAL 2-constructor ℤ `MyZ`:
//   ap-functoriality (recursor-over-hcomp + loop β)  →  (ua e)∙(ua e) as a Glue
//   line (Deliverable A)  →  the general CCHM transp-over-Glue (Deliverable B: the
//   `coe`-over-Glue rule in this commit) composing the two successor-transports  →
//   `ofNat 2`. Non-vacuous: `MyZ` is a genuine 2-ctor ℤ so `ofNat 2 ≢ ofNat 0/1/3`.
// ══════════════════════════════════════════════════════════════════════════════

/// `winding (loopⁿ) := coe (λ i. helix (loopⁿ@i)) i0 i1 (ofNat 0)` over real ℤ.
fn winding_of(loop_path: Expr) -> Expr {
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(loop_path),
        arg: Arc::new(bvar(0)), // i = BVar(0) under the coe line λ i.
    });
    let line = lam(interval(), helix_applied_myz(major));
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(z0()),
    })
}

/// THE MILESTONE: `winding (loop ∙ loop) ↝ ofNat 2` (def-eq), in constructor form,
/// non-vacuously distinct from `ofNat 0`/`1`/`3`.
#[test]
fn test_winding_loop_squared_is_two() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let loop_sq = path_compose(&s1(), lvl1(), &s1_loop(), &s1_loop());
    let winding = winding_of(loop_sq);
    let reduct = tc.whnf(&winding);

    // ↝ ofNat 2, in CONSTRUCTOR form (not a stuck coe/spine).
    assert!(
        tc.is_def_eq(&reduct, &z2()),
        "winding(loop²) must reduce to ofNat 2; got {reduct:?}"
    );
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "the winding number must be in constructor form (ofNat _); got {reduct:?}"
    );

    // NON-VACUITY: ofNat 2 is genuinely distinct from 0, 1, 3.
    let z3 = ofnat(mn_succ(mn_succ(mn_succ(mn_zero()))));
    assert!(!tc.is_def_eq(&reduct, &z0()), "ofNat 2 ≡ ofNat 0 — VACUOUS");
    assert!(
        !tc.is_def_eq(&reduct, &z1()),
        "ofNat 2 ≡ ofNat 1 — wrong winding"
    );
    assert!(
        !tc.is_def_eq(&reduct, &z3),
        "ofNat 2 ≡ ofNat 3 — wrong winding"
    );

    // Type preservation: the winding number lives in MyZ.
    let (w_ty, _) = tc
        .infer_type_with_cert(&winding)
        .expect("winding(loop²) should type-check");
    assert!(
        tc.is_def_eq(&w_ty, &myz()),
        "winding(loop²) : MyZ; got {w_ty:?}"
    );
}

/// `winding (loop ∙ (loop ∙ loop)) ↝ ofNat 3` — the rule composes three
/// successor-transports (the general loopⁿ case beyond the headline loop²).
#[test]
fn test_winding_loop_cubed_is_three() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let loop_sq = path_compose(&s1(), lvl1(), &s1_loop(), &s1_loop());
    let loop_cb = path_compose(&s1(), lvl1(), &s1_loop(), &loop_sq);
    let z3 = ofnat(mn_succ(mn_succ(mn_succ(mn_zero()))));
    let reduct = tc.whnf(&winding_of(loop_cb));
    assert!(
        tc.is_def_eq(&reduct, &z3),
        "winding(loop³) must reduce to ofNat 3; got {reduct:?}"
    );
    assert!(
        !tc.is_def_eq(&reduct, &z2()),
        "ofNat 3 ≡ ofNat 2 — wrong winding"
    );
}

/// DETERMINISM + TYPE-PRESERVATION of the transp-over-Glue reduction on the winding
/// shape: WHNF is reproducible and both redex and reduct infer to `MyZ`.
#[test]
fn test_winding_loop_squared_determinism_and_type_preservation() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let loop_sq = path_compose(&s1(), lvl1(), &s1_loop(), &s1_loop());
    let winding = winding_of(loop_sq);

    let r1 = tc.whnf(&winding);
    let r2 = tc.whnf(&winding);
    assert!(
        tc.is_def_eq(&r1, &r2),
        "WHNF must be deterministic on winding(loop²)"
    );

    let (redex_ty, _) = tc
        .infer_type_with_cert(&winding)
        .expect("redex type-checks");
    let r_ty = tc.infer_type(&r1).expect("reduct type-checks");
    assert!(
        tc.is_def_eq(&redex_ty, &r_ty),
        "transp-over-Glue must preserve type"
    );
    assert!(tc.is_def_eq(&r_ty, &myz()), "reduct : MyZ");
}

/// (c) **Regression**: `winding loop ↝ ofNat 1` still computes over real ℤ — the
/// single-`ua`-line transport (no `hcomp`-of-types) is untouched by Deliverable A.
#[test]
fn test_winding_loop_is_one_over_real_z_regression() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // winding loop := coe (λ i. helix (loop@i)) i0 i1 (ofNat 0).
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(s1_loop()),
        arg: Arc::new(bvar(0)),
    });
    let line = lam(interval(), helix_applied_myz(major));
    let winding = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(z0()),
    });

    let reduct = tc.whnf(&winding);
    assert!(
        tc.is_def_eq(&reduct, &z1()),
        "winding loop must reduce to ofNat 1; got {reduct:?}"
    );
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "winding loop must land on an ofNat constructor; got {reduct:?}"
    );
}

/// `winding := λ p:Ω S¹. coe (λ i. helix (p @ i)) i0 i1 (ofNat 0)` — the encode
/// map as a total function `Ω S¹ → MyZ`. Under `λ p` then the coe line `λ i`,
/// `p = BVar(1)`, `i = BVar(0)`, so `p @ i = BVar(1) @ BVar(0)`.
fn winding_value() -> Expr {
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(bvar(1)), // p, under λp then λi
        arg: Arc::new(bvar(0)),  // i
    });
    let line = lam(interval(), helix_applied_myz(major));
    let coe = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(z0()),
    });
    lam(omega_s1(), coe)
}

// ══════════════════════════════════════════════════════════════════════════════
// 10 — `winding : Ω S¹ → MyZ` as a FUNCTION, and the full `Ω S¹ ≃ ℤ` equivalence
//
// The encode map `winding p := coe (λ i. helix (p @ i)) i0 i1 (ofNat 0)` is now a
// genuine total function `Ω S¹ → MyZ` (it type-checks: the coe's endpoint typing
// `helix (p @ i0) ↝ helix base ↝ MyZ` fires via the neutral-path-endpoint rule
// threaded through the recursor major premise). With `intLoop` the decode map,
// both round-trips are PROVED by the recursors — closing `π₁(S¹) = ℤ` as a
// structured `Equiv`.
// ══════════════════════════════════════════════════════════════════════════════

/// `winding arg` / `intLoop arg` — apply the registered encode / decode constants.
fn winding_n(arg: Expr) -> Expr {
    Expr::app(cst("winding"), arg)
}
fn intloop_n(arg: Expr) -> Expr {
    Expr::app(cst("intLoop"), arg)
}

/// `int_env_with_s1()` plus the registered `winding : Ω S¹ → MyZ` (no scratch
/// axioms — the production environment for the equivalence).
fn int_env_with_winding_clean() -> Environment {
    let mut env = int_env_with_s1();
    env.add_decl(Declaration::Definition {
        name: nm("winding"),
        level_params: vec![],
        type_: Expr::arrow(omega_s1(), myz()),
        value: winding_value(),
        is_reducible: false,
    })
    .expect("winding : Ω S¹ → MyZ should type-check and register");
    env
}

/// `encodeDecode : (n:MyZ) → Path (λ_.MyZ) (winding (intLoop n)) n`  (the ε field).
fn encode_decode_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        myz(),
        path(const_line(myz()), winding_n(intloop_n(bvar(0))), bvar(0)),
    )
}

/// `<i> f (ih @ i)` — `ap f ih` for a unary `f : MyZ → MyZ` and `ih` the IH path.
/// Used as the `MyNat.rec` step minor `λ k. λ ih. <i> f (ih @ i)`; inside the `<i>`
/// path-lam the binders are `i = BVar 0`, `ih = BVar 1`, `k = BVar 2`.
fn ap_unary(f: &str) -> Expr {
    let ih_at_i = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(bvar(1)), // ih
        arg: Arc::new(bvar(0)),  // i
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(Expr::app(cst(f), ih_at_i)),
    })
}

/// PROOF TERM of `encodeDecode`, by `MyZ.rec` / `MyNat.rec`:
/// * `ofNat 0`           : `refl (ofNat 0)`  (winding(intLoop(ofNat 0)) ≡ ofNat 0).
/// * `ofNat (succ k)`    : `ap succ ih`  (winding(intLoop(ofNat(succ k))) ≡
///                          succ(winding(intLoop(ofNat k))), `succ(ofNat k) ≡ ofNat(succ k)`).
/// * `negSucc 0`         : `refl (negSucc 0)` (winding(loop⁻¹) ≡ negSucc 0).
/// * `negSucc (succ k)`  : `ap pred ih`  (winding(intLoop(negSucc(succ k))) ≡
///                          pred(winding(intLoop(negSucc k))), `pred(negSucc k) ≡ negSucc(succ k)`).
/// Every minor closes because the corresponding `winding` round-trip reduces
/// definitionally (forward via `q∙loop ↝ succ`, backward via `q∙loop⁻¹ ↝ pred`).
fn encode_decode_value() -> Expr {
    let motive = lam(
        myz(),
        path(const_line(myz()), winding_n(intloop_n(bvar(0))), bvar(0)),
    );
    // ofNat case: λ n. MyNat.rec C_of (refl (ofNat 0)) (λ k ih. ap succ ih) n
    let cof = {
        let c_of = lam(
            mynat(),
            path(
                const_line(myz()),
                winding_n(intloop_n(ofnat(bvar(0)))),
                ofnat(bvar(0)),
            ),
        );
        let base_of = path_refl(&ofnat(mn_zero()));
        // ih : Path (λ_.MyZ) (winding (intLoop (ofNat k))) (ofNat k)   (k = BVar 0).
        let ih_ty = path(
            const_line(myz()),
            winding_n(intloop_n(ofnat(bvar(0)))),
            ofnat(bvar(0)),
        );
        let step_of = lam(mynat(), lam(ih_ty, ap_unary("MyZ.succ")));
        lam(
            mynat(),
            Expr::apps(rec("MyNat"), [c_of, base_of, step_of, bvar(0)]),
        )
    };
    // negSucc case: λ n. MyNat.rec C_neg (refl (negSucc 0)) (λ k ih. ap pred ih) n
    let cneg = {
        let c_neg = lam(
            mynat(),
            path(
                const_line(myz()),
                winding_n(intloop_n(negsucc(bvar(0)))),
                negsucc(bvar(0)),
            ),
        );
        let base_neg = path_refl(&negsucc(mn_zero()));
        let ih_ty = path(
            const_line(myz()),
            winding_n(intloop_n(negsucc(bvar(0)))),
            negsucc(bvar(0)),
        );
        let step_neg = lam(mynat(), lam(ih_ty, ap_unary("MyZ.pred")));
        lam(
            mynat(),
            Expr::apps(rec("MyNat"), [c_neg, base_neg, step_neg, bvar(0)]),
        )
    };
    Expr::apps(rec("MyZ"), [motive, cof, cneg])
}

/// `int_env_with_winding_clean()` plus the PROVED `encodeDecode`.
fn int_env_with_encode_decode() -> Environment {
    let mut env = int_env_with_winding_clean();
    env.add_decl(Declaration::Definition {
        name: nm("encodeDecode"),
        level_params: vec![],
        type_: encode_decode_ty(),
        value: encode_decode_value(),
        is_reducible: false,
    })
    .expect("encodeDecode proof term should type-check (recursor + ap succ/pred)");
    env
}

#[test]
fn test_winding_is_a_total_function() {
    let env = int_env_with_winding_clean();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let (w_ty, _) = tc
        .infer_type_with_cert(&cst("winding"))
        .expect("winding should type-check");
    assert!(
        tc.is_def_eq(&w_ty, &Expr::arrow(omega_s1(), myz())),
        "winding : Ω S¹ → MyZ; got {w_ty:?}"
    );
}

/// The encode map COMPUTES the winding number on concrete loops:
/// `winding (intLoop n) ↝ n` for `n = 0, 1, 2` (and `-1, -2`), in constructor form.
#[test]
fn test_winding_intloop_computes_to_n() {
    let env = int_env_with_winding_clean();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    for n in [
        z0(),
        z1(),
        z2(),
        negsucc(mn_zero()),          // -1
        negsucc(mn_succ(mn_zero())), // -2
    ] {
        let reduct = tc.whnf(&winding_n(intloop_n(n.clone())));
        assert!(
            tc.is_def_eq(&reduct, &n),
            "winding (intLoop {n:?}) must reduce to {n:?}; got {reduct:?}"
        );
    }
    // Non-vacuity: the integers are genuinely distinct.
    assert!(!tc.is_def_eq(&z1(), &negsucc(mn_zero())), "1 ≢ -1");
}

/// THE ε FIELD: `encodeDecode : (n:MyZ) → Path (λ_.MyZ) (winding (intLoop n)) n`
/// is a PROVED proof term (recursor + `ap succ`/`ap pred`), no axioms.
#[test]
fn test_encode_decode_is_proved() {
    let env = int_env_with_encode_decode();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (ed_ty, _) = tc
        .infer_type_with_cert(&cst("encodeDecode"))
        .expect("encodeDecode should type-check");
    assert!(
        tc.is_def_eq(&ed_ty, &encode_decode_ty()),
        "encodeDecode : (n:MyZ) → Path (λ_.MyZ) (winding (intLoop n)) n; got {ed_ty:?}"
    );

    // Instance on a concrete integer: encodeDecode (ofNat 1) : Path (λ_.MyZ) _ _
    // with both endpoints `ofNat 1` (the round-trip `winding (intLoop 1) = 1`).
    let app = Expr::app(cst("encodeDecode"), z1());
    let (app_ty, _) = tc
        .infer_type_with_cert(&app)
        .expect("encodeDecode (ofNat 1) should type-check");
    let app_ty_whnf = tc.whnf(&app_ty);
    let ExprKind::CubicalPath { left, right, .. } = app_ty_whnf.kind() else {
        panic!("encodeDecode (ofNat 1) must infer to a Path; got {app_ty:?}");
    };
    assert!(
        tc.is_def_eq(left, &z1()) && tc.is_def_eq(right, &z1()),
        "encodeDecode (ofNat 1) : Path (λ_.MyZ) (ofNat 1) (ofNat 1); got {left:?} = {right:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 11 — `decodeEncode` (the η field) via based path-induction `J` — the based maps
//
// `decodeEncode : (p:Ω S¹) → Path (Ω S¹) (intLoop (winding p)) p`. The standard
// proof generalises the endpoint and inducts: with the BASED maps
//   encode : (y:S¹) → (base = y) → helix y      (the transport, definable)
//   decode : (y:S¹) → helix y → (base = y)      (S¹.rec, decode base = intLoop)
// the motive `P y q := Path (decode y (encode y q)) q` is well-formed over the
// VARYING endpoint `y`, `path_J` discharges it (base case `q = refl base`:
// `decode base (encode base (refl base)) = intLoop (ofNat 0) = refl base`), and at
// `y = base` it specialises to `Path (intLoop (winding p)) p` — exactly η.
//
// `encode` builds below. `decode`'s **loop minor** — the S¹.rec PathP
// `Path (λ i. helix(loop@i) → base=loop@i) intLoop intLoop` — is built in §14 NOT
// from the (non-definitional) `intLoopSucc` lemma, but from `decodeSquare` (§13)
// plus a `coe`-transport-and-`predsucc` `hcomp` correction (agda's `decode (loop i)`
// shape). The whole chain `decodeSquare → decode → decodeEncode → windingEquiv` is
// COMPLETED in §13–§15; the tests in this section record the intermediate facts
// (the based `encode`, and that `intLoopSucc` is genuinely non-definitional — the
// reason the correction is needed at all).
// ══════════════════════════════════════════════════════════════════════════════

/// `encode := λ (y:S¹) (q:base=y). coe (λ i. helix (q@i)) i0 i1 (ofNat 0)`, the
/// BASED encode `(y:S¹) → (base = y) → helix y`. Under `λy λq` then the coe line
/// `λi`: `i = BVar 0`, `q = BVar 1`, `y = BVar 2`.
fn encode_based_value() -> Expr {
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(bvar(1)), // q
        arg: Arc::new(bvar(0)),  // i
    });
    let line = lam(interval(), helix_applied_myz(major));
    let coe = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(z0()),
    });
    // λ (y:S¹). λ (q : Path (λ_.S¹) base y). coe …
    lam(s1(), lam(path(const_line(s1()), s1_base(), bvar(0)), coe))
}

/// `encode : (y:S¹) → Path (λ_.S¹) base y → helix y`.  (`helix y`, with `y = BVar 1`
/// under `λy` then the `q`-Pi.)
fn encode_based_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        s1(),
        Expr::pi(
            BinderInfo::Default,
            path(const_line(s1()), s1_base(), bvar(0)),
            helix_applied_myz(bvar(1)),
        ),
    )
}

/// The BASED encode is a genuine total dependent function `(y:S¹) → (base=y) →
/// helix y` — the easy half of the based round-trip maps the `decodeEncode` `J`
/// needs. Its typing relies on the same neutral-path-endpoint reduction through
/// the `helix` recursor that makes `winding` total (`helix (q@i0) ↝ helix base ↝
/// MyZ`), here with the *left* endpoint `base` concrete and the right endpoint `y`
/// abstract.
#[test]
fn test_based_encode_is_a_total_dependent_function() {
    let env = int_env_with_winding_clean();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (ty, _) = tc
        .infer_type_with_cert(&encode_based_value())
        .expect("based encode should type-check");
    assert!(
        tc.is_def_eq(&ty, &encode_based_ty()),
        "encode : (y:S¹) → Path (λ_.S¹) base y → helix y; got {ty:?}"
    );
    // encode base ≡ winding (on the homogeneous loop space): encode base (refl base)
    // reduces to ofNat 0 (= winding (refl base)).
    let enc_base_refl = Expr::apps(encode_based_value(), [s1_base(), path_refl(&s1_base())]);
    assert!(
        tc.is_def_eq(&tc.whnf(&enc_base_refl), &z0()),
        "encode base (refl base) must reduce to ofNat 0"
    );
}

/// WHY `decode`'s loop minor needs an `hcomp` correction (not a bare `intLoopSucc`).
/// The naive function-PathP characterisation would want `intLoop (succ z) =
/// intLoop z ∙ loop` for all `z` (`intLoopSucc`). This test shows that lemma is
/// **not definitional** — at the negSucc boundary it is the groupoid left-inverse
/// `refl base = loop⁻¹ ∙ loop`, which the kernel leaves as a non-trivial
/// (un-equal-by-computation) Path. That is exactly why `decode` (§14) instead
/// `coe`-transports the abstract fibre element back to `MyZ` and repairs the
/// endpoint with the PROVED `predsucc` path inside an `hcomp` — see
/// `decode_loop_minor`. (decode/decodeEncode/windingEquiv are now BUILT, §13–§15.)
#[test]
fn test_decode_loop_minor_blocker_intloopsucc_is_not_definitional() {
    let env = int_env_with_winding_clean();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // The forward cases ARE definitional: intLoop(succ(ofNat k)) ≡ intLoop(ofNat k) ∙ loop.
    // (ofNat(succ k) reduces, and intLoop(ofNat(succ k)) = intLoop(ofNat k) ∙ loop.)
    // The OBSTRUCTION is the negSucc-zero boundary:
    //   intLoop (succ (negSucc 0)) = intLoop (ofNat 0)        ≡ refl base
    //   intLoop (negSucc 0) ∙ loop = loop⁻¹ ∙ loop
    let lhs = Expr::app(cst("intLoop"), z_succ(negsucc(mn_zero()))); // intLoop (ofNat 0) ≡ refl base
    let loop_inv = path_sym_neg(&s1_loop());
    let rhs = path_compose(&s1(), lvl1(), &loop_inv, &s1_loop()); // loop⁻¹ ∙ loop
    assert!(
        !tc.is_def_eq(&lhs, &rhs),
        "intLoopSucc at negSucc 0 (refl base ≡ loop⁻¹ ∙ loop) must NOT be definitional — \
         it is the groupoid left-inverse law, the genuine coherence `decode`'s loop \
         minor needs and the kernel does not compute"
    );
    // Sanity: both have the same endpoints (base/base), so they are PROPOSITIONALLY
    // (not definitionally) equal — confirming the gap is a real coherence, not a typo.
    let lhs_ty = tc.whnf(&tc.infer_type(&lhs).expect("intLoop(ofNat 0) types"));
    let rhs_ty = tc.whnf(&tc.infer_type(&rhs).expect("loop⁻¹ ∙ loop types"));
    let (
        ExprKind::CubicalPath {
            left: ll,
            right: lr,
            ..
        },
        ExprKind::CubicalPath {
            left: rl,
            right: rr,
            ..
        },
    ) = (lhs_ty.kind(), rhs_ty.kind())
    else {
        panic!("both sides must be Path S¹ types");
    };
    assert!(
        tc.is_def_eq(ll, rl) && tc.is_def_eq(lr, rr),
        "both intLoopSucc sides are loops base→base (same endpoints), so the gap is a \
         genuine propositional coherence"
    );
}

/// `windingEquiv` ASSEMBLY CHECK (the partial-application step): `Equiv.mk (Ω S¹)
/// MyZ winding intLoop` expects its next argument (the η homotopy `decodeEncode`)
/// to have EXACTLY the type `(x:Ω S¹) → Path (λ_.Ω S¹) (intLoop (winding x)) x`,
/// and the final argument (the ε homotopy) to be `encodeDecode`. The full assembly
/// `Equiv.mk (Ω S¹) MyZ winding intLoop decodeEncode encodeDecode : Equiv (Ω S¹)
/// MyZ` is now PROVED with a real `decodeEncode` in
/// `test_windingequiv_typechecks_full_pi1_milestone` (§15); this test pins the
/// intermediate fact that the η slot's expected type is exactly `decodeEncode`'s.
#[test]
fn test_windingequiv_assembly_pins_decodeencode_as_the_only_gap() {
    let env = int_env_with_encode_decode();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Equiv.mk.{1} (Ω S¹) MyZ winding intLoop : (η : …) → (ε : …) → Equiv (Ω S¹) MyZ.
    let partial = Expr::apps(
        Expr::const_(nm("Equiv.mk"), vec![type_level()]),
        [omega_s1(), myz(), cst("winding"), cst("intLoop")],
    );
    let (partial_ty, _) = tc
        .infer_type_with_cert(&partial)
        .expect("Equiv.mk (Ω S¹) MyZ winding intLoop should type-check");
    // partial_ty = (η : ETA) → (ε : EPS) → Equiv (Ω S¹) MyZ. Read off ETA.
    let partial_ty_whnf = tc.whnf(&partial_ty);
    let ExprKind::Pi(_, eta_dom, _) = partial_ty_whnf.kind() else {
        panic!("Equiv.mk … winding intLoop must expect the η homotopy next; got {partial_ty:?}");
    };
    // The expected η type is the η of Equiv.mk: (x:Ω S¹) → Path (λ_.Ω S¹) (intLoop (winding x)) x.
    let expected_eta = Expr::pi(
        BinderInfo::Default,
        omega_s1(),
        path(
            const_line(omega_s1()),
            Expr::app(cst("intLoop"), Expr::app(cst("winding"), bvar(0))),
            bvar(0),
        ),
    );
    assert!(
        tc.is_def_eq(eta_dom, &expected_eta),
        "the next Equiv.mk argument (η = decodeEncode) must be \
         (x:Ω S¹) → Path (λ_.Ω S¹) (intLoop (winding x)) x; got {eta_dom:?}"
    );

    // ε = encodeDecode closes the second homotopy; the η field is the real
    // `decodeEncode` proof built in §15 (this test only reads off the η slot type).
}

// ══════════════════════════════════════════════════════════════════════════════
// 12 — Groupoid coherences: the PROVED left-inverse law `lCancel`, the right-unit
//      law `rUnit`, and the crux cases of `intLoopSucc`.
//
// NOTE: bidirectional `coe`-over-Glue computes in both orientations — the backward
// `coe (helix-Glue-line) i1 i0` reduces to `pred` (see
// `test_backward_coe_over_glue_computes_to_pred`). These groupoid laws are genuine
// PROVED coherences; the final `decode` (§14) does NOT route through the full
// `intLoopSucc`/`assoc` family (it uses `decodeSquare` + a `coe`-transport +
// `predsucc` `hcomp` correction instead), so this section now stands as a library
// of proved groupoid laws rather than a list of blockers.
//
// Two SOUND kernel completeness fixes enable these raw-term cubical coherences:
//   (1) `validate_hcomp_system` now checks overlapping tube heads on the *overlap
//       face* (the CCHM adjacency condition) rather than globally — multi-face Kan
//       compositions (which need a collapse face overlapping the path boundary)
//       previously could not even be typed.
//   (2) `hcomp` definitional equality is now Kan-aware: it drops ⊥-faced branches
//       and matches tubes up to *on-face* agreement (a tube is a `Partial φ A`, so
//       its off-face values are immaterial). A collapse-square slice
//       `hcomp [(k=0),(k=1),(i0=1)↦…]` is therefore def-eq to the 2-branch
//       `path_compose` it restricts to — the structural comparison could not see
//       this. Both fixes only ever *accept more*; the soundness guards below pin
//       that genuinely-incoherent systems / genuinely-distinct composites are
//       still rejected.
// ══════════════════════════════════════════════════════════════════════════════

/// Interval connectives / cofibration constructors as `Expr`s.
fn i_neg(x: Expr) -> Expr {
    Expr::app(Expr::const_(nm("I.neg"), vec![]), x)
}
fn i_min(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(nm("I.min"), vec![]), [x, y])
}
fn i_max(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(nm("I.max"), vec![]), [x, y])
}
fn cof_eq0(x: Expr) -> Expr {
    Expr::app(Expr::const_(nm("Cofib.eq0"), vec![]), x)
}
fn cof_eq1(x: Expr) -> Expr {
    Expr::app(Expr::const_(nm("Cofib.eq1"), vec![]), x)
}
fn cof_or(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(nm("Cofib.or"), vec![]), [x, y])
}
fn cpapp(p: Expr, a: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(p),
        arg: Arc::new(a),
    })
}
fn cplam(b: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathLam { body: Arc::new(b) })
}
fn sys_nil_s1() -> Expr {
    Expr::app(Expr::const_(nm("System.nil"), vec![lvl1()]), s1())
}
fn sys_cons_s1(face: Expr, head: Expr, tail: Expr) -> Expr {
    Expr::apps(
        Expr::const_(nm("System.cons"), vec![lvl1()]),
        [s1(), face, head, tail],
    )
}

/// `lCancel loop : Path (λ_.Ω S¹) (sym_neg loop ∙ loop) (refl base)` — the
/// left-inverse groupoid law, built as the agda `rCancel`-of-`sym_neg loop`
/// square matched to `path_compose`'s tube convention. Under `<i><k>`:
/// `i=BVar1`, `k=BVar0`; inside a tube head `λl`: `l=BVar0`, `k=BVar1`, `i=BVar2`.
/// The system is `hcomp^l [(k=0)↦λl.base, (k=1)↦λl. (sym_neg loop)(~l ∧ ~i),
/// (i=1)↦λl.base] ((sym_neg loop)(k ∧ ~i))`: at `i=0` it restricts to exactly
/// `path_compose (sym_neg loop) loop`; at `i=1` the `(i=1)` face collapses it to
/// `base`; the `(k=1)`/`(i=1)` tubes agree on their overlap because
/// `(sym_neg loop)(~l ∧ ~i)|_{i=1} = (sym_neg loop)(i0) = base`.
fn lcancel_value() -> Expr {
    let p = || path_sym_neg(&s1_loop());
    let phi = cof_or(cof_eq0(bvar(0)), cof_or(cof_eq1(bvar(0)), cof_eq1(bvar(1))));
    let head_k0 = lam(interval(), s1_base());
    let head_k1 = lam(
        interval(),
        cpapp(p(), i_min(i_neg(bvar(0)), i_neg(bvar(2)))),
    );
    let head_i1 = lam(interval(), s1_base());
    let system = sys_cons_s1(
        cof_eq0(bvar(0)),
        head_k0,
        sys_cons_s1(
            cof_eq1(bvar(0)),
            head_k1,
            sys_cons_s1(cof_eq1(bvar(1)), head_i1, sys_nil_s1()),
        ),
    );
    let floor = cpapp(p(), i_min(bvar(0), i_neg(bvar(1))));
    cplam(cplam(Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(floor),
    })))
}

/// `lCancel`'s stated type: `Path (λ_.Ω S¹) (sym_neg loop ∙ loop) (refl base)`.
fn lcancel_ty() -> Expr {
    let comp = path_compose(&s1(), lvl1(), &path_sym_neg(&s1_loop()), &s1_loop());
    path(const_line(omega_s1()), comp, path_refl(&s1_base()))
}

/// `rUnit loop : Path (λ_.Ω S¹) loop (loop ∙ refl)` — the right-unit law, built
/// as the `compPath`-filler square. `R(i,k) = hcomp^l [(k=0)↦λl.loop@k,
/// (k=1)↦λl.base, (i=0)↦λl.loop@k] (loop@k)`: at `i=0` the `(i=0)` face collapses
/// to `loop@k` (`= loop`); at `i=1` the surviving `(k=0),(k=1)` faces are exactly
/// `path_compose loop refl`.
fn runit_value() -> Expr {
    let phi = cof_or(cof_eq0(bvar(0)), cof_or(cof_eq1(bvar(0)), cof_eq0(bvar(1))));
    let head_k0 = lam(interval(), cpapp(s1_loop(), bvar(1)));
    let head_k1 = lam(interval(), s1_base());
    let head_i0 = lam(interval(), cpapp(s1_loop(), bvar(1)));
    let system = sys_cons_s1(
        cof_eq0(bvar(0)),
        head_k0,
        sys_cons_s1(
            cof_eq1(bvar(0)),
            head_k1,
            sys_cons_s1(cof_eq0(bvar(1)), head_i0, sys_nil_s1()),
        ),
    );
    let floor = cpapp(s1_loop(), bvar(0));
    cplam(cplam(Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(floor),
    })))
}

fn runit_ty() -> Expr {
    let comp = path_compose(&s1(), lvl1(), &s1_loop(), &path_refl(&s1_base()));
    path(const_line(omega_s1()), s1_loop(), comp)
}

/// `int_env_with_s1()` plus the PROVED `lcancel` and `rUnit` groupoid laws.
fn int_env_with_groupoid_laws() -> Environment {
    let mut env = int_env_with_s1();
    env.add_decl(Declaration::Definition {
        name: nm("lcancel"),
        level_params: vec![],
        type_: lcancel_ty(),
        value: lcancel_value(),
        is_reducible: false,
    })
    .expect("lcancel (left-inverse law) proof term should type-check");
    env.add_decl(Declaration::Definition {
        name: nm("rUnit"),
        level_params: vec![],
        type_: runit_ty(),
        value: runit_value(),
        is_reducible: false,
    })
    .expect("rUnit (right-unit law) proof term should type-check");
    env
}

/// FIX (1) — the `hcomp` overlap-agreement check is **face-restricted** (CCHM
/// adjacency), so a multi-face composition whose tubes agree only on their
/// overlap type-checks; and the SOUNDNESS GUARD: a genuinely-incoherent overlap
/// (tubes disagreeing on the overlap face) is still rejected.
#[test]
fn test_hcomp_overlap_agreement_is_face_restricted() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // COHERENT: faces (k=0),(k=1),(i=1) with heads base, loop@(~k), base. The
    // (k=1)/(i=1) tubes agree on overlap (loop@(~1)=base). Wrap in <i><k> so i,k
    // are FVars at validate time (the real path-lam case).
    let phi = cof_or(cof_eq0(bvar(0)), cof_or(cof_eq1(bvar(0)), cof_eq1(bvar(1))));
    let sys_ok = sys_cons_s1(
        cof_eq0(bvar(0)),
        lam(interval(), s1_base()),
        sys_cons_s1(
            cof_eq1(bvar(0)),
            lam(interval(), cpapp(s1_loop(), i_neg(bvar(1)))),
            sys_cons_s1(cof_eq1(bvar(1)), lam(interval(), s1_base()), sys_nil_s1()),
        ),
    );
    let ok = cplam(cplam(Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(phi.clone()),
        u: Arc::new(sys_ok),
        base: Arc::new(cpapp(s1_loop(), i_neg(bvar(0)))),
    })));
    // SOUNDNESS (cap/floor-agreement, now enforced): this system is OVERLAP-coherent
    // but NOT cap-coherent — on the face (i=1) the `(i=1)↦λl.base` tube caps onto
    // `base`, while the floor is `loop@(~k)` (≢ base for free k). It type-checked only
    // because the cap check was missing; it is genuinely ill-formed and is now
    // correctly REJECTED. (The overlap-agreement property this test targets is still
    // exercised by the INCOHERENT case below.)
    assert!(
        tc.infer_type(&ok).is_err(),
        "a system whose (i=1) tube does not cap onto the floor must be REJECTED \
         (cap/floor-agreement)"
    );

    // INCOHERENT (soundness guard): (k=1)↦λl.loop@l does NOT agree with (i=1)↦λl.base
    // on the overlap (k=1,i=1) — loop@l is not base for free l. Must be REJECTED.
    let sys_bad = sys_cons_s1(
        cof_eq0(bvar(0)),
        lam(interval(), s1_base()),
        sys_cons_s1(
            cof_eq1(bvar(0)),
            lam(interval(), cpapp(s1_loop(), bvar(0))), // λl. loop@l
            sys_cons_s1(cof_eq1(bvar(1)), lam(interval(), s1_base()), sys_nil_s1()),
        ),
    );
    let bad = cplam(cplam(Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(phi),
        u: Arc::new(sys_bad),
        base: Arc::new(s1_base()),
    })));
    assert!(
        tc.infer_type(&bad).is_err(),
        "an incoherent overlap (tubes disagree on the overlap face) must be REJECTED"
    );
}

/// FIX (2) — `hcomp` definitional equality is Kan-aware: a 3-branch collapse-square
/// slice (with a ⊥-faced branch at `i:=i0`) is def-eq to the 2-branch
/// `path_compose` it restricts to; and the SOUNDNESS GUARD: two genuinely-distinct
/// composites are still NOT def-eq.
#[test]
fn test_hcomp_def_eq_is_kan_aware_up_to_bot_branches() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let q = s1_loop();
    let c = path_compose(&s1(), lvl1(), &path_sym_neg(&q), &q);
    // Same hcomp with an extra (CubicalI0=1 ⇒ ⊥) branch λl.base.
    // Under <k>: k=BVar0; tube λl: l=BVar0, k=BVar1.
    let phi = cof_or(cof_eq0(bvar(0)), cof_or(cof_eq1(bvar(0)), cof_eq1(i0())));
    let sys = sys_cons_s1(
        cof_eq0(bvar(0)),
        lam(interval(), cpapp(q.clone(), i_neg(bvar(1)))),
        sys_cons_s1(
            cof_eq1(bvar(0)),
            lam(interval(), cpapp(q.clone(), bvar(0))),
            sys_cons_s1(cof_eq1(i0()), lam(interval(), s1_base()), sys_nil_s1()),
        ),
    );
    let h3 = cplam(Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(phi),
        u: Arc::new(sys),
        base: Arc::new(cpapp(q.clone(), i_neg(bvar(0)))),
    }));
    assert!(
        tc.is_def_eq(&c, &h3),
        "path_compose must be def-eq to itself plus a ⊥-faced branch (Kan-aware hcomp def-eq)"
    );

    // SOUNDNESS GUARD: path_compose(loop,loop) ≢ path_compose(loop,refl) — genuinely
    // different (k=1) tubes (loop@l vs base), not merely off-face.
    let c1 = path_compose(&s1(), lvl1(), &q, &q);
    let c2 = path_compose(&s1(), lvl1(), &q, &path_refl(&s1_base()));
    assert!(
        !tc.is_def_eq(&c1, &c2),
        "genuinely-distinct composites must NOT be def-eq"
    );
}

/// THE CRUX: `lCancel loop : sym_neg loop ∙ loop = refl base` is a PROVED proof
/// term (registration type-checks it; no axioms), and it is a *genuine*
/// (propositional, not definitional) coherence.
#[test]
fn test_lcancel_left_inverse_law_is_proved() {
    let env = int_env_with_groupoid_laws();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (ty, _) = tc
        .infer_type_with_cert(&cst("lcancel"))
        .expect("lcancel should type-check");
    assert!(
        tc.is_def_eq(&ty, &lcancel_ty()),
        "lcancel : Path (λ_.Ω S¹) (sym_neg loop ∙ loop) (refl base); got {ty:?}"
    );

    // NON-VACUITY: the left-inverse is a real coherence — `sym_neg loop ∙ loop` is
    // NOT definitionally `refl base` (the hcomp does not collapse on its own).
    let comp = path_compose(&s1(), lvl1(), &path_sym_neg(&s1_loop()), &s1_loop());
    assert!(
        !tc.is_def_eq(&comp, &path_refl(&s1_base())),
        "sym_neg loop ∙ loop ≡ refl base definitionally — lCancel would be vacuous"
    );
}

/// `rUnit loop : loop = loop ∙ refl` is a PROVED proof term (registration
/// type-checks it; no axioms), and a genuine coherence.
#[test]
fn test_runit_right_unit_law_is_proved() {
    let env = int_env_with_groupoid_laws();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (ty, _) = tc
        .infer_type_with_cert(&cst("rUnit"))
        .expect("rUnit should type-check");
    assert!(
        tc.is_def_eq(&ty, &runit_ty()),
        "rUnit : Path (λ_.Ω S¹) loop (loop ∙ refl); got {ty:?}"
    );
    let comp = path_compose(&s1(), lvl1(), &s1_loop(), &path_refl(&s1_base()));
    assert!(
        !tc.is_def_eq(&s1_loop(), &comp),
        "loop ≡ loop ∙ refl definitionally — rUnit would be vacuous"
    );
}

/// `intLoopSucc`'s crux cases are PROVED (the negSucc-0 case is exactly `lCancel`):
/// * the `ofNat 0` case holds **definitionally**: `intLoop (succ (ofNat 0)) ≡
///   refl ∙ loop`, with `refl ≡ intLoop (ofNat 0)`; and
/// * the `negSucc 0` case is `sym_neg lcancel`, inhabiting `Path (intLoop (succ
///   (negSucc 0)) ≡ refl base) (sym_neg loop ∙ loop)`, with `sym_neg loop ≡
///   intLoop (negSucc 0)` — i.e. the `intLoopSucc` round-trip `intLoop (succ z) =
///   intLoop z ∙ loop` at `z = negSucc 0`.
///
/// Endpoints are stated with the **reduced** `intLoop` values (`refl`, `sym_neg
/// loop`) because `path_compose` is not def-eq-congruent in its argument (a
/// pre-existing convertibility incompleteness: `p ≡ p'` does not give
/// `p ∙ q ≡ p' ∙ q` when `p` is an unreduced recursor-redex), so the literal
/// `intLoop (negSucc 0) ∙ loop` form would need an extra `ap` coherence.
///
/// The full single lemma `intLoopSucc` (whose `negSucc (succ m)` case would need
/// `assoc`) is NOT assembled — and is not needed: `decode` (§14) avoids it via the
/// `decodeSquare` + `coe`-transport + `predsucc` correction route, so the full
/// `windingEquiv` milestone (§15) is reached without `assoc`/`intLoopSucc`.
#[test]
fn test_intloopsucc_crux_cases_proved() {
    let env = int_env_with_groupoid_laws();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // ofNat 0 case (definitional): intLoop (succ (ofNat 0)) ≡ refl ∙ loop, and
    // refl ≡ intLoop (ofNat 0).
    let lhs0 = Expr::app(cst("intLoop"), z_succ(ofnat(mn_zero())));
    let refl_loop = path_compose(&s1(), lvl1(), &path_refl(&s1_base()), &s1_loop());
    assert!(
        tc.is_def_eq(
            &Expr::app(cst("intLoop"), ofnat(mn_zero())),
            &path_refl(&s1_base())
        ),
        "intLoop (ofNat 0) ≡ refl base"
    );
    assert!(
        tc.is_def_eq(&lhs0, &refl_loop),
        "intLoop (succ (ofNat 0)) must be definitionally refl ∙ loop (= intLoop (ofNat 0) ∙ loop)"
    );

    // negSucc 0 case: sym_neg lcancel inhabits the round-trip type (reduced RHS).
    assert!(
        tc.is_def_eq(
            &Expr::app(cst("intLoop"), negsucc(mn_zero())),
            &path_sym_neg(&s1_loop())
        ),
        "intLoop (negSucc 0) ≡ sym_neg loop"
    );
    let witness = path_sym_neg(&cst("lcancel"));
    let stated = path(
        const_line(omega_s1()),
        Expr::app(cst("intLoop"), z_succ(negsucc(mn_zero()))),
        path_compose(&s1(), lvl1(), &path_sym_neg(&s1_loop()), &s1_loop()),
    );
    let (wty, _) = tc
        .infer_type_with_cert(&witness)
        .expect("sym_neg lcancel should type-check");
    assert!(
        tc.is_def_eq(&wty, &stated),
        "intLoopSucc (negSucc 0) = sym_neg lcancel : \
         Path (intLoop (succ (negSucc 0))) (sym_neg loop ∙ loop); got {wty:?}"
    );
}

/// BIDIRECTIONAL `coe`-over-Glue (Deliverable 1): the backward orientation now
/// COMPUTES. `decode : (y:S¹) → helix y → (base = y)` via `S1.rec` needs the loop
/// minor `Path (λ i. helix(loop@i) → (base=loop@i)) intLoop intLoop` — a
/// function-PathP out of the helix **Glue line** — whose endpoint checks need `coe`
/// over that Glue line applied to abstract elements in BOTH directions. The kernel's
/// `coe`-over-Glue rule is now symmetric: it fires on the **target-endpoint-total**
/// case in either orientation, `(i0→i1)` (the winding/`succ` direction) and
/// `(i1→i0)` (the `decode`/`pred` direction). Both degenerate to a single cell and
/// the CCHM correction `hcomp` is vacuous, so the reduct is the fiber-centre point
/// `Equiv.bwd (eₖ@s) (coe A-line r s (unglue@r base))` — sound and type-preserving.
/// A genuinely-residual Glue at the target (no `⊤` cell there) still stays stuck.
#[test]
fn test_backward_coe_over_glue_computes_to_pred() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let line = || {
        let major = Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(s1_loop()),
            arg: Arc::new(bvar(0)),
        });
        lam(interval(), helix_applied_myz(major))
    };
    // FORWARD coe i0→i1 (ofNat 0) ↝ succ ↝ ofNat 1 — still works (regression).
    let fwd = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line()),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(z0()),
    });
    assert!(
        tc.is_def_eq(&tc.whnf(&fwd), &z1()),
        "forward coe over the helix Glue line must compute (ofNat 0 ↦ ofNat 1)"
    );

    // BACKWARD coe i1→i0 (ofNat 1) ↝ pred ↝ ofNat 0 — the new direction `decode` needs.
    let bwd = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line()),
        r: Arc::new(i1()),
        s: Arc::new(i0()),
        base: Arc::new(z1()),
    });
    let bwd_r = tc.whnf(&bwd);
    assert!(
        tc.is_def_eq(&bwd_r, &z0()),
        "backward coe over the helix Glue line must compute pred (ofNat 1 ↦ ofNat 0); got {bwd_r:?}"
    );
    // It really landed on a constructor (`ofNat _`), not a stuck coe.
    assert!(
        matches!(bwd_r.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("MyZ.ofNat")),
        "backward coe must land in constructor form (ofNat _), not a stuck coe; got {bwd_r:?}"
    );
    // NON-VACUITY: pred (ofNat 1) = ofNat 0 is genuinely distinct from ofNat 1.
    assert!(
        !tc.is_def_eq(&bwd_r, &z1()),
        "ofNat 0 ≡ ofNat 1 — MyZ η-collapsed, the pred computation is VACUOUS"
    );

    // Type preservation: both redex and reduct infer to MyZ.
    let (bwd_ty, _) = tc
        .infer_type_with_cert(&bwd)
        .expect("backward coe over the helix Glue line should type-check");
    assert!(
        tc.is_def_eq(&bwd_ty, &myz()),
        "backward coe : MyZ; got {bwd_ty:?}"
    );

    // Iterating the pred-transport again: i1→i0 (ofNat 0) ↝ negSucc 0 (= -1).
    let bwd2 = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line()),
        r: Arc::new(i1()),
        s: Arc::new(i0()),
        base: Arc::new(z0()),
    });
    assert!(
        tc.is_def_eq(&tc.whnf(&bwd2), &negsucc(mn_zero())),
        "backward coe i1→i0 (ofNat 0) must compute to negSucc 0 (= pred 0 = -1)"
    );
}

/// PROBE — `decodeSquare`'s leaf case `ofNat 0` builds purely from interval
/// connections (no groupoid coherence): the connection square `<i><j> loop@(i ∨ ~j)`
/// type-checks as `PathP (λ i. base = loop@i) (intLoop (negSucc 0)) (intLoop (ofNat 0))`
/// = `PathP … (sym_neg loop) (refl base)`. This is the leaf of the full
/// `decodeSquare` (§13), whose recursive `ofNat (succ ·)` and `negSucc` cases are
/// `hfill` squares referencing `intLoop` directly (no `assoc`/`lCancel` needed).
#[test]
fn test_decode_square_ofnat_zero_leaf_builds() {
    let env = int_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // The PathP line `λ i. base = loop@i`.
    let pathp_line = lam(
        interval(),
        path(const_line(s1()), s1_base(), cpapp(s1_loop(), bvar(0))),
    );
    // decodeSquare(ofNat 0) := <i><j> loop@(i ∨ ~j).  Under <i><j>: i=BVar1, j=BVar0.
    let square = cplam(cplam(cpapp(s1_loop(), i_max(bvar(1), i_neg(bvar(0))))));
    // Its stated type: PathP (λ i. base=loop@i) (sym_neg loop) (refl base).
    let stated = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(pathp_line),
        left: Arc::new(path_sym_neg(&s1_loop())),
        right: Arc::new(path_refl(&s1_base())),
    });

    let inferred = tc
        .infer_type(&square)
        .expect("the ofNat-0 connection square should type-check");
    assert!(
        tc.is_def_eq(&inferred, &stated),
        "decodeSquare(ofNat 0) = <i><j> loop@(i∨~j) : PathP (λ i. base=loop@i) (sym_neg loop) (refl base); \
         got {inferred:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 13 — `decodeSquare`, `decode`, `decodeEncode` — the FULL `windingEquiv` milestone
//
// Following agda/cubical `Cubical/HITs/S1/Base.agda`:
//   decodeSquare : (n:ℤ) → PathP (λ i. base ≡ loop i) (intLoop (predℤ n)) (intLoop n)
//   decodeSquare (pos zero)    i j = loop (i ∨ ~ j)
//   decodeSquare (pos (suc n)) i j = hfill [(j=i0)↦base,(j=i1)↦loop k] (intLoop (pos n) j) i
//   decodeSquare (negsuc n)    i j = hfill [(j=i0)↦base,(j=i1)↦loop(~k)] (intLoop (negsuc n) j) (~i)
// Unfolding `hfill u u0 r = hcomp^k [ u(r∧k) , (r=i0)↦u0 ] u0`, each recursive case
// becomes a 3-face `hcomp` over `S¹`. The `negsuc` case is UNIFORM in `n` (no inner
// recursion, references `intLoop (negsuc n)` directly), so — exactly as in agda — it
// needs NO `assoc`/`lCancel`; only the `ofNat (succ ·)` case splits via `MyNat.rec`.
// ══════════════════════════════════════════════════════════════════════════════

/// The PathP line `λ i. base = loop@i` (the decodeSquare / decode-minor line).
fn base_eq_loop_line() -> Expr {
    lam(
        interval(),
        path(const_line(s1()), s1_base(), cpapp(s1_loop(), bvar(0))),
    )
}

/// `PathP (λ i. base = loop@i) (intLoop (pred n)) (intLoop n)` — the stated
/// `decodeSquare n` type for a `MyZ` expression `n`.
fn decode_square_ty_at(n: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(base_eq_loop_line()),
        left: Arc::new(intloop_n(z_pred(n.clone()))),
        right: Arc::new(intloop_n(n)),
    })
}

/// `decodeSquare : (n:MyZ) → PathP (λ i. base = loop@i) (intLoop (pred n)) (intLoop n)`.
fn decode_square_decl_ty() -> Expr {
    Expr::pi(BinderInfo::Default, myz(), decode_square_ty_at(bvar(0)))
}

/// PROOF TERM of `decodeSquare`, by `MyZ.rec` / `MyNat.rec`.
fn decode_square_value() -> Expr {
    // motive : λ n. PathP (λi.base=loop@i) (intLoop (pred n)) (intLoop n)
    let motive = lam(myz(), decode_square_ty_at(bvar(0)));

    // ── ofNat case: λ m. MyNat.rec C_of base_of step_of m ──
    let cof = {
        // C_of : λ m'. PathP … (intLoop (pred (ofNat m'))) (intLoop (ofNat m'))
        let c_of = lam(mynat(), decode_square_ty_at(ofnat(bvar(0))));
        // base_of (m'=0): <i><j> loop@(i ∨ ~j).  Under <i><j>: i=BVar1, j=BVar0.
        let base_of = cplam(cplam(cpapp(s1_loop(), i_max(bvar(1), i_neg(bvar(0))))));
        // ih_ty (k=BVar0 under λk): PathP at ofNat k (the step minor's IH; unused).
        let ih_ty = decode_square_ty_at(ofnat(bvar(0)));
        // step_of: λ k. λ ih. <i><j>
        //   hcomp^k' [ (i=i0)↦λk'. intLoop(ofNat k)@j,
        //              (j=i0)↦λk'. base,
        //              (j=i1)↦λk'. loop@(i ∧ k') ]
        //           (intLoop(ofNat k)@j)
        // At hcomp body level: j=BVar0, i=BVar1, ih=BVar2, k=BVar3.
        // Inside a tube `λk'`: k'=BVar0, j=BVar1, i=BVar2, ih=BVar3, k=BVar4.
        let step_of = {
            let floor = cpapp(intloop_n(ofnat(bvar(3))), bvar(0));
            let tube_i0 = lam(interval(), cpapp(intloop_n(ofnat(bvar(4))), bvar(1)));
            let tube_j0 = lam(interval(), s1_base());
            let tube_j1 = lam(interval(), cpapp(s1_loop(), i_min(bvar(2), bvar(0))));
            let phi = cof_or(cof_eq0(bvar(1)), cof_or(cof_eq0(bvar(0)), cof_eq1(bvar(0))));
            let system = sys_cons_s1(
                cof_eq0(bvar(1)),
                tube_i0,
                sys_cons_s1(
                    cof_eq0(bvar(0)),
                    tube_j0,
                    sys_cons_s1(cof_eq1(bvar(0)), tube_j1, sys_nil_s1()),
                ),
            );
            let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
                ty: Arc::new(s1()),
                phi: Arc::new(phi),
                u: Arc::new(system),
                base: Arc::new(floor),
            });
            lam(mynat(), lam(ih_ty, cplam(cplam(hcomp))))
        };
        lam(
            mynat(),
            Expr::apps(rec("MyNat"), [c_of, base_of, step_of, bvar(0)]),
        )
    };

    // ── negSucc case (uniform): λ m. <i><j>
    //   hcomp^k' [ (i=i1)↦λk'. intLoop(negSucc m)@j,
    //              (j=i0)↦λk'. base,
    //              (j=i1)↦λk'. loop@(i ∨ ~k') ]
    //           (intLoop(negSucc m)@j)
    // At hcomp body level: j=BVar0, i=BVar1, m=BVar2.
    // Inside a tube `λk'`: k'=BVar0, j=BVar1, i=BVar2, m=BVar3.
    let cneg = {
        let floor = cpapp(intloop_n(negsucc(bvar(2))), bvar(0));
        let tube_i1 = lam(interval(), cpapp(intloop_n(negsucc(bvar(3))), bvar(1)));
        let tube_j0 = lam(interval(), s1_base());
        let tube_j1 = lam(interval(), cpapp(s1_loop(), i_max(bvar(2), i_neg(bvar(0)))));
        let phi = cof_or(cof_eq1(bvar(1)), cof_or(cof_eq0(bvar(0)), cof_eq1(bvar(0))));
        let system = sys_cons_s1(
            cof_eq1(bvar(1)),
            tube_i1,
            sys_cons_s1(
                cof_eq0(bvar(0)),
                tube_j0,
                sys_cons_s1(cof_eq1(bvar(0)), tube_j1, sys_nil_s1()),
            ),
        );
        let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(s1()),
            phi: Arc::new(phi),
            u: Arc::new(system),
            base: Arc::new(floor),
        });
        lam(mynat(), cplam(cplam(hcomp)))
    };

    Expr::apps(rec("MyZ"), [motive, cof, cneg])
}

/// `int_env_with_s1()` plus the registered `decodeSquare`.
fn int_env_with_decode_square() -> Environment {
    let mut env = int_env_with_s1();
    env.add_decl(Declaration::Definition {
        name: nm("decodeSquare"),
        level_params: vec![],
        type_: decode_square_decl_ty(),
        value: decode_square_value(),
        is_reducible: false,
    })
    .expect("decodeSquare proof term should type-check (MyZ.rec / MyNat.rec hfill squares)");
    env
}

#[test]
fn test_decode_square_typechecks() {
    let env = int_env_with_decode_square();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (ds_ty, _) = tc
        .infer_type_with_cert(&cst("decodeSquare"))
        .expect("decodeSquare should type-check");
    assert!(
        tc.is_def_eq(&ds_ty, &decode_square_decl_ty()),
        "decodeSquare : (n:MyZ) → PathP (λ i. base=loop@i) (intLoop (pred n)) (intLoop n); got {ds_ty:?}"
    );

    // Instance on a concrete integer: decodeSquare (ofNat 1) : PathP _ (intLoop 0) (intLoop 1).
    let app = Expr::app(cst("decodeSquare"), z1());
    let (app_ty, _) = tc
        .infer_type_with_cert(&app)
        .expect("decodeSquare (ofNat 1) should type-check");
    let app_ty_whnf = tc.whnf(&app_ty);
    let ExprKind::CubicalPath { left, right, .. } = app_ty_whnf.kind() else {
        panic!("decodeSquare (ofNat 1) must infer to a PathP; got {app_ty:?}");
    };
    assert!(
        tc.is_def_eq(left, &intloop_n(z0())) && tc.is_def_eq(right, &intloop_n(z1())),
        "decodeSquare (ofNat 1) : PathP _ (intLoop 0) (intLoop 1); got {left:?} = {right:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 14 — `decode : (x:S¹) → helix x → (base = x)` via `S1.rec`
//
// agda: decode base = intLoop;  decode (loop i) y j = hcomp [...] (decodeSquare (unglue …) i j).
// The loop minor is the function-PathP `PathP (λ i. helix(loop@i) → base=loop@i) intLoop intLoop`.
// Its base is `decodeSquare (unglue (i∨~i) y) @ i @ j`; the hcomp correction fixes the
// i-endpoints (at i=i0 the unglue total-face gives `succ y`, so the base is
// `intLoop (pred (succ y))` — NOT definitionally `intLoop y` for abstract `y`; the
// `(i=i0)` correction tube `intLoop ((predsucc y)@k) @ j` interpolates it to `intLoop y`).
// ══════════════════════════════════════════════════════════════════════════════

/// `helix : S¹ → Type` as a registered (reducible) definition
/// `S1.rec.{2} (λ_:S¹. Type) MyZ (ua sucEquiv)`.
fn helix_value() -> Expr {
    let motive = lam(s1(), Expr::type_());
    let u2 = Level::succ(Level::succ(Level::zero()));
    let rec = Expr::const_(nm("S1.rec"), vec![u2]);
    let ua = glue_ua(&myz(), &myz(), &suc_equiv(), type_level());
    Expr::apps(rec, [motive, myz(), ua])
}
fn helix_n(arg: Expr) -> Expr {
    Expr::app(cst("helix"), arg)
}

/// The line of types `λ i. helix(loop@i) : I → Type` (the helix family read
/// along the loop). `coe` over it transports a fibre element back to `MyZ`.
fn helix_loop_line() -> Expr {
    lam(interval(), helix_n(cpapp(s1_loop(), bvar(0))))
}
/// `coe (λ i. helix(loop@i)) r s y` — transport `y : helix(loop@r)` to `helix(loop@s)`.
fn helix_coe(r: Expr, s: Expr, y: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(helix_loop_line()),
        r: Arc::new(r),
        s: Arc::new(s),
        base: Arc::new(y),
    })
}

/// `decode` motive `λ x:S¹. helix x → (base = x)`.
fn decode_motive() -> Expr {
    lam(
        s1(),
        Expr::pi(
            BinderInfo::Default,
            helix_n(bvar(0)),
            path(const_line(s1()), s1_base(), bvar(1)),
        ),
    )
}

/// `decode`'s S¹.rec **loop minor**: the function-PathP
/// `PathP (λ i. helix(loop@i) → base=loop@i) intLoop intLoop`.
///
/// The CAP-COHERENT (agda-faithful) construction. The crux is the floor's
/// helix-fibre projection `n`: it must be the **forward** transport
/// `coe^{i→i1} y` (the Glue-projection that is `succ y` at `i=i0` and `y` at
/// `i=i1`), so that the floor `decodeSquare n @ i @ j` restricts on the
/// `(i=i0)` face to `decodeSquare (succ y) @ i0 @ j = intLoop (pred (succ y)) @ j`
/// — EXACTLY the `i0`-cap of the `(i=i0)` correction tube
/// `λk. intLoop (predsucc y @ k) @ j` (whose `k=i0` end is `intLoop (pred (succ y)) @ j`).
/// Dually on `(i=i1)` the floor is `decodeSquare y @ i1 @ j = intLoop y @ j`, the
/// `i0`-cap of the constant `(i=i1)` tube. Both caps now agree with the floor on
/// their face, so the kernel's `validate_hcomp_cap` accepts it.
///
/// The previous (rejected) construction used the **backward** `coe^{i→i0} y`
/// (which is `y` at `i=i0`), making the floor `intLoop (pred y) @ j` on `(i=i0)`
/// while the cap was `intLoop (pred (succ y)) @ j` — and `pred (succ y) ≢ pred y`,
/// so the cap disagreed with the floor (the genuine CCHM well-formedness violation
/// that the cap check correctly rejects). See [`decode_loop_minor_incoherent`].
fn decode_loop_minor() -> Expr {
    decode_loop_minor_with(i1())
}

/// The OLD, cap-INCOHERENT loop minor (floor `n := coe^{i→i0} y`). Kept only to
/// drive the soundness regression [`test_decode_rejected_cap_incoherent_loop_minor`]:
/// its `(i=0)` wall caps onto `intLoop (pred (succ y))` while the floor restricts to
/// `intLoop (pred y)` — `pred (succ y) ≢ pred y` — so `validate_hcomp_cap` rejects it.
fn decode_loop_minor_incoherent() -> Expr {
    decode_loop_minor_with(i0())
}

/// Shared builder for `decode`'s loop minor, parameterised by the floor's
/// helix-fibre projection endpoint `s` (the target of `coe^{i→s} y`): `i1` gives the
/// agda-faithful CAP-COHERENT square, `i0` the old cap-incoherent one. Everything
/// else (the four correction tubes, the cofibration, the recursor wiring) is
/// identical — only the floor's `n` differs, which is precisely what determines
/// cap-coherence.
fn decode_loop_minor_with(n_target: Expr) -> Expr {
    // <i>. λ(y:helix(loop@i)). <j>. hcomp^k [...] (decodeSquare (coe i→n_target y) @ i @ j)
    // HCOMP-level De Bruijn: j=BVar0, y=BVar1, i=BVar2.
    // tube-level (under `λk`): k=BVar0, j=BVar1, y=BVar2, i=BVar3.
    // base value n := coe (λi'.helix(loop@i')) i n_target y : MyZ.
    let n = helix_coe(bvar(2), n_target, bvar(1));
    let base = cpapp(cpapp(Expr::app(cst("decodeSquare"), n), bvar(2)), bvar(0));

    // (i=i0) correction: interpolate intLoop(pred(coe i i0 y)) → intLoop(coe i i0 y)
    // via `predsucc`. At i=i0, coe i0 i0 y ≡ y, so this is intLoop((predsucc y)@k)@j.
    let y0 = helix_coe(bvar(3), i0(), bvar(2)); // coe i→i0 y, tube-level i=BVar3, y=BVar2
    let tube_i0 = lam(
        interval(),
        cpapp(
            intloop_n(cpapp(Expr::app(cst("predsucc"), y0), bvar(0))),
            bvar(1),
        ),
    );
    // (i=i1) correction: intLoop(coe i i1 y)@j. At i=i1, coe i1 i1 y ≡ y.
    let y1 = helix_coe(bvar(3), i1(), bvar(2)); // coe i→i1 y
    let tube_i1 = lam(interval(), cpapp(intloop_n(y1), bvar(1)));
    let tube_j0 = lam(interval(), s1_base());
    let tube_j1 = lam(interval(), cpapp(s1_loop(), bvar(3)));

    let phi = cof_or(
        cof_eq0(bvar(2)),
        cof_or(cof_eq1(bvar(2)), cof_or(cof_eq0(bvar(0)), cof_eq1(bvar(0)))),
    );
    let system = sys_cons_s1(
        cof_eq0(bvar(2)),
        tube_i0,
        sys_cons_s1(
            cof_eq1(bvar(2)),
            tube_i1,
            sys_cons_s1(
                cof_eq0(bvar(0)),
                tube_j0,
                sys_cons_s1(cof_eq1(bvar(0)), tube_j1, sys_nil_s1()),
            ),
        ),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(phi),
        u: Arc::new(system),
        base: Arc::new(base),
    });
    // λy domain `helix(loop@i)` sits under `<i>` only, so i=BVar0 there.
    let y_dom = helix_n(cpapp(s1_loop(), bvar(0)));
    cplam(lam(y_dom, cplam(hcomp)))
}

/// `decode := S1.rec.{1} decode_motive intLoop minor`.
fn decode_value_with(minor: Expr) -> Expr {
    Expr::apps(
        Expr::const_(nm("S1.rec"), vec![lvl1()]),
        [decode_motive(), cst("intLoop"), minor],
    )
}
/// `decode` with the CAP-COHERENT loop minor (the genuine, accepted proof term).
fn decode_value() -> Expr {
    decode_value_with(decode_loop_minor())
}
/// `decode` with the OLD cap-INCOHERENT loop minor (rejected by the cap check).
fn decode_value_incoherent() -> Expr {
    decode_value_with(decode_loop_minor_incoherent())
}

/// `decode : (x:S¹) → helix x → (base = x)`.
fn decode_decl_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        s1(),
        Expr::pi(
            BinderInfo::Default,
            helix_n(bvar(0)),
            path(const_line(s1()), s1_base(), bvar(1)),
        ),
    )
}

/// `int_env_with_decode_square()` plus `helix` and `decode`.
fn int_env_with_decode() -> Environment {
    let mut env = int_env_with_decode_square();
    env.add_decl(Declaration::Definition {
        name: nm("helix"),
        level_params: vec![],
        type_: Expr::arrow(s1(), Expr::type_()),
        value: helix_value(),
        is_reducible: true,
    })
    .expect("helix : S¹ → Type should type-check and register");
    env.add_decl(Declaration::Definition {
        name: nm("decode"),
        level_params: vec![],
        type_: decode_decl_ty(),
        value: decode_value(),
        is_reducible: false,
    })
    .expect("decode proof term should type-check (S1.rec with the decodeSquare loop minor)");
    env
}

/// SOUNDNESS regression helper: registering the OLD, cap-INCOHERENT `decode`
/// (built from [`decode_value_incoherent`] / [`decode_loop_minor_incoherent`])
/// must FAIL the hcomp cap/floor-agreement check (`validate_hcomp_cap`). That
/// `decode`'s S¹.rec **loop minor** builds a square whose **(i=0) wall** caps (at
/// the hcomp `i0` end) onto `intLoop(pred(succ y))`, while — because its floor's
/// projection is the BACKWARD `coe^{i→i0} y` (which is `y` at `i=i0`) — the floor
/// restricts to `decodeSquare y @ i0 = intLoop(pred y)`. Since `pred(succ y) ≢ pred y`,
/// the tube does NOT cap onto the floor on the face `(i=0)` — a genuine CCHM
/// well-formedness violation. It type-checked ONLY because the cap check was missing
/// (the reported soundness hole, now closed). The cap-COHERENT [`decode_value`]
/// (forward `coe^{i→i1} y`) is registered and accepted by [`int_env_with_decode`].
fn assert_incoherent_decode_rejected_by_cap_check() {
    let mut env = int_env_with_decode_square();
    env.add_decl(Declaration::Definition {
        name: nm("helix"),
        level_params: vec![],
        type_: Expr::arrow(s1(), Expr::type_()),
        value: helix_value(),
        is_reducible: true,
    })
    .expect("helix : S¹ → Type should still type-check and register");
    let err = env
        .add_decl(Declaration::Definition {
            name: nm("decode"),
            level_params: vec![],
            type_: decode_decl_ty(),
            value: decode_value_incoherent(),
            is_reducible: false,
        })
        .expect_err(
            "the INCOHERENT decode must be REJECTED: its loop-minor hcomp is cap-incoherent \
             (i=0 wall caps onto intLoop(pred(succ y)) ≠ floor intLoop(pred y))",
        );
    assert!(
        matches!(err, crate::env::EnvError::TypeCheckFailed { .. }),
        "incoherent decode rejection must be a type-check failure (cap/floor-agreement); got {err:?}"
    );
}

/// SOUNDNESS regression: the OLD (backward-`coe`) `decode` loop minor is correctly
/// REJECTED by the cap/floor-agreement check — it relied on the now-closed hole.
/// (The cap-COHERENT `decode` is exercised by [`test_decode_typechecks_cap_coherent`].)
#[test]
fn test_decode_rejected_cap_incoherent_loop_minor() {
    assert_incoherent_decode_rejected_by_cap_check();
}

/// THE GENUINE MILESTONE (loop-minor half): the cap-COHERENT `decode` type-checks
/// under the now-enforced `validate_hcomp_cap`. `decode := S1.rec intLoop minor`
/// with the agda-faithful loop minor (forward `coe^{i→i1} y` floor projection): on
/// `(i=i0)` the floor restricts to `intLoop(pred(succ y))`, exactly the `i0`-cap of
/// the `predsucc` correction tube. Since the cap check is enforced, a passing
/// `infer_type` here means the square is genuinely cap-coherent (no hole to exploit).
#[test]
fn test_decode_typechecks_cap_coherent() {
    let env = int_env_with_decode();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (d_ty, _) = tc
        .infer_type_with_cert(&cst("decode"))
        .expect("the cap-coherent decode should type-check (cap check enforced)");
    assert!(
        tc.is_def_eq(&d_ty, &decode_decl_ty()),
        "decode : (x:S¹) → helix x → (base = x); got {d_ty:?}"
    );

    // decode base ≡ intLoop (the base minor): decode base (ofNat 1) ↝ intLoop (ofNat 1).
    let db1 = Expr::apps(cst("decode"), [s1_base(), z1()]);
    assert!(
        tc.is_def_eq(&db1, &intloop_n(z1())),
        "decode base (ofNat 1) must reduce to intLoop (ofNat 1)"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 15 — `decodeEncode` (the η field) via based path-induction, and `windingEquiv`
//
// agda: decodeEncode x p = J (λ y q → decode y (encode y q) ≡ q) (λ _ → refl) p;
//       Iso.ret = decodeEncode base. Here, directly at `a = y = base`:
//   decodeEncode := λ p. coe^{i0→i1} (λ i. P (p@i) (<j> p@(i∧j))) d
//     P := λ (y:S¹) (q:base=y). Path (λ_. base=y) (decode y (encode y q)) q
//     d := <_> refl base : P base (refl base)
//          (decode base (encode base (refl base)) ≡ intLoop (ofNat 0) ≡ refl base)
//   ⇒ result type P base p = Path (λ_.Ω S¹) (decode base (encode base p)) p
//                          = Path (λ_.Ω S¹) (intLoop (winding p)) p — the η field.
// ══════════════════════════════════════════════════════════════════════════════

/// The BASED `encode arg` / its registration name.
fn encode_n(y: Expr, q: Expr) -> Expr {
    Expr::apps(cst("encode"), [y, q])
}

/// `decodeEncode : (p:Ω S¹) → Path (λ_.Ω S¹) (intLoop (winding p)) p` (the η field).
fn decode_encode_full_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        omega_s1(),
        path(
            const_line(omega_s1()),
            intloop_n(winding_n(bvar(0))),
            bvar(0),
        ),
    )
}

/// PROOF TERM of `decodeEncode`, by based path-induction (`coe` over the canonical
/// singleton-contractible line — the `path_J` shape, inlined so the loop `p` is a
/// bound variable with correct de Bruijn lifting under `λ i` / `<j>`).
fn decode_encode_full_value() -> Expr {
    // Motive P (closed): λ (y:S¹) (q:base=y). Path (λ_. base=y) (decode y (encode y q)) q.
    let p_motive = {
        // under λy (y=BVar0); under λq (q=BVar0, y=BVar1).
        let q_ty = path(const_line(s1()), s1_base(), bvar(0)); // base=y, under λy
                                                               // line `λ_:I. base=y`: under its binder y=BVar2.
        let line = lam(interval(), path(const_line(s1()), s1_base(), bvar(2)));
        let dec = Expr::apps(cst("decode"), [bvar(1), encode_n(bvar(1), bvar(0))]);
        let body = Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(line),
            left: Arc::new(dec),
            right: Arc::new(bvar(0)), // q
        });
        lam(s1(), lam(q_ty, body))
    };
    // Base case d := <_> refl base : P base (refl base).
    let d = path_refl(&path_refl(&s1_base()));
    // decodeEncode := λ p. coe^{i0→i1} (λ i. P (p@i) (<j> p@(i∧j))) d.
    // Under λp: p=BVar0. Under λi (coe line): p=BVar1, i=BVar0.
    // Under the diag <j>: p=BVar2, i=BVar1, j=BVar0.
    let p_at_i = cpapp(bvar(1), bvar(0));
    let diag = cplam(cpapp(bvar(2), i_min(bvar(1), bvar(0))));
    let body = Expr::apps(p_motive, [p_at_i, diag]);
    let line = lam(interval(), body);
    let coe = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(d),
    });
    lam(omega_s1(), coe)
}

/// `int_env_with_decode()` plus `winding`, the based `encode`, the PROVED
/// `encodeDecode` (ε), and the PROVED `decodeEncode` (η) — the full equivalence
/// environment.
fn int_env_milestone() -> Environment {
    let mut env = int_env_with_decode();
    env.add_decl(Declaration::Definition {
        name: nm("winding"),
        level_params: vec![],
        type_: Expr::arrow(omega_s1(), myz()),
        value: winding_value(),
        is_reducible: false,
    })
    .expect("winding : Ω S¹ → MyZ should type-check and register");
    env.add_decl(Declaration::Definition {
        name: nm("encode"),
        level_params: vec![],
        type_: encode_based_ty(),
        value: encode_based_value(),
        is_reducible: false,
    })
    .expect("based encode : (y:S¹) → base=y → helix y should type-check and register");
    env.add_decl(Declaration::Definition {
        name: nm("encodeDecode"),
        level_params: vec![],
        type_: encode_decode_ty(),
        value: encode_decode_value(),
        is_reducible: false,
    })
    .expect("encodeDecode (ε) should type-check and register");
    env.add_decl(Declaration::Definition {
        name: nm("decodeEncode"),
        level_params: vec![],
        type_: decode_encode_full_ty(),
        value: decode_encode_full_value(),
        is_reducible: false,
    })
    .expect("decodeEncode (η) proof term should type-check (based path-induction)");
    env
}

/// THE η FIELD, PROVED: `decodeEncode : (p:Ω S¹) → Path (λ_.Ω S¹) (intLoop (winding p)) p`
/// by based path-induction over the cap-COHERENT `decode`. Now that `decode`
/// type-checks under the enforced cap check, the whole `decodeEncode` chain is a
/// genuine proof term (no axioms, no hole).
#[test]
fn test_decode_encode_eta_is_proved() {
    let env = int_env_milestone();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let (de_ty, _) = tc
        .infer_type_with_cert(&cst("decodeEncode"))
        .expect("decodeEncode should type-check");
    assert!(
        tc.is_def_eq(&de_ty, &decode_encode_full_ty()),
        "decodeEncode : (p:Ω S¹) → Path (λ_.Ω S¹) (intLoop (winding p)) p; got {de_ty:?}"
    );
}

/// THE FULL π₁(S¹)=ℤ MILESTONE, GENUINELY CLOSED on the SOUND kernel:
/// `windingEquiv := Equiv.mk (Ω S¹) MyZ winding intLoop decodeEncode encodeDecode`
/// type-checks as `Equiv (Ω S¹) MyZ`. Every component is a real proof term — in
/// particular `decode` (and hence `decodeEncode`) is the cap-COHERENT square, so it
/// passes the now-enforced `validate_hcomp_cap`. This is the honest milestone: no
/// hcomp cap hole to exploit, no axioms for `decode`/`decodeEncode`.
#[test]
fn test_windingequiv_typechecks_full_pi1_milestone() {
    let env = int_env_milestone();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let winding_equiv = Expr::apps(
        Expr::const_(nm("Equiv.mk"), vec![type_level()]),
        [
            omega_s1(),
            myz(),
            cst("winding"),
            cst("intLoop"),
            cst("decodeEncode"),
            cst("encodeDecode"),
        ],
    );

    let (we_ty, _) = tc
        .infer_type_with_cert(&winding_equiv)
        .expect("windingEquiv should type-check — the FULL π₁(S¹)=ℤ milestone");
    let expected = Expr::apps(
        Expr::const_(nm("Equiv"), vec![type_level()]),
        [omega_s1(), myz()],
    );
    assert!(
        tc.is_def_eq(&we_ty, &expected),
        "windingEquiv : Equiv (Ω S¹) MyZ — π₁(S¹)=ℤ; got {we_ty:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 16 — `windingIsEquiv` — upgrading the quasi-inverse `windingEquiv` to a genuine
//      contractible-fibre `isEquiv winding`, via the h-level upgrade engine
//      `biInvToIsEquivOnSet` (proved in `cubical_hlevels`). The kernel `Equiv` is
//      only a quasi-inverse `(f,g,η,ε)`; for the codomain `MyZ` a **set** the
//      fibres of `winding` are contractible, so `winding` is a real equivalence.
//
//      `is_equiv_from_quasi_inv_on_set` is a *proved, axiom-free* term; here it is
//      instantiated at the REAL `winding`/`intLoop`/`decodeEncode`/`encodeDecode`
//      data, abstracting the set hypothesis as a genuine `λ (s : isSet MyZ)`. So
//      this term is itself axiom-free: it inhabits `isSet MyZ → isEquiv winding`.
//      The fully-closed `windingIsEquiv : isEquiv winding` then needs exactly one
//      more input — a proof term `isSet MyZ` — which is the remaining open lemma
//      (Hedberg / encode-decode for ℤ; tracked separately). No isSet-MyZ axiom is
//      introduced here.
// ══════════════════════════════════════════════════════════════════════════════

/// `int_env_milestone()` + the Σ axioms the contractible-fibre layer needs.
fn int_env_milestone_with_sigma() -> Environment {
    let mut env = int_env_milestone();
    register_sigma_axioms(&mut env).expect("register sigma axioms");
    env
}

/// THE GENUINE `isEquiv` UPGRADE (modulo `isSet MyZ`): the proved, axiom-free engine
/// `biInvToIsEquivOnSet`, instantiated at the real `winding` quasi-inverse data,
/// inhabits `isSet MyZ → isEquiv winding` — abstracting the set hypothesis as a real
/// `λ (s : isSet MyZ)`, so the whole term is a closed proof term with NO axioms and
/// NO `sorry` (the contractible-fibre square passes the enforced `validate_hcomp_cap`).
/// This upgrades `windingEquiv` from a quasi-inverse to a genuine contractible-fibre
/// `isEquiv` — the only remaining input being a proof of `isSet MyZ`.
#[test]
fn test_winding_isequiv_from_isset_myz_typechecks() {
    let env = int_env_milestone_with_sigma();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // λ (s : isSet MyZ). biInvToIsEquivOnSet s winding intLoop decodeEncode encodeDecode.
    //   f = winding (Ω S¹ → MyZ), g = intLoop, η = decodeEncode (g∘f~id),
    //   ε = encodeDecode (f∘g~id); set hypothesis s = BVar 0.
    let body = is_equiv_from_quasi_inv_on_set(
        type_level(),
        &omega_s1(),
        &myz(),
        &bvar(0), // s : isSet MyZ
        &cst("winding"),
        &cst("intLoop"),
        &cst("decodeEncode"),
        &cst("encodeDecode"),
    );
    let proof = lam(is_set_type(&myz()), body);
    let (ty, _) = tc
        .infer_type_with_cert(&proof)
        .expect("windingIsEquiv-from-isSet should type-check (the genuine isEquiv upgrade)");

    // Expected: (isSet MyZ) → isEquiv winding.
    let expected = Expr::pi(
        BinderInfo::Default,
        is_set_type(&myz()),
        is_equiv_type(type_level(), &omega_s1(), &myz(), &cst("winding")),
    );
    assert!(
        tc.is_def_eq(&ty, &expected),
        "windingIsEquiv : isSet MyZ → isEquiv winding (genuine fibre-contractible upgrade); got {ty:?}"
    );
}

/// Sanity: `isEquiv winding` (the upgrade TARGET) is a well-formed `Type` over the
/// real `winding` — so the contractible-fibre statement is genuinely about the
/// milestone map, not a degenerate type.
#[test]
fn test_isequiv_winding_is_a_well_formed_type() {
    let env = int_env_milestone_with_sigma();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let is_equiv_winding = is_equiv_type(type_level(), &omega_s1(), &myz(), &cst("winding"));
    let (sort, _) = tc
        .infer_type_with_cert(&is_equiv_winding)
        .expect("isEquiv winding should be a well-formed type");
    assert!(
        matches!(tc.whnf(&sort).kind(), ExprKind::Sort(_)),
        "isEquiv winding : Sort _; got {sort:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 17 — `isSet MyZ` (and `isSet MyNat`) by encode-decode, and the FULLY-CLOSED
//      `windingIsEquiv : isEquiv winding` (the quasi-inverse caveat removed).
//
// The "fundamental theorem of identity types" route (no Hedberg square, no
// decidable-equality detour): a **reflexive, propositional** binary code family
// `code` that **decodes** to identity makes every path space a retract of a
// proposition, hence `isSet`. `codeNat`/`codeZ` are double-recursor case trees into
// `Unit`/`Empty`; `decodeNat`/`decodeZ` rebuild paths with `ap ctor`; `drNat`/`drZ`
// are the diagonal coherence `decode x x (r x) ≡ refl` by induction (using the
// definitional `ap ctor refl ≡ refl`). The generic glue (`is_set_from_encode_decode`,
// `is_prop_retract`) lives in `reduction/kan.rs`. NO axioms, NO `sorry`.
// ══════════════════════════════════════════════════════════════════════════════

/// `Sort 2`'s level — the universe a `code : MyNat → MyNat → Type` motive lives in
/// (it returns `Type = Sort 1`, so the large-eliminating recursor is `_.rec.{2}`).
fn lvl2() -> Level {
    Level::succ(lvl1())
}
/// `X.rec.{2}` — the large-eliminating recursor producing `Type` (`Sort 1`) values.
fn rec2(ind: &str) -> Expr {
    Expr::const_(nm(&format!("{ind}.rec")), vec![lvl2()])
}

// ── Unit / Empty (the code leaves) ────────────────────────────────────────────

fn unit_ty() -> Expr {
    cst("Unit")
}
fn unit_tt() -> Expr {
    cst("Unit.tt")
}
fn empty_ty() -> Expr {
    cst("Empty")
}
/// `Empty.rec.{1} (λ_:Empty. motive_body) e` — eliminate the impossible. `motive_body`
/// is the result type as a term valid under the introduced `λ_:Empty` (so its outer
/// references are pre-lifted by one by the caller).
fn empty_rec1(motive: Expr, e: Expr) -> Expr {
    Expr::apps(Expr::const_(nm("Empty.rec"), vec![lvl1()]), [motive, e])
}

/// `Path (λ_:I.MyNat) l r` / over `MyZ` / `Unit` / `Empty`.
fn path_mynat(l: Expr, r: Expr) -> Expr {
    path(const_line(mynat()), l, r)
}
fn path_myz(l: Expr, r: Expr) -> Expr {
    path(const_line(myz()), l, r)
}

fn code_nat_app(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("codeNat"), [x, y])
}
fn code_z_app(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("codeZ"), [x, y])
}

// ── codeNat : MyNat → MyNat → Type ────────────────────────────────────────────
//   codeNat zero     zero     = Unit
//   codeNat zero     (succ n) = Empty
//   codeNat (succ m) zero     = Empty
//   codeNat (succ m) (succ n) = codeNat m n
fn code_nat_value() -> Expr {
    // motive C = λ _:MyNat. MyNat → Type.
    let motive = lam(mynat(), Expr::arrow(mynat(), Expr::type_()));
    // F_zero = λ n. MyNat.rec.{2} (λ_.Type) Unit (λ n' ih. Empty) n.
    let f_zero = {
        let inner = Expr::apps(
            rec2("MyNat"),
            [
                lam(mynat(), Expr::type_()),
                unit_ty(),
                lam(mynat(), lam(Expr::type_(), empty_ty())),
                bvar(0), // n
            ],
        );
        lam(mynat(), inner)
    };
    // F_succ = λ m'. λ ih. λ n. MyNat.rec.{2} (λ_.Type) Empty (λ n' ihn. ih n') n.
    //   [m', ih, n, n', ihn]: ihn=0, n'=1, n=2, ih=3, m'=4.
    let f_succ = {
        let step = lam(mynat(), lam(Expr::type_(), Expr::app(bvar(3), bvar(1))));
        let inner = Expr::apps(
            rec2("MyNat"),
            [lam(mynat(), Expr::type_()), empty_ty(), step, bvar(0)],
        );
        lam(
            mynat(),
            lam(Expr::arrow(mynat(), Expr::type_()), lam(mynat(), inner)),
        )
    };
    lam(
        mynat(),
        Expr::apps(rec2("MyNat"), [motive, f_zero, f_succ, bvar(0)]),
    )
}

// ── Env scaffolding: Unit / Empty inductives + codeNat ────────────────────────
fn int_env_isset_base() -> Environment {
    let mut env = int_env_milestone();
    register_sigma_axioms(&mut env).expect("register sigma axioms");

    // Unit — a single-constructor unit type (generates Unit.rec).
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("Unit"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: nm("Unit.tt"),
                type_: unit_ty(),
            }],
        }],
    })
    .expect("Unit inductive should register");

    // Empty — the zero-constructor empty type (generates Empty.rec).
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("Empty"),
            type_: Expr::type_(),
            constructors: vec![],
        }],
    })
    .expect("Empty inductive should register");

    env.add_decl(Declaration::Definition {
        name: nm("codeNat"),
        level_params: vec![],
        type_: Expr::arrow(mynat(), Expr::arrow(mynat(), Expr::type_())),
        value: code_nat_value(),
        is_reducible: true,
    })
    .expect("codeNat : MyNat → MyNat → Type should register");
    env
}

/// `codeNat` type-checks and **computes** on constructors: `codeNat zero zero ↝ Unit`,
/// `codeNat (succ m) (succ n) ↝ codeNat m n`, the cross cases `↝ Empty`.
#[test]
fn test_code_nat_computes() {
    let env = int_env_isset_base();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let zz = code_nat_app(mn_zero(), mn_zero());
    assert!(
        tc.is_def_eq(&zz, &unit_ty()),
        "codeNat zero zero ≡ Unit; got {:?}",
        tc.whnf(&zz)
    );
    let zs = code_nat_app(mn_zero(), mn_succ(mn_zero()));
    assert!(
        tc.is_def_eq(&zs, &empty_ty()),
        "codeNat zero (succ zero) ≡ Empty"
    );
    let sz = code_nat_app(mn_succ(mn_zero()), mn_zero());
    assert!(
        tc.is_def_eq(&sz, &empty_ty()),
        "codeNat (succ zero) zero ≡ Empty"
    );
    // codeNat (succ a) (succ b) ≡ codeNat a b  (over opaque a, b via a fresh axiom).
    let ss = code_nat_app(mn_succ(mn_zero()), mn_succ(mn_zero()));
    let rec_zz = code_nat_app(mn_zero(), mn_zero());
    assert!(
        tc.is_def_eq(&ss, &rec_zz),
        "codeNat (succ zero) (succ zero) ≡ codeNat zero zero ≡ Unit"
    );
}

// ── lift-correct path leaves used by the diagonal lemmas ──────────────────────

/// `refl a := <_> a` for an `a` that may contain loose `BVar`s (lifts `a` by one
/// under the introduced path binder, unlike the closed-input `path_refl`).
fn refl_at(a: &Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(a.lift(1)),
    })
}
/// `Path (λ_:I. t) l r` for a `t` that may contain loose `BVar`s (lifts `t`).
fn path_homog_at(t: &Expr, l: Expr, r: Expr) -> Expr {
    path(lam(interval(), t.lift(1)), l, r)
}
fn path_app_e(p: Expr, arg: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(p),
        arg: Arc::new(arg),
    })
}
fn path_lam_e(body: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(body),
    })
}
fn path_unit(l: Expr, r: Expr) -> Expr {
    path(const_line(unit_ty()), l, r)
}

// ── `congCtor c : (a b) → Path dom a b → Path cod (c a) (c b)` ─────────────────
//
// A **named** action-on-paths for a unary constructor, whose *declared codomain*
// `Path cod (c a) (c b)` makes the outer path line of a double-`cong`
// (`ap (congCtor c) ih`) manifestly constant in the running interval — sidestepping
// the nested neutral-endpoint reduction that a raw `<i><j> c((ih@i)@j)` would need.
fn cong_ctor_ty(dom: Expr, cod: Expr, ctor: &str) -> Expr {
    pi(
        dom.clone(),
        pi(
            dom.clone(),
            Expr::arrow(
                path(const_line(dom), bvar(1), bvar(0)), // Path dom a b   [a,b]
                path(
                    const_line(cod),
                    Expr::app(cst(ctor), bvar(2)),
                    Expr::app(cst(ctor), bvar(1)),
                ), // Path cod (c a)(c b)  [a,b,p]
            ),
        ),
    )
}
fn cong_ctor_value(dom: Expr, ctor: &str) -> Expr {
    lam(
        dom.clone(),
        lam(
            dom.clone(),
            lam(
                path(const_line(dom), bvar(1), bvar(0)), // p : Path dom a b
                path_lam_e(Expr::app(cst(ctor), path_app_e(bvar(1), bvar(0)))), // <i> c (p@i)
            ),
        ),
    )
}

// ── isProp Unit / isProp Empty ────────────────────────────────────────────────

fn is_prop_unit_value() -> Expr {
    // λ (x y:Unit). Unit.rec.{1} (λ x'. Path Unit x' y) caseUnit x
    //   caseUnit = Unit.rec.{1} (λ y'. Path Unit unit y') (refl unit) y
    let motive_x = lam(unit_ty(), path_unit(bvar(0), bvar(1))); // [x,y,x']: x'=0,y=1
    let motive_y = lam(unit_ty(), path_unit(unit_tt(), bvar(0))); // [x,y,y']: y'=0
    let case_unit = Expr::apps(
        Expr::const_(nm("Unit.rec"), vec![lvl1()]),
        [motive_y, path_refl(&unit_tt()), bvar(0)], // y
    );
    let outer = Expr::apps(
        Expr::const_(nm("Unit.rec"), vec![lvl1()]),
        [motive_x, case_unit, bvar(1)], // x
    );
    lam(unit_ty(), lam(unit_ty(), outer))
}

fn is_prop_empty_value() -> Expr {
    // λ (x y:Empty). Empty.rec.{1} (λ _:Empty. Path Empty x y) x
    let motive = lam(
        empty_ty(),
        path(const_line(empty_ty()), bvar(2), bvar(1)), // [x,y,_]: x=2,y=1
    );
    lam(empty_ty(), lam(empty_ty(), empty_rec1(motive, bvar(1))))
}

// ── rNat / decodeNat / propCodeNat / drNat ────────────────────────────────────

fn r_nat_value() -> Expr {
    // λ n. MyNat.rec.{1} (λ n'. codeNat n' n') Unit.tt (λ k ih. ih) n
    let motive = lam(mynat(), code_nat_app(bvar(0), bvar(0)));
    let step = lam(mynat(), lam(code_nat_app(bvar(0), bvar(0)), bvar(0)));
    lam(
        mynat(),
        Expr::apps(rec("MyNat"), [motive, unit_tt(), step, bvar(0)]),
    )
}
fn r_nat_ty() -> Expr {
    pi(mynat(), code_nat_app(bvar(0), bvar(0)))
}

fn decode_nat_value() -> Expr {
    // motive Cm = λ m'. Π(n). codeNat m' n → Path MyNat m' n
    let cm = lam(
        mynat(),
        pi(
            mynat(),
            Expr::arrow(code_nat_app(bvar(1), bvar(0)), path_mynat(bvar(2), bvar(1))),
        ),
    );
    // Dzero = λ n. MyNat.rec.{1} Czn (λ _:Unit. refl zero) stepZ n
    let dzero = {
        let czn = lam(
            mynat(),
            Expr::arrow(
                code_nat_app(mn_zero(), bvar(0)),
                path_mynat(mn_zero(), bvar(1)),
            ),
        );
        let base = lam(unit_ty(), path_refl(&mn_zero()));
        let czn_n_dom = Expr::arrow(
            code_nat_app(mn_zero(), bvar(0)),
            path_mynat(mn_zero(), bvar(1)),
        );
        // [n,n',ih',e]: e=0,ih'=1,n'=2,n=3; Empty.rec λ_ → n'=3
        let motive_e = lam(empty_ty(), path_mynat(mn_zero(), mn_succ(bvar(3))));
        let stepz = lam(
            mynat(),
            lam(czn_n_dom, lam(empty_ty(), empty_rec1(motive_e, bvar(0)))),
        );
        lam(
            mynat(),
            Expr::apps(rec("MyNat"), [czn, base, stepz, bvar(0)]),
        )
    };
    // Dsucc = λ m'. λ ihm. λ n. MyNat.rec.{1} Csn stepSZero stepSS n
    let dsucc = {
        let ihm_dom = pi(
            mynat(),
            Expr::arrow(code_nat_app(bvar(1), bvar(0)), path_mynat(bvar(2), bvar(1))),
        );
        // Csn = λ n'. codeNat (succ m') n' → Path (succ m') n'  ([m',ihm,n,n']: m'=3)
        let csn = lam(
            mynat(),
            Expr::arrow(
                code_nat_app(mn_succ(bvar(3)), bvar(0)),
                path_mynat(mn_succ(bvar(4)), bvar(1)),
            ),
        );
        // stepSZero (n=zero): λ e:Empty. Empty.rec (λ_. Path (succ m') zero) e
        //   [m',ihm,n,e]: e=0,n=1,ihm=2,m'=3; Empty.rec λ_ → m'=4
        let step_s_zero = lam(
            empty_ty(),
            empty_rec1(
                lam(empty_ty(), path_mynat(mn_succ(bvar(4)), mn_zero())),
                bvar(0),
            ),
        );
        // stepSS (n=succ n'): λ n'. λ ih. λ c. ap succ (ihm n' c)
        //   [m',ihm,n,n',ih,c]: c=0,ih=1,n'=2,n=3,ihm=4,m'=5
        let step_s_s = {
            let ih_dom = Expr::arrow(
                code_nat_app(mn_succ(bvar(3)), bvar(0)), // codeNat (succ m') n'  ([m',ihm,n,n']: m'=3,n'=0)
                path_mynat(mn_succ(bvar(4)), bvar(1)),
            );
            let c_dom = code_nat_app(mn_succ(bvar(4)), mn_succ(bvar(1))); // codeNat (succ m')(succ n')  ([..,ih]: m'=4,n'=1)
            let ihm_app = Expr::apps(bvar(4), [bvar(2), bvar(0)]); // ihm n' c
            lam(
                mynat(),
                lam(ih_dom, lam(c_dom, ap_cong(&cst("MyNat.succ"), &ihm_app))),
            )
        };
        lam(
            mynat(),
            lam(
                ihm_dom,
                lam(
                    mynat(),
                    Expr::apps(rec("MyNat"), [csn, step_s_zero, step_s_s, bvar(0)]),
                ),
            ),
        )
    };
    lam(
        mynat(),
        Expr::apps(rec("MyNat"), [cm, dzero, dsucc, bvar(0)]),
    )
}
fn decode_nat_ty() -> Expr {
    pi(
        mynat(),
        pi(
            mynat(),
            Expr::arrow(code_nat_app(bvar(1), bvar(0)), path_mynat(bvar(2), bvar(1))),
        ),
    )
}

fn prop_code_nat_value() -> Expr {
    let pm = lam(
        mynat(),
        pi(mynat(), is_prop_type(&code_nat_app(bvar(1), bvar(0)))),
    );
    let pzero = {
        let qn = lam(mynat(), is_prop_type(&code_nat_app(mn_zero(), bvar(0))));
        let step = lam(
            mynat(),
            lam(
                is_prop_type(&code_nat_app(mn_zero(), bvar(0))),
                cst("isPropEmpty"),
            ),
        );
        lam(
            mynat(),
            Expr::apps(rec("MyNat"), [qn, cst("isPropUnit"), step, bvar(0)]),
        )
    };
    let psucc = {
        let ihm_dom = pi(mynat(), is_prop_type(&code_nat_app(bvar(1), bvar(0))));
        let rn = lam(
            mynat(),
            is_prop_type(&code_nat_app(mn_succ(bvar(3)), bvar(0))),
        );
        let step = lam(
            mynat(),
            lam(
                is_prop_type(&code_nat_app(mn_succ(bvar(3)), bvar(0))),
                Expr::app(bvar(3), bvar(1)), // ihm n'
            ),
        );
        lam(
            mynat(),
            lam(
                ihm_dom,
                lam(
                    mynat(),
                    Expr::apps(rec("MyNat"), [rn, cst("isPropEmpty"), step, bvar(0)]),
                ),
            ),
        )
    };
    lam(
        mynat(),
        Expr::apps(rec("MyNat"), [pm, pzero, psucc, bvar(0)]),
    )
}
fn prop_code_nat_ty() -> Expr {
    pi(
        mynat(),
        pi(mynat(), is_prop_type(&code_nat_app(bvar(1), bvar(0)))),
    )
}

fn dr_nat_motive_body(n: Expr) -> Expr {
    // Path (Path MyNat n n) (decodeNat n n (rNat n)) (refl n)
    path_homog_at(
        &path_mynat(n.clone(), n.clone()),
        Expr::apps(
            cst("decodeNat"),
            [n.clone(), n.clone(), Expr::app(cst("rNat"), n.clone())],
        ),
        refl_at(&n),
    )
}
fn dr_nat_value() -> Expr {
    let motive = lam(mynat(), dr_nat_motive_body(bvar(0)));
    let base = path_refl(&path_refl(&mn_zero())); // refl (refl zero)
                                                  // step = λ k ih. ap (congSucc k k) ih  ([n,k,ih]: ih=0, k=1).
    let step = lam(
        mynat(), // k
        lam(
            dr_nat_motive_body(bvar(0)),
            ap_cong(&Expr::apps(cst("congSucc"), [bvar(1), bvar(1)]), &bvar(0)),
        ),
    );
    lam(
        mynat(),
        Expr::apps(rec("MyNat"), [motive, base, step, bvar(0)]),
    )
}
fn dr_nat_ty() -> Expr {
    pi(mynat(), dr_nat_motive_body(bvar(0)))
}

// ── Env with the full MyNat code-family + isSet MyNat ──────────────────────────
/// Everything except `drNat` (so the diagonal lemma can be tested in isolation).
fn int_env_isset_nat_core() -> Environment {
    let mut env = int_env_isset_base();
    let mut def = |name: &str, type_: Expr, value: Expr, red: bool| {
        env.add_decl(Declaration::Definition {
            name: nm(name),
            level_params: vec![],
            type_,
            value,
            is_reducible: red,
        })
        .unwrap_or_else(|e| panic!("{name} should type-check and register: {e:?}"));
    };
    def(
        "isPropUnit",
        is_prop_type(&unit_ty()),
        is_prop_unit_value(),
        false,
    );
    def(
        "isPropEmpty",
        is_prop_type(&empty_ty()),
        is_prop_empty_value(),
        false,
    );
    def(
        "congSucc",
        cong_ctor_ty(mynat(), mynat(), "MyNat.succ"),
        cong_ctor_value(mynat(), "MyNat.succ"),
        true,
    );
    def("rNat", r_nat_ty(), r_nat_value(), true);
    def("decodeNat", decode_nat_ty(), decode_nat_value(), true);
    def(
        "propCodeNat",
        prop_code_nat_ty(),
        prop_code_nat_value(),
        false,
    );
    env
}
fn int_env_isset_nat() -> Environment {
    let mut env = int_env_isset_nat_core();
    env.add_decl(Declaration::Definition {
        name: nm("drNat"),
        level_params: vec![],
        type_: dr_nat_ty(),
        value: dr_nat_value(),
        is_reducible: false,
    })
    .expect("drNat should type-check and register");
    env
}

/// `isSet MyNat` — a PROVED, axiom-free term: the encode-decode criterion applied
/// to the propositional code family `codeNat`. Each subterm (`codeNat`/`rNat`/
/// `decodeNat`/`propCodeNat`/`drNat`) already type-checked on registration.
#[test]
fn test_isset_mynat_is_proved() {
    let env = int_env_isset_nat();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let isset = is_set_from_encode_decode(
        type_level(),
        &mynat(),
        &cst("codeNat"),
        &cst("rNat"),
        &cst("decodeNat"),
        &cst("propCodeNat"),
        &cst("drNat"),
    );
    let (ty, _) = tc
        .infer_type_with_cert(&isset)
        .expect("isSet MyNat should type-check (encode-decode, axiom-free)");
    assert!(
        tc.is_def_eq(&ty, &is_set_type(&mynat())),
        "isSet MyNat; got {ty:?}"
    );
}

#[test]
fn test_deep_path_beta_diagonal_regression() {
    // Regression for the cubical def-eq fix that the `isSet` diagonal lemmas need:
    // a path application whose head only becomes a `<i> …` after delta-unfolding a
    // named helper (`congSucc`) and/or a nested typed endpoint projection
    // (`ih @ i1 ↝ right(ih)`) must still reduce under a binder. Here `ihh` stands in
    // for a recursor's induction hypothesis `ih : decodeNat k k (rNat k) ≡ refl k`.
    let mut env = int_env_isset_nat_core();
    env.add_decl(Declaration::Axiom {
        name: nm("kk"),
        level_params: vec![],
        type_: mynat(),
    })
    .expect("kk : MyNat");
    let k = cst("kk");
    let motive_at_k = path_homog_at(
        &path_mynat(k.clone(), k.clone()),
        Expr::apps(
            cst("decodeNat"),
            [k.clone(), k.clone(), Expr::app(cst("rNat"), k.clone())],
        ),
        refl_at(&k),
    );
    env.add_decl(Declaration::Axiom {
        name: nm("ihh"),
        level_params: vec![],
        type_: motive_at_k,
    })
    .expect("ihh : motive k");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // `ap (congSucc k k) ihh : motive (succ k)` — exactly the `drNat` succ-case shape.
    let ap_term = ap_cong(
        &Expr::apps(cst("congSucc"), [k.clone(), k.clone()]),
        &cst("ihh"),
    );
    let (ap_ty, _) = tc
        .infer_type_with_cert(&ap_term)
        .expect("ap (congSucc k k) ihh infers");
    let expected = path_homog_at(
        &path_mynat(mn_succ(k.clone()), mn_succ(k.clone())),
        Expr::apps(
            cst("decodeNat"),
            [
                mn_succ(k.clone()),
                mn_succ(k.clone()),
                Expr::app(cst("rNat"), mn_succ(k.clone())),
            ],
        ),
        refl_at(&mn_succ(k.clone())),
    );
    assert!(
        tc.is_def_eq(&ap_ty, &expected),
        "ap (congSucc k k) ihh : motive (succ k) — deep path-beta must reduce both \
         the named-helper head and the nested IH endpoint; got {ap_ty:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// MyZ code family (over codeNat) and isSet MyZ
// ══════════════════════════════════════════════════════════════════════════════

// codeZ : MyZ → MyZ → Type
//   codeZ (ofNat m)   (ofNat n)   = codeNat m n
//   codeZ (ofNat m)   (negSucc n) = Empty
//   codeZ (negSucc m) (ofNat n)   = Empty
//   codeZ (negSucc m) (negSucc n) = codeNat m n
fn code_z_value() -> Expr {
    let motive = lam(myz(), Expr::arrow(myz(), Expr::type_()));
    // F_ofNat = λ m. λ y. MyZ.rec.{2} (λ_.Type) (λ n. codeNat m n) (λ n. Empty) y
    let f_ofnat = {
        let inner = Expr::apps(
            rec2("MyZ"),
            [
                lam(myz(), Expr::type_()),
                lam(mynat(), code_nat_app(bvar(2), bvar(0))), // [x,m,y,n]: m=2,n=0
                lam(mynat(), empty_ty()),
                bvar(0), // y
            ],
        );
        lam(mynat(), lam(myz(), inner))
    };
    // F_negSucc = λ m. λ y. MyZ.rec.{2} (λ_.Type) (λ n. Empty) (λ n. codeNat m n) y
    let f_negsucc = {
        let inner = Expr::apps(
            rec2("MyZ"),
            [
                lam(myz(), Expr::type_()),
                lam(mynat(), empty_ty()),
                lam(mynat(), code_nat_app(bvar(2), bvar(0))),
                bvar(0),
            ],
        );
        lam(mynat(), lam(myz(), inner))
    };
    lam(
        myz(),
        Expr::apps(rec2("MyZ"), [motive, f_ofnat, f_negsucc, bvar(0)]),
    )
}
fn code_z_ty() -> Expr {
    Expr::arrow(myz(), Expr::arrow(myz(), Expr::type_()))
}

fn r_z_value() -> Expr {
    // λ z. MyZ.rec.{1} (λ z'. codeZ z' z') (λ m. rNat m) (λ m. rNat m) z
    let motive = lam(myz(), code_z_app(bvar(0), bvar(0)));
    let on = lam(mynat(), Expr::app(cst("rNat"), bvar(0)));
    let ns = lam(mynat(), Expr::app(cst("rNat"), bvar(0)));
    lam(myz(), Expr::apps(rec("MyZ"), [motive, on, ns, bvar(0)]))
}
fn r_z_ty() -> Expr {
    pi(myz(), code_z_app(bvar(0), bvar(0)))
}

fn decode_z_value() -> Expr {
    // Cx = λ x'. Π(y). codeZ x' y → Path MyZ x' y
    let cx = lam(
        myz(),
        pi(
            myz(),
            Expr::arrow(code_z_app(bvar(1), bvar(0)), path_myz(bvar(2), bvar(1))),
        ),
    );
    // D_ofNat = λ m. λ y. MyZ.rec.{1} Cofn onMin nsMin y
    let d_ofnat = {
        // Cofn = λ y'. codeZ (ofNat m) y' → Path MyZ (ofNat m) y'   [x,m,y,y']: m=2 ; under arrow m=3
        let cofn = lam(
            myz(),
            Expr::arrow(
                code_z_app(ofnat(bvar(2)), bvar(0)),
                path_myz(ofnat(bvar(3)), bvar(1)),
            ),
        );
        // ofNat n: λ n. λ c. congOfNat m n (decodeNat m n c)   [x,m,y,n,c]: m=3,n=1,c=0
        let on_min = lam(
            mynat(),
            lam(
                code_nat_app(bvar(2), bvar(0)), // codeNat m n  [x,m,y,n]: m=2,n=0
                Expr::apps(
                    cst("congOfNat"),
                    [
                        bvar(3),
                        bvar(1),
                        Expr::apps(cst("decodeNat"), [bvar(3), bvar(1), bvar(0)]),
                    ],
                ),
            ),
        );
        // negSucc n: λ n. λ e. Empty.rec (λ_. Path MyZ (ofNat m)(negSucc n)) e  [x,m,y,n,e,_]: m=4,n=2
        let ns_min = lam(
            mynat(),
            lam(
                empty_ty(),
                empty_rec1(
                    lam(empty_ty(), path_myz(ofnat(bvar(4)), negsucc(bvar(2)))),
                    bvar(0),
                ),
            ),
        );
        lam(
            mynat(),
            lam(
                myz(),
                Expr::apps(rec("MyZ"), [cofn, on_min, ns_min, bvar(0)]),
            ),
        )
    };
    // D_negSucc = λ m. λ y. MyZ.rec.{1} Cneg onMin nsMin y
    let d_negsucc = {
        let cneg = lam(
            myz(),
            Expr::arrow(
                code_z_app(negsucc(bvar(2)), bvar(0)),
                path_myz(negsucc(bvar(3)), bvar(1)),
            ),
        );
        // ofNat n: Empty.rec (λ_. Path MyZ (negSucc m)(ofNat n)) e   [.,e,_]: m=4,n=2
        let on_min = lam(
            mynat(),
            lam(
                empty_ty(),
                empty_rec1(
                    lam(empty_ty(), path_myz(negsucc(bvar(4)), ofnat(bvar(2)))),
                    bvar(0),
                ),
            ),
        );
        // negSucc n: congNegSucc m n (decodeNat m n c)
        let ns_min = lam(
            mynat(),
            lam(
                code_nat_app(bvar(2), bvar(0)),
                Expr::apps(
                    cst("congNegSucc"),
                    [
                        bvar(3),
                        bvar(1),
                        Expr::apps(cst("decodeNat"), [bvar(3), bvar(1), bvar(0)]),
                    ],
                ),
            ),
        );
        lam(
            mynat(),
            lam(
                myz(),
                Expr::apps(rec("MyZ"), [cneg, on_min, ns_min, bvar(0)]),
            ),
        )
    };
    lam(
        myz(),
        Expr::apps(rec("MyZ"), [cx, d_ofnat, d_negsucc, bvar(0)]),
    )
}
fn decode_z_ty() -> Expr {
    pi(
        myz(),
        pi(
            myz(),
            Expr::arrow(code_z_app(bvar(1), bvar(0)), path_myz(bvar(2), bvar(1))),
        ),
    )
}

fn prop_code_z_value() -> Expr {
    let px = lam(
        myz(),
        pi(myz(), is_prop_type(&code_z_app(bvar(1), bvar(0)))),
    );
    let p_ofnat = {
        let qofn = lam(myz(), is_prop_type(&code_z_app(ofnat(bvar(2)), bvar(0))));
        let on_min = lam(mynat(), Expr::apps(cst("propCodeNat"), [bvar(2), bvar(0)]));
        let ns_min = lam(mynat(), cst("isPropEmpty"));
        lam(
            mynat(),
            lam(
                myz(),
                Expr::apps(rec("MyZ"), [qofn, on_min, ns_min, bvar(0)]),
            ),
        )
    };
    let p_negsucc = {
        let qneg = lam(myz(), is_prop_type(&code_z_app(negsucc(bvar(2)), bvar(0))));
        let on_min = lam(mynat(), cst("isPropEmpty"));
        let ns_min = lam(mynat(), Expr::apps(cst("propCodeNat"), [bvar(2), bvar(0)]));
        lam(
            mynat(),
            lam(
                myz(),
                Expr::apps(rec("MyZ"), [qneg, on_min, ns_min, bvar(0)]),
            ),
        )
    };
    lam(
        myz(),
        Expr::apps(rec("MyZ"), [px, p_ofnat, p_negsucc, bvar(0)]),
    )
}
fn prop_code_z_ty() -> Expr {
    pi(
        myz(),
        pi(myz(), is_prop_type(&code_z_app(bvar(1), bvar(0)))),
    )
}

fn dr_z_motive_body(z: Expr) -> Expr {
    path_homog_at(
        &path_myz(z.clone(), z.clone()),
        Expr::apps(
            cst("decodeZ"),
            [z.clone(), z.clone(), Expr::app(cst("rZ"), z.clone())],
        ),
        refl_at(&z),
    )
}
fn dr_z_value() -> Expr {
    let motive = lam(myz(), dr_z_motive_body(bvar(0)));
    // ofNat m: ap (congOfNat m m) (drNat m)   [z,m]: m=0
    let on_min = lam(
        mynat(),
        ap_cong(
            &Expr::apps(cst("congOfNat"), [bvar(0), bvar(0)]),
            &Expr::app(cst("drNat"), bvar(0)),
        ),
    );
    let ns_min = lam(
        mynat(),
        ap_cong(
            &Expr::apps(cst("congNegSucc"), [bvar(0), bvar(0)]),
            &Expr::app(cst("drNat"), bvar(0)),
        ),
    );
    lam(
        myz(),
        Expr::apps(rec("MyZ"), [motive, on_min, ns_min, bvar(0)]),
    )
}
fn dr_z_ty() -> Expr {
    pi(myz(), dr_z_motive_body(bvar(0)))
}

fn int_env_isset_z() -> Environment {
    let mut env = int_env_isset_nat();
    let mut def = |name: &str, type_: Expr, value: Expr, red: bool| {
        env.add_decl(Declaration::Definition {
            name: nm(name),
            level_params: vec![],
            type_,
            value,
            is_reducible: red,
        })
        .unwrap_or_else(|e| panic!("{name} should type-check and register: {e:?}"));
    };
    def(
        "congOfNat",
        cong_ctor_ty(mynat(), myz(), "MyZ.ofNat"),
        cong_ctor_value(mynat(), "MyZ.ofNat"),
        true,
    );
    def(
        "congNegSucc",
        cong_ctor_ty(mynat(), myz(), "MyZ.negSucc"),
        cong_ctor_value(mynat(), "MyZ.negSucc"),
        true,
    );
    def("codeZ", code_z_ty(), code_z_value(), true);
    def("rZ", r_z_ty(), r_z_value(), true);
    def("decodeZ", decode_z_ty(), decode_z_value(), true);
    def("propCodeZ", prop_code_z_ty(), prop_code_z_value(), false);
    def("drZ", dr_z_ty(), dr_z_value(), false);
    env
}

/// **`isSet MyZ`** — the headline deliverable: a PROVED, axiom-free term via the
/// encode-decode criterion over the propositional code family `codeZ` (built on
/// `codeNat`). Every subterm type-checked on registration (no `sorry`, no axiom).
#[test]
fn test_isset_myz_is_proved() {
    let env = int_env_isset_z();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let isset = is_set_from_encode_decode(
        type_level(),
        &myz(),
        &cst("codeZ"),
        &cst("rZ"),
        &cst("decodeZ"),
        &cst("propCodeZ"),
        &cst("drZ"),
    );
    let (ty, _) = tc
        .infer_type_with_cert(&isset)
        .expect("isSet MyZ should type-check (encode-decode, axiom-free)");
    assert!(
        tc.is_def_eq(&ty, &is_set_type(&myz())),
        "isSet MyZ; got {ty:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 18 — FULLY-CLOSED `windingIsEquiv : isEquiv winding` (quasi-inverse caveat GONE)
//
// Apply the PROVED, axiom-free engine `biInvToIsEquivOnSet` to the PROVED,
// axiom-free `isSet MyZ` — yielding `isEquiv winding` with NO remaining hypothesis.
// This upgrades the milestone `windingEquiv` (a quasi-inverse `(f,g,η,ε)`) to a
// genuine contractible-fibre equivalence. No `sorry`, no axiom for `isSet MyZ`.
// ══════════════════════════════════════════════════════════════════════════════

fn isset_myz_term() -> Expr {
    is_set_from_encode_decode(
        type_level(),
        &myz(),
        &cst("codeZ"),
        &cst("rZ"),
        &cst("decodeZ"),
        &cst("propCodeZ"),
        &cst("drZ"),
    )
}

/// `int_env_isset_z` + registered `isSetMyZ`, `isSetMyNat`, and the FULLY-CLOSED
/// `windingIsEquiv : isEquiv winding`. Every `add_decl` here type-checks a genuine
/// closed proof term — if `isSet MyZ` or the upgrade were unsound they would fail.
fn int_env_winding_isequiv() -> Environment {
    let mut env = int_env_isset_z();
    env.add_decl(Declaration::Definition {
        name: nm("isSetMyNat"),
        level_params: vec![],
        type_: is_set_type(&mynat()),
        value: is_set_from_encode_decode(
            type_level(),
            &mynat(),
            &cst("codeNat"),
            &cst("rNat"),
            &cst("decodeNat"),
            &cst("propCodeNat"),
            &cst("drNat"),
        ),
        is_reducible: false,
    })
    .expect("isSetMyNat : isSet MyNat should type-check (encode-decode, axiom-free)");
    env.add_decl(Declaration::Definition {
        name: nm("isSetMyZ"),
        level_params: vec![],
        type_: is_set_type(&myz()),
        value: isset_myz_term(),
        is_reducible: false,
    })
    .expect("isSetMyZ : isSet MyZ should type-check (encode-decode, axiom-free)");
    // windingIsEquiv := biInvToIsEquivOnSet isSetMyZ winding intLoop decodeEncode encodeDecode.
    let winding_is_equiv = is_equiv_from_quasi_inv_on_set(
        type_level(),
        &omega_s1(),
        &myz(),
        &cst("isSetMyZ"),
        &cst("winding"),
        &cst("intLoop"),
        &cst("decodeEncode"),
        &cst("encodeDecode"),
    );
    env.add_decl(Declaration::Definition {
        name: nm("windingIsEquiv"),
        level_params: vec![],
        type_: is_equiv_type(type_level(), &omega_s1(), &myz(), &cst("winding")),
        value: winding_is_equiv,
        is_reducible: false,
    })
    .expect("windingIsEquiv : isEquiv winding should type-check FULLY CLOSED (no hypothesis)");
    env
}

/// THE CLOSURE: `windingIsEquiv : isEquiv winding` type-checks **fully closed** —
/// the quasi-inverse caveat on π₁(S¹)=ℤ is removed entirely. The term has NO
/// remaining `isSet MyZ` hypothesis (it is supplied by the proved `isSetMyZ`), NO
/// axiom for `isSet MyZ`, NO `sorry`.
#[test]
fn test_winding_isequiv_fully_closed() {
    let env = int_env_winding_isequiv();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // The registered `windingIsEquiv` re-infers to exactly `isEquiv winding`.
    let (ty, _) = tc
        .infer_type_with_cert(&cst("windingIsEquiv"))
        .expect("windingIsEquiv should type-check");
    let expected = is_equiv_type(type_level(), &omega_s1(), &myz(), &cst("winding"));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "windingIsEquiv : isEquiv winding (fully closed, quasi-inverse caveat removed); got {ty:?}"
    );

    // It is a CLOSED term: no free variables, no remaining hypothesis. Confirm the
    // type is genuinely `isEquiv winding` (a Π over `Ω S¹` into `isContr (fiber …)`),
    // i.e. NOT a `isSet MyZ → …` arrow.
    let whnf_ty = tc.whnf(&ty);
    assert!(
        matches!(whnf_ty.kind(), ExprKind::Pi(..)),
        "isEquiv winding is a Π (y:Ω S¹) → isContr (fiber winding y); got {whnf_ty:?}"
    );
    // And `windingEquiv` (the quasi-inverse milestone record) still type-checks.
    let winding_equiv = Expr::apps(
        Expr::const_(nm("Equiv.mk"), vec![type_level()]),
        [
            omega_s1(),
            myz(),
            cst("winding"),
            cst("intLoop"),
            cst("decodeEncode"),
            cst("encodeDecode"),
        ],
    );
    let (we_ty, _) = tc
        .infer_type_with_cert(&winding_equiv)
        .expect("windingEquiv (quasi-inverse) still type-checks");
    assert!(tc.is_def_eq(
        &we_ty,
        &Expr::apps(
            Expr::const_(nm("Equiv"), vec![type_level()]),
            [omega_s1(), myz()]
        )
    ));
}
