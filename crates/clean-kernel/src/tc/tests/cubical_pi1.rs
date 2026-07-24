// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for the **computational heart of π₁(S¹) = ℤ**: the
//! *winding number*.
//!
//! These build on the structured `Equiv` (record `{f,g,η,ε}` via `Equiv.mk`, with
//! `Equiv.fwd` the *computing* first projection — `Equiv.fwd (Equiv.mk f …) ↝ f`)
//! and on the existing univalence computation rule
//! `transport (ua e) x ↝ Equiv.fwd e x`. Composing the two, the forward map now
//! reduces **concretely**:
//!
//! ```text
//! transport (ua (Equiv.mk f g η ε)) x  ↝  Equiv.fwd (Equiv.mk f g η ε) x  ↝  f x
//! ```
//!
//! With `sucEquiv := Equiv.mk succ pred predsucc succpred : Equiv ℤ ℤ` (the
//! successor automorphism of ℤ), the winding number computes:
//!
//! ```text
//! transport (ua sucEquiv) (0:ℤ)  ↝  succ 0  ( = 1)
//! ```
//!
//! and, through the universal cover `helix := S¹.rec {λ_.Type} ℤ (ua sucEquiv)`,
//!
//! ```text
//! winding loop := transport (λ i. helix (loop@i)) (0:ℤ)
//!               ↝ transport (ua sucEquiv) 0  ↝  succ 0  ( = 1).
//! ```
//!
//! Everything is built directly as kernel `Expr`s over the reserved Glue/Equiv
//! axioms ([`register_glue_axioms`]) and cofibration faces
//! ([`register_kan_system_axioms`]) — plain `Const`/`App` spines, no new
//! `ExprKind` variant, no certificate change.

use super::*;

use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{
    glue_ua, path_compose, path_refl, register_glue_axioms, register_kan_system_axioms,
};
use std::sync::Arc;

// ── Leaves ──────────────────────────────────────────────────────────────────

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
/// The level of `Type` (= `Sort 1`); the universe `Equiv.{1}`/`Glue.{1}` live at.
fn type_level() -> Level {
    Level::succ(Level::zero())
}
fn path(line: Expr, left: Expr, right: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(left),
        right: Arc::new(right),
    })
}

// ── ℤ (MyInt) and the successor automorphism ────────────────────────────────

fn myint() -> Expr {
    cst("MyInt")
}
fn zero() -> Expr {
    cst("MyInt.zero")
}
/// `succ 0` — the integer literal `1` (literally the successor of `0`).
fn one() -> Expr {
    Expr::app(cst("succ"), zero())
}
/// `succ (succ 0)` — the integer literal `2`.
fn two() -> Expr {
    Expr::app(cst("succ"), one())
}

/// `predsucc : (n:MyInt) → Path (λ_:I. MyInt) (pred (succ n)) n`  (g∘f ~ id).
fn predsucc_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        myint(), // n : MyInt
        path(
            Expr::lam(BinderInfo::Default, interval(), myint()), // λ_:I. MyInt
            Expr::app(cst("pred"), Expr::app(cst("succ"), Expr::bvar(0))), // pred (succ n)
            Expr::bvar(0),                                       // n
        ),
    )
}
/// `succpred : (n:MyInt) → Path (λ_:I. MyInt) (succ (pred n)) n`  (f∘g ~ id).
fn succpred_ty() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        myint(),
        path(
            Expr::lam(BinderInfo::Default, interval(), myint()),
            Expr::app(cst("succ"), Expr::app(cst("pred"), Expr::bvar(0))), // succ (pred n)
            Expr::bvar(0),
        ),
    )
}

/// `sucEquiv := Equiv.mk.{1} ℤ ℤ succ pred predsucc succpred : Equiv ℤ ℤ`.
fn suc_equiv() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Equiv.mk"), vec![type_level()]),
        [
            myint(),
            myint(),
            cst("succ"),
            cst("pred"),
            cst("predsucc"),
            cst("succpred"),
        ],
    )
}

/// `Equiv.mk.{1} A B f g η ε` — a general structured equivalence.
fn equiv_mk(a: &Expr, b: &Expr, f: &Expr, g: &Expr, eta: &Expr, eps: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Equiv.mk"), vec![type_level()]),
        [
            a.clone(),
            b.clone(),
            f.clone(),
            g.clone(),
            eta.clone(),
            eps.clone(),
        ],
    )
}

/// `Equiv.fwd.{1} A B e` — the (now computing) forward-map projection.
fn equiv_fwd(a: &Expr, b: &Expr, e: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Equiv.fwd"), vec![type_level()]),
        [a.clone(), b.clone(), e.clone()],
    )
}

/// The `ua` coercion line `λ i. Glue B [(i=0)↦(A,e), (i=1)↦(B, Equiv.idEquiv B)]`
/// — the body of `glue_ua e` rewrapped from a path-lam into a `coe`-shaped lambda,
/// so `transport (ua e) x = coe (ua-line) i0 i1 x`.
fn ua_line(a: &Expr, b: &Expr, e: &Expr, level: Level) -> Expr {
    let ua = glue_ua(a, b, e, level);
    let ExprKind::CubicalPathLam { body } = ua.kind() else {
        panic!("glue_ua must produce a CubicalPathLam");
    };
    Expr::lam(BinderInfo::Default, interval(), body.as_ref().clone())
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

// ── Environments ────────────────────────────────────────────────────────────

/// Register `succ`/`pred` and the inverse-homotopy coherences `predsucc`/`succpred`
/// into a Cubical env that already has the Kan + Glue axioms and the MyInt type.
fn declare_int(env: &mut Environment) {
    // MyInt — an OPAQUE axiomatized type standing in for ℤ. Declared as an
    // *axiom* (NOT a single-constructor inductive) ON PURPOSE: a single nullary
    // constructor triggers structure-η, which collapses EVERY element to `zero`
    // (`0 ≡ 1 ≡ 2`), making the winding `is_def_eq` assertions VACUOUS. As an
    // opaque axiom there is no η, so `zero`, `succ zero`, `succ (succ zero)` are
    // DISTINCT neutral terms and `winding loop ≡ 1`, `≡ 2` are MEANINGFUL.
    // `succ`/`pred`/the inverse laws are axiomatized — all true of ℤ and jointly
    // satisfiable (e.g. the unit model succ=pred=id, η=ε=refl) — consistency-preserving.
    let predsucc = predsucc_ty();
    let succpred = succpred_ty();
    let int_to_int = Expr::arrow(myint(), myint());
    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };
    axiom("MyInt", Expr::type_()); // opaque type — no structure-η collapse
    axiom("MyInt.zero", myint()); // the basepoint 0 : MyInt
    axiom("succ", int_to_int.clone());
    axiom("pred", int_to_int);
    axiom("predsucc", predsucc);
    axiom("succpred", succpred);
}

/// Cubical env: Kan + Glue axioms, plus ℤ with its successor automorphism.
fn pi1_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("register kan system axioms");
    register_glue_axioms(&mut env).expect("register glue axioms");
    declare_int(&mut env);
    env
}

/// `pi1_env` plus the circle `S¹` (`base` + `loop`), for the universal-cover
/// `helix` winding test.
fn pi1_env_with_s1() -> Environment {
    let mut env = pi1_env();
    let loop_ty = path(
        Expr::lam(BinderInfo::Default, interval(), cst("S1")), // λ_:I. S¹
        cst("S1.base"),
        cst("S1.base"),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("S1"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("S1.base"),
                    type_: cst("S1"),
                },
                Constructor {
                    name: Name::from_string("S1.loop"),
                    type_: loop_ty,
                },
            ],
        }],
    })
    .expect("S¹ should declare without error");
    env
}

/// A general structured-equivalence env: `A B : Type`, `f : A→B`, `g : B→A`, the
/// two coherences `eta`/`eps`, and a point `xa : A`.
fn generic_equiv_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("kan axioms");
    register_glue_axioms(&mut env).expect("glue axioms");

    // eta : (x:A) → Path (λ_:I. A) (g (f x)) x
    let eta_ty = Expr::pi(
        BinderInfo::Default,
        cst("A"),
        path(
            Expr::lam(BinderInfo::Default, interval(), cst("A")),
            Expr::app(cst("g"), Expr::app(cst("f"), Expr::bvar(0))),
            Expr::bvar(0),
        ),
    );
    // eps : (y:B) → Path (λ_:I. B) (f (g y)) y
    let eps_ty = Expr::pi(
        BinderInfo::Default,
        cst("B"),
        path(
            Expr::lam(BinderInfo::Default, interval(), cst("B")),
            Expr::app(cst("f"), Expr::app(cst("g"), Expr::bvar(0))),
            Expr::bvar(0),
        ),
    );
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
    axiom("f", Expr::arrow(cst("A"), cst("B")));
    axiom("g", Expr::arrow(cst("B"), cst("A")));
    axiom("eta", eta_ty);
    axiom("eps", eps_ty);
    axiom("xa", cst("A"));
    env
}

// ═════════════════════════════════════════════════════════════════════════════
// Anchor 1 — `Equiv.fwd (Equiv.mk f g η ε) ≡ f`  (the computing projection)
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn test_equiv_fwd_mk_computes_to_forward_map() {
    let env = generic_equiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let mk = equiv_mk(
        &cst("A"),
        &cst("B"),
        &cst("f"),
        &cst("g"),
        &cst("eta"),
        &cst("eps"),
    );
    let fwd = equiv_fwd(&cst("A"), &cst("B"), &mk);

    // β-rule: Equiv.fwd A B (Equiv.mk A B f g η ε) ↝ f.
    let reduct = tc.whnf(&fwd);
    assert!(
        tc.is_def_eq(&reduct, &cst("f")),
        "Equiv.fwd (Equiv.mk f g η ε) must reduce to f; got {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&fwd, &cst("f")),
        "Equiv.fwd (Equiv.mk f …) ≡ f definitionally"
    );

    // Type preservation: both sides infer to `A → B`.
    let (fwd_ty, _) = tc
        .infer_type_with_cert(&fwd)
        .expect("Equiv.fwd (mk …) should type-check");
    let (f_ty, _) = tc
        .infer_type_with_cert(&cst("f"))
        .expect("f should type-check");
    assert!(
        tc.is_def_eq(&fwd_ty, &f_ty),
        "Equiv.fwd β must preserve type: fwd : {fwd_ty:?}, f : {f_ty:?}"
    );
}

/// `Equiv.fwd (Equiv.idEquiv A) ↝ λ x:A. x` — the identity instance of the rule.
#[test]
fn test_equiv_fwd_idequiv_computes_to_identity() {
    let env = generic_equiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let id_equiv = Expr::app(
        Expr::const_(Name::from_string("Equiv.idEquiv"), vec![type_level()]),
        cst("A"),
    );
    let fwd = equiv_fwd(&cst("A"), &cst("A"), &id_equiv);
    let id_fn = Expr::lam(BinderInfo::Default, cst("A"), Expr::bvar(0)); // λ x:A. x

    let reduct = tc.whnf(&fwd);
    assert!(
        tc.is_def_eq(&reduct, &id_fn),
        "Equiv.fwd (Equiv.idEquiv A) must reduce to λx.x; got {reduct:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// Anchor 2 — concrete `ua` transport: `transport (ua (Equiv.mk f …)) x ↝ f x`
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn test_transport_ua_mk_computes_concretely() {
    let env = generic_equiv_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let mk = equiv_mk(
        &cst("A"),
        &cst("B"),
        &cst("f"),
        &cst("g"),
        &cst("eta"),
        &cst("eps"),
    );
    let transport = transport_ua(&cst("A"), &cst("B"), &mk, &cst("xa"));
    let f_xa = Expr::app(cst("f"), cst("xa"));

    // (1) transport (ua (mk f …)) x  ↝  Equiv.fwd (mk f …) x  ↝  f x.
    let reduct = tc.whnf(&transport);
    assert!(
        tc.is_def_eq(&reduct, &f_xa),
        "transport (ua (mk f …)) x must reduce to f x; got {reduct:?}"
    );

    // (2) Type preservation: infer(transport) ≡ infer(f x) ≡ B.
    let (t_ty, _) = tc
        .infer_type_with_cert(&transport)
        .expect("transport (ua (mk …)) x should type-check");
    let (fx_ty, _) = tc
        .infer_type_with_cert(&f_xa)
        .expect("f x should type-check");
    assert!(
        tc.is_def_eq(&t_ty, &fx_ty),
        "the concrete ua rewrite must preserve type: lhs : {t_ty:?}, rhs : {fx_ty:?}"
    );
    assert!(
        tc.is_def_eq(&t_ty, &cst("B")),
        "transport (ua (mk f …)) x : B; got {t_ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// Anchor 3a — THE WINDING NUMBER (direct): `transport (ua sucEquiv) 0 ↝ 1`
// ═════════════════════════════════════════════════════════════════════════════

/// VACUITY GUARD: `MyInt` must NOT η-collapse — `0`, `1`, `2` must be DISTINCT.
/// If this fails, `MyInt` became a single-constructor inductive again (structure-η
/// collapses every element to `zero`), and EVERY `is_def_eq(reduct, one/two)`
/// winding assertion below is vacuous. See `declare_int`. This guard makes the
/// `π₁` "heart" claim falsifiable.
#[test]
fn test_myint_integers_are_distinct_else_winding_is_vacuous() {
    let env = pi1_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    assert!(
        !tc.is_def_eq(&zero(), &one()),
        "0 ≡ 1: MyInt η-collapsed — winding tests are VACUOUS"
    );
    assert!(
        !tc.is_def_eq(&one(), &two()),
        "1 ≡ 2: MyInt η-collapsed — winding tests are VACUOUS"
    );
    assert!(
        !tc.is_def_eq(&zero(), &two()),
        "0 ≡ 2: MyInt η-collapsed — winding tests are VACUOUS"
    );
}

#[test]
fn test_winding_transport_sucequiv_zero_is_one() {
    let env = pi1_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // First confirm `sucEquiv` itself type-checks as `Equiv ℤ ℤ` (so the η/ε
    // coherence fields really line up against `Equiv.mk`'s record type).
    let (se_ty, _) = tc
        .infer_type_with_cert(&suc_equiv())
        .expect("sucEquiv should type-check");
    let expected_equiv = Expr::apps(
        Expr::const_(Name::from_string("Equiv"), vec![type_level()]),
        [myint(), myint()],
    );
    assert!(
        tc.is_def_eq(&se_ty, &expected_equiv),
        "sucEquiv : Equiv ℤ ℤ; got {se_ty:?}"
    );

    // THE KEY COMPUTATION: transport (ua sucEquiv) 0 ↝ succ 0 (= 1).
    let transport = transport_ua(&myint(), &myint(), &suc_equiv(), &zero());
    let reduct = tc.whnf(&transport);
    assert!(
        tc.is_def_eq(&reduct, &one()),
        "transport (ua sucEquiv) 0 must reduce to succ 0 (= 1); got {reduct:?}"
    );

    // Type preservation: the winding number lives in ℤ.
    let (t_ty, _) = tc
        .infer_type_with_cert(&transport)
        .expect("transport (ua sucEquiv) 0 should type-check");
    assert!(
        tc.is_def_eq(&t_ty, &myint()),
        "winding number : ℤ; got {t_ty:?}"
    );

    // Iterating the successor-transport twice gives 2 (the equivalence composes).
    // NOTE: this is *iterated single transport*, not `winding (loop ∙ loop)` — see
    // the module/test notes; genuine transport over a composite path would need a
    // coe-over-hcomp rule the kernel does not yet have.
    let transport2 = transport_ua(&myint(), &myint(), &suc_equiv(), &reduct);
    let reduct2 = tc.whnf(&transport2);
    assert!(
        tc.is_def_eq(&reduct2, &two()),
        "transport (ua sucEquiv) (transport (ua sucEquiv) 0) must reduce to 2; got {reduct2:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// Anchor 3b — THE WINDING NUMBER through the universal cover `helix`:
//             `winding loop := transport (λ i. helix (loop@i)) 0 ↝ 1`
// ═════════════════════════════════════════════════════════════════════════════

/// `helix (loop @ i)` with the interval `i = BVar(0)`, where
/// `helix := S¹.rec.{2} (λ_:S¹. Type) ℤ (ua sucEquiv)`.
fn helix_loop_at_bvar0() -> Expr {
    let motive = Expr::lam(BinderInfo::Default, cst("S1"), Expr::type_()); // λ_:S¹. Type
    let ua = glue_ua(&myint(), &myint(), &suc_equiv(), type_level()); // ua sucEquiv : ℤ = ℤ
    let u2 = Level::succ(Level::succ(Level::zero())); // motive lands in Sort 2
    let rec = Expr::const_(Name::from_string("S1.rec"), vec![u2]);
    let loop_at_i = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(cst("S1.loop")),
        arg: Arc::new(Expr::bvar(0)),
    });
    // S¹.rec.{2} C cb cl (loop@i)  with  C = motive, cb = ℤ, cl = ua sucEquiv.
    Expr::apps(rec, [motive, myint(), ua, loop_at_i])
}

#[test]
fn test_winding_loop_via_universal_cover_is_one() {
    let env = pi1_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // winding loop := transport (λ i. helix (loop@i)) 0
    //              := coe (λ i. helix (loop@i)) i0 i1 0.
    let line = Expr::lam(BinderInfo::Default, interval(), helix_loop_at_bvar0());
    let winding = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(zero()),
    });

    // The reduction chain:
    //   coe (λ i. helix(loop@i)) i0 i1 0
    //     ↝ coe (λ i. (ua sucEquiv)@i) i0 i1 0   (S¹.rec loop-iota under the line)
    //     ↝ Equiv.fwd sucEquiv 0                 (univalence computation rule)
    //     ↝ succ 0  (= 1).                       (Equiv.fwd β on Equiv.mk)
    let reduct = tc.whnf(&winding);
    assert!(
        tc.is_def_eq(&reduct, &one()),
        "winding loop must reduce to succ 0 (= 1); got {reduct:?}"
    );

    // Type preservation: `winding loop : ℤ`.
    let (w_ty, _) = tc
        .infer_type_with_cert(&winding)
        .expect("winding loop should type-check");
    assert!(
        tc.is_def_eq(&w_ty, &myint()),
        "winding loop : ℤ; got {w_ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// Anchor 4 — no over-fire / soundness: `Equiv.fwd` on a NEUTRAL equiv stays stuck
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn test_equiv_fwd_on_neutral_equiv_stays_stuck() {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("kan axioms");
    register_glue_axioms(&mut env).expect("glue axioms");
    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name}: {e:?}"));
    };
    axiom("A", Expr::type_());
    axiom("B", Expr::type_());
    // `ene` is an opaque equivalence value — NOT built by `Equiv.mk`.
    axiom(
        "ene",
        Expr::apps(
            Expr::const_(Name::from_string("Equiv"), vec![type_level()]),
            [cst("A"), cst("B")],
        ),
    );

    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let fwd = equiv_fwd(&cst("A"), &cst("B"), &cst("ene"));

    // `Equiv.fwd A B ene` must stay stuck (head still `Equiv.fwd`): the β-rule
    // fires only when the equivalence argument is a literal `Equiv.mk`/`idEquiv`.
    let reduct = tc.whnf(&fwd);
    let ExprKind::Const(head, _) = reduct.get_app_fn().kind() else {
        panic!("Equiv.fwd on a neutral equiv must stay a Const-headed spine; got {reduct:?}");
    };
    assert_eq!(
        *head,
        Name::from_string("Equiv.fwd"),
        "Equiv.fwd on a neutral (non-mk) equiv must stay stuck; got head {head:?}"
    );
    // The neutral equivalence is still the third spine argument (unchanged) — no
    // forward map was fabricated.
    let args = reduct.get_app_args();
    assert!(
        args.len() == 3 && tc.is_def_eq(args[2], &cst("ene")),
        "Equiv.fwd on a neutral equiv must keep the equiv argument intact; got {reduct:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// Anchor 5 — the sound HIT-recursor Kan rule: `S¹.rec` pushes through `hcomp`
//            (non-dependent / constant motive ⇒ no correction term)
// ═════════════════════════════════════════════════════════════════════════════

fn s1() -> Expr {
    cst("S1")
}
fn s1_base() -> Expr {
    cst("S1.base")
}
fn s1_loop() -> Expr {
    cst("S1.loop")
}
/// `Sort 1`-level (the universe of `MyInt`/`S¹` themselves): `S¹.rec.{1}`.
fn level1() -> Level {
    Level::succ(Level::zero())
}

fn cofib_top() -> Expr {
    cst("Cofib.top")
}
fn cofib_eq1(arg: Expr) -> Expr {
    Expr::app(cst("Cofib.eq1"), arg)
}

/// `System.cons.{ℓ} A φ head tail` — one branch of the partial-element encoding.
fn system_cons(level: Level, a: Expr, face: Expr, head: Expr, tail: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("System.cons"), vec![level]),
        [a, face, head, tail],
    )
}
/// `System.nil.{ℓ} A` — the empty terminator of the system.
fn system_nil(level: Level, a: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("System.nil"), vec![level]),
        a,
    )
}

/// The **non-dependent** motive `C ≡ λ_:S¹. MyInt` (the constant motive `K = ℤ`).
fn const_motive_myint() -> Expr {
    Expr::lam(BinderInfo::Default, s1(), myint())
}

/// `S¹.rec.{1} (λ_:S¹. MyInt) 0 (refl 0) <major>` — the eliminator at the constant
/// motive `K = ℤ` (`cb = 0 : ℤ`, `cl = refl 0 : Path (λ_. ℤ) 0 0`).
fn s1_rec_const_myint(major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("S1.rec"), vec![level1()]),
        [const_motive_myint(), zero(), path_refl(&zero()), major],
    )
}

/// Test 1 — **boundary coherence** (the key soundness check): on a *total* face the
/// pushed hcomp agrees with the on-a-face value, i.e.
/// `S¹.rec {λ_.K} cb cl (hcomp {S¹} [⊤ ↦ u] base) ≡ S¹.rec {λ_.K} cb cl (u i1)`.
#[test]
fn test_s1_rec_over_hcomp_total_face_boundary_coherence() {
    let env = pi1_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // u = λ_:I. S¹.base ; base = S¹.base ; the single face is ⊤.
    let u_fn = Expr::lam(BinderInfo::Default, interval(), s1_base());
    let system = system_cons(
        level1(),
        s1(),
        cofib_top(),
        u_fn.clone(),
        system_nil(level1(), s1()),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(cofib_top()),
        u: Arc::new(system),
        base: Arc::new(s1_base()),
    });

    let lhs = s1_rec_const_myint(hcomp);
    let rhs = s1_rec_const_myint(Expr::app(u_fn, i1())); // S¹.rec … (u i1)

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "S¹.rec over a total-face hcomp must agree with the on-a-face value (u i1)"
    );
    // And both land on `cb = 0` (the on-a-face value `u i1 = S¹.base` ↝ cb).
    let lhs_whnf = tc.whnf(&lhs);
    assert!(
        tc.is_def_eq(&lhs_whnf, &zero()),
        "S¹.rec over [⊤ ↦ λ_.base] base must reduce to cb = 0; got {lhs_whnf:?}"
    );
}

/// Test 2 — **the rule fires** on a *neutral* face and is **type-preserving**.
/// With a neutral interval `j`, `S¹.rec {λ_.ℤ} 0 (refl 0) (hcomp {S¹} [(j=1) ↦ u] base)`
/// pushes to `hcomp {ℤ} [(j=1) ↦ λk. recf (u k)] (recf base)`, and both the redex
/// and its reduct infer to `ℤ`.
#[test]
fn test_s1_rec_over_hcomp_neutral_face_pushes_and_preserves_type() {
    let mut env = pi1_env_with_s1();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("jI"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("declare neutral interval j : I");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let face = cofib_eq1(cst("jI")); // (j = 1) — a neutral cofibration ⇒ hcomp stuck
    let u_fn = Expr::lam(BinderInfo::Default, interval(), s1_base());
    let system = system_cons(
        level1(),
        s1(),
        face.clone(),
        u_fn,
        system_nil(level1(), s1()),
    );
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(s1()),
        phi: Arc::new(face),
        u: Arc::new(system),
        base: Arc::new(s1_base()),
    });
    let elim = s1_rec_const_myint(hcomp);

    // The recursor pushes through the stuck hcomp, landing in a hcomp at the
    // constant motive K = ℤ (proving the new rule fired).
    let reduct = tc.whnf(&elim);
    let ExprKind::CubicalHComp { ty, .. } = reduct.kind() else {
        panic!("S¹.rec over a neutral hcomp must push to a hcomp at K; got {reduct:?}");
    };
    assert!(
        tc.is_def_eq(ty, &myint()),
        "the pushed hcomp must be at the constant motive K = ℤ; got ty {ty:?}"
    );

    // Type preservation: infer(redex) ≡ infer(reduct) ≡ ℤ.
    let (elim_ty, _) = tc
        .infer_type_with_cert(&elim)
        .expect("S¹.rec over hcomp should type-check");
    let (reduct_ty, _) = tc
        .infer_type_with_cert(&reduct)
        .expect("the pushed hcomp should type-check");
    assert!(
        tc.is_def_eq(&elim_ty, &reduct_ty),
        "recursor-over-hcomp must preserve type: redex : {elim_ty:?}, reduct : {reduct_ty:?}"
    );
    assert!(
        tc.is_def_eq(&elim_ty, &myint()),
        "result of S¹.rec at the constant ℤ motive : ℤ; got {elim_ty:?}"
    );
}

/// Test 3 — `winding (loop ∙ loop)` **COMPUTES** to `succ (succ 0)` (= 2) via the
/// general CCHM `transp`-over-`Glue` rule. The chain is: recursor-over-`hcomp`
/// pushes `helix` through the `loop∙loop` `hcomp` and loop-β turns it into the
/// `Type`-composite of `ua sucEquiv` (Deliverable A ⇒ an explicit `Glue` line);
/// the outer `coe` over that `Glue` line then fires the genuine transp-over-`Glue`
/// rule (`unglue` the base → coerce along the base line → the `i1`-cell's backward
/// map), iterating the successor twice. Over the **opaque** `MyInt` (an axiom, no
/// structure-η), `0`, `succ 0`, `succ (succ 0)` are DISTINCT neutral terms, so the
/// `≡ 2` / `≢ 0` / `≢ 1` assertions are MEANINGFUL — this is the unsound-shortcut's
/// opposite: the value is the genuine iterated transport, not an over-identification.
#[test]
fn test_winding_loop_compose_loop_computes_to_two() {
    let env = pi1_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // loop ∙ loop : Path (λ_. S¹) base base  (its body is a stuck hcomp).
    let loop_sq = path_compose(&s1(), level1(), &s1_loop(), &s1_loop());

    // winding (loop∙loop) := coe (λ i. helix ((loop∙loop) @ i)) i0 i1 0
    //   with helix := S¹.rec.{2} (λ_:S¹. Type) ℤ (ua sucEquiv).
    let motive = Expr::lam(BinderInfo::Default, s1(), Expr::type_());
    let ua = glue_ua(&myint(), &myint(), &suc_equiv(), type_level());
    let u2 = Level::succ(Level::succ(Level::zero()));
    let rec = Expr::const_(Name::from_string("S1.rec"), vec![u2]);
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(loop_sq),
        arg: Arc::new(Expr::bvar(0)),
    });
    let helix_body = Expr::apps(rec, [motive, myint(), ua, major]);
    let line = Expr::lam(BinderInfo::Default, interval(), helix_body);
    let winding = Expr::from_kind(ExprKind::CubicalCoe {
        ty: Arc::new(line),
        r: Arc::new(i0()),
        s: Arc::new(i1()),
        base: Arc::new(zero()),
    });

    // It computes to `succ (succ 0)` (= 2) — the iterated successor-transport.
    let reduct = tc.whnf(&winding);
    assert!(
        tc.is_def_eq(&reduct, &two()),
        "winding (loop∙loop) must compute to succ (succ 0) (= 2); got {reduct:?}"
    );
    // NON-VACUITY (opaque MyInt ⇒ no structure-η): 2 ≢ 0, 2 ≢ 1.
    assert!(
        !tc.is_def_eq(&reduct, &zero()),
        "winding (loop∙loop) ≡ 0 — MyInt η-collapsed, the test is VACUOUS"
    );
    assert!(
        !tc.is_def_eq(&reduct, &one()),
        "winding (loop∙loop) ≡ 1 — wrong winding number"
    );

    // Type preservation: the winding number lives in MyInt.
    let (w_ty, _) = tc
        .infer_type_with_cert(&winding)
        .expect("winding (loop∙loop) should type-check as a transport");
    assert!(
        tc.is_def_eq(&w_ty, &myint()),
        "winding (loop∙loop) : MyInt; got {w_ty:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// Anchor 6 — ap-FUNCTORIALITY for the universal cover `helix`
//            (`ap helix (p ∙ q) ≡ (ap helix p) ∙ (ap helix q)`), the SOUND
//            companion of `winding(loop²)`: NO transport / NO `coe`-over-`hcomp`.
//
// `ap helix p := <i> helix (p @ i)` is the action of `helix` on a *path* — a path
// in the universe, NOT a transport. It computes **purely** by the two already-
// landed rules:
//   • the HIT path-constructor iota (loop β): `helix (loop @ r) ↝ (ua sucEquiv) @ r`,
//   • the recursor-over-`hcomp` rule (constant motive `C ≡ λ_.Type`, no correction):
//     `helix (hcomp {S¹} [φ↦u] base) ↝ hcomp {Type} [φ↦λj. helix(u j)] (helix base)`.
// Pushing `helix` through the `hcomp` that *is* `loop ∙ loop` and loop-β-reducing
// each tube turns the inner `S¹`-composite into exactly the `Type`-composite of
// `ua sucEquiv` with itself. This needs no `coe`-over-`hcomp` (the unsound
// transport-over-composition rule), so — unlike `winding(loop²)` — it DOES compute.
// ═════════════════════════════════════════════════════════════════════════════

/// `ua sucEquiv : ℤ = ℤ` — the univalence path used as `helix`'s loop case `cl`.
fn ua_suc() -> Expr {
    glue_ua(&myint(), &myint(), &suc_equiv(), type_level())
}
/// `S¹.rec.{2} (λ_:S¹. Type) ℤ (ua sucEquiv) <major>` — `helix` applied to `major`.
fn helix_applied(major: Expr) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, s1(), Expr::type_()); // λ_:S¹. Type
    let u2 = Level::succ(Level::succ(Level::zero())); // motive target Sort 2
    let rec = Expr::const_(Name::from_string("S1.rec"), vec![u2]);
    Expr::apps(rec, [motive, myint(), ua_suc(), major])
}
/// `ap helix p := <i> helix (p @ i)` — the action of `helix` on the path `p`.
fn ap_helix(p: Expr) -> Expr {
    let major = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(p),
        arg: Arc::new(Expr::bvar(0)), // i = BVar(0) under the outer <i>
    });
    Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(helix_applied(major)),
    })
}

/// Test 1 — the **loop β-rule on the cover**, made explicit:
/// `ap helix loop ≡ ua sucEquiv`.  `ap helix loop := <i> helix (loop@i)`, and the
/// HIT path-constructor iota gives `helix (loop@i) ↝ (ua sucEquiv)@i`, so the
/// whole path-lam is `<i> (ua sucEquiv)@i ≡ ua sucEquiv` (path-η).
#[test]
fn test_ap_helix_loop_is_ua_sucequiv() {
    let env = pi1_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ap = ap_helix(s1_loop()); // <i> helix (loop@i)
    let ua = ua_suc(); // ua sucEquiv : ℤ = ℤ

    assert!(
        tc.is_def_eq(&ap, &ua),
        "ap helix loop must be def-eq to ua sucEquiv (loop β on the universal cover)"
    );

    // Type preservation: both are paths `ℤ = ℤ` in the universe.
    let (ap_ty, _) = tc
        .infer_type_with_cert(&ap)
        .expect("ap helix loop should type-check");
    let ExprKind::CubicalPath { left, right, .. } = ap_ty.kind() else {
        panic!("ap helix loop must infer to a Path; got {ap_ty:?}");
    };
    assert!(
        tc.is_def_eq(left, &myint()) && tc.is_def_eq(right, &myint()),
        "ap helix loop : ℤ = ℤ; got {left:?} = {right:?}"
    );
}

/// Test 2 — **THE TARGET**: `ap helix (loop ∙ loop) ≡ (ua sucEquiv) ∙ (ua sucEquiv)`.
///
/// `loop² := loop ∙ loop` is a `Path (λ_.S¹) base base` whose body is a `hcomp {S¹}`.
/// `ap helix loop² := <i> helix (loop²@i)` pushes `helix` through that `hcomp`
/// (recursor-over-`hcomp`, constant motive `λ_.Type` ⇒ no correction), and each
/// tube/base loop-β-reduces `helix (loop@·) ↝ (ua sucEquiv)@·`, yielding exactly
/// the `Type`-level `hcomp` that **is** `(ua sucEquiv) ∙ (ua sucEquiv)`. No
/// transport / `coe`-over-`hcomp` is involved — so this DOES compute.
#[test]
fn test_ap_helix_loop_squared_is_ua_compose_ua() {
    let env = pi1_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // loop² := loop ∙ loop : Path (λ_.S¹) base base.
    let loop_sq = path_compose(&s1(), level1(), &s1_loop(), &s1_loop());
    // ap helix loop² := <i> helix (loop²@i).
    let lhs = ap_helix(loop_sq);

    // RHS: (ua sucEquiv) ∙ (ua sucEquiv) : Path (λ_.Type) ℤ ℤ — a composite in the
    // universe. `Type = Sort 1 : Sort 2`, so the System lives at level 2 (the same
    // `k_sort` the recursor-over-hcomp push reads off `K = Type`).
    let u2 = Level::succ(Level::succ(Level::zero()));
    let rhs = path_compose(&Expr::type_(), u2, &ua_suc(), &ua_suc());

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "ap helix (loop ∙ loop) must be def-eq to (ua sucEquiv) ∙ (ua sucEquiv)"
    );
}

/// Test 3 — **type preservation**: `ap helix loop²` infers to a `Path` in the
/// universe with endpoints `ℤ = ℤ` (the line family is constant `λ_:I. Type`).
#[test]
fn test_ap_helix_loop_squared_infers_path_in_universe() {
    let env = pi1_env_with_s1();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let loop_sq = path_compose(&s1(), level1(), &s1_loop(), &s1_loop());
    let ap = ap_helix(loop_sq);

    let (ap_ty, _) = tc
        .infer_type_with_cert(&ap)
        .expect("ap helix loop² should type-check");
    let ExprKind::CubicalPath { ty, left, right } = ap_ty.kind() else {
        panic!("ap helix loop² must infer to a CubicalPath; got {ap_ty:?}");
    };
    // Endpoints: both ℤ (loop²@i0 ↝ base ↝ helix base = ℤ; symmetrically at i1).
    assert!(
        tc.is_def_eq(left, &myint()),
        "ap helix loop² left endpoint must be ℤ; got {left:?}"
    );
    assert!(
        tc.is_def_eq(right, &myint()),
        "ap helix loop² right endpoint must be ℤ; got {right:?}"
    );
    // Line family: constant `λ_:I. Type` (a path *in the universe*).
    let constant_type_line = Expr::lam(BinderInfo::Default, interval(), Expr::type_());
    assert!(
        tc.is_def_eq(ty, &constant_type_line),
        "ap helix loop² line family must be λ_:I. Type; got {ty:?}"
    );
}
