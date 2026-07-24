// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Higher Inductive Type tests: the circle `S¹` (`base` + `loop`).
//!
//! `S¹` is declared (in Cubical mode) with a point constructor `base : S¹` and a
//! path constructor `loop : Path (λ _:I. S¹) base base`. The kernel must
//! generate the *dependent* eliminator
//!
//! ```text
//! S¹.rec : {C : S¹ → Sort u} → (cb : C base)
//!        → (cl : Path (λ i:I. C (loop @ i)) cb cb)
//!        → (x : S¹) → C x
//! ```
//!
//! with iota rules `S¹.rec C cb cl base ↝ cb` and
//! `S¹.rec C cb cl (loop @ i) ↝ cl @ i`, coherent at the endpoints
//! (`loop @ i0 = base`, so `cl @ i0 = cb`).
//!
//! Test (b) is the soundness check: the generated recursor TYPE is compared
//! (`is_def_eq`) against a hand-built copy of the intended type above. A wrong
//! recursor type is the failure mode for HIT soundness.

use super::*;
use crate::env::Declaration;
use crate::expr::{BinderInfo, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::TypeChecker;
use std::sync::Arc;

// ── Names ────────────────────────────────────────────────────────────────

fn s1() -> Name {
    Name::from_string("S1")
}
fn base() -> Name {
    Name::from_string("S1.base")
}
fn loop_() -> Name {
    Name::from_string("S1.loop")
}
fn rec() -> Name {
    Name::from_string("S1.rec")
}

// ── Cubical leaves ─────────────────────────────────────────────────────────

fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}
fn i0() -> Expr {
    Expr::from_kind(ExprKind::CubicalI0)
}
fn i1() -> Expr {
    Expr::from_kind(ExprKind::CubicalI1)
}
fn path_app(path: Expr, arg: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(path),
        arg: Arc::new(arg),
    })
}

// ── S¹ declaration ─────────────────────────────────────────────────────────

/// `loop : Path (λ _:I. S¹) base base`.
fn loop_ctor_type() -> Expr {
    let line = Expr::lam(BinderInfo::Default, interval(), Expr::const_(s1(), vec![]));
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(Expr::const_(base(), vec![])),
        right: Arc::new(Expr::const_(base(), vec![])),
    })
}

fn s1_decl() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: s1(),
            type_: Expr::type_(), // S¹ : Type (Sort 1)
            constructors: vec![
                Constructor {
                    name: base(),
                    type_: Expr::const_(s1(), vec![]),
                },
                Constructor {
                    name: loop_(),
                    type_: loop_ctor_type(),
                },
            ],
        }],
    }
}

fn s1_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.add_inductive(s1_decl())
        .expect("S¹ (base + loop) should declare without error");
    env
}

// ── Local witnesses (axioms) for the reduction tests ────────────────────────
//
// Concrete closed motive/point/path so the recursor can be applied and reduced
// without a fresh local context. Declaring `cl` as an axiom of `Path` type also
// exercises endpoint reduction (`loop @ i0 = base`), since that type only checks
// if `cb : (λ i. C (loop @ i)) i0 ≡ C base`.

fn c_name() -> Name {
    Name::from_string("hit.C")
}
fn cb_name() -> Name {
    Name::from_string("hit.cb")
}
fn cl_name() -> Name {
    Name::from_string("hit.cl")
}
fn j_name() -> Name {
    Name::from_string("hit.j")
}

fn c() -> Expr {
    Expr::const_(c_name(), vec![])
}
fn cb() -> Expr {
    Expr::const_(cb_name(), vec![])
}
fn cl() -> Expr {
    Expr::const_(cl_name(), vec![])
}

/// `S¹` env plus a concrete motive `C : S¹ → Type`, `cb : C base`,
/// `cl : Path (λ i. C (loop @ i)) cb cb`, and a neutral interval `j : I`.
fn s1_env_with_witnesses() -> Environment {
    let mut env = s1_env();

    // C : S¹ → Type
    env.add_decl(Declaration::Axiom {
        name: c_name(),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(s1(), vec![]),
            Expr::type_(),
        ),
    })
    .expect("declare motive C");

    // cb : C base
    env.add_decl(Declaration::Axiom {
        name: cb_name(),
        level_params: vec![],
        type_: Expr::app(c(), Expr::const_(base(), vec![])),
    })
    .expect("declare cb : C base");

    // cl : Path (λ i. C (loop @ i)) cb cb
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(c(), path_app(Expr::const_(loop_(), vec![]), Expr::bvar(0))),
    );
    let cl_ty = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(cb()),
        right: Arc::new(cb()),
    });
    env.add_decl(Declaration::Axiom {
        name: cl_name(),
        level_params: vec![],
        type_: cl_ty,
    })
    .expect("declare cl : Path (λ i. C (loop @ i)) cb cb (exercises endpoint reduction)");

    // j : I
    env.add_decl(Declaration::Axiom {
        name: j_name(),
        level_params: vec![],
        type_: interval(),
    })
    .expect("declare neutral interval j : I");

    env
}

/// `S¹.rec.{1} C cb cl <major>`.
fn rec_apply(major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(rec(), vec![Level::succ(Level::zero())]),
        [c(), cb(), cl(), major],
    )
}

/// Hand-built intended recursor type — built from the spec, NOT from kernel
/// output. `u` is the motive universe parameter (read off the generated
/// recursor purely for alpha-naming; the *structure* is independent).
///
/// ```text
/// {C : S¹ → Sort u} → (cb : C base)
///   → (cl : Path (λ i:I. C (loop @ i)) cb cb) → (x : S¹) → C x
/// ```
fn expected_s1_rec_type(u: &Name) -> Expr {
    let s1c = Expr::const_(s1(), vec![]);

    // C : S¹ → Sort u
    let c_ty = Expr::pi(
        BinderInfo::Default,
        s1c.clone(),
        Expr::sort(Level::param(u.clone())),
    );

    // cb : C base                          (C = BVar 0)
    let cb_ty = Expr::app(Expr::bvar(0), Expr::const_(base(), vec![]));

    // cl : Path (λ i. C (loop @ i)) cb cb  (outside λ: cb = BVar 0, C = BVar 1;
    //                                       under λ: i = BVar 0, C = BVar 2)
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(
            Expr::bvar(2),
            path_app(Expr::const_(loop_(), vec![]), Expr::bvar(0)),
        ),
    );
    let cl_ty = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(Expr::bvar(0)),
        right: Arc::new(Expr::bvar(0)),
    });

    // x : S¹  ;  body : C x                (C = BVar 3, x = BVar 0)
    let body = Expr::app(Expr::bvar(3), Expr::bvar(0));

    Expr::pi(
        BinderInfo::Implicit,
        c_ty,
        Expr::pi(
            BinderInfo::Default,
            cb_ty,
            Expr::pi(
                BinderInfo::Default,
                cl_ty,
                Expr::pi(BinderInfo::Default, s1c, body),
            ),
        ),
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// (a) S¹ declares without error
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_s1_declares_without_error() {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.add_inductive(s1_decl())
        .expect("S¹ (base + loop) should declare without error");
    assert!(
        env.get_recursor(&rec()).is_some(),
        "S¹.rec should be generated"
    );
    assert!(env.get_constructor(&base()).is_some(), "base constructor");
    assert!(env.get_constructor(&loop_()).is_some(), "loop constructor");

    // noConfusion is SKIPPED for HITs (constructor injectivity is unsound for a
    // path constructor — one cannot prove `base ≠ loop @ i`).
    assert!(
        env.get_const(&Name::from_string("S1.noConfusion"))
            .is_none(),
        "S1.noConfusion must NOT be generated (path constructor)"
    );
    // structural casesOn / recOn are NOT generated, consistently with `∥A∥` and
    // `Susp` — no HIT exposes structural casesOn/recOn through a path constructor.
    // (S¹ elimination goes through the dependent `S¹.rec`; the structural pair is
    // unused, and we do not ship untested trusted recursors. See the skip guard
    // in `inductive_builder.rs`, gated on `has_path_constructor`.)
    assert!(
        env.get_recursor(&Name::from_string("S1.casesOn")).is_none(),
        "S1.casesOn must NOT be generated (path constructor)"
    );
    assert!(
        env.get_recursor(&Name::from_string("S1.recOn")).is_none(),
        "S1.recOn must NOT be generated (path constructor)"
    );

    // Late Eq/HEq initialization invokes noConfusion regeneration. The repair
    // path must apply the same block-level HIT exclusion as initial generation,
    // rather than reconstructing S1 as an ordinary singleton inductive.
    env.init_eq()
        .expect("late Eq initialization in Cubical mode");
    env.init_heq()
        .expect("late HEq initialization in Cubical mode");
    let report = env.regenerate_missing_no_confusion_with_report();
    for suffix in ["noConfusionType", "noConfusion"] {
        assert!(
            env.get_const(&Name::from_string(&format!("S1.{suffix}")))
                .is_none(),
            "S1.{suffix} must remain absent after every late repair pass"
        );
    }
    assert!(report.diagnostics.iter().any(|diagnostic| {
        matches!(
            &diagnostic.issue,
            NoConfusionRegenerationIssue::HigherInductive { member }
                if member == &s1()
        )
    }));
}

// ═══════════════════════════════════════════════════════════════════════════
// (b) Recursor TYPE correctness — the key soundness test
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_s1_recursor_type_is_the_intended_dependent_eliminator() {
    let env = s1_env();
    let rec_val = env.get_recursor(&rec()).expect("S¹.rec");

    // Motive universe param (for alpha-correct comparison of `Sort u`).
    let u = rec_val
        .level_params
        .first()
        .expect("S¹.rec must carry a motive universe parameter")
        .clone();

    let expected = expected_s1_rec_type(&u);
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    assert!(
        tc.is_def_eq(&rec_val.type_, &expected),
        "generated S¹.rec type is NOT the intended dependent eliminator\n\
         generated:\n{:#?}\n\nexpected:\n{:#?}",
        rec_val.type_,
        expected,
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (c) S¹.rec C cb cl base ↝ cb
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_s1_rec_base_reduces_to_cb() {
    let env = s1_env_with_witnesses();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let reduced = tc.whnf(&rec_apply(Expr::const_(base(), vec![])));
    assert!(
        tc.is_def_eq(&reduced, &cb()),
        "S¹.rec C cb cl base should reduce to cb, got {reduced:#?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (d) Boundary coherence: S¹.rec C cb cl (loop @ i0)/(loop @ i1) both ≡ cb
//     (and agree with the base rule's result)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_s1_rec_loop_endpoints_boundary_coherence() {
    let env = s1_env_with_witnesses();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let base_rule_result = tc.whnf(&rec_apply(Expr::const_(base(), vec![])));

    for (label, endpoint) in [("i0", i0()), ("i1", i1())] {
        let loop_at_e = path_app(Expr::const_(loop_(), vec![]), endpoint);
        let reduced = tc.whnf(&rec_apply(loop_at_e));

        assert!(
            tc.is_def_eq(&reduced, &cb()),
            "S¹.rec C cb cl (loop @ {label}) must equal cb (boundary), got {reduced:#?}",
        );
        assert!(
            tc.is_def_eq(&reduced, &base_rule_result),
            "boundary coherence: S¹.rec C cb cl (loop @ {label}) must agree with the base rule",
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (e) S¹.rec C cb cl (loop @ j) ↝ cl @ j  (neutral interval j)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_s1_rec_loop_neutral_reduces_to_cl_at_j() {
    let env = s1_env_with_witnesses();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let j = Expr::const_(j_name(), vec![]);
    let reduced = tc.whnf(&rec_apply(path_app(
        Expr::const_(loop_(), vec![]),
        j.clone(),
    )));
    let cl_at_j = path_app(cl(), j);

    assert!(
        tc.is_def_eq(&reduced, &cl_at_j),
        "S¹.rec C cb cl (loop @ j) should reduce to cl @ j, got {reduced:#?}",
    );
}
