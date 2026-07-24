// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Higher Inductive Type tests: propositional truncation `∥A∥` — the SECOND
//! HIT (after S¹), demonstrating Clean's HIT support is not S¹-specific.
//!
//! `∥A∥` is declared (in Cubical mode) as a parametric HIT with a *point*
//! constructor `∥A∥.in : A → ∥A∥` and a *path* constructor
//! `∥A∥.squash : (x y : ∥A∥) → Path (λ _:I. ∥A∥) x y` (so `∥A∥` is a
//! proposition). The kernel must generate the sound **prop-restricted**
//! eliminator
//!
//! ```text
//! ∥A∥.rec : {A : Type} → {P : Sort u} → isProp P → (A → P) → ∥A∥ A → P
//! ```
//!
//! with iota `∥A∥.rec A P pP f (∥A∥.in a) ↝ f a` and the `squash` case
//! discharged by the supplied `isProp P` witness `pP`
//! (`∥A∥.rec … (squash x y @ i) ↝ pP (rec … x) (rec … y) @ i`), coherent at the
//! endpoints (`squash x y @ i0 = x`, so the path collapses to `rec … x`).
//!
//! Test (b) is the soundness check: the generated recursor TYPE is compared
//! (`is_def_eq`) against a hand-built copy of the intended type above — a wrong
//! recursor type is the failure mode for HIT soundness. `noConfusion` is skipped
//! (constructor injectivity is unsound for a path constructor).

use super::*;
use crate::env::Declaration;
use crate::expr::{BinderInfo, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::{is_prop_type, TypeChecker};
use std::sync::Arc;

// ── Names ────────────────────────────────────────────────────────────────────

fn trunc() -> Name {
    Name::from_string("Trunc")
}
fn trunc_in() -> Name {
    Name::from_string("Trunc.in")
}
fn trunc_squash() -> Name {
    Name::from_string("Trunc.squash")
}
fn rec() -> Name {
    Name::from_string("Trunc.rec")
}
fn two() -> Name {
    Name::from_string("Two")
}
fn t0() -> Name {
    Name::from_string("Two.t0")
}
fn t1() -> Name {
    Name::from_string("Two.t1")
}
fn pp() -> Name {
    Name::from_string("pP")
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
fn cst(name: Name) -> Expr {
    Expr::const_(name, vec![])
}
/// `Trunc A` for a closed `a`.
fn trunc_app(a: Expr) -> Expr {
    Expr::app(cst(trunc()), a)
}

// ── ∥A∥ declaration ──────────────────────────────────────────────────────────

/// `Trunc.in : {A : Type} → A → Trunc A`.
fn in_ctor_type() -> Expr {
    Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // A
            Expr::app(cst(trunc()), Expr::bvar(1)),
        ),
    )
}

/// `Trunc.squash : {A : Type} → (x y : Trunc A) → Path (λ _:I. Trunc A) x y`.
fn squash_ctor_type() -> Expr {
    // line: λ _:I. Trunc A   (A = BVar3 under [A, x, y, _i])
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(cst(trunc()), Expr::bvar(3)),
    );
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(Expr::bvar(1)),  // x
        right: Arc::new(Expr::bvar(0)), // y
    });
    Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cst(trunc()), Expr::bvar(0)), // x : Trunc A
            Expr::pi(
                BinderInfo::Default,
                Expr::app(cst(trunc()), Expr::bvar(1)), // y : Trunc A
                path,
            ),
        ),
    )
}

fn trunc_decl() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: trunc(),
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()), // Type → Type
            constructors: vec![
                Constructor {
                    name: trunc_in(),
                    type_: in_ctor_type(),
                },
                Constructor {
                    name: trunc_squash(),
                    type_: squash_ctor_type(),
                },
            ],
        }],
    }
}

/// A concrete 2-constructor target `Two : Type` with `t0`, `t1 : Two`.
fn two_decl() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: two(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: t0(),
                    type_: cst(two()),
                },
                Constructor {
                    name: t1(),
                    type_: cst(two()),
                },
            ],
        }],
    }
}

/// `Trunc` env: the truncation HIT plus a concrete `Two` target and an opaque
/// `pP : isProp Two` witness (its truth is irrelevant — like S¹'s opaque `cl`,
/// it only makes the recursor *applicable* so the iota can be exercised).
fn trunc_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.add_inductive(two_decl())
        .expect("Two should declare without error");
    env.add_inductive(trunc_decl())
        .expect("∥A∥ (in + squash) should declare without error");
    env.add_decl(Declaration::Axiom {
        name: pp(),
        level_params: vec![],
        type_: is_prop_type(&cst(two())),
    })
    .expect("opaque pP : isProp Two registers");
    env
}

/// `Sort 1` (the universe `Type`).
fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// `Trunc.in Two a`.
fn in_two(a: Expr) -> Expr {
    Expr::apps(cst(trunc_in()), [cst(two()), a])
}

/// `Trunc.rec.{1} Two Two pP f major` — eliminate into `Two` with `f : Two → Two`.
fn rec_apply(f: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(rec(), vec![lvl1()]),
        [cst(two()), cst(two()), cst(pp()), f, major],
    )
}

/// The identity map `λ (x:Two). x`, used as the non-vacuous `f : Two → Two`.
fn id_two() -> Expr {
    Expr::lam(BinderInfo::Default, cst(two()), Expr::bvar(0))
}

/// Hand-built INTENDED recursor type (built from the spec, NOT kernel output):
///
/// ```text
/// {A : Type} → {P : Sort u} → isProp P → (A → P) → Trunc A → P
/// ```
fn expected_trunc_rec_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // result P, depth [A,P,pP,f,major]: P = BVar3
    let result = Expr::bvar(3);
    // major : Trunc A   (A = BVar3 at depth [A,P,pP,f])
    let major = Expr::pi(
        BinderInfo::Default,
        Expr::app(cst(trunc()), Expr::bvar(3)),
        result,
    );
    // f : A → P   (depth [A,P,pP]: A=BVar2, P lifts to BVar2 under the arrow)
    let f = Expr::pi(
        BinderInfo::Default,
        Expr::arrow(Expr::bvar(2), Expr::bvar(2)),
        major,
    );
    // pP : isProp P   (depth [A,P]: P = BVar0)
    let pp_ty = Expr::pi(BinderInfo::Default, is_prop_type(&Expr::bvar(0)), f);
    // {P : Sort u}
    let p = Expr::pi(BinderInfo::Implicit, sort_u, pp_ty);
    // {A : Type}
    Expr::pi(BinderInfo::Implicit, Expr::type_(), p)
}

// ═══════════════════════════════════════════════════════════════════════════
// (a) ∥A∥ declares without error; rec + constructors are generated
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_trunc_declares_without_error() {
    let env = trunc_env();
    assert!(
        env.get_recursor(&rec()).is_some(),
        "Trunc.rec should be generated"
    );
    assert!(env.get_constructor(&trunc_in()).is_some(), "in constructor");
    assert!(
        env.get_constructor(&trunc_squash()).is_some(),
        "squash constructor"
    );
    // noConfusion is SKIPPED for HITs (constructor injectivity is unsound for a
    // path constructor).
    assert!(
        env.get_const(&Name::from_string("Trunc.noConfusion"))
            .is_none(),
        "Trunc.noConfusion must NOT be generated (path constructor)"
    );
    // casesOn / recOn are NOT generated (no structural recursion through squash).
    assert!(
        env.get_recursor(&Name::from_string("Trunc.casesOn"))
            .is_none(),
        "Trunc.casesOn must NOT be generated"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (b) Recursor TYPE correctness — the key soundness test
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_trunc_recursor_type_is_the_intended_prop_eliminator() {
    let env = trunc_env();
    let rec_val = env.get_recursor(&rec()).expect("Trunc.rec");

    let u = rec_val
        .level_params
        .first()
        .expect("Trunc.rec must carry a motive universe parameter")
        .clone();

    let expected = expected_trunc_rec_type(&u);
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    assert!(
        tc.is_def_eq(&rec_val.type_, &expected),
        "generated Trunc.rec type is NOT the intended prop-restricted eliminator\n\
         generated:\n{:#?}\n\nexpected:\n{:#?}",
        rec_val.type_,
        expected,
    );
}

/// The recursor type type-checks end-to-end: a full application infers `Two`.
#[test]
fn test_trunc_rec_application_typechecks() {
    let env = trunc_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let app = rec_apply(id_two(), in_two(cst(t0())));
    let (ty, _) = tc
        .infer_type_with_cert(&app)
        .expect("Trunc.rec Two Two pP id (in t0) should infer");
    assert!(
        tc.is_def_eq(&ty, &cst(two())),
        "Trunc.rec into Two should infer Two; got {ty:?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (c) ∥A∥.rec A P pP f (in a) ↝ f a  — the point-constructor iota
//     Non-vacuous: over the 2-ctor target `Two`, `f t0 ↝ t0 ≢ t1 ↝ f t1`.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_trunc_rec_in_reduces_to_f_applied_non_vacuous() {
    let env = trunc_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let reduced_t0 = tc.whnf(&rec_apply(id_two(), in_two(cst(t0()))));
    let reduced_t1 = tc.whnf(&rec_apply(id_two(), in_two(cst(t1()))));

    assert!(
        tc.is_def_eq(&reduced_t0, &cst(t0())),
        "Trunc.rec … id (in t0) should reduce to t0, got {reduced_t0:#?}",
    );
    assert!(
        tc.is_def_eq(&reduced_t1, &cst(t1())),
        "Trunc.rec … id (in t1) should reduce to t1, got {reduced_t1:#?}",
    );
    // Non-vacuity guard: the two reductions land on DISTINCT constructors.
    assert!(
        !tc.is_def_eq(&reduced_t0, &reduced_t1),
        "iota is vacuous: t0 ≡ t1 (the target is not genuinely 2-valued)",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (d) squash boundary coherence: rec (squash x y @ i0/i1) agrees with rec x / rec y
//     and the neutral interval reduces via the isProp witness.
// ═══════════════════════════════════════════════════════════════════════════

/// `squash Two (in t0) (in t1)` — a concrete propositional path in `Trunc Two`.
fn squash_t0_t1() -> Expr {
    Expr::apps(
        cst(trunc_squash()),
        [cst(two()), in_two(cst(t0())), in_two(cst(t1()))],
    )
}

#[test]
fn test_trunc_rec_squash_endpoints_boundary_coherence() {
    let env = trunc_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let rec_in_t0 = tc.whnf(&rec_apply(id_two(), in_two(cst(t0()))));
    let rec_in_t1 = tc.whnf(&rec_apply(id_two(), in_two(cst(t1()))));

    // rec (squash (in t0) (in t1) @ i0) ≡ rec (in t0) ≡ t0  (left endpoint).
    let at_i0 = tc.whnf(&rec_apply(id_two(), path_app(squash_t0_t1(), i0())));
    assert!(
        tc.is_def_eq(&at_i0, &rec_in_t0),
        "rec (squash @ i0) must agree with rec (in t0); got {at_i0:#?}",
    );
    assert!(
        tc.is_def_eq(&at_i0, &cst(t0())),
        "rec (squash @ i0) must be t0 (boundary); got {at_i0:#?}",
    );

    // rec (squash (in t0) (in t1) @ i1) ≡ rec (in t1) ≡ t1  (right endpoint).
    let at_i1 = tc.whnf(&rec_apply(id_two(), path_app(squash_t0_t1(), i1())));
    assert!(
        tc.is_def_eq(&at_i1, &rec_in_t1),
        "rec (squash @ i1) must agree with rec (in t1); got {at_i1:#?}",
    );
    assert!(
        tc.is_def_eq(&at_i1, &cst(t1())),
        "rec (squash @ i1) must be t1 (boundary); got {at_i1:#?}",
    );
}

#[test]
fn test_trunc_rec_squash_neutral_reduces_via_isprop() {
    let mut env = trunc_env();
    // A neutral interval `j : I`.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hit.j"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("declare neutral interval j : I");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let j = Expr::const_(Name::from_string("hit.j"), vec![]);
    let reduced = tc.whnf(&rec_apply(id_two(), path_app(squash_t0_t1(), j.clone())));

    // Expected: pP (rec … (in t0)) (rec … (in t1)) @ j  (the isProp witness path).
    let expected = path_app(
        Expr::apps(
            cst(pp()),
            [
                rec_apply(id_two(), in_two(cst(t0()))),
                rec_apply(id_two(), in_two(cst(t1()))),
            ],
        ),
        j,
    );
    assert!(
        tc.is_def_eq(&reduced, &expected),
        "rec (squash @ j) should reduce to pP (rec…)(rec…) @ j, got {reduced:#?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (e) isProp ∥A∥ — directly from squash (it IS the proof)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_trunc_is_a_proposition_via_squash() {
    let env = trunc_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // `Trunc.squash Two : (x y : Trunc Two) → Path (λ_.Trunc Two) x y`
    //   which is exactly `isProp (Trunc Two)`.
    let squash_at_two = Expr::apps(cst(trunc_squash()), [cst(two())]);
    let (ty, _) = tc
        .infer_type_with_cert(&squash_at_two)
        .expect("Trunc.squash Two should infer");

    let expected = is_prop_type(&trunc_app(cst(two())));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Trunc.squash Two : isProp (Trunc Two); got {ty:?}",
    );
}
