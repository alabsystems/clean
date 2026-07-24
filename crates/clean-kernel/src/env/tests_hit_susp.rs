// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Higher Inductive Type tests: the suspension `Susp A` — the THIRD HIT (after
//! S¹ and propositional truncation). It generalizes Clean's HIT schema past
//! S¹/truncation to a path constructor that is a *family*
//! (`merid : A → north ≡ south`).
//!
//! `Susp A` is declared (in Cubical mode) as a parametric HIT with two *point*
//! constructors `north`/`south : Susp A` and a *path-family* constructor
//! `merid : (a : A) → Path (λ _:I. Susp A) (north A) (south A)`. The kernel must
//! generate the sound **dependent** eliminator
//!
//! ```text
//! Susp.rec : {A : Type} → {C : Susp A → Sort u}
//!   → (cn : C (north A)) → (cs : C (south A))
//!   → (cm : (a : A) → PathP (λ i. C (merid A a @ i)) cn cs)
//!   → (x : Susp A) → C x
//! ```
//!
//! with iota `Susp.rec … (north A) ↝ cn`, `Susp.rec … (south A) ↝ cs`, and
//! `Susp.rec … (merid A a @ r) ↝ (cm a) @ r`, coherent at the endpoints
//! (`merid A a @ i0 = north A`, so the merid rule at `i0` agrees with the north
//! rule: `(cm a) @ i0 = cn`).
//!
//! Test (b) is the soundness check: the generated recursor TYPE is compared
//! (`is_def_eq`) against a hand-built copy of the intended type above — a wrong
//! recursor type is the failure mode for HIT soundness. `noConfusion` / `casesOn`
//! / `recOn` are skipped (injectivity & structural recursion are unsound for a
//! path constructor).
//!
//! Roadmap (stated, not proved here): `Susp Bool ≃ S¹` and `Susp ⊥ ≃ Bool`.

use super::*;
use crate::env::Declaration;
use crate::expr::{BinderInfo, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::TypeChecker;
use std::sync::Arc;

// ── Names ────────────────────────────────────────────────────────────────────

fn susp() -> Name {
    Name::from_string("Susp")
}
fn north() -> Name {
    Name::from_string("Susp.north")
}
fn south() -> Name {
    Name::from_string("Susp.south")
}
fn merid() -> Name {
    Name::from_string("Susp.merid")
}
fn rec() -> Name {
    Name::from_string("Susp.rec")
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
fn my_a() -> Name {
    Name::from_string("MyA")
}
fn pt_a() -> Name {
    Name::from_string("a")
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
/// `Susp a` for a closed `a`.
fn susp_app(a: Expr) -> Expr {
    Expr::app(cst(susp()), a)
}
fn north_app(a: Expr) -> Expr {
    Expr::app(cst(north()), a)
}
fn south_app(a: Expr) -> Expr {
    Expr::app(cst(south()), a)
}
fn merid_app(a_param: Expr, a_field: Expr) -> Expr {
    Expr::apps(cst(merid()), [a_param, a_field])
}

// ── Susp declaration ─────────────────────────────────────────────────────────

/// `Susp.north : Π (A : Type). Susp A` (and `south` identically).
fn point_ctor_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(cst(susp()), Expr::bvar(0)), // Susp A
    )
}

/// `Susp.merid : Π (A : Type). Π (a : A). Path (λ _:I. Susp A) (north A) (south A)`.
fn merid_ctor_type() -> Expr {
    // line: λ _:I. Susp A   (A = BVar2 under [A, a, _i])
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(cst(susp()), Expr::bvar(2)),
    );
    // endpoints north A / south A   (A = BVar1 under [A, a])
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(Expr::app(cst(north()), Expr::bvar(1))),
        right: Arc::new(Expr::app(cst(south()), Expr::bvar(1))),
    });
    Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A : Type
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // a : A
            path,
        ),
    )
}

fn susp_decl() -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: susp(),
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()), // Type → Type
            constructors: vec![
                Constructor {
                    name: north(),
                    type_: point_ctor_type(),
                },
                Constructor {
                    name: south(),
                    type_: point_ctor_type(),
                },
                Constructor {
                    name: merid(),
                    type_: merid_ctor_type(),
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

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// Base `Susp` env: the suspension HIT, a concrete `Two` target, plus an opaque
/// `MyA : Type` and `a : MyA` so the recursor can be applied over a real
/// parameter without a fresh local context.
fn susp_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.add_inductive(two_decl())
        .expect("Two should declare without error");
    env.add_inductive(susp_decl())
        .expect("Susp (north + south + merid) should declare without error");
    env.add_decl(Declaration::Axiom {
        name: my_a(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("MyA : Type registers");
    env.add_decl(Declaration::Axiom {
        name: pt_a(),
        level_params: vec![],
        type_: cst(my_a()),
    })
    .expect("a : MyA registers");
    env
}

/// The **constant** motive `λ (_ : Susp MyA). Two` — turns `Susp.rec` into the
/// non-dependent eliminator into `Two` (the bonus `Susp.rec {A}{B} (n s)(m)`).
fn const_motive() -> Expr {
    Expr::lam(BinderInfo::Default, susp_app(cst(my_a())), cst(two()))
}

/// `cm : (a : MyA) → Path (λ _:I. Two) t0 t1` — the constant-motive merid minor
/// (the line `λ i. (λ_.Two)(merid MyA a @ i)` beta-collapses to `λ _:I. Two`).
fn cm_const_name() -> Name {
    Name::from_string("susp.cmConst")
}
fn cm_const_type() -> Expr {
    let line = Expr::lam(BinderInfo::Default, interval(), cst(two()));
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(cst(t0())),
        right: Arc::new(cst(t1())),
    });
    Expr::pi(BinderInfo::Default, cst(my_a()), path)
}

/// `Susp` env + the constant-motive merid witness `cm : (a:MyA) → Path Two t0 t1`.
fn susp_env_const() -> Environment {
    let mut env = susp_env();
    env.add_decl(Declaration::Axiom {
        name: cm_const_name(),
        level_params: vec![],
        type_: cm_const_type(),
    })
    .expect("cmConst : (a:MyA) → Path (λ_.Two) t0 t1 registers");
    env
}

/// `Susp.rec.{1} MyA (λ_.Two) t0 t1 cmConst major` — eliminate into `Two`.
fn rec_apply_const(major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(rec(), vec![lvl1()]),
        [
            cst(my_a()),
            const_motive(),
            cst(t0()),
            cst(t1()),
            cst(cm_const_name()),
            major,
        ],
    )
}

/// Hand-built INTENDED recursor type (built from the spec, NOT kernel output):
///
/// ```text
/// {A : Type} → {C : Susp A → Sort u}
///   → (cn : C (north A)) → (cs : C (south A))
///   → (cm : (a : A) → PathP (λ i. C (merid A a @ i)) cn cs)
///   → (x : Susp A) → C x
/// ```
fn expected_susp_rec_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));

    // body: C x   (context [A,C,cn,cs,cm,x]: C = BVar4, x = BVar0)
    let mut t = Expr::app(Expr::bvar(4), Expr::bvar(0));
    // (x : Susp A)   (context [A,C,cn,cs,cm]: A = BVar4)
    t = Expr::pi(BinderInfo::Default, susp_app(Expr::bvar(4)), t);

    // (cm : (a : A) → PathP (λ i. C (merid A a @ i)) cn cs)
    //   context [A,C,cn,cs]: A=3, C=2, cn=1, cs=0
    //   under a   [.,a]:  a=0, cs=1, cn=2, C=3, A=4
    //   under λ i [.,a,i]: i=0, a=1, cs=2, cn=3, C=4, A=5
    let line_body = Expr::app(
        Expr::bvar(4), // C
        path_app(merid_app(Expr::bvar(5), Expr::bvar(1)), Expr::bvar(0)),
    );
    let line = Expr::lam(BinderInfo::Default, interval(), line_body);
    let pathp = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(Expr::bvar(2)),  // cn
        right: Arc::new(Expr::bvar(1)), // cs
    });
    let cm_ty = Expr::pi(BinderInfo::Default, Expr::bvar(3) /* A */, pathp);
    t = Expr::pi(BinderInfo::Default, cm_ty, t);

    // (cs : C (south A))   (context [A,C,cn]: C=1, A=2)
    t = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::bvar(1), south_app(Expr::bvar(2))),
        t,
    );
    // (cn : C (north A))   (context [A,C]: C=0, A=1)
    t = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::bvar(0), north_app(Expr::bvar(1))),
        t,
    );
    // {C : Susp A → Sort u}   (context [A]: A=0)
    t = Expr::pi(
        BinderInfo::Implicit,
        Expr::pi(BinderInfo::Default, susp_app(Expr::bvar(0)), sort_u),
        t,
    );
    // {A : Type}
    Expr::pi(BinderInfo::Implicit, Expr::type_(), t)
}

// ═══════════════════════════════════════════════════════════════════════════
// (a) Susp declares without error; rec + constructors are generated; the
//     structural aux defs (noConfusion / casesOn / recOn) are SKIPPED.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_susp_declares_without_error() {
    let env = susp_env();
    assert!(
        env.get_recursor(&rec()).is_some(),
        "Susp.rec should be generated"
    );
    assert!(env.get_constructor(&north()).is_some(), "north constructor");
    assert!(env.get_constructor(&south()).is_some(), "south constructor");
    assert!(env.get_constructor(&merid()).is_some(), "merid constructor");
    // noConfusion is SKIPPED for HITs (constructor injectivity is unsound for a
    // path constructor).
    assert!(
        env.get_const(&Name::from_string("Susp.noConfusion"))
            .is_none(),
        "Susp.noConfusion must NOT be generated (path constructor)"
    );
    // casesOn / recOn are NOT generated (no structural recursion through merid).
    assert!(
        env.get_recursor(&Name::from_string("Susp.casesOn"))
            .is_none(),
        "Susp.casesOn must NOT be generated"
    );
    assert!(
        env.get_recursor(&Name::from_string("Susp.recOn")).is_none(),
        "Susp.recOn must NOT be generated"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (b) Recursor TYPE correctness — the key soundness test
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_susp_recursor_type_is_the_intended_dependent_eliminator() {
    let env = susp_env();
    let rec_val = env.get_recursor(&rec()).expect("Susp.rec");

    let u = rec_val
        .level_params
        .first()
        .expect("Susp.rec must carry a motive universe parameter")
        .clone();

    let expected = expected_susp_rec_type(&u);
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    assert!(
        tc.is_def_eq(&rec_val.type_, &expected),
        "generated Susp.rec type is NOT the intended dependent eliminator\n\
         generated:\n{:#?}\n\nexpected:\n{:#?}",
        rec_val.type_,
        expected,
    );
}

/// `Susp.merid MyA : (a : MyA) → Path (λ_.Susp MyA) (north MyA) (south MyA)`.
/// Confirms `merid` is the intended path *family* (and exercises endpoint
/// coherence at the type level).
#[test]
fn test_susp_merid_is_a_path_family() {
    let env = susp_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let merid_at_a = Expr::app(cst(merid()), cst(my_a()));
    let (ty, _) = tc
        .infer_type_with_cert(&merid_at_a)
        .expect("Susp.merid MyA should infer");

    // Expected: (a : MyA) → Path (λ _:I. Susp MyA) (north MyA) (south MyA).
    let line = Expr::lam(BinderInfo::Default, interval(), susp_app(cst(my_a())));
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(north_app(cst(my_a()))),
        right: Arc::new(south_app(cst(my_a()))),
    });
    let expected = Expr::pi(BinderInfo::Default, cst(my_a()), path);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Susp.merid MyA : (a:MyA) → Path (λ_.Susp MyA)(north MyA)(south MyA); got {ty:?}",
    );
}

/// The recursor type type-checks end-to-end: a full application infers `Two`
/// (the constant-motive / non-dependent eliminator — bonus deliverable).
#[test]
fn test_susp_rec_application_typechecks_nondependent() {
    let env = susp_env_const();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let app = rec_apply_const(north_app(cst(my_a())));
    let (ty, _) = tc
        .infer_type_with_cert(&app)
        .expect("Susp.rec MyA (λ_.Two) t0 t1 cmConst (north MyA) should infer");
    assert!(
        tc.is_def_eq(&ty, &cst(two())),
        "Susp.rec into Two should infer Two; got {ty:?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (c) Point-constructor iota: Susp.rec … (north A) ↝ cn, (south A) ↝ cs.
//     Non-vacuous: over the 2-ctor target `Two`, cn = t0 ≢ t1 = cs.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_susp_rec_north_south_reduce_non_vacuous() {
    let env = susp_env_const();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let reduced_n = tc.whnf(&rec_apply_const(north_app(cst(my_a()))));
    let reduced_s = tc.whnf(&rec_apply_const(south_app(cst(my_a()))));

    assert!(
        tc.is_def_eq(&reduced_n, &cst(t0())),
        "Susp.rec … (north MyA) should reduce to cn = t0, got {reduced_n:#?}",
    );
    assert!(
        tc.is_def_eq(&reduced_s, &cst(t1())),
        "Susp.rec … (south MyA) should reduce to cs = t1, got {reduced_s:#?}",
    );
    // Non-vacuity guard: the two reductions land on DISTINCT constructors.
    assert!(
        !tc.is_def_eq(&reduced_n, &reduced_s),
        "iota is vacuous: t0 ≡ t1 (the target is not genuinely 2-valued)",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (d) merid boundary coherence: rec (merid A a @ i0/i1) agrees with
//     rec (north A) = cn / rec (south A) = cs.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_susp_rec_merid_endpoints_boundary_coherence() {
    let env = susp_env_const();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let rec_north = tc.whnf(&rec_apply_const(north_app(cst(my_a()))));
    let rec_south = tc.whnf(&rec_apply_const(south_app(cst(my_a()))));
    let merid_aa = merid_app(cst(my_a()), cst(pt_a()));

    // rec (merid MyA a @ i0) ≡ rec (north MyA) ≡ t0  (left endpoint).
    let at_i0 = tc.whnf(&rec_apply_const(path_app(merid_aa.clone(), i0())));
    assert!(
        tc.is_def_eq(&at_i0, &rec_north),
        "rec (merid @ i0) must agree with rec (north MyA); got {at_i0:#?}",
    );
    assert!(
        tc.is_def_eq(&at_i0, &cst(t0())),
        "rec (merid @ i0) must be cn = t0 (boundary); got {at_i0:#?}",
    );

    // rec (merid MyA a @ i1) ≡ rec (south MyA) ≡ t1  (right endpoint).
    let at_i1 = tc.whnf(&rec_apply_const(path_app(merid_aa, i1())));
    assert!(
        tc.is_def_eq(&at_i1, &rec_south),
        "rec (merid @ i1) must agree with rec (south MyA); got {at_i1:#?}",
    );
    assert!(
        tc.is_def_eq(&at_i1, &cst(t1())),
        "rec (merid @ i1) must be cs = t1 (boundary); got {at_i1:#?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (e) merid neutral iota: Susp.rec … (merid A a @ j) ↝ (cm a) @ j  (neutral j).
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_susp_rec_merid_neutral_reduces_to_cm_at_j() {
    let mut env = susp_env_const();
    // A neutral interval `j : I`.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("susp.j"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("declare neutral interval j : I");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let j = Expr::const_(Name::from_string("susp.j"), vec![]);
    let merid_aa = merid_app(cst(my_a()), cst(pt_a()));
    let reduced = tc.whnf(&rec_apply_const(path_app(merid_aa, j.clone())));

    // Expected: (cmConst a) @ j.
    let expected = path_app(Expr::app(cst(cm_const_name()), cst(pt_a())), j);
    assert!(
        tc.is_def_eq(&reduced, &expected),
        "rec (merid @ j) should reduce to (cm a) @ j, got {reduced:#?}",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (f) DEPENDENT merid minor is well-formed — the real "teeth" for a NON-constant
//     motive: declaring `cm : (a:A) → PathP (λ i. C (merid A a @ i)) cn cs`
//     forces the kernel to check `cn : C (merid A a @ i0)` ≡ `C (north A)`,
//     i.e. it exercises the merid path-endpoint reduction `merid A a @ i0 ↝
//     north A` (the constant-motive scenario collapses the line and never does).
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_susp_dependent_merid_minor_is_wellformed() {
    let mut env = susp_env();

    // C : Susp MyA → Type
    let c_name = Name::from_string("susp.C");
    env.add_decl(Declaration::Axiom {
        name: c_name.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, susp_app(cst(my_a())), Expr::type_()),
    })
    .expect("declare dependent motive C : Susp MyA → Type");

    // cn : C (north MyA),  cs : C (south MyA)
    let cn_name = Name::from_string("susp.cn");
    let cs_name = Name::from_string("susp.cs");
    env.add_decl(Declaration::Axiom {
        name: cn_name.clone(),
        level_params: vec![],
        type_: Expr::app(cst(c_name.clone()), north_app(cst(my_a()))),
    })
    .expect("declare cn : C (north MyA)");
    env.add_decl(Declaration::Axiom {
        name: cs_name.clone(),
        level_params: vec![],
        type_: Expr::app(cst(c_name.clone()), south_app(cst(my_a()))),
    })
    .expect("declare cs : C (south MyA)");

    // cm : (a : MyA) → PathP (λ i. C (merid MyA a @ i)) cn cs
    //   under a   [a]:    a = BVar0
    //   under λ i [a, i]: i = BVar0, a = BVar1
    let line = Expr::lam(
        BinderInfo::Default,
        interval(),
        Expr::app(
            cst(c_name.clone()),
            path_app(merid_app(cst(my_a()), Expr::bvar(1)), Expr::bvar(0)),
        ),
    );
    let pathp = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(line),
        left: Arc::new(cst(cn_name)),
        right: Arc::new(cst(cs_name)),
    });
    let cm_ty = Expr::pi(BinderInfo::Default, cst(my_a()), pathp);

    // Declaring this axiom is the test: success ⟺ the PathP endpoints check out,
    // i.e. `merid MyA a @ i0 ↝ north MyA` (and `@ i1 ↝ south MyA`) fired.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("susp.cmDep"),
        level_params: vec![],
        type_: cm_ty,
    })
    .expect(
        "dependent merid minor (a:MyA) → PathP (λ i. C (merid MyA a @ i)) cn cs must be \
         well-formed (exercises merid endpoint reduction)",
    );
}
