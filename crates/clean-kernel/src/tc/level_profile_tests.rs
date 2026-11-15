// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The checker's universe levels in each kernel theory, over the shapes
//! pinned Lean v4.30.0-rc2 decides (`reports/level-normalizer-probe-2026-10-17/`,
//! design §1): `t5`/`t5b` (constant instantiation), `t10`/`t10b` (the Π sort),
//! and the object-sharing dependence of the critic's `Eqp` probe.

use crate::env::{Declaration, EnvError, Environment, KernelTheory};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use crate::tc::{TypeChecker, TypeError};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn p(s: &str) -> Level {
    Level::param(n(s))
}

fn max(a: Level, b: Level) -> Level {
    Level::lean_max_core(a, b)
}

fn imax(a: Level, b: Level) -> Level {
    Level::lean_imax_core(a, b)
}

fn uv() -> Vec<Name> {
    vec![n("u"), n("v")]
}

/// An environment holding honest `Sort`-typed axioms (pinned Lean admits
/// each: `t5a`, `t10a` in the probe).
fn env_with_axioms(axioms: &[(&str, Vec<Name>, Level)]) -> Environment {
    let mut env = Environment::for_lean_replay();
    for (name, level_params, level) in axioms {
        env.add_decl(Declaration::Axiom {
            name: n(name),
            level_params: level_params.clone(),
            type_: Expr::sort(level.clone()),
        })
        .expect("honest Sort-typed axiom");
    }
    env
}

/// `def name.{u,v} : Sort declared := value`, checked in `theory`.
fn add_def(
    env: &Environment,
    theory: KernelTheory,
    name: &str,
    declared: Level,
    value: Expr,
) -> Result<(), EnvError> {
    let mut env = env.clone();
    env.set_kernel_theory(theory);
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: uv(),
        type_: Expr::sort(declared),
        value,
        is_reducible: false,
    })
}

/// The same check through a checker, so the refusal's error is visible.
fn check_in(
    env: &Environment,
    theory: KernelTheory,
    value: &Expr,
    declared: Level,
) -> Result<(), TypeError> {
    let mut tc = TypeChecker::new(env);
    tc.set_kernel_theory(theory);
    tc.set_level_params(uv());
    tc.check_type(value, &Expr::sort(declared))
}

fn k_env() -> Environment {
    env_with_axioms(&[(
        "K",
        vec![n("u"), n("v"), n("w")],
        max(max(p("u"), p("v")), p("w")),
    )])
}

fn k_use() -> Expr {
    Expr::const_(n("K"), vec![p("u"), p("v"), imax(p("u"), p("v"))])
}

/// t5 / t5b: `K.{u,v,imax u v}` has type `Sort (max (max u v) (imax u v))`
/// under Lean's `instantiate` (the `max` node is rebuilt by `mk_max`, which
/// keeps both sides) and `Sort (max u v)` under Clean's (its `Level::max`
/// collapses the `imax`).
#[test]
fn lean_profile_const_instantiation_builds_like_lean() {
    let env = k_env();
    let t5 = max(p("u"), p("v"));
    let t5b = max(max(p("u"), p("v")), imax(p("u"), p("v")));
    for theory in [KernelTheory::Lean, KernelTheory::LeanReference] {
        let err = add_def(&env, theory, "t5", t5.clone(), k_use()).expect_err(
            "t5: pinned Lean refuses `def t5.{u,v} : Sort (max u v) := K.{u,v,imax u v}`",
        );
        assert!(
            format!("{err:?}").contains("TypeMismatch"),
            "t5 under {theory:?} is refused as a declaration type mismatch, got {err:?}"
        );
        add_def(&env, theory, "t5b", t5b.clone(), k_use())
            .unwrap_or_else(|e| panic!("t5b: pinned Lean admits it, {theory:?} refused: {e:?}"));
    }
    add_def(&env, KernelTheory::Extended, "t5", t5, k_use())
        .expect("Extended keeps Clean's collapse");
    add_def(&env, KernelTheory::Extended, "t5b", t5b, k_use()).expect("Extended admits t5b");
}

fn ab_env() -> Environment {
    env_with_axioms(&[
        ("A", uv(), imax(p("u"), p("v"))),
        ("B", uv(), max(p("u"), Level::succ(p("v")))),
    ])
}

fn a_to_b() -> Expr {
    Expr::arrow(
        Expr::const_(n("A"), vec![p("u"), p("v")]),
        Expr::const_(n("B"), vec![p("u"), p("v")]),
    )
}

/// t10 / t10b: `A.{u,v} → B.{u,v}` has sort `mk_imax (imax u v) (max u (v+1))`
/// `= max (imax u v) (max u (v+1))` (raw) under Lean's `infer_pi`, and
/// `max u (v+1)` under Clean's `Level::imax`.
#[test]
fn lean_profile_pi_sort_builds_like_lean() {
    let env = ab_env();
    let t10 = max(p("u"), Level::succ(p("v")));
    let t10b = max(imax(p("u"), p("v")), max(p("u"), Level::succ(p("v"))));
    for theory in [KernelTheory::Lean, KernelTheory::LeanReference] {
        let err = add_def(&env, theory, "t10", t10.clone(), a_to_b())
            .expect_err("t10: pinned Lean refuses `def t10 : Sort (max u (v+1)) := A → B`");
        assert!(
            format!("{err:?}").contains("TypeMismatch"),
            "t10 under {theory:?} is refused as a declaration type mismatch, got {err:?}"
        );
        add_def(&env, theory, "t10b", t10b.clone(), a_to_b())
            .unwrap_or_else(|e| panic!("t10b: pinned Lean admits it, {theory:?} refused: {e:?}"));
    }
    add_def(&env, KernelTheory::Extended, "t10", t10, a_to_b())
        .expect("Extended keeps Clean's imax");
    add_def(&env, KernelTheory::Extended, "t10b", t10b, a_to_b()).expect("Extended admits t10b");
}

fn cs_env() -> Environment {
    // `imax v (u+1)` is not what `mk_imax` builds (`max v (u+1)`).
    env_with_axioms(&[("cS", uv(), imax(p("v"), Level::succ(p("u"))))])
}

/// The critic's `Eqp` probe: `cS.{u,v}` instantiated by the identity keeps or
/// rebuilds its stored `imax v (u+1)` according to object sharing, and pinned
/// Lean's verdict follows (`leanchecker`: same-module `inA1_same` admitted,
/// cross-module `inC_same`/`inB_same` refused). Clean cannot see sharing, so
/// the Lean theories refuse the instantiation by name; Extended admits.
#[test]
fn lean_profile_refuses_sharing_dependent_instantiation() {
    let env = cs_env();
    let same = Expr::const_(n("cS"), vec![p("u"), p("v")]);
    for declared in [
        imax(p("v"), Level::succ(p("u"))),
        max(Level::succ(p("u")), p("v")),
    ] {
        for theory in [KernelTheory::Lean, KernelTheory::LeanReference] {
            let err = check_in(&env, theory, &same, declared.clone())
                .expect_err("a sharing-dependent instantiation is refused under the Lean theories");
            assert!(
                matches!(&err, TypeError::LevelSharingDependent { name } if *name == n("cS")),
                "refused by name as sharing-dependent, got {err:?}"
            );
        }
    }
    check_in(
        &env,
        KernelTheory::Extended,
        &same,
        imax(p("v"), Level::succ(p("u"))),
    )
    .expect("Extended admits the identity instantiation");
}

/// A real renaming changes every parameter, so Lean rebuilds the node with
/// `mk_imax` whatever the sharing: `cS.{a,b} : Sort (max b (a+1))`, raw.
/// Admitted at that spelling, refused at the stored `imax` spelling (Lean's
/// `normalize` of `imax b (a+1)` is the UNSORTED `max b (a+1)`).
#[test]
fn lean_profile_rebuilds_renamed_instantiation() {
    let env = cs_env();
    let renamed = Expr::const_(n("cS"), vec![p("a"), p("b")]);
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(KernelTheory::Lean);
    let ty = tc
        .infer_type(&renamed)
        .expect("renamed instantiation infers");
    assert_eq!(ty, Expr::sort(max(p("b"), Level::succ(p("a")))));
    assert!(tc.is_def_eq(&ty, &Expr::sort(max(p("b"), Level::succ(p("a"))))));
    assert!(!tc.is_def_eq(&ty, &Expr::sort(imax(p("b"), Level::succ(p("a"))))));
}

/// On a path that cannot fail, a sharing dependence is recorded and every
/// later answer of the checker is refused: heartbeat sites error, public
/// `is_def_eq` answers false, and exported caches are empty.
#[test]
fn lean_profile_sharing_dependence_is_sticky_on_error_free_paths() {
    let env = cs_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(KernelTheory::Lean);
    let prop = Expr::sort(Level::zero());
    assert!(tc.is_def_eq(&prop, &prop), "nothing recorded yet");
    let stored = Expr::sort(imax(p("v"), Level::succ(p("u"))));
    let kept = tc.instantiate_levels_or_record(&n("cS"), &stored, &uv(), &[p("u"), p("v")]);
    assert!(
        kept.is_none(),
        "the sharing-dependent instantiation is not served"
    );
    assert!(
        !tc.is_def_eq(&prop, &prop),
        "every later def-eq answer is refused"
    );
    let err = tc
        .infer_type(&prop)
        .expect_err("every later heartbeat site refuses");
    assert!(
        matches!(err, TypeError::LevelSharingDependent { .. }),
        "got {err:?}"
    );
    let caches = tc.take_caches();
    assert!(
        caches.whnf.is_empty()
            && caches.whnf_core.is_empty()
            && caches.def_eq.is_empty()
            && caches.unfold.is_empty()
            && caches.equiv.is_empty(),
        "no answer is handed on"
    );

    // Extended keeps Clean's substitution and records nothing.
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(KernelTheory::Extended);
    let kept = tc.instantiate_levels_or_record(&n("cS"), &stored, &uv(), &[p("u"), p("v")]);
    assert_eq!(kept, Some(stored));
    assert!(tc.is_def_eq(&prop, &prop));
}
