// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the canonical `Rat.min_le_max` lattice lemma (Part of #3615).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "Rat.min_le_max";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_rat_min_le_max().expect("init should succeed");
    env
}

#[test]
fn test_rat_min_le_max_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(TARGET)).is_some(),
        "{TARGET} must be registered"
    );
    assert!(env.has_rat_min_le_max());
}

#[test]
fn test_rat_min_le_max_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{TARGET} must be a Theorem, not an Axiom"
    );
}

#[test]
fn test_rat_min_le_max_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

#[test]
fn test_rat_min_le_max_axiom_closure_is_foundational() {
    // The canonical proof composes:
    //   Rat.le_total, Rat.min_def, Rat.min_def', Rat.max_def,
    //   Rat.max_def', Or.rec, Eq.symm, Eq.subst
    // All are in FOUNDATIONAL_AXIOMS (or registered as constructive
    // Theorems, which the axiom_deps classifier skips). No `sorry` /
    // `sorryAx` may appear in the closure, and no non-foundational
    // domain axiom may appear.
    use crate::env::axiom_audit::FOUNDATIONAL_AXIOMS;

    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("axiom_deps");
    let foundational: std::collections::HashSet<&str> =
        FOUNDATIONAL_AXIOMS.iter().copied().collect();

    for dep in &deps {
        let name = dep.to_string();
        assert_ne!(name, "sorry", "{TARGET} closure must not reach sorry");
        assert_ne!(name, "sorryAx", "{TARGET} closure must not reach sorryAx");
        assert!(
            foundational.contains(name.as_str()),
            "{TARGET} dep {name} must be a foundational axiom; closure = {deps:?}"
        );
    }
}

#[test]
fn test_rat_min_le_max_idempotent() {
    let mut env = Environment::new();
    env.init_rat_min_le_max().unwrap();
    env.init_rat_min_le_max().unwrap();
    assert!(env.has_rat_min_le_max());
}

#[test]
fn test_rat_min_le_max_has_expected_type() {
    // Pin the signature: ∀ a b : Rat, Rat.le (Rat.min a b) (Rat.max a b).
    // We don't spell the full pi-type by hand — instantiating the theorem
    // at two concrete rationals and checking the conclusion type is
    // sufficient to catch signature drift.
    let env = make_env();
    let thm = Expr::const_(Name::from_string(TARGET), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    // thm Rat.zero Rat.zero  :  Rat.le (Rat.min 0 0) (Rat.max 0 0)
    let inst = Expr::app(Expr::app(thm, rat_zero.clone()), rat_zero.clone());
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&inst)
        .unwrap_or_else(|err| panic!("{TARGET} application should type-check: {err:?}"));

    // Expected: Rat.le (Rat.min 0 0) (Rat.max 0 0).
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
    let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
    let min_zz = Expr::app(Expr::app(rat_min, rat_zero.clone()), rat_zero.clone());
    let max_zz = Expr::app(Expr::app(rat_max, rat_zero.clone()), rat_zero);
    let expected = Expr::app(Expr::app(rat_le, min_zz), max_zz);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "{TARGET} 0 0 should have type Rat.le (Rat.min 0 0) (Rat.max 0 0); got {ty:?}"
    );
}
