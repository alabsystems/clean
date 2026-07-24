// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.zero_eq_min_zero_zero` (#3551).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.zero_eq_min_zero_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_zero_eq_min()
        .expect("init should succeed");
    env
}

#[test]
fn test_zero_eq_min_zero_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_zero_eq_min());
}

#[test]
fn test_zero_eq_min_zero_zero_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_zero_eq_min_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

#[test]
fn test_zero_eq_min_zero_zero_rests_on_admitted_domain_axioms() {
    // #integrity-audit (2026-06): this theorem's proof reduces (via
    // `NNVerify.Rat.min_zero_zero`) to `Rat.min_def` and `Rat.le_refl`, both of
    // which are admitted Rat ordered-field/lattice DOMAIN axioms that were
    // previously dishonestly whitelisted as "foundational" (so the closure was
    // reported empty / Constructive). They are now excluded from
    // `is_foundational_axiom`, so `axiom_deps` honestly RETURNS them. The honest
    // state: the closure is NON-EMPTY, contains NO sorry/sorryAx and NO rogue
    // axiom, and every member is an admitted domain axiom — i.e. the theorem is
    // `AxiomDependent` on admitted domain assumptions.
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("axiom_deps");
    let deps: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(!deps.contains("sorry"));
    assert!(!deps.contains("sorryAx"));
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET} is now FULLY CONSTRUCTIVE — `Rat.min`/`Rat.max` (and \
         `Rat.{{min,max}}_def`, the lattice lemmas) are kernel-checked over the \
         quotient carrier, so its axiom closure is EMPTY; got {deps:?}"
    );
    let admitted: std::collections::HashSet<&str> = crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .collect();
    for a in &deps {
        assert!(
            admitted.contains(a.as_str()),
            "unexpected non-admitted axiom in {TARGET} closure: {a}; full closure {deps:?}"
        );
    }
}

#[test]
fn test_zero_eq_min_zero_zero_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_zero_eq_min().unwrap();
    env.init_nn_verify_tier_a_rat_zero_eq_min().unwrap();
    assert!(env.has_nn_verify_tier_a_rat_zero_eq_min());
}
