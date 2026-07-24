// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.max_eq_min_zero_zero` (#3551).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.max_eq_min_zero_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_max_eq_min()
        .expect("init should succeed");
    env
}

#[test]
fn test_max_eq_min_zero_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_max_eq_min());
}

#[test]
fn test_max_eq_min_zero_zero_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_max_eq_min_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

#[test]
fn test_max_eq_min_zero_zero_axiom_closure_is_admitted_domain_only() {
    // #integrity-audit (2026-06): `Rat.max` / `Rat.min` / `Rat.max_def` /
    // `Rat.min_def` / `Rat.le_refl` (and friends) were dishonestly whitelisted
    // as "foundational", so this transitive-`Eq.trans` theorem was reported as
    // having an EMPTY axiom closure (Constructive). They are now admitted DOMAIN
    // axioms (excluded from `is_foundational_axiom`), so the honest closure is
    // NON-EMPTY. The truthful invariant is: it rests ONLY on admitted domain
    // axioms — no `sorry`/`sorryAx`, no rogue/unexpected axiom.
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("axiom_deps");
    let dep_strs: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(!dep_strs.contains("sorry"));
    assert!(!dep_strs.contains("sorryAx"));
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET} is now FULLY CONSTRUCTIVE — `Rat.min`/`Rat.max` (and \
         `Rat.{{min,max}}_def`, the lattice lemmas) are kernel-checked over the \
         quotient carrier, so its axiom closure is EMPTY; got {dep_strs:?}"
    );
    let admitted: std::collections::HashSet<&str> = crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .collect();
    for a in &deps {
        assert!(
            admitted.contains(a.to_string().as_str()),
            "unexpected non-admitted axiom in {TARGET} closure: {a}"
        );
    }
}

#[test]
fn test_max_eq_min_zero_zero_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_max_eq_min().unwrap();
    env.init_nn_verify_tier_a_rat_max_eq_min().unwrap();
    assert!(env.has_nn_verify_tier_a_rat_max_eq_min());
}
