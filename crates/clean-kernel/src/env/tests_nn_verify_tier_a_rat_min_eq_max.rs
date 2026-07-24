// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.min_eq_max_zero_zero` (#3551 Batch 2).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.min_eq_max_zero_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_eq_max()
        .expect("init should succeed");
    env
}

#[test]
fn test_min_eq_max_zero_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_min_eq_max());
}

#[test]
fn test_min_eq_max_zero_zero_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_min_eq_max_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

// #integrity-audit (2026-06): this test previously asserted the axiom closure
// of `NNVerify.Rat.min_eq_max_zero_zero` was EMPTY (reported "Constructive /
// 0 domain axioms"). That was an overstatement: the proof routes through
// `Rat.min` / `Rat.max`, which are admitted DOMAIN axioms (mathematically
// true but carrying NO Clean-kernel proof term). They are now excluded from
// `is_foundational_axiom` (listed in `ADMITTED_DOMAIN_AXIOMS`), so the closure
// is honestly NON-EMPTY. The honest invariant: the closure is non-empty, has
// no `sorry`/`sorryAx` trust marker, and contains ONLY admitted domain axioms
// (no rogue/unexpected axiom) — i.e. the theorem is `AxiomDependent` on
// admitted domain assumptions, sorry-free.
#[test]
fn test_min_eq_max_zero_zero_axiom_closure_only_admitted_domain() {
    use super::axiom_audit::ADMITTED_DOMAIN_AXIOMS;
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
    for a in &deps {
        let a_str = a.to_string();
        assert!(
            ADMITTED_DOMAIN_AXIOMS.contains(&a_str.as_str()),
            "unexpected non-admitted axiom in {TARGET} closure: {a}"
        );
    }
}

#[test]
fn test_min_eq_max_zero_zero_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_eq_max().unwrap();
    env.init_nn_verify_tier_a_rat_min_eq_max().unwrap();
    assert!(env.has_nn_verify_tier_a_rat_min_eq_max());
}
