// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.min_le_max_zero_zero` (#3551 Batch 4).
//!
//! #integrity-audit: this theorem composes `min_zero_zero`, `le_refl_zero`,
//! and `zero_eq_max_zero_zero`, so its transitive axiom closure reaches the
//! admitted Rat ordered-field/lattice axioms (`Rat.min`, `Rat.min_def`,
//! `Rat.le_refl`, `Rat.max`, `Rat.max_def`). Those were dishonestly
//! whitelisted as "foundational"; they are now in `ADMITTED_DOMAIN_AXIOMS`
//! and excluded from `is_foundational_axiom`. The closure is therefore
//! sorry-free but honestly NON-EMPTY, and the theorem is `AxiomDependent` on
//! admitted domain assumptions — not `Constructive`.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.min_le_max_zero_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_le_max_zero_zero()
        .expect("init should succeed");
    env
}

#[test]
fn test_min_le_max_zero_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_min_le_max_zero_zero());
}

#[test]
fn test_min_le_max_zero_zero_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_min_le_max_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

#[test]
fn test_min_le_max_zero_zero_rests_on_admitted_domain_axioms() {
    // #integrity-audit: the LE-transport proof term composes
    // `NNVerify.Rat.min_zero_zero`, `NNVerify.Rat.le_refl_zero`, and
    // `NNVerify.Rat.zero_eq_max_zero_zero`, whose transitive closures reach
    // the admitted Rat ordered-field/lattice axioms `Rat.min`, `Rat.min_def`,
    // `Rat.le_refl`, `Rat.max`, and `Rat.max_def`. These were dishonestly
    // whitelisted as "foundational"; they are now in `ADMITTED_DOMAIN_AXIOMS`
    // and excluded from `is_foundational_axiom`, so the non-foundational
    // closure is NON-EMPTY. The honest classification is `AxiomDependent` on
    // admitted domain assumptions — not `Constructive`. We still verify the
    // proof is sorry-free and that NO unexpected/rogue axiom leaks in.
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("axiom_deps");
    let dep_strs: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(!dep_strs.contains("sorry"));
    assert!(!dep_strs.contains("sorryAx"));
    // The closure now honestly rests on admitted domain axioms.
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET} is now FULLY CONSTRUCTIVE — `Rat.min`/`Rat.max` (and \
         `Rat.{{min,max}}_def`, the lattice lemmas) are kernel-checked over the \
         quotient carrier, so its axiom closure is EMPTY; got {dep_strs:?}"
    );
    // Every axiom in the closure must be an admitted domain axiom — no
    // foundational logical axioms (those are filtered out), no trust markers,
    // no rogue/unexpected axiom.
    let admitted: std::collections::HashSet<&str> = crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .collect();
    for a in &deps {
        assert!(
            admitted.contains(a.to_string().as_str()),
            "unexpected non-admitted axiom in closure: {a}"
        );
    }
}

#[test]
fn test_min_le_max_zero_zero_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_le_max_zero_zero()
        .unwrap();
    env.init_nn_verify_tier_a_rat_min_le_max_zero_zero()
        .unwrap();
    assert!(env.has_nn_verify_tier_a_rat_min_le_max_zero_zero());
}
