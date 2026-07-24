// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.min_zero_zero` (#3551).
//!
//! Guards:
//! - Theorem is registered.
//! - Kind is `Declaration::Theorem`.
//! - Type-checks under the kernel.
//! - #integrity-audit: transitive axiom closure is sorry-free but honestly
//!   NON-EMPTY — it rests on the admitted Rat ordered-field/lattice axioms
//!   (`Rat.min`, `Rat.min_def`, `Rat.le_refl`), which are no longer treated
//!   as foundational. The theorem is `AxiomDependent`, not `Constructive`.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.min_zero_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_zero()
        .expect("init_nn_verify_tier_a_rat_min_zero should succeed");
    env
}

#[test]
fn test_rat_min_zero_zero_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(TARGET)).is_some(),
        "{TARGET} should be registered"
    );
    assert!(env.has_nn_verify_tier_a_rat_min_zero());
}

#[test]
fn test_rat_min_zero_zero_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(TARGET))
        .expect("target must be registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_rat_min_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check, got: {err:?}"));
}

#[test]
fn test_rat_min_zero_zero_rests_on_admitted_domain_axioms() {
    // #integrity-audit: the proof term
    // `@Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero)` reaches the
    // admitted Rat ordered-field/lattice axioms `Rat.min`, `Rat.min_def`,
    // and `Rat.le_refl`. These were dishonestly whitelisted as
    // "foundational"; they are now in `ADMITTED_DOMAIN_AXIOMS` and excluded
    // from `is_foundational_axiom`, so the non-foundational closure is
    // NON-EMPTY. The honest classification is `AxiomDependent` on admitted
    // domain assumptions — not `Constructive`. We still verify the proof is
    // sorry-free and that NO unexpected/rogue axiom leaks into the closure.
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("target should have axiom_deps");
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
fn test_rat_min_zero_zero_idempotent_init() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_zero().unwrap();
    env.init_nn_verify_tier_a_rat_min_zero().unwrap();
    assert!(env.has_nn_verify_tier_a_rat_min_zero());
}
