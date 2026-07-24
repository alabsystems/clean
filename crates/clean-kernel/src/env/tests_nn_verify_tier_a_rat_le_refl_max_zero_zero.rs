// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.le_refl_max_zero_zero` (#3551 Batch 2).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.le_refl_max_zero_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_le_refl_max_zero_zero()
        .expect("init should succeed");
    env
}

#[test]
fn test_le_refl_max_zero_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_le_refl_max_zero_zero());
}

#[test]
fn test_le_refl_max_zero_zero_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_le_refl_max_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

#[test]
fn test_le_refl_max_zero_zero_axiom_closure_admitted_domain_only() {
    // #integrity-audit (2026-06): the proof of `le_refl_max_zero_zero` is
    // `Rat.le_refl (Rat.max Rat.zero Rat.zero)`. Its axiom closure reaches
    // `Rat.max` (still an admitted lattice axiom).
    //
    // NOTE (#3470 Lane #2/#3): `Rat.le_refl` has been GENUINELY ELIMINATED to a
    // constructive kernel Theorem, so it no longer appears in the closure —
    // `axiom_deps` walks into its constructive proof instead of stopping on it.
    // The closure is therefore now exactly `{Rat.max}`: still NON-EMPTY, still
    // honestly `AxiomDependent` (on the remaining admitted lattice axiom
    // `Rat.max`), with no `sorry`/`sorryAx` and no rogue non-admitted axiom.
    use crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS;
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
        let s = a.to_string();
        assert!(
            ADMITTED_DOMAIN_AXIOMS.contains(&s.as_str()),
            "unexpected non-admitted axiom in {TARGET} closure: {s}"
        );
    }
}

#[test]
fn test_le_refl_max_zero_zero_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_le_refl_max_zero_zero()
        .unwrap();
    env.init_nn_verify_tier_a_rat_le_refl_max_zero_zero()
        .unwrap();
    assert!(env.has_nn_verify_tier_a_rat_le_refl_max_zero_zero());
}
