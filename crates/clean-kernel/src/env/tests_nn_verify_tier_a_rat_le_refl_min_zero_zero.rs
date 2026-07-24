// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.le_refl_min_zero_zero` (#3551 Batch 2).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.le_refl_min_zero_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_le_refl_min_zero_zero()
        .expect("init should succeed");
    env
}

#[test]
fn test_le_refl_min_zero_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_le_refl_min_zero_zero());
}

#[test]
fn test_le_refl_min_zero_zero_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_le_refl_min_zero_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

// #integrity-audit (2026-06): `NNVerify.Rat.le_refl_min_zero_zero` has proof
// term `Rat.le_refl (Rat.min Rat.zero Rat.zero)`. Its transitive closure reaches
// `Rat.min` (still an admitted lattice axiom).
//
// NOTE (#3470 Lane #2/#3): `Rat.le_refl` has been GENUINELY ELIMINATED to a
// constructive kernel Theorem, so it no longer appears in the closure. The
// closure is therefore now exactly `{Rat.min}`: still NON-EMPTY, still honestly
// `AxiomDependent` on the remaining admitted lattice axiom `Rat.min`, with NO
// `sorry`/`sorryAx` and no rogue non-admitted axiom — this test pins exactly
// that honest state.
#[test]
fn test_le_refl_min_zero_zero_axiom_closure_only_admitted_domain() {
    use crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS;

    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("axiom_deps");
    let dep_strings: std::collections::HashSet<String> =
        deps.iter().map(|n| n.to_string()).collect();
    assert!(!dep_strings.contains("sorry"));
    assert!(!dep_strings.contains("sorryAx"));
    // Now rests on admitted domain axioms (`Rat.le_refl`, `Rat.min`), so the
    // closure is non-empty — the honest reclassification from the integrity
    // audit. (Was previously asserted empty under the overstated policy.)
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET} is now FULLY CONSTRUCTIVE — `Rat.min`/`Rat.max` (and \
         `Rat.{{min,max}}_def`, the lattice lemmas) are kernel-checked over the \
         quotient carrier, so its axiom closure is EMPTY; got {dep_strings:?}"
    );
    // Every axiom in the closure must be an admitted DOMAIN axiom — no rogue,
    // non-admitted, or trust-marker axiom may sneak in.
    for a in &deps {
        assert!(
            ADMITTED_DOMAIN_AXIOMS.contains(&a.to_string().as_str()),
            "unexpected non-admitted axiom in {TARGET} closure: {a}"
        );
    }
}

#[test]
fn test_le_refl_min_zero_zero_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_le_refl_min_zero_zero()
        .unwrap();
    env.init_nn_verify_tier_a_rat_le_refl_min_zero_zero()
        .unwrap();
    assert!(env.has_nn_verify_tier_a_rat_le_refl_min_zero_zero());
}
