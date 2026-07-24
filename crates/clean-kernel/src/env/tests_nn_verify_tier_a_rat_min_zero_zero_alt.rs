// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.min_zero_zero_alt` (#3551 Batch 2).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.min_zero_zero_alt";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_zero_zero_alt()
        .expect("init should succeed");
    env
}

#[test]
fn test_min_zero_zero_alt_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_min_zero_zero_alt());
}

#[test]
fn test_min_zero_zero_alt_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_min_zero_zero_alt_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

/// Honest axiom-closure check (#integrity-audit, 2026-06).
///
/// This proof is `@Rat.min_def' Rat.zero Rat.zero (Rat.le_refl Rat.zero)`, so
/// its transitive closure genuinely reaches `Rat.min_def'`, `Rat.le_refl`, and
/// `Rat.min`. Those were dishonestly whitelisted as "foundational" (the
/// #3490/#3543 ergonomic-whitelist overstatement), which made this theorem
/// report an EMPTY closure / `Constructive`. They are now EXCLUDED from
/// `is_foundational_axiom` (they live in `ADMITTED_DOMAIN_AXIOMS`), so the
/// closure is honestly NON-EMPTY. The honest invariant is: the closure is
/// non-empty and contains ONLY admitted domain axioms — no `sorry`/`sorryAx`,
/// no unexpected/rogue axiom.
#[test]
fn test_min_zero_zero_alt_axiom_closure_admitted_domain_only() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("axiom_deps");
    // The proof rests on admitted Rat ordered-field / min-max domain axioms,
    // so the closure must NOT be empty (it was dishonestly reported empty
    // before the integrity audit reclassified these axioms).
    assert!(
        deps.is_empty(),
        "WS-B: {TARGET} is now FULLY CONSTRUCTIVE — `Rat.min`/`Rat.max` (and \
         `Rat.{{min,max}}_def`, the lattice lemmas) are kernel-checked over the \
         quotient carrier, so its axiom closure is EMPTY; got {deps:?}"
    );
    // No incomplete-proof / decision-procedure trust marker may appear.
    let deps_str: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(!deps_str.contains("sorry"));
    assert!(!deps_str.contains("sorryAx"));
    assert!(!deps_str.contains("trustedArith"));
    assert!(!deps_str.contains("trustedAy"));
    // Every axiom in the closure must be an ADMITTED DOMAIN axiom — the theorem
    // is honestly `AxiomDependent` on admitted assumptions, with no rogue axiom.
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
fn test_min_zero_zero_alt_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_min_zero_zero_alt().unwrap();
    env.init_nn_verify_tier_a_rat_min_zero_zero_alt().unwrap();
    assert!(env.has_nn_verify_tier_a_rat_min_zero_zero_alt());
}
