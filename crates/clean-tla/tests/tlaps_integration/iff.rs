// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Biconditional obligation and environment regression controls.

use clean_tla::tactic::prove_tla_obligation;
use clean_tla::{TlaFormula, TlaObligation};

// ================================================================
// Biconditional (Iff) Tests - Root Cause Analysis for #67
// ================================================================

/// Regression guard: Iff reflexivity (TRUE ↔ TRUE) requires Iff.intro
///
/// HISTORY: This was a canary test documenting missing Iff.intro (#67).
/// TlaTacticEngine::new() now calls env.init_iff(), so this passes.
#[test]
fn test_iff_reflexivity_true_true() {
    // Simplest possible biconditional: TRUE ↔ TRUE
    let obligation = TlaObligation {
        module: "IffTest".to_string(),
        line: Some(1),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Iff(Box::new(TlaFormula::True), Box::new(TlaFormula::True)),
        tactic_hint: Some("auto".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // Iff.intro is now available in the environment (Part of #67)
    assert!(
        result.proved,
        "Iff reflexivity (TRUE ↔ TRUE) should pass with Iff.intro available: {:?}",
        result
    );
}

/// Discriminating test: `FALSE ↔ FALSE` PASSES via superposition
///
/// This test documents that some Iff goals can be proved without Iff.intro
/// via the superposition prover (likely through CNF/SMT reasoning).
#[test]
fn test_iff_false_false_passes_via_superposition() {
    let obligation = TlaObligation {
        module: "IffTest".to_string(),
        line: Some(2),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Iff(Box::new(TlaFormula::False), Box::new(TlaFormula::False)),
        tactic_hint: Some("auto".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // This passes via superposition or simp, not tauto's split_
    // The solver treats Iff semantically
    assert!(
        result.proved,
        "Iff (FALSE ↔ FALSE) should be proved: {:?}",
        result
    );

    // Document which tactic succeeded (for tracking)
    println!(
        "FALSE ↔ FALSE proved via: {:?}, certificate: {:?}",
        result.tactics_tried, result.certificate
    );
}

/// Discriminating test: `(TRUE → TRUE) ↔ (TRUE → TRUE)` PASSES via superposition
///
/// Simple implication equivalence - passes via superposition
#[test]
fn test_iff_impl_passes_via_superposition() {
    let obligation = TlaObligation {
        module: "IffTest".to_string(),
        line: Some(3),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Iff(
            Box::new(TlaFormula::Implies(
                Box::new(TlaFormula::True),
                Box::new(TlaFormula::True),
            )),
            Box::new(TlaFormula::Implies(
                Box::new(TlaFormula::True),
                Box::new(TlaFormula::True),
            )),
        ),
        tactic_hint: Some("auto".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // This passes via superposition
    assert!(
        result.proved,
        "Iff with implications passes via superposition: {:?}",
        result
    );
}

/// Test verifying the exact mechanism: split_ on Iff without Iff.intro
///
/// This test constructs an Iff goal manually and verifies Iff.intro presence.
#[test]
fn test_iff_intro_missing_in_default_env() {
    use clean_kernel::env::Environment;
    use clean_kernel::name::Name;

    // Create empty environment (like TlaTacticEngine::new() does)
    let env = Environment::new();

    // Check that Iff.intro is NOT in the environment
    let iff_intro_name = Name::from_string("Iff.intro");
    assert!(
        env.get_const(&iff_intro_name).is_none(),
        "Empty environment should not have Iff.intro - this is the root cause of #67"
    );

    // Also verify Iff itself is missing
    let iff_name = Name::from_string("Iff");
    assert!(
        env.get_const(&iff_name).is_none(),
        "Empty environment should not have Iff type"
    );
}

/// Test showing that initialized environment DOES have Iff.intro
#[test]
fn test_iff_intro_present_after_init() {
    use clean_kernel::env::Environment;
    use clean_kernel::name::Name;

    // Create environment WITH init_iff
    let mut env_with_iff = Environment::new();
    env_with_iff.init_iff().expect("init_iff should succeed");

    // Verify Iff.intro IS in the initialized environment
    let iff_intro_name = Name::from_string("Iff.intro");
    assert!(
        env_with_iff.get_const(&iff_intro_name).is_some(),
        "Initialized environment should have Iff.intro"
    );

    // Also verify Iff.mp and Iff.mpr
    let iff_mp_name = Name::from_string("Iff.mp");
    let iff_mpr_name = Name::from_string("Iff.mpr");
    assert!(
        env_with_iff.get_const(&iff_mp_name).is_some(),
        "Initialized environment should have Iff.mp"
    );
    assert!(
        env_with_iff.get_const(&iff_mpr_name).is_some(),
        "Initialized environment should have Iff.mpr"
    );
}
