// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for VeriPB deletion enforcement (#3328).
//!
//! The `VeriPbStep::Delete` handler must mark the referenced derived
//! constraint as unavailable AND every PbRule that indexes into the
//! derived sequence must reject references to deleted constraints. The
//! production fix lives in `veripb.rs::verify` (marks `derived[id] = None`)
//! and `veripb.rs::check_rule_references_live` (pre-flight gate before
//! rule evaluation).
//!
//! These tests pin the invariant per-rule-variant so any future refactor
//! that narrows the check surfaces as a test failure.

use super::rules::PbRule;
use super::types::{PbConstraint, PbFormula};
use super::veripb::{VeriPbProof, VeriPbStep};
use super::PbError;

// --- Negative: each rule variant referencing a deleted constraint is rejected ---

#[test]
fn test_soundness_veripb_delete_blocks_addition_reference() {
    let mut formula = PbFormula::new(2);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, 2)], 1));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1)], 1),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 2)], 1),
        rule: PbRule::Input(1),
    });
    proof.add_step(VeriPbStep::Delete { id: 0 });
    // Addition referencing deleted index 0 must fail.
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1), (1, 2)], 2),
        rule: PbRule::Addition { left: 0, right: 1 },
    });

    let err = proof.verify().unwrap_err();
    assert!(
        matches!(err, PbError::IndexOutOfBounds { index: 0, .. }),
        "Addition referencing deleted constraint must be rejected, got: {err}"
    );
}

#[test]
fn test_soundness_veripb_delete_blocks_multiplication_reference() {
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1)], 1),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::Delete { id: 0 });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(2, 1)], 2),
        rule: PbRule::Multiplication {
            constraint: 0,
            scalar: 2,
        },
    });

    let err = proof.verify().unwrap_err();
    assert!(
        matches!(err, PbError::IndexOutOfBounds { index: 0, .. }),
        "Multiplication referencing deleted constraint must be rejected, got: {err}"
    );
}

#[test]
fn test_soundness_veripb_delete_blocks_division_reference() {
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(4, 1)], 4));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(4, 1)], 4),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::Delete { id: 0 });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(2, 1)], 2),
        rule: PbRule::Division {
            constraint: 0,
            divisor: 2,
        },
    });

    let err = proof.verify().unwrap_err();
    assert!(
        matches!(err, PbError::IndexOutOfBounds { index: 0, .. }),
        "Division referencing deleted constraint must be rejected, got: {err}"
    );
}

#[test]
fn test_soundness_veripb_delete_blocks_saturation_reference() {
    let mut formula = PbFormula::new(2);
    formula.add_constraint(PbConstraint::new(vec![(5, 1), (3, 2)], 3));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(5, 1), (3, 2)], 3),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::Delete { id: 0 });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(3, 1), (3, 2)], 3),
        rule: PbRule::Saturation(0),
    });

    let err = proof.verify().unwrap_err();
    assert!(
        matches!(err, PbError::IndexOutOfBounds { index: 0, .. }),
        "Saturation referencing deleted constraint must be rejected, got: {err}"
    );
}

#[test]
fn test_soundness_veripb_delete_blocks_rounding_reference() {
    let mut formula = PbFormula::new(2);
    formula.add_constraint(PbConstraint::new(vec![(4, 1), (2, 2)], 4));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(4, 1), (2, 2)], 4),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::Delete { id: 0 });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(2, 1), (1, 2)], 2),
        rule: PbRule::Rounding(0),
    });

    let err = proof.verify().unwrap_err();
    assert!(
        matches!(err, PbError::IndexOutOfBounds { index: 0, .. }),
        "Rounding referencing deleted constraint must be rejected, got: {err}"
    );
}

// --- Positive: deleting an unrelated constraint does not block valid derivation ---

#[test]
fn test_veripb_delete_allows_unrelated_derivation() {
    // Deleting a constraint must be local: derivations that reference OTHER
    // (still-live) constraints must continue to verify. Guards against an
    // over-eager fix that would invalidate ALL subsequent references.
    let mut formula = PbFormula::new(2);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, 2)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, -2)], 1));

    let mut proof = VeriPbProof::new(formula);
    // Step 0: x1 >= 1 from input 0.
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1)], 1),
        rule: PbRule::Input(0),
    });
    // Step 1: x2 >= 1 from input 1.
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 2)], 1),
        rule: PbRule::Input(1),
    });
    // Step 2: ~x2 >= 1 from input 2.
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, -2)], 1),
        rule: PbRule::Input(2),
    });
    // Delete step 0 (x1 >= 1) — unrelated to the resolution below.
    proof.add_step(VeriPbStep::Delete { id: 0 });
    // Resolve steps 1 and 2 on variable 2 to derive 0 >= 1 (contradiction).
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![], 1),
        rule: PbRule::GeneralizedResolution {
            left: 1,
            right: 2,
            var: 2,
        },
    });
    proof.add_step(VeriPbStep::Conclude);

    proof
        .verify()
        .expect("deletion of unrelated constraint must not block subsequent valid derivation");
}
