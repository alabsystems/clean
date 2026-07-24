// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser/format-detection properties: PB/VeriPB parsing and the pipeline
//! format-detection layer. These properties focus on panic-safety and
//! round-trip consistency.

use super::generators::cnf_strategy;
use crate::sat_verify::pipeline::{detect_format, verify_any_proof};
use crate::sat_verify::pseudo_boolean::{
    cnf_to_pb, is_tautology, normalize, parse_opb, parse_veripb, write_opb, PbConstraint,
    PbFormula, PbRule, VeriPbProof, VeriPbStep,
};

use proptest::collection::vec;
use proptest::prelude::*;

// ============================================================================
// PB / VeriPB soundness properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Soundness: multiplication by zero must be rejected.
    #[test]
    fn prop_pb_multiply_by_zero_rejected(
        coeff in 1i64..=10,
        lit in 1i32..=5,
    ) {
        let mut formula = PbFormula::new(5);
        formula.add_constraint(PbConstraint::new(vec![(coeff, lit)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(coeff, lit)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![], 0),
            rule: PbRule::Multiplication { constraint: 0, scalar: 0 },
        });
        prop_assert!(
            proof.verify().is_err(),
            "VeriPB multiplication by zero accepted — soundness violated"
        );
    }

    /// Soundness: division by zero rejected.
    #[test]
    fn prop_pb_divide_by_zero_rejected(
        coeff in 1i64..=10,
        lit in 1i32..=5,
    ) {
        let mut formula = PbFormula::new(5);
        formula.add_constraint(PbConstraint::new(vec![(coeff, lit)], 1));

        let mut proof = VeriPbProof::new(formula);
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(coeff, lit)], 1),
            rule: PbRule::Input(0),
        });
        proof.add_step(VeriPbStep::PolynomialAddition {
            result: PbConstraint::new(vec![(coeff, lit)], 1),
            rule: PbRule::Division { constraint: 0, divisor: 0 },
        });
        prop_assert!(
            proof.verify().is_err(),
            "VeriPB division by zero accepted — soundness violated"
        );
    }

    /// Tautology detection is consistent with the arithmetic definition.
    #[test]
    fn prop_pb_tautology_trivial_bounds(
        rhs in -100i64..=0,
    ) {
        let c = PbConstraint::new(vec![], rhs);
        prop_assert!(is_tautology(&c), "0 >= {rhs} should be tautology");
    }

    /// Normalization does not panic on arbitrary constraints.
    #[test]
    fn prop_pb_normalize_no_panic(
        coeffs in vec((-1000i64..=1000, -5i32..=5), 0..=5),
        degree in -1000i64..=1000,
    ) {
        let c = PbConstraint::new(coeffs, degree);
        let result = std::panic::catch_unwind(|| normalize(&c));
        prop_assert!(result.is_ok(), "normalize panicked");
    }

    /// CNF-to-PB conversion preserves constraint count.
    #[test]
    fn prop_pb_cnf_to_pb_preserves_count(
        clauses in cnf_strategy(4, 6, 3),
    ) {
        let pb = cnf_to_pb(&clauses);
        prop_assert_eq!(pb.constraints.len(), clauses.len());
    }

    /// OPB roundtrip: writing then parsing preserves constraint count.
    #[test]
    fn prop_pb_opb_roundtrip_preserves_count(
        coeffs in vec((1i64..=100, 1i32..=5), 1..=5),
        degree in 1i64..=20,
    ) {
        let mut formula = PbFormula::new(5);
        formula.add_constraint(PbConstraint::new(coeffs, degree));
        let text = write_opb(&formula);
        let reparsed = parse_opb(&text).expect("roundtrip should parse");
        prop_assert_eq!(reparsed.constraints.len(), formula.constraints.len());
    }

    /// `parse_opb` does not panic on arbitrary text.
    #[test]
    fn prop_pb_parse_opb_no_panic(
        text in "[a-zA-Z0-9 \\-+=;<>~#*\n]{0,200}",
    ) {
        let result = std::panic::catch_unwind(|| parse_opb(&text));
        prop_assert!(result.is_ok(), "parse_opb panicked on text: {text:?}");
    }

    /// `parse_veripb` does not panic on arbitrary text.
    #[test]
    fn prop_pb_parse_veripb_no_panic(
        text in "[a-zA-Z0-9 \\-+=;<>~#*\n]{0,200}",
    ) {
        let result = std::panic::catch_unwind(|| parse_veripb(&text, PbFormula::new(3)));
        prop_assert!(result.is_ok(), "parse_veripb panicked");
    }
}

// ============================================================================
// Pipeline (format detection + dispatch) properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// `detect_format` must not panic on arbitrary bytes.
    #[test]
    fn prop_pipeline_detect_format_no_panic(
        data in vec(any::<u8>(), 0..=200),
    ) {
        let result = std::panic::catch_unwind(|| detect_format(&data));
        prop_assert!(result.is_ok(), "detect_format panicked");
    }

    /// `verify_any_proof` must not panic on arbitrary bytes.
    #[test]
    fn prop_pipeline_verify_any_no_panic(
        formula in vec(any::<u8>(), 0..=100),
        proof in vec(any::<u8>(), 0..=100),
    ) {
        let result = std::panic::catch_unwind(|| verify_any_proof(&formula, &proof));
        prop_assert!(result.is_ok(), "verify_any_proof panicked");
    }

    /// Deterministic: verifying twice gives the same answer.
    #[test]
    fn prop_pipeline_verify_deterministic(
        formula in vec(any::<u8>(), 0..=50),
        proof in vec(any::<u8>(), 0..=50),
    ) {
        let r1 = verify_any_proof(&formula, &proof).map(|r| r.valid).ok();
        let r2 = verify_any_proof(&formula, &proof).map(|r| r.valid).ok();
        prop_assert_eq!(r1, r2);
    }
}
