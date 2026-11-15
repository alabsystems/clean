// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The real certificate adapter explicitly selects Clean's checked rule dialect.
use super::verify_alethe_proof;

#[test]
fn bv_offset_rule_runs_through_the_production_adapter() {
    for width in [1, 8, 64, 128] {
        let theorem = format!("(= (= (bvadd x (_ bv0 {width})) (bvadd (_ bv1 {width}) x)) false)");
        let problem =
            format!("(declare-const x (_ BitVec {width}))(assert (not {theorem}))(check-sat)");
        let proof = format!("(assume h (not {theorem}))\n(step e (cl {theorem}) :rule eq_simplify)\n(step done (cl) :rule resolution :premises (h e))");
        assert!(verify_alethe_proof(&problem, &proof).unwrap());
        // Keep the authored problem and assumption identical. Only the
        // intrinsic rule's claimed value is wrong, so this must fail at e.
        let wrong_theorem = theorem.replacen("false", "true", 1);
        let wrong = proof.replacen(
            &format!("(step e (cl {theorem})"),
            &format!("(step e (cl {wrong_theorem})"),
            1,
        );
        let error = verify_alethe_proof(&problem, &wrong).expect_err("wrong scalar value");
        assert!(
            format!("{error}").contains("step 'e' with rule 'eq_simplify'"),
            "{error}"
        );
    }
}
