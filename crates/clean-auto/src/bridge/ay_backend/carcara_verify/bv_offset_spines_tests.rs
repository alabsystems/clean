// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The production adapter explicitly selects the versioned bounded rule.
use super::verify_alethe_proof;

const RULE: &str = "eq_simplify_bv_offset_spines";
fn certificate(defs: &str, theorem: &str) -> (String, String) {
    (format!("{defs}(assert (not {theorem}))(check-sat)"),format!("(assume h (not {theorem}))\n(step e (cl {theorem}) :rule {RULE})\n(step done (cl) :rule resolution :premises (h e))"))
}

#[test]
fn bounded_spines_run_through_the_production_adapter_with_causal_wrong_truth_controls() {
    for width in [1, 8, 64, 128] {
        let defs = format!("(declare-const x (_ BitVec {width}))");
        let max = format!("#b{}", "1".repeat(width));
        let theorem = format!("(= (= (bvadd (bvadd x {max}) (_ bv1 {width})) x) true)");
        let (problem, proof) = certificate(&defs, &theorem);
        assert!(verify_alethe_proof(&problem, &proof).unwrap());
        let false_theorem = theorem.replacen("true", "false", 1);
        let wrong = proof.replacen(
            &format!("(step e (cl {theorem})"),
            &format!("(step e (cl {false_theorem})"),
            1,
        );
        let error = verify_alethe_proof(&problem, &wrong).expect_err("wrong claimed truth");
        assert!(
            format!("{error}").contains("step 'e' with rule 'eq_simplify_bv_offset_spines'"),
            "{error}"
        );
    }
}

#[test]
fn bounded_spines_reject_alias_authority_and_frame_seventeen_in_the_adapter() {
    let defs = "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(assert (= x y))";
    let alias = "(= (= (bvadd (bvadd x #x01) #x02) (bvadd y #x03)) true)";
    let (problem, proof) = certificate(defs, alias);
    let error =
        verify_alethe_proof(&problem, &proof).expect_err("source alias needs explicit congruence");
    assert!(
        format!("{error}").contains("step 'e' with rule 'eq_simplify_bv_offset_spines'"),
        "{error}"
    );
    let mut source = "x".to_owned();
    for frames in 1..=17 {
        source = format!("(bvadd {source} #x00)");
        if frames >= 16 {
            let theorem = format!("(= (= {source} x) true)");
            let (problem, proof) = certificate("(declare-const x (_ BitVec 8))", &theorem);
            let result = verify_alethe_proof(&problem, &proof);
            if frames == 16 {
                assert!(result.unwrap());
            } else {
                let error = result.expect_err("frame 17");
                assert!(format!("{error}").contains("step 'e'"), "{error}");
            }
        }
    }
}
