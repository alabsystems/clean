// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::verify_alethe_proof;
#[test]
fn full_width_reconstruction_production_adapter_checks_actual_bv_semantics() {
    for width in [1, 8, 64, 128] {
        let mut parts = Vec::new();
        for low in 0..width {
            let piece = format!(
                "((_ zero_extend {}) ((_ extract {low} {low}) x))",
                width - 1
            );
            parts.push(if low == 0 {
                piece
            } else {
                format!("(bvshl {piece} (_ bv{low} {width}))")
            });
        }
        let mut packed = parts.remove(0);
        for p in parts {
            packed = format!("(bvor {packed} {p})");
        }
        let source = format!("(= {packed} x)");
        let wrong = format!("(= {packed} y)");
        let problem=format!("(declare-const x (_ BitVec {width}))(declare-const y (_ BitVec {width}))(assert (not {source}))(check-sat)");
        let proof=format!("(assume h (not {source}))\n(step e (cl {source}) :rule bv_reconstruct_v1)\n(step done (cl) :rule resolution :premises (h e))");
        assert!(verify_alethe_proof(&problem, &proof).unwrap());
        let wrong = proof.replacen(
            &format!("(step e (cl {source})"),
            &format!("(step e (cl {wrong})"),
            1,
        );
        let error = verify_alethe_proof(&problem, &wrong).expect_err("one changed semantic step");
        assert!(
            format!("{error}").contains("step 'e' with rule 'bv_reconstruct_v1'"),
            "{error}"
        );
    }
}
