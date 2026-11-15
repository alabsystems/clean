// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::verify_alethe_proof;

#[test]
fn array_const_select_production_clean_adapter_rederives_and_refuses_false_units() {
    let read = "(select ((as const (Array (_ BitVec 32) Bool)) f) k)";
    let claim = format!("(= {read} f)");
    let problem = format!("(set-logic ALL)(declare-const k (_ BitVec 32))(declare-const f Bool)(declare-const g Bool)(assert (not {claim}))(check-sat)");
    let proof = format!("(assume h (not {claim}))(step e (cl {claim}) :rule array_const_select_v1)(step done (cl) :rule resolution :premises (h e))");
    assert!(verify_alethe_proof(&problem, &proof).unwrap());
    let forged = proof.replacen(
        &format!("(step e (cl {claim})"),
        &format!("(step e (cl (= {read} g))"),
        1,
    );
    let error =
        verify_alethe_proof(&problem, &forged).expect_err("a different fill is not the unit");
    assert!(
        format!("{error}").contains("step 'e' with rule 'array_const_select_v1'"),
        "{error}"
    );
}
