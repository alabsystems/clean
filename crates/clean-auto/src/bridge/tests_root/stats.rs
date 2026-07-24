// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn assert_smt_unsat_method(result: &SmtVerificationResult) {
    assert!(
        matches!(
            result,
            SmtVerificationResult::Verified(_) | SmtVerificationResult::Unverified { .. }
        ),
        "prove should succeed (Verified or Unverified), got {:?}",
        result
    );

    if let SmtVerificationResult::Verified(proof) = result {
        assert!(
            matches!(proof.method(), ProofMethod::SmtUnsat),
            "stats test proof should use SmtUnsat method, got {:?}",
            proof.method()
        );
    }
    if let SmtVerificationResult::Unverified { method, .. } = result {
        assert!(
            matches!(method, ProofMethod::SmtUnsat),
            "stats test should use SmtUnsat method, got {:?}",
            method
        );
    }
}

#[test]
fn test_stats() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let hyp = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis(&hyp)
        .expect("equality hypothesis should register successfully");

    let goal = make_eq(a_ty, b, a);
    let result = bridge
        .prove(&goal)
        .expect("prove should return a verification result");
    assert_smt_unsat_method(&result);

    let stats = bridge.stats();
    assert_eq!(
        stats.num_terms, 2,
        "Should have exactly 2 terms (constants a, b), got {}",
        stats.num_terms
    );
    assert!(
        stats.num_vars >= 1,
        "Solver should have at least 1 variable after proving, got {}",
        stats.num_vars
    );
}
