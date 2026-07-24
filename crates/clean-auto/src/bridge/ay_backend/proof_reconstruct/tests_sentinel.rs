// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for sentinel FVarId range guards (#2407).

use super::VariableMapping;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

#[test]
fn test_fvarid_sentinel_range_constant() {
    // Verify sentinel range covers top 65536 values
    assert_eq!(FVarId::SENTINEL_RANGE_START, u64::MAX - 65536);
    assert!(FVarId::new(u64::MAX).is_sentinel());
    assert!(FVarId::new(u64::MAX - 1).is_sentinel());
    assert!(FVarId::new(u64::MAX - 65536).is_sentinel());
    assert!(!FVarId::new(u64::MAX - 65537).is_sentinel());
    assert!(!FVarId::new(0).is_sentinel());
    assert!(!FVarId::new(42).is_sentinel());
}

#[test]
fn test_register_hypothesis_accepts_normal_fvarid() {
    let mut map = VariableMapping::new();
    let fvar_id = FVarId::new(42);
    let proof = Expr::fvar(fvar_id);
    let prop_ty = Expr::const_(Name::from_string("True"), vec![]);
    // Should not panic — FVarId 42 is well below sentinel range
    map.register_hypothesis("h0", fvar_id, proof, prop_ty);
    assert!(
        map.get_hypothesis("h0").is_some(),
        "hypothesis 'h0' should be retrievable after registration with normal FVarId"
    );
}

#[test]
#[should_panic(expected = "sentinel range")]
fn test_register_hypothesis_rejects_sentinel_fvarid() {
    let mut map = VariableMapping::new();
    let sentinel_id = FVarId::new(u64::MAX);
    let proof = Expr::fvar(sentinel_id);
    let prop_ty = Expr::const_(Name::from_string("True"), vec![]);
    // Should panic — sentinel FVarId would collide with negated-goal witness
    map.register_hypothesis("h_bad", sentinel_id, proof, prop_ty);
}

#[test]
fn test_register_var_accepts_normal_fvar() {
    let mut map = VariableMapping::new();
    let expr = Expr::fvar(FVarId::new(100));
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    // Should not panic — FVarId 100 is well below sentinel range
    map.register_var("x", expr, ty);
    assert!(
        map.get_var("x").is_some(),
        "variable 'x' should be retrievable after registration with normal FVarId"
    );
}

#[test]
#[should_panic(expected = "sentinel range")]
fn test_register_var_rejects_sentinel_fvar() {
    let mut map = VariableMapping::new();
    let expr = Expr::fvar(FVarId::new(u64::MAX - 10));
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    // Should panic — sentinel FVarId would collide with compound witnesses
    map.register_var("x_bad", expr, ty);
}

/// Regression test for #2433: compound witness FVarId was derived from step_id
/// instead of a dedicated witness counter. For proofs with >65536 steps where
/// a compound witness appears at a high index, the old code produced an FVarId
/// below the sentinel range (now caught by assert! in all builds per #2606).
///
/// This test creates a proof with 66001 steps: 66000 matched hypothesis assumes
/// plus 1 compound witness at index 66000 (> 65535). With the fix, the witness
/// counter is 0 (only 1 compound witness), producing FVarId u64::MAX-1 (valid).
#[test]
fn test_compound_witness_high_step_id_succeeds() {
    use super::{attempt_reconstruction, VariableMapping};
    use ay::Sort;
    use ay_core::{Proof, ProofStep, TermStore};
    use clean_kernel::ExprKind;

    let mut terms = TermStore::new();
    let hyp_term = terms.mk_var("h0", Sort::Bool);
    let unmatched_term = terms.mk_var("unmatched_compound", Sort::Bool);

    let mut map = VariableMapping::new();
    let hyp_fvar = FVarId::new(1);
    let hyp_proof = Expr::fvar(hyp_fvar);
    let prop_ty = Expr::const_(Name::from_string("True"), vec![]);
    map.register_hypothesis("h0", hyp_fvar, hyp_proof, prop_ty);

    let bool_ty = Expr::sort(clean_kernel::Level::Zero);
    map.register_var("h0", Expr::fvar(hyp_fvar), bool_ty.clone());
    map.register_var("unmatched_compound", Expr::fvar(FVarId::new(2)), bool_ty);

    // 66000 matched assumes + 1 compound witness at index 66000
    let mut proof = Proof::new();
    for _ in 0..66_000 {
        proof.add_step(ProofStep::Assume(hyp_term));
    }
    proof.add_step(ProofStep::Assume(unmatched_term));

    let negated_goal = Expr::const_(Name::from_string("UnrelatedGoal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    // The compound witness at step 66000 should succeed
    assert_eq!(
        result.stats.reconstructed_steps, 66_001,
        "all 66001 steps should reconstruct successfully"
    );
    assert!(
        result.stats.first_error.is_none(),
        "no errors expected, got: {:?}",
        result.stats.first_error
    );

    // The last step (compound witness) should produce a sentinel FVar
    let proof_term = result
        .proof_term
        .expect("last step should produce a proof term");
    match proof_term.kind() {
        ExprKind::FVar(id) => {
            assert!(
                id.is_sentinel(),
                "compound witness FVarId {} should be in sentinel range",
                id.as_u64()
            );
            // First compound witness: FVarId = u64::MAX - 1 - 0 = u64::MAX - 1
            assert_eq!(
                id.as_u64(),
                u64::MAX - 1,
                "first compound witness should get FVarId u64::MAX - 1"
            );
        }
        _ => panic!(
            "expected FVar for compound witness, got {:?}",
            proof_term.kind()
        ),
    }
}

/// Verify that multiple compound witnesses get sequential FVarIds based
/// on witness count (0, 1, 2, ...) rather than step index.
#[test]
fn test_compound_witness_sequential_allocation() {
    use super::{attempt_reconstruction, VariableMapping};
    use ay::Sort;
    use ay_core::{Proof, ProofStep, TermStore};
    use clean_kernel::ExprKind;

    let mut terms = TermStore::new();
    // Three distinct unmatched terms — each will become a compound witness
    let t0 = terms.mk_var("unmatched_0", Sort::Bool);
    let t1 = terms.mk_var("unmatched_1", Sort::Bool);
    let t2 = terms.mk_var("unmatched_2", Sort::Bool);

    let mut map = VariableMapping::new();
    let bool_ty = Expr::sort(clean_kernel::Level::Zero);
    map.register_var("unmatched_0", Expr::fvar(FVarId::new(10)), bool_ty.clone());
    map.register_var("unmatched_1", Expr::fvar(FVarId::new(11)), bool_ty.clone());
    map.register_var("unmatched_2", Expr::fvar(FVarId::new(12)), bool_ty);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(t0)); // step 0 → witness 0
    proof.add_step(ProofStep::Assume(t1)); // step 1 → witness 1
    proof.add_step(ProofStep::Assume(t2)); // step 2 → witness 2

    let negated_goal = Expr::const_(Name::from_string("UnrelatedGoal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.reconstructed_steps, 3);
    assert!(result.stats.first_error.is_none());

    // Last step (witness 2) should have FVarId = u64::MAX - 1 - 2
    let proof_term = result.proof_term.expect("should have proof term");
    match proof_term.kind() {
        ExprKind::FVar(id) => {
            assert!(id.is_sentinel());
            assert_eq!(
                id.as_u64(),
                u64::MAX - 1 - 2,
                "third compound witness should get FVarId u64::MAX - 3"
            );
        }
        _ => panic!("expected FVar, got {:?}", proof_term.kind()),
    }
}
