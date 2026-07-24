// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Invariance regression tests for chain resolution soundness (#3345).
//!
//! These tests exercise the key invariant of `resolution::check_resolution`:
//! the chain-resolution path must never depend on the *claimed* result clause
//! to guide its pivot selection. Independently of what clause the prover
//! claims, the verdict for a given (premises, claim) pair must only accept
//! when the premises genuinely derive the claim.
//!
//! Rationale (AI Model 3.1 Pro soundness review, F1):
//! A previous implementation used the claimed clause's literal set as a
//! filter to decide which literals were "candidates for elimination". When
//! the prover claimed the empty clause, ALL literals became elimination
//! candidates, letting greedy pairing produce a bogus empty resolvent even
//! from jointly-satisfiable premises. The fixed implementation folds
//! premises left-to-right, branching on every complementary pivot pair,
//! with pivot selection computed from the premises alone. It then compares
//! the computed resolvent set against the claimed clause.
//!
//! The tests here verify that invariant as a behavioral contract: if any
//! future change re-introduces claim-guided pivot selection, at least one
//! of the 6 permutations of the AI Model F1 satisfiable premise set would
//! flip to accepting the empty clause.

use super::dag::{SmtProofDag, SmtProofStep, SmtSort, SmtStepId, SmtTerm, SmtTermId};
use super::resolution::check_resolution;
use super::trust::StepTrustLevel;

/// Build the AI Model F1 jointly-satisfiable 3-premise DAG:
/// `{X, Y}`, `{~X, Z}`, `{~Y, ~Z}`.
///
/// Returns `(dag, derived_clauses, [z, not_z])` so callers can reuse the
/// same term IDs for both the satisfiability test and the positive control.
fn build_gemini_f1_dag() -> (
    SmtProofDag,
    Vec<Option<Vec<SmtTermId>>>,
    SmtTermId, // z
    SmtTermId, // not_z
) {
    let mut dag = SmtProofDag::new();
    let x = dag.add_term(SmtTerm::Var("X".to_string(), SmtSort::Bool));
    let y = dag.add_term(SmtTerm::Var("Y".to_string(), SmtSort::Bool));
    let z = dag.add_term(SmtTerm::Var("Z".to_string(), SmtSort::Bool));
    let not_x = dag.add_term(SmtTerm::Not(x));
    let not_y = dag.add_term(SmtTerm::Not(y));
    let not_z = dag.add_term(SmtTerm::Not(z));

    // Placeholder steps so premise step IDs line up with indices 0, 1, 2.
    let _s0 = dag.add_step(SmtProofStep::Assume(x));
    let _s1 = dag.add_step(SmtProofStep::Assume(not_x));
    let _s2 = dag.add_step(SmtProofStep::Assume(y));

    let derived = vec![
        Some(vec![x, y]),
        Some(vec![not_x, z]),
        Some(vec![not_y, not_z]),
    ];
    (dag, derived, z, not_z)
}

#[test]
fn test_invariance_satisfiable_premises_empty_claim_all_orderings() {
    // Premises: {X, Y}, {~X, Z}, {~Y, ~Z}. Model X=0, Y=1, Z=1 satisfies
    // all three. No pivot sequence derives the empty clause.
    //
    // For EVERY permutation of these 3 premises, claiming the empty clause
    // MUST be rejected.
    let (dag, derived, _z, _not_z) = build_gemini_f1_dag();
    let step_id = SmtStepId(3);
    let premise_permutations: [[SmtStepId; 3]; 6] = [
        [SmtStepId(0), SmtStepId(1), SmtStepId(2)],
        [SmtStepId(0), SmtStepId(2), SmtStepId(1)],
        [SmtStepId(1), SmtStepId(0), SmtStepId(2)],
        [SmtStepId(1), SmtStepId(2), SmtStepId(0)],
        [SmtStepId(2), SmtStepId(0), SmtStepId(1)],
        [SmtStepId(2), SmtStepId(1), SmtStepId(0)],
    ];

    for (i, perm) in premise_permutations.iter().enumerate() {
        let verdict = check_resolution(&dag, step_id, &[], perm, None, &derived);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "INVARIANCE: permutation {} of satisfiable premises must REJECT \
             empty-clause claim (checker must never let claimed clause guide \
             pivot selection): {:?}",
            i,
            verdict.detail,
        );
    }
}

#[test]
fn test_invariance_valid_resolvent_still_accepts() {
    // Positive control: the SAME jointly-SAT premise set DOES derive the
    // tautological clause {Z, ~Z}. Fold (0, 1, 2) on X then Y: {X,Y} + {~X,Z}
    // → {Y, Z}; {Y, Z} + {~Y, ~Z} → {Z, ~Z}.
    //
    // The checker must still accept this valid claim — demonstrating that
    // the invariance test above rejects specifically because the empty
    // claim is underivable, not because the checker is over-strict.
    let (dag, derived, z, not_z) = build_gemini_f1_dag();
    let step_id = SmtStepId(3);
    let verdict = check_resolution(
        &dag,
        step_id,
        &[z, not_z],
        &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
        None,
        &derived,
    );
    assert_eq!(
        verdict.trust_level,
        StepTrustLevel::KernelVerified,
        "POSITIVE CONTROL: the tautological clause {{Z, ~Z}} IS a valid \
         resolvent of the premise set and must be accepted: {:?}",
        verdict.detail,
    );
}
