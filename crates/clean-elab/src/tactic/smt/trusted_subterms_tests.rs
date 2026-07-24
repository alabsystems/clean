// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::trusted_subterms::{
    count_embedded_trusted_ay_terms, record_embedded_trust_subterms_from_proof,
};
use crate::tactic::ProofState;
use clean_kernel::{Environment, Expr, Name};

fn trusted_ay_term(goal: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![]),
        Expr::const_(Name::from_string(goal), vec![]),
    )
}

#[test]
fn test_count_embedded_trusted_ay_terms_counts_each_subterm() {
    let proof = Expr::app(trusted_ay_term("P"), trusted_ay_term("Q"));

    assert_eq!(
        count_embedded_trusted_ay_terms(&proof),
        2,
        "two embedded trustedAy applications should count as two sub-terms"
    );
}

#[test]
fn test_record_embedded_trust_subterms_from_proof_updates_ledger() {
    let mut state = ProofState::new(Environment::default(), Expr::prop());
    let proof = Expr::app(trusted_ay_term("P"), trusted_ay_term("Q"));

    let recorded = record_embedded_trust_subterms_from_proof(&mut state, &proof);

    assert_eq!(
        recorded, 2,
        "helper should return the exact embedded trust count"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        2,
        "proof-state ledger should mirror the embedded trustedAy sub-terms"
    );
}
