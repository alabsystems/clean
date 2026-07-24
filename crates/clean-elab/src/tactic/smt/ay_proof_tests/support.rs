// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Reset shared trust observability counters before each certificate test.
///
/// This file relies directly on a clean `ay_proof_count()` baseline for its
/// whole-goal `trustedAy` delta checks. The wider reset keeps the neighboring
/// trust metrics on an explicit zero baseline while these serial certificate
/// tests run.
pub(super) fn reset_all_trust_counters() {
    reset_sorry_counter();
    reset_arith_counter();
    reset_ay_counter();
    reset_ay_reconstruction_failure_counter();
    reset_local_ay_reconstruction_success_counter();
}

pub(super) fn setup_certificate_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("P axiom should register");
    env
}

pub(super) fn prop_p() -> Expr {
    Expr::const_(Name::from_string("P"), vec![])
}

pub(super) fn not(expr: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr)
}

pub(super) fn false_prop() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

pub(super) fn contradiction_state() -> ProofState {
    let p = prop_p();
    ProofState::with_context(
        setup_certificate_env(),
        false_prop(),
        vec![
            LocalDecl {
                fvar: FVarId::new(1),
                name: "hp".to_string(),
                ty: p.clone(),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "hnp".to_string(),
                ty: not(p),
                value: None,
            },
        ],
    )
}

pub(super) fn contradiction_formula() -> CnfFormula {
    let mut formula = CnfFormula::new();
    formula.add_clause(vec![1]);
    formula.add_clause(vec![-1]);
    formula
}

pub(super) fn contradiction_drat_proof() -> DratProof {
    let mut proof = DratProof::new();
    proof.operations.push(DratOp::Add(vec![]));
    proof
}

pub(super) fn contradiction_lrat_proof() -> LratProof {
    let mut proof = LratProof::new();
    proof.operations.push(LratOp::Add {
        id: 3,
        clause: vec![],
        hints: vec![1, 2],
    });
    proof
}

pub(super) fn trusted_ay_proof(target: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![Level::zero()]),
        target,
    )
}

pub(super) fn trusted_bridge_candidate(target: Expr) -> BridgeReconstructionCandidate {
    BridgeReconstructionCandidate {
        proof: trusted_ay_proof(target),
        trust_subterm_count: 1,
    }
}

pub(super) fn run_verifystrict_public_certificate_with_injected_candidate(
    logic: AyLogic,
    run: impl FnOnce(&mut ProofState, AyProofConfig) -> Result<(), TacticError>,
) -> (ProofState, Result<(), TacticError>, u64) {
    reset_all_trust_counters();
    let mut state = contradiction_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);
    let _guard = install_test_bridge_candidate(trusted_bridge_candidate(target));
    let ay_before = ay_proof_count();

    let result = run(
        &mut state,
        AyProofConfig::new(
            AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict),
            logic,
            contradiction_formula(),
        ),
    );

    (state, result, ay_proof_count() - ay_before)
}

pub(super) fn assert_certificate_recovery_avoids_non_ay_fallbacks(
    state: &ProofState,
    context: &str,
) {
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.sorry_count, 0,
        "{context} should not degrade to sorry on a simple contradiction"
    );
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "{context} should not route through trustedArith on a propositional contradiction"
    );
}
