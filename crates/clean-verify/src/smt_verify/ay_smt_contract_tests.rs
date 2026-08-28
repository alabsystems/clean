// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`super`] (`ay_smt_contract`), externalized verbatim from the
//! in-file `mod tests` (paragon files_over_1000 paydown; behavior identical —
//! the module is `#[path]`-included from the parent, so `super::*` resolves
//! exactly as before).

use super::*;
use crate::smt_verify::dag::{SmtSort, SmtSymbol, SmtTerm, SmtTermId};

fn add_binop(dag: &mut SmtProofDag, op: &str, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
    dag.add_term(SmtTerm::App(
        SmtSymbol::Named(op.to_string()),
        vec![lhs, rhs],
    ))
}

fn build_simple_lra_proof(kind: TheoryLemmaDetail) -> SmtProofDag {
    let mut dag = SmtProofDag::new();
    dag.declare("x".to_string(), SmtSort::Real);

    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
    let zero = dag.add_term(SmtTerm::Int(0));
    let neg_one = dag.add_term(SmtTerm::Int(-1));

    let ge_x_0 = add_binop(&mut dag, ">=", x, zero);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_0 = dag.add_term(SmtTerm::Not(ge_x_0));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    let s0 = dag.add_step(SmtProofStep::Assume(ge_x_0));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_neg1));
    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lra,
        kind,
        clause: vec![not_ge_x_0, not_le_x_neg1],
    });
    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s0, s2],
        pivot: Some(ge_x_0),
    });
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(le_x_neg1),
    });

    dag
}

#[test]
fn test_standard_qf_lra_contract_has_farkas_obligation() {
    let contract = standard_qf_lra_contract();
    assert!(contract.obligations.iter().any(|obligation| {
        obligation.theory == SmtTheory::Lra
            && obligation.required_detail == RequiredDetail::FarkasCoefficients
    }));
}

#[test]
fn test_standard_qf_uf_contract_has_congruence_obligation() {
    let contract = standard_qf_uf_contract();
    assert!(contract.obligations.iter().any(|obligation| {
        obligation.theory == SmtTheory::Euf
            && obligation.required_detail == RequiredDetail::CongruencePaths
    }));
}

#[test]
fn test_standard_bv_contract_has_bitblast_obligation() {
    let contract = standard_bv_contract();
    assert!(contract.obligations.iter().any(|obligation| {
        obligation.theory == SmtTheory::Bv
            && obligation.required_detail == RequiredDetail::BitBlastWitness
    }));
}

#[test]
fn test_verify_contract_simple_valid_proof() {
    let dag = build_simple_lra_proof(TheoryLemmaDetail::LraFarkas {
        coefficients: vec![(1, 1), (1, 1)],
    });
    let result = verify_ay_contract(&dag, &standard_qf_lra_contract());

    assert!(result.passed, "violations: {:?}", result.violations);
    assert!(result.coverage.is_fully_verified());
    assert_eq!(
        result.coverage.theory_lemma_counts.get(&SmtTheory::Lra),
        Some(&1)
    );
}

#[test]
fn test_verify_contract_missing_theory_detail() {
    let dag = build_simple_lra_proof(TheoryLemmaDetail::Generic);
    let result = verify_ay_contract(&dag, &standard_qf_lra_contract());

    assert!(!result.passed);
    assert!(result
        .violations
        .iter()
        .any(|violation| matches!(violation, ContractViolation::MissingTheoryDetail { theory, required, .. } if *theory == SmtTheory::Lra && *required == RequiredDetail::FarkasCoefficients)));
}

#[test]
fn test_verify_contract_trust_gap_in_full_mode() {
    let dag = build_simple_lra_proof(TheoryLemmaDetail::Generic);
    let contract = SmtProofContract {
        solver_version: "ay".to_string(),
        logic: SmtLogic::QfLra,
        features_used: features_for_logic(SmtLogic::QfLra),
        obligations: vec![TheoryProofObligation {
            theory: SmtTheory::Lra,
            required_detail: RequiredDetail::GenericLemma,
            minimum_trust: StepTrustLevel::Trusted,
        }],
        completeness: ProofCompleteness::Full,
    };
    let result = verify_ay_contract(&dag, &contract);

    assert!(!result.passed);
    assert!(result.violations.iter().any(|violation| {
        matches!(
            violation,
            ContractViolation::UnexpectedTrustStep {
                actual: StepTrustLevel::Trusted,
                required: StepTrustLevel::KernelVerified,
                ..
            }
        )
    }));
    assert!(result.violations.iter().any(|violation| {
        matches!(
            violation,
            ContractViolation::ExcessTrustSteps {
                completeness: ProofCompleteness::Full,
                ..
            }
        )
    }));
}

#[test]
fn test_verify_contract_structural_only_accepts_trust() {
    let dag = build_simple_lra_proof(TheoryLemmaDetail::Generic);
    let contract = SmtProofContract {
        solver_version: "ay".to_string(),
        logic: SmtLogic::QfLra,
        features_used: features_for_logic(SmtLogic::QfLra),
        obligations: vec![TheoryProofObligation {
            theory: SmtTheory::Lra,
            required_detail: RequiredDetail::GenericLemma,
            minimum_trust: StepTrustLevel::Trusted,
        }],
        completeness: ProofCompleteness::StructuralOnly,
    };
    let result = verify_ay_contract(&dag, &contract);

    assert!(result.passed, "violations: {:?}", result.violations);
}

#[test]
fn test_contract_registry_default_has_entries() {
    let registry = SmtContractRegistry::default();
    assert!(!registry.is_empty());
    assert!(registry.feature_mapping_len() > 0);
    assert!(registry.logic_contract_len() > 0);
    assert!(registry
        .obligations_for_feature(SolverFeature::TheoryLemma)
        .is_some());
}

#[test]
fn test_registry_lookup_by_logic() {
    let registry = SmtContractRegistry::default();
    let contract = registry
        .get_by_logic(SmtLogic::QfLra)
        .expect("QF_LRA contract should be registered");

    assert_eq!(contract.logic, SmtLogic::QfLra);
    assert!(contract.obligations.iter().any(|obligation| {
        obligation.theory == SmtTheory::Lra
            && obligation.required_detail == RequiredDetail::FarkasCoefficients
    }));
}

#[test]
fn test_full_pipeline_contract_plus_verify() {
    let dag = build_simple_lra_proof(TheoryLemmaDetail::LraFarkas {
        coefficients: vec![(1, 1), (1, 1)],
    });
    let proof_result = verify_smt_proof(&dag, VerifyMode::Strict);
    let contract_result = verify_ay_contract(&dag, &standard_qf_lra_contract());

    assert!(
        proof_result.valid,
        "proof error: {:?}",
        proof_result.first_error
    );
    assert!(
        contract_result.passed,
        "violations: {:?}",
        contract_result.violations
    );
    assert!(contract_result.coverage.is_fully_verified());
    // A genuine, fully-verified refutation discharges the obligation.
    assert!(
        contract_result.fully_verified,
        "a fully-verified refutation must discharge the ay contract",
    );
}

// SOUNDNESS (root cause B/C): a proof whose empty clause is laundered from a
// structurally-accepted step's *false* clause structurally derives the empty
// clause (`verification.valid == true`) but is NOT a discharged obligation.
// `fully_verified` must be false; under a `Full` contract, `passed` must be
// false too (the per-step gate rejects the structurally-accepted hole). See
// docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md.
#[test]
fn test_verify_contract_holey_launder_not_discharged() {
    // assume p; bv theory-lemma claiming {¬p} (unparseable -> structurally
    // accepted, admitting the false unit); resolve to empty.
    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
    let not_p = dag.add_term(SmtTerm::Not(p));

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    let s1 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Bv,
        kind: TheoryLemmaDetail::BvBitBlast {
            gate_type: None,
            width: None,
        },
        clause: vec![not_p],
    });
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(p),
    });

    // The proof structurally derives the empty clause (real hole).
    let verification = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(verification.valid, "exploit must derive the empty clause");
    assert!(verification.stats.structurally_accepted > 0);

    // The `standard_full_contract` is `ProofCompleteness::Partial`, which by
    // documented design ACCEPTS holes — so `passed` is true (this is exactly
    // the audit finding). The soundness invariant is that it must NEVER be
    // reported as a discharged obligation: `fully_verified` must be false.
    let partial = verify_ay_contract(&dag, &standard_full_contract());
    assert!(
        !partial.fully_verified,
        "holey laundered proof must NOT be marked fully verified (discharge)",
    );

    // A genuine `Full`-completeness contract rejects the structurally-accepted
    // hole at the per-step gate: `passed` is false AND it is not discharged.
    let full = SmtProofContract {
        solver_version: "ay".to_string(),
        logic: SmtLogic::QfBv,
        features_used: features_for_logic(SmtLogic::QfBv),
        obligations: vec![bv_obligation()],
        completeness: ProofCompleteness::Full,
    };
    let full_result = verify_ay_contract(&dag, &full);
    assert!(
        !full_result.fully_verified,
        "Full contract: holey laundered proof is not fully verified",
    );
    assert!(
        !full_result.passed,
        "Full-completeness contract must reject a structurally-accepted hole: {:?}",
        full_result.violations,
    );
}
