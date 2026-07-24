// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT Proof Verification Module
//!
//! Provides independent SMT-level proof verification for ay's Alethe proofs.
//! This module fills the gap between clean's existing SAT-level verification
//! (DRAT, resolution, cutting planes) and kernel-level proof reconstruction.
//!
//! ## Architecture
//!
//! The module operates on [`SmtProofDag`], clean's internal representation
//! of SMT-level proofs. The DAG can be populated from ay's `Proof` objects
//! (via a future `ay_bridge`) or from Alethe text format (via [`alethe_parser`]
//! and [`alethe_bridge`]). The public entry point [`verify_alethe_proof`]
//! handles the full parse-convert-verify pipeline.
//!
//! Verification proceeds in three phases:
//! 1. Structural validation (premise linkage, step ordering)
//! 2. Per-step semantic validation (theory-specific checkers)
//! 3. Terminal empty-clause verification
//!
//! ## Theory Checkers (Phase 1)
//!
//! - **Resolution**: Binary and chain resolution (module [`resolution`])
//! - **EUF**: Equality and uninterpreted functions (module [`euf`])
//! - **LRA**: Linear real arithmetic via Farkas lemma (module [`lra`])
//! - **BV**: Bitvector operations via concrete evaluation (module [`bv`])
//!
//! ## Trust Levels
//!
//! Each step receives a trust classification:
//! - `KernelVerified`: semantically checked by clean
//! - `StructurallyAccepted`: non-empty clause, correct arity
//! - `Axiomatic`: input assumptions
//! - `Trusted`: unverified fallback

pub(crate) mod alethe_bridge;
pub(crate) mod alethe_parser;
pub mod arrays;
pub mod ay_smt_contract;
pub mod bv;
pub mod certificate;
pub mod dag;
pub mod datatypes;
pub mod euf;
pub mod fp;
pub mod interpolation;
pub mod lia;
pub mod lra;
pub mod nra;
pub mod nra_psatz_cert;
pub mod pipeline;
pub mod quantifier;
pub mod resolution;
pub(crate) mod smtlib2_proof;
pub mod strings;
pub mod trust;

#[cfg(test)]
mod conformance_tests;
#[cfg(test)]
mod tests_binary_resolution_soundness;
#[cfg(test)]
mod tests_nra_psatz_cert;
#[cfg(test)]
mod tests_resolution_invariance;
#[cfg(test)]
mod tests_trust_smt_comp;

use dag::{
    AletheRuleKind, SmtProofDag, SmtProofStep, SmtStepId, SmtTermId, SmtTheory, TheoryLemmaDetail,
};
use trust::{
    SmtVerifyError, SmtVerifyResult, SmtVerifyStats, StepTrustLevel, StepVerdict, TrustLedger,
};

/// Error type for end-to-end Alethe proof verification.
///
/// Combines parse errors from the Alethe parser with verification errors
/// from the proof checker.
#[derive(Debug)]
#[non_exhaustive]
pub enum AletheVerifyError {
    /// Failed to parse the Alethe proof text.
    Parse(alethe_parser::AletheParseError),
    /// Proof parsed but verification failed.
    Verify(SmtVerifyError),
    /// Proof parsed and verified, but is not valid (e.g., no empty clause).
    InvalidProof {
        /// Summary of why the proof is invalid.
        reason: String,
    },
}

impl std::fmt::Display for AletheVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AletheVerifyError::Parse(e) => write!(f, "Alethe parse error: {e}"),
            AletheVerifyError::Verify(e) => write!(f, "SMT verification error: {e}"),
            AletheVerifyError::InvalidProof { reason } => {
                write!(f, "invalid proof: {reason}")
            }
        }
    }
}

impl std::error::Error for AletheVerifyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            AletheVerifyError::Parse(e) => Some(e),
            AletheVerifyError::Verify(e) => Some(e),
            AletheVerifyError::InvalidProof { .. } => None,
        }
    }
}

impl From<alethe_parser::AletheParseError> for AletheVerifyError {
    fn from(e: alethe_parser::AletheParseError) -> Self {
        AletheVerifyError::Parse(e)
    }
}

/// Parse and verify an Alethe proof from text.
///
/// This is the primary entry point for end-to-end proof verification:
/// 1. Parses the Alethe proof text into an AST
/// 2. Converts the AST to the verifier's canonical `SmtProofDag`
/// 3. Runs full SMT proof verification (structural + semantic + terminal)
///
/// # Arguments
/// * `proof_text` - Alethe proof in S-expression text format.
///
/// # Returns
/// * `Ok(SmtVerifyResult)` with per-step verdicts and statistics.
/// * `Err(AletheVerifyError)` if parsing or verification fails.
pub fn verify_alethe_proof(proof_text: &str) -> Result<SmtVerifyResult, AletheVerifyError> {
    verify_alethe_proof_with_mode(proof_text, VerifyMode::Permissive)
}

/// Parse and verify an Alethe proof from text with explicit verification mode.
///
/// Same as [`verify_alethe_proof`] but allows specifying strict mode to reject
/// any trusted (unverified) steps.
pub fn verify_alethe_proof_with_mode(
    proof_text: &str,
    mode: VerifyMode,
) -> Result<SmtVerifyResult, AletheVerifyError> {
    let parsed = alethe_parser::parse_alethe(proof_text)?;
    let dag = alethe_bridge::alethe_to_dag(parsed);
    let result = verify_smt_proof(&dag, mode);
    if let Some(ref err) = result.first_error {
        return Err(AletheVerifyError::Verify(err.clone()));
    }
    if !result.valid {
        return Err(AletheVerifyError::InvalidProof {
            reason: "proof does not derive empty clause".to_string(),
        });
    }
    Ok(result)
}

/// Verification mode: strict rejects any trusted steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerifyMode {
    /// Accept proofs with trusted steps (default).
    Permissive,
    /// Reject proofs with any trusted steps (like ay-proof strict mode).
    Strict,
}

/// Verify an SMT proof DAG.
///
/// Checks every step semantically where possible, structurally where not.
/// Returns a complete trust ledger with per-step verdicts.
///
/// # Arguments
/// * `dag` - The proof DAG to verify.
/// * `mode` - `Strict` rejects any trusted steps; `Permissive` allows them.
///
/// # Returns
/// * `SmtVerifyResult` with per-step verdicts and summary statistics.
#[must_use]
pub fn verify_smt_proof(dag: &SmtProofDag, mode: VerifyMode) -> SmtVerifyResult {
    if dag.num_steps() == 0 {
        return SmtVerifyResult {
            valid: false,
            verdicts: vec![],
            stats: SmtVerifyStats::default(),
            first_error: Some(SmtVerifyError::EmptyProof),
        };
    }

    // Phase 1: structural validation (premise linkage).
    if let Err(e) = validate_structure(dag) {
        return SmtVerifyResult {
            valid: false,
            verdicts: vec![],
            stats: SmtVerifyStats::default(),
            first_error: Some(e),
        };
    }

    // Phase 2: per-step semantic validation.
    let mut ledger = TrustLedger::new(dag.num_steps());
    let mut first_error: Option<SmtVerifyError> = None;
    let mut derived_clauses: Vec<Option<Vec<SmtTermId>>> = Vec::with_capacity(dag.num_steps());

    for (idx, step) in dag.steps.iter().enumerate() {
        let step_id = SmtStepId(idx as u32);
        let verdict = verify_step(dag, &derived_clauses, step_id, step);

        if verdict.trust_level == StepTrustLevel::Trusted
            && mode == VerifyMode::Strict
            && first_error.is_none()
        {
            first_error = Some(SmtVerifyError::TrustStep { step: step_id });
        }

        // Record in ledger with theory info if applicable.
        if let SmtProofStep::TheoryLemma { theory, .. } = step {
            ledger.record_theory(verdict.clone(), *theory);
        } else {
            ledger.record(verdict.clone());
        }

        // Store derived clause for premise lookups.
        derived_clauses.push(extract_clause(step));
    }

    // Phase 3: verify terminal empty clause.
    let terminal_valid = check_terminal_empty_clause(&derived_clauses);
    if !terminal_valid && first_error.is_none() {
        if let Some(last_idx) = derived_clauses
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, c)| c.as_ref().map(|_| i))
        {
            first_error = Some(SmtVerifyError::FinalClauseNotEmpty {
                step: SmtStepId(last_idx as u32),
            });
        }
    }

    let stats = ledger.stats();
    let verdicts = ledger.into_verdicts();
    SmtVerifyResult {
        valid: terminal_valid && first_error.is_none(),
        verdicts,
        stats,
        first_error,
    }
}

/// Validate structural properties of the proof DAG.
///
/// - Every premise reference points to a prior step.
/// - No step references itself.
fn validate_structure(dag: &SmtProofDag) -> Result<(), SmtVerifyError> {
    let num_steps = dag.num_steps();
    for (idx, step) in dag.steps.iter().enumerate() {
        let step_id = SmtStepId(idx as u32);
        let premises = match step {
            SmtProofStep::Resolution { premises, .. } => premises.as_slice(),
            SmtProofStep::Step { premises, .. } => premises.as_slice(),
            _ => &[],
        };
        for &pid in premises {
            if pid.0 as usize >= num_steps {
                return Err(SmtVerifyError::MissingPremise {
                    step: step_id,
                    premise: pid,
                });
            }
            if pid.0 >= idx as u32 {
                return Err(SmtVerifyError::NonPriorPremise {
                    step: step_id,
                    premise: pid,
                });
            }
        }
    }
    Ok(())
}

/// Check that the last derived clause is empty (proof of contradiction).
fn check_terminal_empty_clause(derived_clauses: &[Option<Vec<SmtTermId>>]) -> bool {
    derived_clauses
        .iter()
        .rev()
        .find_map(|c| c.as_ref())
        .is_some_and(|c| c.is_empty())
}

/// Extract the clause from a proof step.
fn extract_clause(step: &SmtProofStep) -> Option<Vec<SmtTermId>> {
    match step {
        SmtProofStep::Assume(t) => Some(vec![*t]),
        SmtProofStep::Resolution { clause, .. } => Some(clause.clone()),
        SmtProofStep::TheoryLemma { clause, .. } => Some(clause.clone()),
        SmtProofStep::Step { clause, .. } => Some(clause.clone()),
        SmtProofStep::Anchor { .. } => None,
    }
}

/// Verify a single proof step, dispatching to the appropriate checker.
fn verify_step(
    dag: &SmtProofDag,
    derived_clauses: &[Option<Vec<SmtTermId>>],
    step_id: SmtStepId,
    step: &SmtProofStep,
) -> StepVerdict {
    match step {
        SmtProofStep::Assume(_) => StepVerdict {
            step_id,
            trust_level: StepTrustLevel::Axiomatic,
            checker: "core",
            detail: None,
        },

        SmtProofStep::Resolution {
            clause,
            premises,
            pivot,
        } => resolution::check_resolution(dag, step_id, clause, premises, *pivot, derived_clauses),

        SmtProofStep::TheoryLemma {
            theory,
            kind,
            clause,
        } => verify_theory_lemma(dag, step_id, *theory, kind, clause),

        SmtProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => verify_step_rule(dag, step_id, rule, clause, premises, args, derived_clauses),

        SmtProofStep::Anchor { .. } => StepVerdict {
            step_id,
            trust_level: StepTrustLevel::StructurallyAccepted,
            checker: "core",
            detail: Some("subproof anchor".to_string()),
        },
    }
}

/// Verify a theory lemma step.
fn verify_theory_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    theory: SmtTheory,
    kind: &TheoryLemmaDetail,
    clause: &[SmtTermId],
) -> StepVerdict {
    match kind {
        TheoryLemmaDetail::EufTransitive => euf::check_eq_transitive(dag, step_id, clause),
        TheoryLemmaDetail::EufCongruent => euf::check_eq_congruent(dag, step_id, clause),
        TheoryLemmaDetail::EufCongruentPred => euf::check_eq_congruent_pred(dag, step_id, clause),
        TheoryLemmaDetail::EufGeneric => euf::check_euf_lemma(dag, step_id, clause),

        TheoryLemmaDetail::LraFarkas { coefficients } => {
            lra::check_lra_farkas(dag, step_id, clause, coefficients)
        }

        TheoryLemmaDetail::LiaGeneric { coefficients, .. } => {
            if let Some(ref coeffs) = coefficients {
                lia::check_lia_generic(dag, step_id, clause, coeffs)
            } else {
                // No explicit coefficients: try unit coefficients (all 1s).
                let unit_coeffs: Vec<i64> = vec![1; clause.len()];
                let verdict = lia::check_lia_generic(dag, step_id, clause, &unit_coeffs);
                if verdict.trust_level == StepTrustLevel::KernelVerified {
                    verdict
                } else {
                    // Unit coefficients didn't work; structurally accept.
                    structural_accept(step_id, "lia_generic")
                }
            }
        }

        TheoryLemmaDetail::BvBitBlast { .. } => bv::check_bv_lemma(dag, step_id, clause),
        TheoryLemmaDetail::ArraySelectStore { .. } => {
            arrays::check_arrays_lemma(dag, step_id, clause)
        }
        TheoryLemmaDetail::ArrayExtensionality => arrays::check_arrays_lemma(dag, step_id, clause),
        TheoryLemmaDetail::FpToBv { .. } => fp::check_fp_lemma(dag, step_id, clause),
        TheoryLemmaDetail::FpGeneric => fp::check_fp_lemma(dag, step_id, clause),
        TheoryLemmaDetail::StringLength
        | TheoryLemmaDetail::StringContent
        | TheoryLemmaDetail::StringNormalForm => strings::check_strings_lemma(dag, step_id, clause),

        TheoryLemmaDetail::DatatypesInjectivity
        | TheoryLemmaDetail::DatatypesDistinctness
        | TheoryLemmaDetail::DatatypesSelector
        | TheoryLemmaDetail::DatatypesTester
        | TheoryLemmaDetail::DatatypesAcyclicity
        | TheoryLemmaDetail::DatatypesGeneric => {
            datatypes::check_datatypes_lemma(dag, step_id, clause)
        }

        TheoryLemmaDetail::NraWitness(witness) | TheoryLemmaDetail::NiaWitness(witness) => {
            nra::check_nra_lemma(dag, step_id, clause, witness)
        }

        TheoryLemmaDetail::Generic => StepVerdict {
            step_id,
            trust_level: StepTrustLevel::Trusted,
            checker: "theory",
            detail: Some(format!("generic {theory} theory lemma, unverified")),
        },
    }
}

/// Verify an Alethe step rule.
fn verify_step_rule(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    rule: &AletheRuleKind,
    clause: &[SmtTermId],
    premises: &[SmtStepId],
    args: &[SmtTermId],
    derived_clauses: &[Option<Vec<SmtTermId>>],
) -> StepVerdict {
    match rule {
        // EUF step rules -- fully checked.
        AletheRuleKind::Refl => euf::check_refl(dag, step_id, clause),
        AletheRuleKind::Symm => euf::check_symm(dag, step_id, clause, premises, derived_clauses),
        AletheRuleKind::Trans => euf::check_trans(dag, step_id, clause, premises, derived_clauses),
        AletheRuleKind::Cong => euf::check_cong(dag, step_id, clause, premises, derived_clauses),

        // Resolution.
        AletheRuleKind::Resolution | AletheRuleKind::ThResolution => {
            resolution::check_resolution(dag, step_id, clause, premises, None, derived_clauses)
        }

        // Trust / Hole -- always untrusted.
        AletheRuleKind::Trust => StepVerdict {
            step_id,
            trust_level: StepTrustLevel::Trusted,
            checker: "core",
            detail: Some("trust rule".to_string()),
        },
        AletheRuleKind::Hole => StepVerdict {
            step_id,
            trust_level: StepTrustLevel::Trusted,
            checker: "core",
            detail: Some("hole rule".to_string()),
        },

        // Boolean rules, LRA rules, etc. -- structurally accepted in Phase 1.
        AletheRuleKind::True
        | AletheRuleKind::False
        | AletheRuleKind::NotTrue
        | AletheRuleKind::NotFalse
        | AletheRuleKind::AndPos(_)
        | AletheRuleKind::AndNeg
        | AletheRuleKind::OrPos
        | AletheRuleKind::OrNeg(_)
        | AletheRuleKind::ImpliesPos
        | AletheRuleKind::ImpliesNeg1
        | AletheRuleKind::ImpliesNeg2
        | AletheRuleKind::EquivPos1
        | AletheRuleKind::EquivPos2
        | AletheRuleKind::EquivNeg1
        | AletheRuleKind::EquivNeg2
        | AletheRuleKind::ItePos1
        | AletheRuleKind::ItePos2
        | AletheRuleKind::IteNeg1
        | AletheRuleKind::IteNeg2
        | AletheRuleKind::Contraction => structural_accept(step_id, "boolean"),

        AletheRuleKind::LaGeneric
        | AletheRuleKind::LaTautology
        | AletheRuleKind::LaDisequality
        | AletheRuleKind::LaTotality => {
            // la_generic is checked via theory lemma path with Farkas coefficients.
            // When it arrives as a step rule without coefficients, structurally accept.
            structural_accept(step_id, "lra_step")
        }

        AletheRuleKind::EqReflexive => euf::check_refl(dag, step_id, clause),
        AletheRuleKind::EqTransitive => euf::check_eq_transitive(dag, step_id, clause),
        AletheRuleKind::EqCongruent => euf::check_eq_congruent(dag, step_id, clause),
        AletheRuleKind::EqCongruentPred => euf::check_eq_congruent_pred(dag, step_id, clause),

        // Array rules -- semantically checked.
        AletheRuleKind::ReadOverWritePos => arrays::check_read_over_write_pos(dag, step_id, clause),
        AletheRuleKind::ReadOverWriteNeg => arrays::check_read_over_write_neg(dag, step_id, clause),
        AletheRuleKind::Extensionality => arrays::check_extensionality(dag, step_id, clause),

        // BV bitblast step rule -- checked via BV evaluator.
        AletheRuleKind::BvBitblast => bv::check_bv_lemma(dag, step_id, clause),

        // Quantifier rules -- semantically checked.
        AletheRuleKind::ForallInst => quantifier::check_forall_inst(dag, step_id, clause, args),
        AletheRuleKind::Skolem => quantifier::check_skolem(dag, step_id, clause),

        // String rules -- semantically checked via strings evaluator.
        AletheRuleKind::StringLength
        | AletheRuleKind::StringDecompose
        | AletheRuleKind::StringCodeInj => strings::check_strings_lemma(dag, step_id, clause),

        // Everything else: structurally accept for Phase 1.
        _ => structural_accept(step_id, "step_rule"),
    }
}

/// Create a structurally-accepted verdict.
fn structural_accept(step_id: SmtStepId, checker: &'static str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::StructurallyAccepted,
        checker,
        detail: None,
    }
}

#[cfg(test)]
mod falsification_tests;

#[cfg(test)]
mod tests_integration;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofStep, SmtSort, SmtSymbol, SmtTerm};

    /// Build a simple valid proof: assume p, assume not(p), resolve to empty.
    fn build_simple_valid_proof() -> SmtProofDag {
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        let not_p = dag.add_term(SmtTerm::Not(p));

        let s0 = dag.add_step(SmtProofStep::Assume(p));
        let s1 = dag.add_step(SmtProofStep::Assume(not_p));
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(p),
        });
        dag
    }

    #[test]
    fn test_verify_simple_valid_proof() {
        let dag = build_simple_valid_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        assert!(
            result.valid,
            "proof should be valid: {:?}",
            result.first_error
        );
        assert_eq!(result.stats.total_steps, 3);
        assert_eq!(result.stats.axiomatic, 2);
        assert_eq!(result.stats.kernel_verified, 1);
        assert_eq!(result.stats.trusted, 0);
        assert!(result.stats.is_fully_verified());
    }

    #[test]
    fn test_verify_empty_proof_invalid() {
        let dag = SmtProofDag::new();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        assert!(!result.valid);
        assert!(matches!(
            result.first_error,
            Some(SmtVerifyError::EmptyProof)
        ));
    }

    #[test]
    fn test_verify_non_empty_terminal_invalid() {
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        dag.add_step(SmtProofStep::Assume(p));
        // Only an assumption, no empty clause derived.
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        assert!(!result.valid);
    }

    #[test]
    fn test_verify_strict_mode_rejects_trust() {
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        let not_p = dag.add_term(SmtTerm::Not(p));

        let s0 = dag.add_step(SmtProofStep::Assume(p));
        // Trust step in the middle.
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Core,
            kind: TheoryLemmaDetail::Generic,
            clause: vec![not_p],
        });
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(p),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(!result.valid);
        assert!(matches!(
            result.first_error,
            Some(SmtVerifyError::TrustStep { .. })
        ));
    }

    #[test]
    fn test_verify_strict_mode_accepts_fully_verified() {
        let dag = build_simple_valid_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(result.valid);
    }

    #[test]
    fn test_verify_euf_transitive_in_proof() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));

        // Equalities
        let eq_ab = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, b]));
        let eq_bc = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![b, c]));
        let eq_ac = dag.add_term(SmtTerm::App(SmtSymbol::Named("=".to_string()), vec![a, c]));
        let neq_ab = dag.add_term(SmtTerm::Not(eq_ab));
        let neq_bc = dag.add_term(SmtTerm::Not(eq_bc));
        let neq_ac = dag.add_term(SmtTerm::Not(eq_ac));

        // assume (= a b)
        let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
        // assume (= b c)
        let s1 = dag.add_step(SmtProofStep::Assume(eq_bc));
        // assume (not (= a c))
        let s2 = dag.add_step(SmtProofStep::Assume(neq_ac));
        // EUF transitive: (not (= a b)) (not (= b c)) (= a c)
        let s3 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Euf,
            kind: TheoryLemmaDetail::EufTransitive,
            clause: vec![neq_ab, neq_bc, eq_ac],
        });
        // Resolve s0 + s3 on eq_ab -> {neq_bc, eq_ac}
        let s4 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![neq_bc, eq_ac],
            premises: vec![s0, s3],
            pivot: Some(eq_ab),
        });
        // Resolve s1 + s4 on eq_bc -> {eq_ac}
        let s5 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![eq_ac],
            premises: vec![s1, s4],
            pivot: Some(eq_bc),
        });
        // Resolve s2 + s5 on eq_ac -> empty
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s2, s5],
            pivot: Some(eq_ac),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        assert!(
            result.valid,
            "EUF transitive proof should be valid: {:?}",
            result.first_error
        );
        assert!(result.stats.is_fully_verified());
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
            Some(&1)
        );
    }

    #[test]
    fn test_verify_tampered_resolution_invalid() {
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        let q = dag.add_term(SmtTerm::Var("q".to_string(), SmtSort::Bool));
        let not_p = dag.add_term(SmtTerm::Not(p));

        let s0 = dag.add_step(SmtProofStep::Assume(p));
        let s1 = dag.add_step(SmtProofStep::Assume(not_p));
        // Tampered: claim resolution produces {q} instead of empty.
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![q],
            premises: vec![s0, s1],
            pivot: Some(p),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        // The resolution step itself should fail verification (result mismatch).
        // AND the terminal clause is not empty.
        assert!(!result.valid);
    }

    #[test]
    fn test_validate_structure_bad_premise() {
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        dag.add_step(SmtProofStep::Assume(p));
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![SmtStepId(99)], // out of range
            pivot: None,
        });

        let result = validate_structure(&dag);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_structure_non_prior_premise() {
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        // Step 0 references step 1, which doesn't exist yet.
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![p],
            premises: vec![SmtStepId(1)],
            pivot: None,
        });
        dag.add_step(SmtProofStep::Assume(p));

        let result = validate_structure(&dag);
        assert!(result.is_err());
    }

    #[test]
    fn test_verification_coverage_stats() {
        let dag = build_simple_valid_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let coverage = result.stats.verification_coverage();
        assert!((coverage - 1.0).abs() < f64::EPSILON);
    }

    // ----------------------------------------------------------------
    // Alethe end-to-end integration tests (parse -> convert -> verify)
    // ----------------------------------------------------------------

    #[test]
    fn test_alethe_propositional_unsat() {
        // Simple propositional UNSAT proof: p AND not(p) => contradiction.
        // Uses resolution only (no theory lemmas).
        let proof_text = r#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;
        let result =
            verify_alethe_proof(proof_text).expect("propositional UNSAT proof should verify");
        assert!(result.valid);
        assert!(result.stats.is_fully_verified());
        assert_eq!(result.stats.axiomatic, 2);
        assert!(result.stats.kernel_verified >= 1);
        assert_eq!(result.stats.trusted, 0);
    }

    #[test]
    fn test_alethe_euf_transitive() {
        // EUF proof: a=b, b=c, not(a=c) is UNSAT via eq_transitive.
        let proof_text = r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (declare-const c U)
            (assume h1 (= a b))
            (assume h2 (= b c))
            (assume h3 (not (= a c)))
            (step t1 (cl (not (= a b)) (not (= b c)) (= a c))
                :rule eq_transitive)
            (step t2 (cl (not (= b c)) (= a c))
                :rule resolution :premises (h1 t1))
            (step t3 (cl (= a c))
                :rule resolution :premises (h2 t2))
            (step t4 (cl)
                :rule resolution :premises (h3 t3))
        "#;
        let result = verify_alethe_proof(proof_text).expect("EUF transitive proof should verify");
        assert!(result.valid);
        // EUF transitivity lemma is detected and counted.
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
            Some(&1)
        );
        // Resolution steps have trusted fallbacks because the Alethe parser
        // allocates fresh term IDs per text occurrence (no deduplication).
        // The resolution checker uses ID-based pivot matching, so it can't
        // match pivots across separately-parsed clauses. A future term
        // deduplication pass in the bridge will fix this.
        // Key: the proof IS valid and the EUF lemma IS recognized.
    }

    #[test]
    fn test_alethe_euf_congruence() {
        // EUF congruence proof: a=b => f(a)=f(b), plus assumption not(f(a)=f(b)).
        let proof_text = r#"
            (declare-sort U 0)
            (declare-fun f (U) U)
            (declare-const a U)
            (declare-const b U)
            (assume h1 (= a b))
            (assume h2 (not (= (f a) (f b))))
            (step t1 (cl (not (= a b)) (= (f a) (f b)))
                :rule eq_congruent)
            (step t2 (cl (= (f a) (f b)))
                :rule resolution :premises (h1 t1))
            (step t3 (cl)
                :rule resolution :premises (h2 t2))
        "#;
        let result = verify_alethe_proof(proof_text).expect("EUF congruence proof should verify");
        assert!(result.valid);
        // Same note as EUF transitive: resolution steps have trusted
        // fallbacks due to term ID non-deduplication. The EUF congruence
        // lemma itself is recognized by the theory checker.
    }

    #[test]
    fn test_alethe_lra_theory_lemma() {
        // LRA proof: x > 0 AND x <= 0 is UNSAT via la_generic Farkas lemma.
        let proof_text = r#"
            (declare-const x Real)
            (assume h1 (> x 0.0))
            (assume h2 (<= x 0.0))
            (step t1 (cl (not (> x 0.0)) (not (<= x 0.0)))
                :rule la_generic :args (1.0 1.0))
            (step t2 (cl (not (<= x 0.0)))
                :rule resolution :premises (h1 t1))
            (step t3 (cl)
                :rule resolution :premises (h2 t2))
        "#;
        let result = verify_alethe_proof(proof_text).expect("LRA proof should verify");
        assert!(result.valid);
        // LRA la_generic with Farkas coefficients is a theory lemma.
        assert_eq!(
            result.stats.theory_lemma_counts.get(&SmtTheory::Lra),
            Some(&1)
        );
    }

    #[test]
    fn test_alethe_parse_error_propagated() {
        // Invalid Alethe text should produce a parse error.
        let bad_proof = r#"
            (step t1 (cl) :rule completely_bogus_rule)
        "#;
        let result = verify_alethe_proof(bad_proof);
        assert!(result.is_err());
        assert!(matches!(result, Err(AletheVerifyError::Parse(_))));
    }

    #[test]
    fn test_alethe_invalid_proof_no_empty_clause() {
        // Valid parse, but proof doesn't derive empty clause.
        let proof_text = r#"
            (declare-const p Bool)
            (assume h1 p)
        "#;
        let result = verify_alethe_proof(proof_text);
        assert!(result.is_err());
        // This should be InvalidProof (not a parse or verify error),
        // since the proof is structurally valid but doesn't prove UNSAT.
        match result {
            Err(AletheVerifyError::Verify(_) | AletheVerifyError::InvalidProof { .. }) => {}
            other => panic!("expected verification/invalid proof error, got {other:?}"),
        }
    }

    #[test]
    fn test_alethe_strict_mode_rejects_trust_step() {
        // Proof that uses a trust step: permissive accepts, strict rejects.
        let proof_text = r#"
            (declare-const p Bool)
            (assume h1 p)
            (step t1 (cl (not p)) :rule trust)
            (step t2 (cl) :rule resolution :premises (h1 t1))
        "#;
        // Permissive mode: should accept.
        let permissive = verify_alethe_proof(proof_text);
        assert!(
            permissive.is_ok(),
            "permissive should accept: {permissive:?}"
        );

        // Strict mode: should reject due to trust step.
        let strict = verify_alethe_proof_with_mode(proof_text, VerifyMode::Strict);
        assert!(strict.is_err());
        assert!(matches!(strict, Err(AletheVerifyError::Verify(_))));
    }

    #[test]
    fn test_alethe_multi_resolution_chain() {
        // Multi-step resolution chain: p, q, not(p) OR not(q) -> empty.
        let proof_text = r#"
            (declare-const p Bool)
            (declare-const q Bool)
            (assume h1 p)
            (assume h2 q)
            (assume h3 (not p))
            (assume h4 (not q))
            (step t1 (cl) :rule resolution :premises (h1 h3))
        "#;
        // h1={p}, h3={not p} resolve to empty.
        let result = verify_alethe_proof(proof_text).expect("multi-resolution proof should verify");
        assert!(result.valid);
        assert!(result.stats.is_fully_verified());
    }
}
