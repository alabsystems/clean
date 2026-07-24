// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ay-to-clean SMT proof export contract.
//!
//! This module defines the proof-shape contract that ay is expected to satisfy
//! when it exports SMT-level UNSAT proofs for clean's verifier. The contract is
//! intentionally lightweight: it describes which proof details must be present,
//! which theories may appear, and how much trust the downstream verifier is
//! allowed to consume for a proof to be considered acceptable.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::dag::{SmtProofDag, SmtProofStep, SmtStepId, SmtTheory, TheoryLemmaDetail};
use super::trust::{SmtVerifyStats, StepTrustLevel};
use super::{verify_smt_proof, VerifyMode};

/// SMT logic fragment for a proof contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum SmtLogic {
    QfUf,
    QfLra,
    QfLia,
    QfBv,
    QfA,
    QfAuf,
    QfAbv,
    QfUflia,
    QfUflra,
    QfUfbv,
    QfAuflia,
    QfAuflra,
    QfAufbv,
    Full,
}

/// ay solver features that affect proof output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum SolverFeature {
    Cdcl,
    TheoryPropagation,
    TheoryLemma,
    Preprocessing,
    Quantifiers,
}

/// Required proof detail for a theory lemma.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum RequiredDetail {
    LratCertificate,
    FarkasCoefficients,
    CongruencePaths,
    BitBlastWitness,
    ArrayAxiomInstances,
    DatatypeAxiomInstances,
    GenericLemma,
    None,
}

/// Contract completeness level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum ProofCompleteness {
    /// No structural or theory trust gaps are allowed.
    Full,
    /// Theory lemmas must avoid trusted fallbacks, but some structural
    /// acceptance is allowed.
    TheoryComplete,
    /// The proof DAG shape is verified, but theory steps may remain trusted.
    StructuralOnly,
    /// Some steps may remain unverified.
    Partial,
}

/// Per-theory proof obligation required by the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TheoryProofObligation {
    pub theory: SmtTheory,
    pub required_detail: RequiredDetail,
    pub minimum_trust: StepTrustLevel,
}

/// Contract promised for each ay UNSAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtProofContract {
    pub solver_version: String,
    pub logic: SmtLogic,
    pub features_used: Vec<SolverFeature>,
    pub obligations: Vec<TheoryProofObligation>,
    pub completeness: ProofCompleteness,
}

/// Contract verification failure.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum ContractViolation {
    #[error(
        "step {step:?}: {theory} lemma is missing required detail {required:?} (found {found})"
    )]
    MissingTheoryDetail {
        step: SmtStepId,
        theory: SmtTheory,
        required: RequiredDetail,
        found: String,
    },

    #[error("proof DAG does not satisfy the export contract: {reason}")]
    IncompleteDag { reason: String },

    #[error("step {step:?}: trust level {actual} is below required {required} for the contract")]
    UnexpectedTrustStep {
        step: SmtStepId,
        actual: StepTrustLevel,
        required: StepTrustLevel,
    },

    #[error(
        "proof uses {count} {theory} theory lemmas but the contract has no matching obligation"
    )]
    MissingObligation { theory: SmtTheory, count: u32 },

    #[error("proof has {count} trust gaps beyond {completeness:?} completeness")]
    ExcessTrustSteps {
        count: usize,
        completeness: ProofCompleteness,
    },
}

/// Result of checking a proof against a ay SMT contract.
#[derive(Debug, Clone)]
pub struct ContractVerificationResult {
    /// Whether the proof satisfies the contract at its stated completeness
    /// level. For `StructuralOnly`/`Partial` contracts this is `true` even for
    /// holey/trusted proofs — it is a "meets stated completeness" signal, **not**
    /// a discharge claim. Callers that need a discharge (a verified refutation)
    /// must check [`fully_verified`](Self::fully_verified) instead.
    pub passed: bool,
    /// Whether the proof is a *fully kernel-verified* refutation: it structurally
    /// derives the empty clause and its derivation contains no structurally-
    /// accepted or trusted steps.
    ///
    // SOUNDNESS (root cause B/C): a discharged obligation ("verified refutation")
    // requires the empty clause to be fully kernel-verified. `passed` alone is
    // insufficient because weak-completeness contracts intentionally accept holes;
    // this field is the fail-closed discharge signal. See
    // docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md.
    pub fully_verified: bool,
    pub violations: Vec<ContractViolation>,
    pub coverage: SmtVerifyStats,
}

/// Registry of standard contracts and feature-to-obligation mappings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtContractRegistry {
    feature_obligations: BTreeMap<SolverFeature, Vec<TheoryProofObligation>>,
    logic_contracts: BTreeMap<SmtLogic, SmtProofContract>,
}

impl Default for SmtContractRegistry {
    fn default() -> Self {
        let mut registry = Self::empty();
        registry.register_feature_obligations(SolverFeature::Cdcl, vec![]);
        registry.register_feature_obligations(
            SolverFeature::TheoryPropagation,
            supported_theory_obligations(),
        );
        registry.register_feature_obligations(
            SolverFeature::TheoryLemma,
            supported_theory_obligations(),
        );
        registry.register_feature_obligations(SolverFeature::Preprocessing, vec![]);
        registry.register_feature_obligations(SolverFeature::Quantifiers, vec![]);

        for logic in standard_logics() {
            registry.register_logic_contract(standard_contract_for_logic(logic));
        }

        registry
    }
}

impl SmtContractRegistry {
    /// Create an empty contract registry.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            feature_obligations: BTreeMap::new(),
            logic_contracts: BTreeMap::new(),
        }
    }

    /// Register obligations implied by a solver feature.
    pub fn register_feature_obligations(
        &mut self,
        feature: SolverFeature,
        obligations: Vec<TheoryProofObligation>,
    ) {
        self.feature_obligations.insert(feature, obligations);
    }

    /// Register a standard contract keyed by logic.
    pub fn register_logic_contract(&mut self, contract: SmtProofContract) {
        self.logic_contracts.insert(contract.logic, contract);
    }

    /// Look up the obligations implied by a feature.
    #[must_use]
    pub fn obligations_for_feature(
        &self,
        feature: SolverFeature,
    ) -> Option<&[TheoryProofObligation]> {
        self.feature_obligations.get(&feature).map(Vec::as_slice)
    }

    /// Look up a contract by logic.
    #[must_use]
    pub fn get_by_logic(&self, logic: SmtLogic) -> Option<&SmtProofContract> {
        self.logic_contracts.get(&logic)
    }

    /// Number of feature-to-obligation mappings.
    #[must_use]
    pub fn feature_mapping_len(&self) -> usize {
        self.feature_obligations.len()
    }

    /// Number of registered logic contracts.
    #[must_use]
    pub fn logic_contract_len(&self) -> usize {
        self.logic_contracts.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.feature_obligations.is_empty() && self.logic_contracts.is_empty()
    }
}

/// Standard contract for LRA proofs.
#[must_use]
pub fn standard_lra_contract() -> SmtProofContract {
    standard_contract(
        SmtLogic::QfLra,
        vec![lra_obligation()],
        ProofCompleteness::Full,
    )
}

/// Standard contract for EUF proofs.
#[must_use]
pub fn standard_euf_contract() -> SmtProofContract {
    standard_contract(
        SmtLogic::QfUf,
        vec![euf_obligation()],
        ProofCompleteness::Full,
    )
}

/// Standard contract for BV proofs.
#[must_use]
pub fn standard_bv_contract() -> SmtProofContract {
    standard_contract(
        SmtLogic::QfBv,
        vec![bv_obligation()],
        ProofCompleteness::StructuralOnly,
    )
}

/// Standard contract for QF_UF proofs.
#[must_use]
pub fn standard_qf_uf_contract() -> SmtProofContract {
    standard_euf_contract()
}

/// Standard contract for QF_LRA proofs.
#[must_use]
pub fn standard_qf_lra_contract() -> SmtProofContract {
    standard_lra_contract()
}

/// Standard contract for the full SMT pipeline.
#[must_use]
pub fn standard_full_contract() -> SmtProofContract {
    standard_contract(
        SmtLogic::Full,
        supported_theory_obligations(),
        ProofCompleteness::Partial,
    )
}

/// Verify that a proof DAG satisfies the ay export contract.
#[must_use]
pub fn verify_ay_contract(
    proof: &SmtProofDag,
    contract: &SmtProofContract,
) -> ContractVerificationResult {
    let verification = verify_smt_proof(proof, VerifyMode::Permissive);
    let mut violations = Vec::new();
    let mut trust_gap_steps = BTreeSet::new();
    let obligations = obligations_by_theory(contract);
    let theory_counts = count_theory_lemmas(proof);

    if !verification.valid {
        let reason = verification
            .first_error
            .as_ref()
            .map(ToString::to_string)
            .unwrap_or_else(|| "proof does not derive the empty clause".to_string());
        violations.push(ContractViolation::IncompleteDag { reason });
    }

    for (theory, count) in &theory_counts {
        if !obligations.contains_key(theory) {
            violations.push(ContractViolation::MissingObligation {
                theory: *theory,
                count: *count,
            });
        }
    }

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = SmtStepId(idx as u32);
        let verdict = verification.verdicts.get(idx);

        if let Some(verdict) = verdict {
            if !completeness_accepts(contract.completeness, step, verdict.trust_level) {
                trust_gap_steps.insert(step_id);
                violations.push(ContractViolation::UnexpectedTrustStep {
                    step: step_id,
                    actual: verdict.trust_level,
                    required: minimum_trust_for_completeness(contract.completeness),
                });
            }
        }

        let SmtProofStep::TheoryLemma { theory, kind, .. } = step else {
            continue;
        };

        let Some(obligation) = obligations.get(theory).copied() else {
            continue;
        };

        if !detail_satisfies_required(kind, obligation.required_detail) {
            violations.push(ContractViolation::MissingTheoryDetail {
                step: step_id,
                theory: *theory,
                required: obligation.required_detail,
                found: describe_theory_detail(kind),
            });
        }

        if let Some(verdict) = verdict {
            if !trust_satisfies_minimum(verdict.trust_level, obligation.minimum_trust) {
                trust_gap_steps.insert(step_id);
                violations.push(ContractViolation::UnexpectedTrustStep {
                    step: step_id,
                    actual: verdict.trust_level,
                    required: obligation.minimum_trust,
                });
            }
        }
    }

    if !trust_gap_steps.is_empty() {
        violations.push(ContractViolation::ExcessTrustSteps {
            count: trust_gap_steps.len(),
            completeness: contract.completeness,
        });
    }

    // SOUNDNESS (root cause B/C): a discharged obligation ("verified refutation")
    // requires the empty clause to be fully kernel-verified — it must derive the
    // empty clause AND contain no structurally-accepted or trusted steps. This is
    // strictly stronger than `passed`, which merely reflects the contract's stated
    // (possibly weak) completeness level. A holey proof whose empty clause was
    // laundered from an unchecked step's false clause has `valid == true` but is
    // NOT fully verified. See docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md.
    let fully_verified = verification.valid && verification.stats.is_fully_verified();

    ContractVerificationResult {
        passed: violations.is_empty(),
        fully_verified,
        violations,
        coverage: verification.stats,
    }
}

#[must_use]
fn standard_contract(
    logic: SmtLogic,
    obligations: Vec<TheoryProofObligation>,
    completeness: ProofCompleteness,
) -> SmtProofContract {
    SmtProofContract {
        solver_version: "ay".to_string(),
        logic,
        features_used: features_for_logic(logic),
        obligations,
        completeness,
    }
}

#[must_use]
fn standard_contract_for_logic(logic: SmtLogic) -> SmtProofContract {
    match logic {
        SmtLogic::QfUf => standard_qf_uf_contract(),
        SmtLogic::QfLra => standard_qf_lra_contract(),
        SmtLogic::QfLia => standard_contract(
            SmtLogic::QfLia,
            vec![lia_obligation()],
            ProofCompleteness::TheoryComplete,
        ),
        SmtLogic::QfBv => standard_bv_contract(),
        SmtLogic::QfA => standard_contract(
            SmtLogic::QfA,
            vec![arrays_obligation()],
            ProofCompleteness::StructuralOnly,
        ),
        SmtLogic::QfAuf => standard_contract(
            SmtLogic::QfAuf,
            vec![arrays_obligation(), euf_obligation()],
            ProofCompleteness::StructuralOnly,
        ),
        SmtLogic::QfAbv => standard_contract(
            SmtLogic::QfAbv,
            vec![arrays_obligation(), bv_obligation()],
            ProofCompleteness::StructuralOnly,
        ),
        SmtLogic::QfUflia => standard_contract(
            SmtLogic::QfUflia,
            vec![euf_obligation(), lia_obligation()],
            ProofCompleteness::TheoryComplete,
        ),
        SmtLogic::QfUflra => standard_contract(
            SmtLogic::QfUflra,
            vec![euf_obligation(), lra_obligation()],
            ProofCompleteness::Full,
        ),
        SmtLogic::QfUfbv => standard_contract(
            SmtLogic::QfUfbv,
            vec![euf_obligation(), bv_obligation()],
            ProofCompleteness::StructuralOnly,
        ),
        SmtLogic::QfAuflia => standard_contract(
            SmtLogic::QfAuflia,
            vec![arrays_obligation(), euf_obligation(), lia_obligation()],
            ProofCompleteness::StructuralOnly,
        ),
        SmtLogic::QfAuflra => standard_contract(
            SmtLogic::QfAuflra,
            vec![arrays_obligation(), euf_obligation(), lra_obligation()],
            ProofCompleteness::StructuralOnly,
        ),
        SmtLogic::QfAufbv => standard_contract(
            SmtLogic::QfAufbv,
            vec![arrays_obligation(), euf_obligation(), bv_obligation()],
            ProofCompleteness::StructuralOnly,
        ),
        SmtLogic::Full => standard_full_contract(),
    }
}

#[must_use]
fn obligations_by_theory(contract: &SmtProofContract) -> HashMap<SmtTheory, TheoryProofObligation> {
    let mut obligations = HashMap::with_capacity(contract.obligations.len());
    for obligation in &contract.obligations {
        obligations.insert(obligation.theory, *obligation);
    }
    obligations
}

#[must_use]
fn count_theory_lemmas(proof: &SmtProofDag) -> HashMap<SmtTheory, u32> {
    let mut counts = HashMap::new();
    for step in &proof.steps {
        if let SmtProofStep::TheoryLemma { theory, .. } = step {
            *counts.entry(*theory).or_insert(0) += 1;
        }
    }
    counts
}

#[must_use]
fn completeness_accepts(
    completeness: ProofCompleteness,
    _step: &SmtProofStep,
    trust: StepTrustLevel,
) -> bool {
    match completeness {
        ProofCompleteness::Full => {
            matches!(
                trust,
                StepTrustLevel::KernelVerified | StepTrustLevel::Axiomatic
            )
        }
        ProofCompleteness::TheoryComplete => trust != StepTrustLevel::Trusted,
        ProofCompleteness::StructuralOnly | ProofCompleteness::Partial => true,
    }
}

#[must_use]
fn minimum_trust_for_completeness(completeness: ProofCompleteness) -> StepTrustLevel {
    match completeness {
        ProofCompleteness::Full => StepTrustLevel::KernelVerified,
        ProofCompleteness::TheoryComplete => StepTrustLevel::StructurallyAccepted,
        ProofCompleteness::StructuralOnly | ProofCompleteness::Partial => StepTrustLevel::Trusted,
    }
}

#[must_use]
fn trust_satisfies_minimum(actual: StepTrustLevel, minimum: StepTrustLevel) -> bool {
    trust_strength(actual) >= trust_strength(minimum)
}

#[must_use]
fn trust_strength(level: StepTrustLevel) -> u8 {
    match level {
        StepTrustLevel::KernelVerified => 3,
        StepTrustLevel::StructurallyAccepted => 2,
        StepTrustLevel::Axiomatic => 1,
        StepTrustLevel::Trusted => 0,
    }
}

#[must_use]
fn detail_satisfies_required(kind: &TheoryLemmaDetail, required: RequiredDetail) -> bool {
    match required {
        RequiredDetail::None | RequiredDetail::GenericLemma => true,
        RequiredDetail::LratCertificate => false,
        RequiredDetail::FarkasCoefficients => matches!(
            kind,
            TheoryLemmaDetail::LraFarkas { .. }
                | TheoryLemmaDetail::LiaGeneric {
                    coefficients: Some(_),
                    ..
                }
        ),
        RequiredDetail::CongruencePaths => matches!(
            kind,
            TheoryLemmaDetail::EufTransitive
                | TheoryLemmaDetail::EufCongruent
                | TheoryLemmaDetail::EufCongruentPred
                | TheoryLemmaDetail::EufGeneric
        ),
        RequiredDetail::BitBlastWitness => {
            matches!(kind, TheoryLemmaDetail::BvBitBlast { .. })
        }
        RequiredDetail::ArrayAxiomInstances => matches!(
            kind,
            TheoryLemmaDetail::ArraySelectStore { .. } | TheoryLemmaDetail::ArrayExtensionality
        ),
        RequiredDetail::DatatypeAxiomInstances => matches!(
            kind,
            TheoryLemmaDetail::DatatypesInjectivity
                | TheoryLemmaDetail::DatatypesDistinctness
                | TheoryLemmaDetail::DatatypesSelector
                | TheoryLemmaDetail::DatatypesTester
                | TheoryLemmaDetail::DatatypesAcyclicity
                | TheoryLemmaDetail::DatatypesGeneric
        ),
    }
}

#[must_use]
fn describe_theory_detail(kind: &TheoryLemmaDetail) -> String {
    match kind {
        TheoryLemmaDetail::EufTransitive => "euf_transitive".to_string(),
        TheoryLemmaDetail::EufCongruent => "euf_congruent".to_string(),
        TheoryLemmaDetail::EufCongruentPred => "euf_congruent_pred".to_string(),
        TheoryLemmaDetail::LraFarkas { .. } => "lra_farkas".to_string(),
        TheoryLemmaDetail::LiaGeneric {
            coefficients: Some(_),
            ..
        } => "lia_generic(coefficients)".to_string(),
        TheoryLemmaDetail::LiaGeneric {
            coefficients: None, ..
        } => "lia_generic".to_string(),
        TheoryLemmaDetail::BvBitBlast { .. } => "bv_bitblast".to_string(),
        TheoryLemmaDetail::ArraySelectStore { .. } => "array_select_store".to_string(),
        TheoryLemmaDetail::ArrayExtensionality => "array_extensionality".to_string(),
        TheoryLemmaDetail::FpToBv { .. } => "fp_to_bv".to_string(),
        TheoryLemmaDetail::FpGeneric => "fp_generic".to_string(),
        TheoryLemmaDetail::StringLength => "string_length".to_string(),
        TheoryLemmaDetail::StringContent => "string_content".to_string(),
        TheoryLemmaDetail::StringNormalForm => "string_normal_form".to_string(),
        TheoryLemmaDetail::EufGeneric => "euf_generic".to_string(),
        TheoryLemmaDetail::DatatypesInjectivity => "datatypes_injectivity".to_string(),
        TheoryLemmaDetail::DatatypesDistinctness => "datatypes_distinctness".to_string(),
        TheoryLemmaDetail::DatatypesSelector => "datatypes_selector".to_string(),
        TheoryLemmaDetail::DatatypesTester => "datatypes_tester".to_string(),
        TheoryLemmaDetail::DatatypesAcyclicity => "datatypes_acyclicity".to_string(),
        TheoryLemmaDetail::DatatypesGeneric => "datatypes_generic".to_string(),
        TheoryLemmaDetail::NraWitness(_) => "nra_witness".to_string(),
        TheoryLemmaDetail::NiaWitness(_) => "nia_witness".to_string(),
        TheoryLemmaDetail::Generic => "generic".to_string(),
    }
}

#[must_use]
fn features_for_logic(logic: SmtLogic) -> Vec<SolverFeature> {
    match logic {
        SmtLogic::QfUf
        | SmtLogic::QfLra
        | SmtLogic::QfLia
        | SmtLogic::QfUflia
        | SmtLogic::QfUflra => {
            vec![
                SolverFeature::Cdcl,
                SolverFeature::TheoryPropagation,
                SolverFeature::TheoryLemma,
            ]
        }
        SmtLogic::QfBv
        | SmtLogic::QfA
        | SmtLogic::QfAuf
        | SmtLogic::QfAbv
        | SmtLogic::QfUfbv
        | SmtLogic::QfAuflia
        | SmtLogic::QfAuflra
        | SmtLogic::QfAufbv => vec![
            SolverFeature::Cdcl,
            SolverFeature::TheoryPropagation,
            SolverFeature::TheoryLemma,
            SolverFeature::Preprocessing,
        ],
        SmtLogic::Full => vec![
            SolverFeature::Cdcl,
            SolverFeature::TheoryPropagation,
            SolverFeature::TheoryLemma,
            SolverFeature::Preprocessing,
            SolverFeature::Quantifiers,
        ],
    }
}

#[must_use]
fn standard_logics() -> [SmtLogic; 14] {
    [
        SmtLogic::QfUf,
        SmtLogic::QfLra,
        SmtLogic::QfLia,
        SmtLogic::QfBv,
        SmtLogic::QfA,
        SmtLogic::QfAuf,
        SmtLogic::QfAbv,
        SmtLogic::QfUflia,
        SmtLogic::QfUflra,
        SmtLogic::QfUfbv,
        SmtLogic::QfAuflia,
        SmtLogic::QfAuflra,
        SmtLogic::QfAufbv,
        SmtLogic::Full,
    ]
}

#[must_use]
fn supported_theory_obligations() -> Vec<TheoryProofObligation> {
    vec![
        euf_obligation(),
        lra_obligation(),
        lia_obligation(),
        bv_obligation(),
        arrays_obligation(),
        datatypes_obligation(),
    ]
}

#[must_use]
fn euf_obligation() -> TheoryProofObligation {
    TheoryProofObligation {
        theory: SmtTheory::Euf,
        required_detail: RequiredDetail::CongruencePaths,
        minimum_trust: StepTrustLevel::KernelVerified,
    }
}

#[must_use]
fn lra_obligation() -> TheoryProofObligation {
    TheoryProofObligation {
        theory: SmtTheory::Lra,
        required_detail: RequiredDetail::FarkasCoefficients,
        minimum_trust: StepTrustLevel::KernelVerified,
    }
}

#[must_use]
fn lia_obligation() -> TheoryProofObligation {
    TheoryProofObligation {
        theory: SmtTheory::Lia,
        required_detail: RequiredDetail::GenericLemma,
        minimum_trust: StepTrustLevel::StructurallyAccepted,
    }
}

#[must_use]
fn bv_obligation() -> TheoryProofObligation {
    TheoryProofObligation {
        theory: SmtTheory::Bv,
        required_detail: RequiredDetail::BitBlastWitness,
        minimum_trust: StepTrustLevel::StructurallyAccepted,
    }
}

#[must_use]
fn arrays_obligation() -> TheoryProofObligation {
    TheoryProofObligation {
        theory: SmtTheory::Arrays,
        required_detail: RequiredDetail::ArrayAxiomInstances,
        minimum_trust: StepTrustLevel::StructurallyAccepted,
    }
}

#[must_use]
fn datatypes_obligation() -> TheoryProofObligation {
    TheoryProofObligation {
        theory: SmtTheory::Datatypes,
        required_detail: RequiredDetail::DatatypeAxiomInstances,
        minimum_trust: StepTrustLevel::KernelVerified,
    }
}

#[cfg(test)]
mod tests {
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
}
