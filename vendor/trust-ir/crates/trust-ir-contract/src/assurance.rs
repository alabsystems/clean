// trust-ir-contract/assurance: proof-strength / assurance vocabulary
//
// The proof-assurance enums that cross the Trust <-> backend boundary, moved
// out of trust-verifier-api (which keeps the engine trait + execution
// machinery). trust-verifier-api re-exports these so its existing dependents
// (trust-router, trust-wp, trust-vc-bridge, trust-mir-extract, trust-bmc) are
// unchanged; backends (clean) depend on them here instead of reaching into the
// Trust repo. Derives and serde attributes are preserved verbatim so the wire
// format is byte-identical.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// How a variable sort was established during compiler lowering.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "origin", rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSpecVariableOrigin {
    Local { index: usize },
    Quantified,
    Inferred,
}

/// How a proof was obtained and how much assurance backs it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProofStrength {
    pub reasoning: ReasoningKind,
    pub assurance: AssuranceLevel,
}

impl ProofStrength {
    /// SMT solver returned UNSAT for the encoded obligation.
    #[must_use]
    pub fn smt_unsat() -> Self {
        Self {
            reasoning: ReasoningKind::Smt,
            assurance: AssuranceLevel::SmtBacked,
        }
    }

    /// Bounded model checking explored executions up to `depth`.
    #[must_use]
    pub fn bounded(depth: u64) -> Self {
        Self {
            reasoning: ReasoningKind::BoundedModelCheck { depth },
            assurance: AssuranceLevel::Bounded { depth },
        }
    }

    /// Native deductive verification discharged the obligation.
    #[must_use]
    pub fn deductive() -> Self {
        Self {
            reasoning: ReasoningKind::Deductive,
            assurance: AssuranceLevel::Sound,
        }
    }

    /// An independently checked proof certificate discharged the obligation.
    #[must_use]
    pub fn certified(reasoning: ReasoningKind) -> Self {
        Self {
            reasoning,
            assurance: AssuranceLevel::Certified,
        }
    }

    /// Returns true for bounded evidence, which must not be upgraded during
    /// aggregation or publication.
    #[must_use]
    pub fn is_bounded(&self) -> bool {
        matches!(
            (&self.reasoning, &self.assurance),
            (ReasoningKind::BoundedModelCheck { .. }, _) | (_, AssuranceLevel::Bounded { .. })
        )
    }

    /// Returns true for proof strengths that may count toward a publication
    /// run-level `Proved` result.
    #[must_use]
    pub fn is_publication_grade(&self) -> bool {
        !self.is_bounded()
            && matches!(
                self.assurance,
                AssuranceLevel::SmtBacked | AssuranceLevel::Sound | AssuranceLevel::Certified
            )
    }

    /// Returns true when this evidence is explicitly backed by a solver result
    /// that can be audited through solver transcript artifacts.
    #[must_use]
    pub fn is_solver_backed(&self) -> bool {
        self.assurance == AssuranceLevel::SmtBacked
            && matches!(
                self.reasoning,
                ReasoningKind::Smt | ReasoningKind::Pdr | ReasoningKind::Chc
            )
    }

    /// Returns true when this proof strength is strong enough for an explicit
    /// obligation requirement.
    #[must_use]
    pub fn satisfies_requirement(&self, required: &ProofStrength) -> bool {
        if !self.is_publication_grade() {
            return false;
        }
        if !self.reasoning_satisfies_requirement(&required.reasoning) {
            return false;
        }
        match required.assurance {
            AssuranceLevel::Certified => self.assurance == AssuranceLevel::Certified,
            AssuranceLevel::Sound => {
                matches!(
                    self.assurance,
                    AssuranceLevel::Sound | AssuranceLevel::Certified
                )
            }
            AssuranceLevel::SmtBacked => matches!(
                self.assurance,
                AssuranceLevel::SmtBacked | AssuranceLevel::Sound | AssuranceLevel::Certified
            ),
            AssuranceLevel::Unchecked
            | AssuranceLevel::Heuristic
            | AssuranceLevel::RuntimeObserved
            | AssuranceLevel::Bounded { .. } => true,
        }
    }

    fn reasoning_satisfies_requirement(&self, required: &ReasoningKind) -> bool {
        self.reasoning == *required
    }
}

/// Reasoning technique used by an engine.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReasoningKind {
    Smt,
    BoundedModelCheck { depth: u64 },
    Inductive,
    Deductive,
    Constructive,
    Pdr,
    Chc,
    AbstractInterpretation,
    OwnershipAnalysis,
    ExplicitStateModel,
    TemporalModelCheck,
    ProofCalculus,
    RuntimeMonitoring,
}

/// Assurance provided by proof evidence.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AssuranceLevel {
    Unchecked,
    Heuristic,
    Bounded { depth: u64 },
    RuntimeObserved,
    SmtBacked,
    Sound,
    Certified,
}
