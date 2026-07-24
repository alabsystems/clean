// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust ledger for SMT proof verification.
//!
//! Tracks per-step trust classification for the entire proof, providing
//! a 4-level trust hierarchy: KernelVerified > StructurallyAccepted >
//! Axiomatic > Trusted.

use std::collections::HashMap;

use super::dag::{SmtStepId, SmtTheory};

/// Trust classification for a single proof step.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum StepTrustLevel {
    /// Semantically verified by clean's checker (resolution, EUF, LRA Farkas).
    KernelVerified,
    /// Structurally accepted (non-empty clause, correct arity) but not
    /// semantically checked. Examples: BV bit-blast, array axioms.
    StructurallyAccepted,
    /// Axiomatically accepted (input assumptions).
    Axiomatic,
    /// Unverified trust fallback (`:rule trust` or `Generic` theory lemma).
    Trusted,
}

impl std::fmt::Display for StepTrustLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StepTrustLevel::KernelVerified => write!(f, "kernel-verified"),
            StepTrustLevel::StructurallyAccepted => write!(f, "structurally-accepted"),
            StepTrustLevel::Axiomatic => write!(f, "axiomatic"),
            StepTrustLevel::Trusted => write!(f, "trusted"),
        }
    }
}

/// Per-step verification verdict.
#[derive(Debug, Clone)]
pub struct StepVerdict {
    pub step_id: SmtStepId,
    pub trust_level: StepTrustLevel,
    /// Which checker produced this verdict.
    pub checker: &'static str,
    /// Optional diagnostic message.
    pub detail: Option<String>,
}

/// Overall SMT proof verification result.
#[derive(Debug, Clone)]
pub struct SmtVerifyResult {
    /// Whether the proof is valid (terminal step derives empty clause).
    pub valid: bool,
    /// Per-step verdicts.
    pub verdicts: Vec<StepVerdict>,
    /// Summary statistics.
    pub stats: SmtVerifyStats,
    /// First error encountered, if any.
    pub first_error: Option<SmtVerifyError>,
}

/// Summary statistics for proof verification.
#[derive(Debug, Clone, Default)]
pub struct SmtVerifyStats {
    pub total_steps: u32,
    pub kernel_verified: u32,
    pub structurally_accepted: u32,
    pub axiomatic: u32,
    pub trusted: u32,
    /// Theory lemma breakdown by theory.
    pub theory_lemma_counts: HashMap<SmtTheory, u32>,
}

impl SmtVerifyStats {
    /// Fraction of steps that are kernel-verified, structurally accepted,
    /// or axiomatic.
    #[must_use]
    pub fn verification_coverage(&self) -> f64 {
        if self.total_steps == 0 {
            return 1.0;
        }
        f64::from(self.kernel_verified + self.structurally_accepted + self.axiomatic)
            / f64::from(self.total_steps)
    }

    /// True if no trusted or structurally accepted steps exist.
    ///
    /// In SMT-COMP terminology, a proof with `is_fully_verified() == true`
    /// has verdict "valid": every step was kernel-verified or axiomatic.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.trusted == 0 && self.structurally_accepted == 0
    }

    /// True if some steps are structurally accepted but none are blindly trusted.
    ///
    /// In SMT-COMP terminology, this is a "holey" proof: structurally sound
    /// but with gaps that were not semantically rechecked.
    #[must_use]
    pub fn is_holey(&self) -> bool {
        self.trusted == 0 && self.structurally_accepted > 0
    }

    /// Number of structurally accepted holes (steps not semantically checked).
    #[must_use]
    pub fn holes_count(&self) -> u32 {
        self.structurally_accepted
    }

    /// Competition-style proof verdict string.
    ///
    /// Returns `"valid"` if fully verified, `"holey"` if structurally accepted
    /// steps exist but no trusted steps, or `"invalid"` if any trusted steps
    /// remain.
    #[must_use]
    pub fn competition_verdict(&self) -> &'static str {
        if self.is_fully_verified() {
            "valid"
        } else if self.is_holey() {
            "holey"
        } else {
            "invalid"
        }
    }
}

impl std::fmt::Display for SmtVerifyStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "total_steps={}, kernel_verified={}, holes={}, axiomatic={}, trusted={}, verdict={}",
            self.total_steps,
            self.kernel_verified,
            self.holes_count(),
            self.axiomatic,
            self.trusted,
            self.competition_verdict(),
        )
    }
}

/// Verification error.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SmtVerifyError {
    EmptyProof,
    MissingPremise {
        step: SmtStepId,
        premise: SmtStepId,
    },
    NonPriorPremise {
        step: SmtStepId,
        premise: SmtStepId,
    },
    InvalidResolution {
        step: SmtStepId,
        reason: String,
    },
    InvalidTheoryLemma {
        step: SmtStepId,
        theory: SmtTheory,
        reason: String,
    },
    InvalidBooleanRule {
        step: SmtStepId,
        rule: String,
        reason: String,
    },
    FinalClauseNotEmpty {
        step: SmtStepId,
    },
    TrustStep {
        step: SmtStepId,
    },
    UnsupportedRule {
        step: SmtStepId,
        rule: String,
    },
}

impl std::fmt::Display for SmtVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtVerifyError::EmptyProof => write!(f, "empty proof"),
            SmtVerifyError::MissingPremise { step, premise } => {
                write!(
                    f,
                    "step {} references missing premise {}",
                    step.0, premise.0
                )
            }
            SmtVerifyError::NonPriorPremise { step, premise } => {
                write!(
                    f,
                    "step {} references non-prior premise {}",
                    step.0, premise.0
                )
            }
            SmtVerifyError::InvalidResolution { step, reason } => {
                write!(f, "step {}: invalid resolution: {reason}", step.0)
            }
            SmtVerifyError::InvalidTheoryLemma {
                step,
                theory,
                reason,
            } => {
                write!(
                    f,
                    "step {}: invalid {theory} theory lemma: {reason}",
                    step.0
                )
            }
            SmtVerifyError::InvalidBooleanRule { step, rule, reason } => {
                write!(f, "step {}: invalid boolean rule {rule}: {reason}", step.0)
            }
            SmtVerifyError::FinalClauseNotEmpty { step } => {
                write!(f, "step {}: final clause is not empty", step.0)
            }
            SmtVerifyError::TrustStep { step } => {
                write!(f, "step {}: unverified trust step", step.0)
            }
            SmtVerifyError::UnsupportedRule { step, rule } => {
                write!(f, "step {}: unsupported rule: {rule}", step.0)
            }
        }
    }
}

impl std::error::Error for SmtVerifyError {}

/// A complete trust ledger for an SMT proof.
#[derive(Debug, Clone)]
pub struct TrustLedger {
    /// Per-step trust entries, indexed by SmtStepId.
    entries: Vec<TrustEntry>,
}

/// Single ledger entry.
#[derive(Debug, Clone)]
pub struct TrustEntry {
    pub step_id: SmtStepId,
    pub trust_level: StepTrustLevel,
    /// Theory that produced this step (if theory lemma).
    pub theory: Option<SmtTheory>,
    /// Which checker verified this step.
    pub checker_name: &'static str,
}

impl TrustLedger {
    /// Create a new ledger with pre-allocated capacity.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
        }
    }

    /// Record a step verdict.
    pub fn record(&mut self, verdict: StepVerdict) {
        self.entries.push(TrustEntry {
            step_id: verdict.step_id,
            trust_level: verdict.trust_level,
            theory: None,
            checker_name: verdict.checker,
        });
    }

    /// Record a step verdict with theory information.
    pub fn record_theory(&mut self, verdict: StepVerdict, theory: SmtTheory) {
        self.entries.push(TrustEntry {
            step_id: verdict.step_id,
            trust_level: verdict.trust_level,
            theory: Some(theory),
            checker_name: verdict.checker,
        });
    }

    /// Summary statistics.
    #[must_use]
    pub fn stats(&self) -> SmtVerifyStats {
        let mut stats = SmtVerifyStats {
            total_steps: self.entries.len() as u32,
            ..Default::default()
        };
        for entry in &self.entries {
            match entry.trust_level {
                StepTrustLevel::KernelVerified => stats.kernel_verified += 1,
                StepTrustLevel::StructurallyAccepted => stats.structurally_accepted += 1,
                StepTrustLevel::Axiomatic => stats.axiomatic += 1,
                StepTrustLevel::Trusted => stats.trusted += 1,
            }
            if let Some(theory) = entry.theory {
                *stats.theory_lemma_counts.entry(theory).or_insert(0) += 1;
            }
        }
        stats
    }

    /// All trusted (unverified) steps.
    #[must_use]
    pub fn trusted_steps(&self) -> Vec<&TrustEntry> {
        self.entries
            .iter()
            .filter(|e| e.trust_level == StepTrustLevel::Trusted)
            .collect()
    }

    /// All theory lemma steps grouped by theory.
    #[must_use]
    pub fn theory_breakdown(&self) -> HashMap<SmtTheory, Vec<&TrustEntry>> {
        let mut map: HashMap<SmtTheory, Vec<&TrustEntry>> = HashMap::new();
        for entry in &self.entries {
            if let Some(theory) = entry.theory {
                map.entry(theory).or_default().push(entry);
            }
        }
        map
    }

    /// Convert ledger into a list of verdicts.
    #[must_use]
    pub fn into_verdicts(self) -> Vec<StepVerdict> {
        self.entries
            .into_iter()
            .map(|e| StepVerdict {
                step_id: e.step_id,
                trust_level: e.trust_level,
                checker: e.checker_name,
                detail: None,
            })
            .collect()
    }

    /// Number of entries recorded.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the ledger is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_verdict(step: u32, level: StepTrustLevel) -> StepVerdict {
        StepVerdict {
            step_id: SmtStepId(step),
            trust_level: level,
            checker: "test",
            detail: None,
        }
    }

    #[test]
    fn test_trust_ledger_record_and_stats() {
        let mut ledger = TrustLedger::new(4);
        ledger.record(make_verdict(0, StepTrustLevel::Axiomatic));
        ledger.record(make_verdict(1, StepTrustLevel::Axiomatic));
        ledger.record(make_verdict(2, StepTrustLevel::KernelVerified));
        ledger.record(make_verdict(3, StepTrustLevel::KernelVerified));

        let stats = ledger.stats();
        assert_eq!(stats.total_steps, 4);
        assert_eq!(stats.kernel_verified, 2);
        assert_eq!(stats.axiomatic, 2);
        assert_eq!(stats.trusted, 0);
        assert!(stats.is_fully_verified());
    }

    #[test]
    fn test_trust_ledger_trusted_steps() {
        let mut ledger = TrustLedger::new(3);
        ledger.record(make_verdict(0, StepTrustLevel::KernelVerified));
        ledger.record(make_verdict(1, StepTrustLevel::Trusted));
        ledger.record(make_verdict(2, StepTrustLevel::KernelVerified));

        let trusted = ledger.trusted_steps();
        assert_eq!(trusted.len(), 1);
        assert_eq!(trusted[0].step_id, SmtStepId(1));
    }

    #[test]
    fn test_trust_ledger_theory_breakdown() {
        let mut ledger = TrustLedger::new(3);
        ledger.record_theory(
            make_verdict(0, StepTrustLevel::KernelVerified),
            SmtTheory::Euf,
        );
        ledger.record_theory(
            make_verdict(1, StepTrustLevel::KernelVerified),
            SmtTheory::Lra,
        );
        ledger.record_theory(
            make_verdict(2, StepTrustLevel::KernelVerified),
            SmtTheory::Euf,
        );

        let breakdown = ledger.theory_breakdown();
        assert_eq!(breakdown[&SmtTheory::Euf].len(), 2);
        assert_eq!(breakdown[&SmtTheory::Lra].len(), 1);
    }

    #[test]
    fn test_verification_coverage_empty() {
        let stats = SmtVerifyStats::default();
        assert!((stats.verification_coverage() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_verification_coverage_mixed() {
        let stats = SmtVerifyStats {
            total_steps: 10,
            kernel_verified: 6,
            structurally_accepted: 2,
            axiomatic: 1,
            trusted: 1,
            ..Default::default()
        };
        assert!((stats.verification_coverage() - 0.9).abs() < f64::EPSILON);
        assert!(!stats.is_fully_verified());
    }

    #[test]
    fn test_trust_level_display() {
        assert_eq!(
            StepTrustLevel::KernelVerified.to_string(),
            "kernel-verified"
        );
        assert_eq!(StepTrustLevel::Trusted.to_string(), "trusted");
    }

    #[test]
    fn test_trust_level_ordering() {
        // KernelVerified < StructurallyAccepted < Axiomatic < Trusted
        assert!(StepTrustLevel::KernelVerified < StepTrustLevel::StructurallyAccepted);
        assert!(StepTrustLevel::StructurallyAccepted < StepTrustLevel::Axiomatic);
        assert!(StepTrustLevel::Axiomatic < StepTrustLevel::Trusted);
    }

    #[test]
    fn test_verify_error_display() {
        let err = SmtVerifyError::InvalidResolution {
            step: SmtStepId(5),
            reason: "pivot not found".to_string(),
        };
        let msg = err.to_string();
        assert!(msg.contains("step 5"));
        assert!(msg.contains("pivot not found"));
    }

    #[test]
    fn test_ledger_into_verdicts() {
        let mut ledger = TrustLedger::new(2);
        ledger.record(make_verdict(0, StepTrustLevel::Axiomatic));
        ledger.record(make_verdict(1, StepTrustLevel::KernelVerified));

        let verdicts = ledger.into_verdicts();
        assert_eq!(verdicts.len(), 2);
        assert_eq!(verdicts[0].trust_level, StepTrustLevel::Axiomatic);
        assert_eq!(verdicts[1].trust_level, StepTrustLevel::KernelVerified);
    }

    // ---- valid/holey classification tests ----

    #[test]
    fn test_is_fully_verified_false_with_structurally_accepted_steps() {
        let stats = SmtVerifyStats {
            total_steps: 1,
            structurally_accepted: 1,
            ..Default::default()
        };
        assert!(!stats.is_fully_verified());
    }

    #[test]
    fn test_is_fully_verified_true_with_no_trusted_or_holes() {
        let stats = SmtVerifyStats {
            total_steps: 2,
            kernel_verified: 1,
            axiomatic: 1,
            ..Default::default()
        };
        assert!(stats.is_fully_verified());
    }

    #[test]
    fn test_is_holey_true_with_structurally_accepted_and_no_trusted() {
        let stats = SmtVerifyStats {
            total_steps: 2,
            structurally_accepted: 2,
            ..Default::default()
        };
        assert!(stats.is_holey());
    }

    #[test]
    fn test_is_holey_false_with_trusted_steps() {
        let stats = SmtVerifyStats {
            total_steps: 3,
            structurally_accepted: 2,
            trusted: 1,
            ..Default::default()
        };
        assert!(!stats.is_holey());
    }

    #[test]
    fn test_is_holey_false_when_both_counts_are_zero() {
        let stats = SmtVerifyStats::default();
        assert!(!stats.is_holey());
    }

    #[test]
    fn test_holes_count_returns_structurally_accepted() {
        let stats = SmtVerifyStats {
            total_steps: 4,
            kernel_verified: 1,
            structurally_accepted: 3,
            ..Default::default()
        };
        assert_eq!(stats.holes_count(), 3);
    }

    #[test]
    fn test_competition_verdict_valid() {
        let stats = SmtVerifyStats {
            total_steps: 2,
            kernel_verified: 1,
            axiomatic: 1,
            ..Default::default()
        };
        assert_eq!(stats.competition_verdict(), "valid");
    }

    #[test]
    fn test_competition_verdict_holey() {
        let stats = SmtVerifyStats {
            total_steps: 2,
            structurally_accepted: 2,
            ..Default::default()
        };
        assert_eq!(stats.competition_verdict(), "holey");
    }

    #[test]
    fn test_competition_verdict_invalid() {
        let stats = SmtVerifyStats {
            total_steps: 2,
            kernel_verified: 1,
            trusted: 1,
            ..Default::default()
        };
        assert_eq!(stats.competition_verdict(), "invalid");
    }

    #[test]
    fn test_competition_verdict_invalid_with_holes_and_trusted() {
        let stats = SmtVerifyStats {
            total_steps: 3,
            kernel_verified: 1,
            structurally_accepted: 1,
            trusted: 1,
            ..Default::default()
        };
        assert_eq!(stats.competition_verdict(), "invalid");
    }

    #[test]
    fn test_stats_display_shows_holes() {
        let stats = SmtVerifyStats {
            total_steps: 4,
            kernel_verified: 1,
            structurally_accepted: 2,
            axiomatic: 1,
            ..Default::default()
        };
        let display = stats.to_string();
        assert!(display.contains("holes=2"));
        assert!(display.contains("verdict=holey"));
    }

    #[test]
    fn test_stats_display_valid_verdict() {
        let stats = SmtVerifyStats {
            total_steps: 3,
            kernel_verified: 2,
            axiomatic: 1,
            ..Default::default()
        };
        let display = stats.to_string();
        assert!(display.contains("holes=0"));
        assert!(display.contains("verdict=valid"));
    }

    // ---- AI Model-flagged adversarial soundness tests ----

    #[test]
    fn test_verdict_all_structurally_accepted_with_resolution_verified_is_holey() {
        let stats = SmtVerifyStats {
            total_steps: 4,
            kernel_verified: 1,
            structurally_accepted: 3,
            axiomatic: 0,
            trusted: 0,
            theory_lemma_counts: Default::default(),
        };
        assert!(!stats.is_fully_verified());
        assert!(stats.is_holey());
        assert_eq!(stats.competition_verdict(), "holey");
    }

    #[test]
    fn test_verdict_zero_trusted_zero_accepted_is_valid() {
        let stats = SmtVerifyStats {
            total_steps: 5,
            kernel_verified: 0,
            structurally_accepted: 0,
            axiomatic: 5,
            trusted: 0,
            theory_lemma_counts: Default::default(),
        };
        assert!(stats.is_fully_verified());
        assert!(!stats.is_holey());
        assert_eq!(stats.competition_verdict(), "valid");
    }

    #[test]
    fn test_verdict_one_trusted_among_many_verified_strict_invalid() {
        let stats = SmtVerifyStats {
            total_steps: 101,
            kernel_verified: 100,
            structurally_accepted: 0,
            axiomatic: 0,
            trusted: 1,
            theory_lemma_counts: Default::default(),
        };
        assert!(!stats.is_fully_verified());
        assert!(!stats.is_holey());
        assert_eq!(stats.competition_verdict(), "invalid");
    }

    #[test]
    fn test_verdict_mixed_all_three_is_invalid() {
        let stats = SmtVerifyStats {
            total_steps: 8,
            kernel_verified: 5,
            structurally_accepted: 2,
            axiomatic: 0,
            trusted: 1,
            theory_lemma_counts: Default::default(),
        };
        assert!(!stats.is_fully_verified());
        assert!(!stats.is_holey());
        assert_eq!(stats.competition_verdict(), "invalid");
    }

    #[test]
    fn test_competition_verdict_empty_proof() {
        let stats = SmtVerifyStats {
            total_steps: 0,
            kernel_verified: 0,
            structurally_accepted: 0,
            axiomatic: 0,
            trusted: 0,
            theory_lemma_counts: Default::default(),
        };
        assert!(stats.is_fully_verified());
        assert!(!stats.is_holey());
        assert_eq!(stats.competition_verdict(), "valid");
    }
}
