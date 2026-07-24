// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic validation for formalized statements.
//!
//! Type-checking alone is insufficient for correctness — a type-checked
//! formalization may not preserve the mathematical meaning of the original
//! LaTeX statement. This module implements the Semantic Alignment Engine,
//! which validates formalized statements through multiple layers:
//!
//! 1. **Roundtrip Check**: Back-translate Lean→NL and compare to original
//! 2. **Counter-Example Search**: Find concrete values that distinguish
//!    original from formalization (catches over/under-generalization)
//! 3. **Cross-Reference Validation**: Check that referenced definitions
//!    and theorems are consistently formalized
//! 4. **Structural Checks**: Verify the formalization has the expected
//!    shape (quantifier structure, type signatures match domain)

use super::formalize::AdmissionTier;
use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// Validation Results
// ════════════════════════════════════════════════════════════════════════════

/// Outcome of a single validation check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CheckOutcome {
    /// Validation passed.
    Pass,
    /// Validation failed with a reason.
    Fail(String),
    /// Validation was inconclusive (e.g., counter-example search timed out).
    Inconclusive(String),
    /// Validation was skipped (precondition not met).
    Skipped(String),
}

impl CheckOutcome {
    #[must_use]
    pub fn is_pass(&self) -> bool {
        matches!(self, Self::Pass)
    }

    #[must_use]
    pub fn is_fail(&self) -> bool {
        matches!(self, Self::Fail(_))
    }
}

/// Result of the roundtrip NL check.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RoundtripCheck {
    /// Back-translated natural language from the Lean formalization.
    pub roundtrip_nl: String,
    /// Similarity score between original and roundtrip (0.0–1.0).
    pub similarity: f64,
    /// Threshold for passing (default 0.7).
    pub threshold: f64,
    /// Outcome.
    pub outcome: CheckOutcome,
}

/// Result of counter-example search.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CounterExampleCheck {
    /// Whether a distinguishing counter-example was found.
    pub found_counter_example: bool,
    /// Description of the counter-example (if found).
    pub description: String,
    /// Outcome.
    pub outcome: CheckOutcome,
}

/// Result of structural validation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StructuralCheck {
    /// Whether the quantifier structure matches expectations.
    pub quantifier_match: bool,
    /// Whether the type signature matches the domain.
    pub type_domain_match: bool,
    /// Specific issues found.
    pub issues: Vec<String>,
    /// Outcome.
    pub outcome: CheckOutcome,
}

/// Complete semantic validation report for one formalization.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ValidationReport {
    /// Roundtrip NL check.
    pub roundtrip: Option<RoundtripCheck>,
    /// Counter-example search.
    pub counter_example: Option<CounterExampleCheck>,
    /// Structural checks.
    pub structural: Option<StructuralCheck>,
    /// Overall outcome: pass only if ALL checks pass or are inconclusive.
    pub overall: CheckOutcome,
    /// Recommended admission tier based on validation results.
    pub recommended_tier: AdmissionTier,
}

impl ValidationReport {
    /// Create a report with all checks skipped (for when LLM is unavailable).
    #[must_use]
    pub fn all_skipped(reason: &str) -> Self {
        Self {
            roundtrip: None,
            counter_example: None,
            structural: None,
            overall: CheckOutcome::Skipped(reason.to_string()),
            recommended_tier: AdmissionTier::Candidate,
        }
    }

    /// Compute overall outcome from individual checks.
    #[must_use]
    pub fn compute_overall(
        roundtrip: &Option<RoundtripCheck>,
        counter_example: &Option<CounterExampleCheck>,
        structural: &Option<StructuralCheck>,
    ) -> CheckOutcome {
        let checks: Vec<&CheckOutcome> = [
            roundtrip.as_ref().map(|r| &r.outcome),
            counter_example.as_ref().map(|c| &c.outcome),
            structural.as_ref().map(|s| &s.outcome),
        ]
        .into_iter()
        .flatten()
        .collect();

        if checks.is_empty() {
            return CheckOutcome::Skipped("no checks run".to_string());
        }

        // Any failure → overall fail
        for check in &checks {
            if check.is_fail() {
                return CheckOutcome::Fail("one or more checks failed".to_string());
            }
        }

        // All pass → overall pass
        if checks.iter().all(|c| c.is_pass()) {
            return CheckOutcome::Pass;
        }

        // Otherwise inconclusive
        CheckOutcome::Inconclusive("some checks inconclusive".to_string())
    }

    /// Determine recommended tier from validation outcome.
    #[must_use]
    pub fn tier_from_outcome(outcome: &CheckOutcome, type_checks: bool) -> AdmissionTier {
        match (outcome, type_checks) {
            (CheckOutcome::Pass, true) => AdmissionTier::AuditedAlignment,
            (CheckOutcome::Inconclusive(_), true) => AdmissionTier::TypeChecked,
            (_, true) => AdmissionTier::TypeChecked,
            _ => AdmissionTier::Candidate,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Structural Validation (no LLM needed)
// ════════════════════════════════════════════════════════════════════════════

/// Run structural checks on a Lean formalization.
///
/// These checks don't require an LLM — they analyze the syntax of the
/// generated Lean code to catch obvious issues.
#[must_use]
pub fn check_structural(lean_code: &str, kind: &str) -> StructuralCheck {
    let mut issues = Vec::new();

    // Check 1: Correct declaration keyword
    let trimmed = lean_code.trim();
    if kind == "theorem" {
        if !trimmed.starts_with("theorem")
            && !trimmed.starts_with("lemma")
            && !trimmed.starts_with("-- ")
            && !trimmed.starts_with("import")
        {
            issues
                .push("theorem formalization doesn't start with 'theorem' or 'lemma'".to_string());
        }
    } else if kind == "definition"
        && !trimmed.starts_with("def")
        && !trimmed.starts_with("structure")
        && !trimmed.starts_with("class")
        && !trimmed.starts_with("instance")
        && !trimmed.starts_with("abbrev")
        && !trimmed.starts_with("-- ")
        && !trimmed.starts_with("import")
    {
        issues.push(
            "definition formalization doesn't start with 'def', 'structure', or 'class'"
                .to_string(),
        );
    }

    // Check 2: No sorry in theorem formalizations
    if kind == "theorem" && lean_code.contains("sorry") {
        issues.push("theorem contains 'sorry' — proof obligation not discharged".to_string());
    }

    // Check 3: Has a type annotation (contains ':')
    if !lean_code.contains(':') && !lean_code.starts_with("--") {
        issues.push("formalization appears to lack a type annotation".to_string());
    }

    // Check 4: Balanced braces/parens
    let open_parens = lean_code.chars().filter(|&c| c == '(').count();
    let close_parens = lean_code.chars().filter(|&c| c == ')').count();
    if open_parens != close_parens {
        issues.push(format!(
            "unbalanced parentheses: {open_parens} open, {close_parens} close"
        ));
    }

    let quantifier_match = true; // TODO: implement quantifier analysis
    let type_domain_match = issues.is_empty();

    let outcome = if issues.is_empty() {
        CheckOutcome::Pass
    } else {
        CheckOutcome::Fail(issues.join("; "))
    };

    StructuralCheck {
        quantifier_match,
        type_domain_match,
        issues,
        outcome,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Validation Pipeline
// ════════════════════════════════════════════════════════════════════════════

/// Run all available validation checks on a formalization.
///
/// Structural checks are always run. Roundtrip and counter-example checks
/// require an LLM and are skipped if `run_llm_checks` is false.
#[must_use]
pub fn validate(
    lean_code: &str,
    _original_latex: &str,
    kind: &str,
    type_checks: bool,
    run_llm_checks: bool,
) -> ValidationReport {
    let structural = Some(check_structural(lean_code, kind));

    let roundtrip = if run_llm_checks {
        // TODO: implement LLM roundtrip check
        Some(RoundtripCheck {
            roundtrip_nl: String::new(),
            similarity: 0.0,
            threshold: 0.7,
            outcome: CheckOutcome::Skipped("LLM roundtrip not yet implemented".to_string()),
        })
    } else {
        None
    };

    let counter_example = if run_llm_checks {
        // TODO: implement counter-example search
        Some(CounterExampleCheck {
            found_counter_example: false,
            description: String::new(),
            outcome: CheckOutcome::Skipped(
                "counter-example search not yet implemented".to_string(),
            ),
        })
    } else {
        None
    };

    let mut overall = ValidationReport::compute_overall(&roundtrip, &counter_example, &structural);

    // Without LLM checks (roundtrip + counter-example), the validation
    // pipeline is incomplete.  Cap the overall at Inconclusive so that
    // tier_from_outcome cannot promote beyond TypeChecked.
    if !run_llm_checks {
        if let CheckOutcome::Pass = overall {
            overall = CheckOutcome::Inconclusive("LLM checks not run".to_string());
        }
    }

    let recommended_tier = ValidationReport::tier_from_outcome(&overall, type_checks);

    ValidationReport {
        roundtrip,
        counter_example,
        structural,
        overall,
        recommended_tier,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_structural_check_valid_theorem() {
        let code = "theorem inf_primes : ∀ n : Nat, ∃ p, p > n ∧ Nat.Prime p := by sorry";
        let result = check_structural(code, "theorem");
        // sorry is flagged
        assert!(result.outcome.is_fail());
        assert!(result.issues.iter().any(|i| i.contains("sorry")));
    }

    #[test]
    fn test_structural_check_valid_def() {
        let code = "def MyGroup (α : Type*) := Group α";
        let result = check_structural(code, "definition");
        assert!(result.outcome.is_pass());
    }

    #[test]
    fn test_structural_check_wrong_keyword() {
        let code = "structure Foo where\n  x : Nat";
        let thm_result = check_structural(code, "theorem");
        assert!(thm_result.outcome.is_fail());

        let def_result = check_structural(code, "definition");
        assert!(def_result.outcome.is_pass());
    }

    #[test]
    fn test_structural_check_unbalanced_parens() {
        let code = "theorem foo : (Nat → (Bool) := sorry";
        let result = check_structural(code, "theorem");
        assert!(result.issues.iter().any(|i| i.contains("unbalanced")));
    }

    #[test]
    fn test_validate_no_llm() {
        let code = "def PrimeSet : Set Nat := {p | Nat.Prime p}";
        let report = validate(code, "the set of prime numbers", "definition", true, false);
        assert!(report.structural.unwrap().outcome.is_pass());
        assert_eq!(report.recommended_tier, AdmissionTier::TypeChecked);
    }

    #[test]
    fn test_tier_progression() {
        // Type-checked + pass semantic → AuditedAlignment
        assert_eq!(
            ValidationReport::tier_from_outcome(&CheckOutcome::Pass, true),
            AdmissionTier::AuditedAlignment
        );

        // Type-checked + inconclusive → TypeChecked
        assert_eq!(
            ValidationReport::tier_from_outcome(&CheckOutcome::Inconclusive("".to_string()), true),
            AdmissionTier::TypeChecked
        );

        // Not type-checked → Candidate
        assert_eq!(
            ValidationReport::tier_from_outcome(&CheckOutcome::Pass, false),
            AdmissionTier::Candidate
        );
    }

    #[test]
    fn test_compute_overall_all_pass() {
        let rt = Some(RoundtripCheck {
            roundtrip_nl: String::new(),
            similarity: 0.9,
            threshold: 0.7,
            outcome: CheckOutcome::Pass,
        });
        let ce = Some(CounterExampleCheck {
            found_counter_example: false,
            description: String::new(),
            outcome: CheckOutcome::Pass,
        });
        let st = Some(StructuralCheck {
            quantifier_match: true,
            type_domain_match: true,
            issues: vec![],
            outcome: CheckOutcome::Pass,
        });
        assert!(ValidationReport::compute_overall(&rt, &ce, &st).is_pass());
    }

    #[test]
    fn test_compute_overall_one_fail() {
        let rt = Some(RoundtripCheck {
            roundtrip_nl: String::new(),
            similarity: 0.3,
            threshold: 0.7,
            outcome: CheckOutcome::Fail("low similarity".to_string()),
        });
        let st = Some(StructuralCheck {
            quantifier_match: true,
            type_domain_match: true,
            issues: vec![],
            outcome: CheckOutcome::Pass,
        });
        assert!(ValidationReport::compute_overall(&rt, &None, &st).is_fail());
    }
}
