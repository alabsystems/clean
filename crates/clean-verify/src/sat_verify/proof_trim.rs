// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT proof trimming via backward dependency marking.
//!
//! Removes unnecessary clauses from an LRAT proof, producing a minimal
//! certificate that still constitutes a valid refutation. This is the
//! Rust equivalent of the trimming pass in `drat-trim`.
//!
//! ## Algorithm
//!
//! 1. Identify the empty clause (the refutation target).
//! 2. Mark it as needed.
//! 3. Walk backward through Add steps. For each needed step, mark its
//!    hint clause IDs as needed (positive hints only; negative hints are
//!    RAT pivots, not clause references).
//! 4. Collect only needed Add steps in forward order.
//! 5. Delete steps are retained only when they reference needed clauses.
//!
//! ## Performance
//!
//! The algorithm is O(proof_size) in time and space: one backward pass
//! to propagate marks, one forward pass to collect results.
//!
//! ## References
//!
//! - Heule, Hunt, Wetzler (2017): "Trimming while Checking Clausal Proofs"
//! - drat-trim: <https://github.com/marijnheule/drat-trim>

use std::collections::HashSet;

use super::lrat::{ClauseId, LratError, LratStep};

use thiserror::Error;

/// Errors from proof trimming operations.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum TrimError {
    /// The proof contains no empty clause (no refutation to anchor on).
    #[error("proof contains no empty clause; nothing to trim to")]
    NoRefutation,

    /// LRAT parse error forwarded from the parser.
    #[error("LRAT parse error: {0}")]
    ParseError(#[from] LratError),
}

/// Statistics from a trimming operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrimStats {
    /// Number of Add steps in the original proof.
    pub original_add_steps: usize,
    /// Number of Delete steps in the original proof.
    pub original_delete_steps: usize,
    /// Number of Add steps retained after trimming.
    pub trimmed_add_steps: usize,
    /// Number of Delete steps retained after trimming.
    pub trimmed_delete_steps: usize,
}

impl TrimStats {
    /// Trimming ratio: original add steps / trimmed add steps.
    ///
    /// Returns 1.0 if the trimmed proof has the same number of steps,
    /// `f64::INFINITY` if the trimmed proof has 0 steps (degenerate).
    #[must_use]
    pub fn trim_ratio(&self) -> f64 {
        if self.trimmed_add_steps == 0 {
            if self.original_add_steps == 0 {
                return 1.0;
            }
            return f64::INFINITY;
        }
        self.original_add_steps as f64 / self.trimmed_add_steps as f64
    }

    /// Fraction of Add steps removed (0.0 = none removed, 1.0 = all removed).
    #[must_use]
    pub fn removal_fraction(&self) -> f64 {
        if self.original_add_steps == 0 {
            return 0.0;
        }
        let removed = self.original_add_steps - self.trimmed_add_steps;
        removed as f64 / self.original_add_steps as f64
    }
}

/// Result of a trimming operation: the trimmed steps plus statistics.
#[derive(Debug, Clone)]
pub struct TrimResult {
    /// The trimmed proof steps.
    pub steps: Vec<LratStep>,
    /// Trimming statistics.
    pub stats: TrimStats,
}

/// Trim an LRAT proof to contain only clauses needed for the refutation.
///
/// The algorithm walks backward from the empty clause, marking hint
/// dependencies as needed, then collects only the needed steps in their
/// original forward order.
///
/// # Errors
///
/// Returns [`TrimError::NoRefutation`] if the proof contains no empty clause.
pub fn trim_lrat(steps: &[LratStep]) -> Result<TrimResult, TrimError> {
    // Count original steps by type.
    let original_add_steps = steps
        .iter()
        .filter(|s| matches!(s, LratStep::Add { .. }))
        .count();
    let original_delete_steps = steps
        .iter()
        .filter(|s| matches!(s, LratStep::Delete { .. }))
        .count();

    // Find the empty clause (the refutation). We want the *last* empty
    // clause in case there are multiple (the one that concludes the proof).
    let refutation_id = steps
        .iter()
        .rev()
        .find_map(|step| match step {
            LratStep::Add { id, clause, .. } if clause.is_empty() => Some(*id),
            _ => None,
        })
        .ok_or(TrimError::NoRefutation)?;

    // Backward pass: mark needed clause IDs.
    let mut needed: HashSet<ClauseId> = HashSet::new();
    needed.insert(refutation_id);

    // Walk backward through steps. For each needed Add step, mark its
    // positive hint IDs as needed.
    for step in steps.iter().rev() {
        if let LratStep::Add { id, hints, .. } = step {
            if needed.contains(id) {
                for &hint in hints {
                    // Positive hints are clause references.
                    // Negative hints are RAT pivot indicators (not clause refs).
                    if hint > 0 {
                        let hint_id = ClauseId(hint as u64);
                        needed.insert(hint_id);
                    }
                }
            }
        }
    }

    // Forward pass: collect needed steps in original order.
    let mut trimmed_steps = Vec::new();
    let mut trimmed_add_count = 0usize;
    let mut trimmed_delete_count = 0usize;

    for step in steps {
        match step {
            LratStep::Add { id, .. } => {
                if needed.contains(id) {
                    trimmed_steps.push(step.clone());
                    trimmed_add_count += 1;
                }
            }
            LratStep::Delete { clause_ids } => {
                // Retain delete steps that reference at least one needed clause.
                let relevant_ids: Vec<ClauseId> = clause_ids
                    .iter()
                    .copied()
                    .filter(|cid| needed.contains(cid))
                    .collect();
                if !relevant_ids.is_empty() {
                    trimmed_steps.push(LratStep::Delete {
                        clause_ids: relevant_ids,
                    });
                    trimmed_delete_count += 1;
                }
            }
        }
    }

    Ok(TrimResult {
        steps: trimmed_steps,
        stats: TrimStats {
            original_add_steps,
            original_delete_steps,
            trimmed_add_steps: trimmed_add_count,
            trimmed_delete_steps: trimmed_delete_count,
        },
    })
}

/// Serialize LRAT steps to text format.
///
/// Each Add step becomes: `<id> <lit1> <lit2> ... 0 <hint1> <hint2> ... 0`
/// Each Delete step becomes: `<id> d <cid1> <cid2> ... 0`
/// (Delete steps use the first clause ID as the line ID, per LRAT convention.)
#[must_use]
pub fn steps_to_text(steps: &[LratStep]) -> String {
    let mut out = String::new();
    for step in steps {
        match step {
            LratStep::Add { id, clause, hints } => {
                out.push_str(&id.0.to_string());
                for lit in clause {
                    out.push(' ');
                    out.push_str(&lit.0.to_string());
                }
                out.push_str(" 0");
                for hint in hints {
                    out.push(' ');
                    out.push_str(&hint.to_string());
                }
                out.push_str(" 0\n");
            }
            LratStep::Delete { clause_ids } => {
                // LRAT delete format: any positive id, then 'd', then the ids.
                // By convention we use the first clause_id as the line anchor.
                if let Some(first) = clause_ids.first() {
                    out.push_str(&first.0.to_string());
                }
                out.push_str(" d");
                for cid in clause_ids {
                    out.push(' ');
                    out.push_str(&cid.0.to_string());
                }
                out.push_str(" 0\n");
            }
        }
    }
    out
}

/// Parse a text LRAT proof, trim it, and return the trimmed text.
///
/// Convenience function that chains parsing, trimming, and serialization.
///
/// # Errors
///
/// Returns [`TrimError`] on parse failure or if no refutation is found.
pub fn trim_lrat_text(proof: &str) -> Result<(String, TrimStats), TrimError> {
    let steps = super::lrat::parse_text_lrat(proof)?;
    let result = trim_lrat(&steps)?;
    let text = steps_to_text(&result.steps);
    Ok((text, result.stats))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::lrat::{parse_text_lrat, ClauseId, LratChecker, LratStep};
    use crate::sat_verify::types::Lit;

    /// Helper: build Add step.
    fn add(id: u64, clause: &[i32], hints: &[i64]) -> LratStep {
        LratStep::Add {
            id: ClauseId(id),
            clause: clause.iter().map(|&v| Lit(v)).collect(),
            hints: hints.to_vec(),
        }
    }

    /// Helper: build Delete step.
    fn del(ids: &[u64]) -> LratStep {
        LratStep::Delete {
            clause_ids: ids.iter().map(|&v| ClauseId(v)).collect(),
        }
    }

    // ------------------------------------------------------------------
    // Test 1: Simple trimming — 2 needed, 3 unnecessary
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_simple_removes_unnecessary() {
        // Original clauses (hypothetical, ids 1-3):
        //   1: {x1}
        //   2: {-x1}
        //   3: {x2}   (unrelated)
        //
        // Proof steps:
        //   4: {x2, x1} from hints [1, 3]    <- unnecessary
        //   5: {-x2}    from hints [2]        <- unnecessary
        //   6: {}        from hints [1, 2]    <- NEEDED (empty clause)
        //
        // The empty clause (6) only needs clauses 1 and 2 (original).
        // Steps 4 and 5 are not in the dependency chain.
        let steps = vec![
            add(4, &[2, 1], &[1, 3]),
            add(5, &[-2], &[2]),
            add(6, &[], &[1, 2]),
        ];

        let result = trim_lrat(&steps).expect("should trim");
        assert_eq!(result.stats.original_add_steps, 3);
        assert_eq!(result.stats.trimmed_add_steps, 1);
        assert_eq!(result.stats.trim_ratio(), 3.0);

        // Only the empty clause should remain.
        assert_eq!(result.steps.len(), 1);
        assert!(matches!(&result.steps[0], LratStep::Add { id, clause, .. }
            if *id == ClauseId(6) && clause.is_empty()));
    }

    // ------------------------------------------------------------------
    // Test 2: Already minimal — all clauses needed
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_already_minimal() {
        // Original clauses:
        //   1: {x1, x2}
        //   2: {-x1}
        //   3: {-x2}
        //
        // Proof:
        //   4: {x2}  from [1, 2]  <- needed (hint of 5)
        //   5: {}     from [4, 3]  <- needed (empty clause)
        let steps = vec![add(4, &[2], &[1, 2]), add(5, &[], &[4, 3])];

        let result = trim_lrat(&steps).expect("should trim");
        assert_eq!(result.stats.original_add_steps, 2);
        assert_eq!(result.stats.trimmed_add_steps, 2);
        assert!((result.stats.trim_ratio() - 1.0).abs() < f64::EPSILON);
        assert!((result.stats.removal_fraction() - 0.0).abs() < f64::EPSILON);
    }

    // ------------------------------------------------------------------
    // Test 3: Deep chain with branching
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_deep_chain_with_branching() {
        // Original clauses:
        //   1: {x1, x2}
        //   2: {-x1}
        //   3: {-x2, x3}
        //   4: {-x3}
        //
        // Proof:
        //   5:  {x2}    from [1, 2]    <- needed
        //   6:  {x3}    from [3, 5]    <- needed
        //   7:  {}      from [6, 4]    <- needed (empty clause)
        //   8:  {x1}    from [1, 3]    <- NOT needed (dead branch)
        //   9:  {-x1}   from [2]       <- NOT needed (dead branch)
        //
        // Empty clause 7 needs 6 and 4(orig). 6 needs 3(orig) and 5. 5 needs 1(orig) and 2(orig).
        // Steps 8 and 9 are dead branches.
        let steps = vec![
            add(5, &[2], &[1, 2]),
            add(6, &[3], &[3, 5]),
            add(7, &[], &[6, 4]),
            add(8, &[1], &[1, 3]),
            add(9, &[-1], &[2]),
        ];

        let result = trim_lrat(&steps).expect("should trim");
        assert_eq!(result.stats.original_add_steps, 5);
        assert_eq!(result.stats.trimmed_add_steps, 3);

        // Verify the trimmed steps are 5, 6, 7 in order.
        let trimmed_ids: Vec<u64> = result
            .steps
            .iter()
            .filter_map(|s| match s {
                LratStep::Add { id, .. } => Some(id.0),
                _ => None,
            })
            .collect();
        assert_eq!(trimmed_ids, vec![5, 6, 7]);
    }

    // ------------------------------------------------------------------
    // Test 4: No refutation — error
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_no_refutation_errors() {
        let steps = vec![add(4, &[1, 2], &[1]), add(5, &[-1], &[2])];

        let err = trim_lrat(&steps).expect_err("should fail");
        assert_eq!(err, TrimError::NoRefutation);
    }

    // ------------------------------------------------------------------
    // Test 5: Delete steps are filtered
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_filters_delete_steps() {
        // Steps:
        //   4: {x2}  from [1, 2]    <- needed
        //   del: [1]                 <- needed (references clause 1 which is needed)
        //   5: {}     from [4, 3]    <- needed
        //   del: [99]               <- NOT needed (references unneeded clause)
        let steps = vec![
            add(4, &[2], &[1, 2]),
            del(&[1]),
            add(5, &[], &[4, 3]),
            del(&[99]),
        ];

        let result = trim_lrat(&steps).expect("should trim");
        assert_eq!(result.stats.trimmed_delete_steps, 1);

        // The delete for clause 1 should be retained.
        let delete_step = result
            .steps
            .iter()
            .find(|s| matches!(s, LratStep::Delete { .. }));
        assert!(delete_step.is_some());
        if let Some(LratStep::Delete { clause_ids }) = delete_step {
            assert_eq!(clause_ids, &[ClauseId(1)]);
        }
    }

    // ------------------------------------------------------------------
    // Test 6: Round-trip — trim then verify
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_roundtrip_verify() {
        // Full proof for 3-variable UNSAT:
        //   1: {1, 2}    (original)
        //   2: {-1}      (original)
        //   3: {-2, 3}   (original)
        //   4: {-3}      (original)
        //
        // Proof with some dead steps:
        //   5: {2}   from [1, 2]    <- needed
        //   6: {3}   from [3, 5]    <- needed
        //   7: {1}   from [1]       <- dead (not needed for refutation)
        //   8: {}    from [6, 4]    <- needed (empty clause)
        let steps = vec![
            add(5, &[2], &[1, 2]),
            add(6, &[3], &[3, 5]),
            add(7, &[1], &[1]),
            add(8, &[], &[6, 4]),
        ];

        let result = trim_lrat(&steps).expect("should trim");

        // Verify: step 7 should be removed.
        assert_eq!(result.stats.trimmed_add_steps, 3);

        // Now verify the trimmed proof passes the LRAT checker.
        let mut checker = LratChecker::new(3);
        checker
            .add_original(ClauseId(1), &[Lit(1), Lit(2)])
            .expect("add original");
        checker
            .add_original(ClauseId(2), &[Lit(-1)])
            .expect("add original");
        checker
            .add_original(ClauseId(3), &[Lit(-2), Lit(3)])
            .expect("add original");
        checker
            .add_original(ClauseId(4), &[Lit(-3)])
            .expect("add original");

        let verify_result = checker
            .verify_proof(&result.steps)
            .expect("trimmed proof should verify");
        assert!(verify_result.refuted);
        assert!(verify_result.valid);
    }

    // ------------------------------------------------------------------
    // Test 7: Text round-trip
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_text_roundtrip() {
        let proof_text = "\
5 2 0 1 2 0
6 3 0 3 5 0
7 1 0 1 0
8 0 6 4 0
";
        let (trimmed_text, stats) = trim_lrat_text(proof_text).expect("should trim text");

        assert_eq!(stats.original_add_steps, 4);
        assert_eq!(stats.trimmed_add_steps, 3);

        // The trimmed text should be parseable.
        let reparsed = parse_text_lrat(&trimmed_text).expect("should reparse");
        assert_eq!(reparsed.len(), 3);

        // Verify step 7 (clause {1}) is not in the trimmed output.
        let ids: Vec<u64> = reparsed
            .iter()
            .filter_map(|s| match s {
                LratStep::Add { id, .. } => Some(id.0),
                _ => None,
            })
            .collect();
        assert_eq!(ids, vec![5, 6, 8]);
    }

    // ------------------------------------------------------------------
    // Test 8: Serialization format
    // ------------------------------------------------------------------

    #[test]
    fn test_steps_to_text_format() {
        let steps = vec![add(5, &[1, -2], &[3, 4]), del(&[1, 2]), add(6, &[], &[5])];

        let text = steps_to_text(&steps);
        assert_eq!(text, "5 1 -2 0 3 4 0\n1 d 1 2 0\n6 0 5 0\n");
    }

    // ------------------------------------------------------------------
    // Test 9: Empty proof (only delete steps, no adds)
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_empty_proof_no_adds() {
        let steps = vec![del(&[1, 2])];
        let err = trim_lrat(&steps).expect_err("should fail");
        assert_eq!(err, TrimError::NoRefutation);
    }

    // ------------------------------------------------------------------
    // Test 10: Stats helpers
    // ------------------------------------------------------------------

    #[test]
    fn test_trim_stats_removal_fraction() {
        let stats = TrimStats {
            original_add_steps: 10,
            original_delete_steps: 3,
            trimmed_add_steps: 4,
            trimmed_delete_steps: 1,
        };
        assert!((stats.removal_fraction() - 0.6).abs() < f64::EPSILON);
        assert!((stats.trim_ratio() - 2.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_trim_stats_zero_original() {
        let stats = TrimStats {
            original_add_steps: 0,
            original_delete_steps: 0,
            trimmed_add_steps: 0,
            trimmed_delete_steps: 0,
        };
        assert!((stats.removal_fraction() - 0.0).abs() < f64::EPSILON);
        assert!((stats.trim_ratio() - 1.0).abs() < f64::EPSILON);
    }
}
