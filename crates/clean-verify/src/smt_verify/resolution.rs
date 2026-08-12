// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Resolution checker for SMT proof steps.
//!
//! Validates binary resolution and theory resolution steps by checking
//! that the conclusion clause follows from the premises by resolving
//! on a pivot literal.

use super::dag::{SmtProofDag, SmtStepId, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "resolution";

/// Verify a resolution step.
///
/// A resolution step combines two or more premise clauses by resolving
/// on pivot literals. The conclusion contains all literals from the
/// premises except the complementary pivot pair.
///
/// # Algorithm
///
/// 1. If exactly 2 premises and a pivot is given, do strict binary resolution.
/// 2. For multi-premise chain resolution:
///    a. Compute the resolvent independently by folding premises left-to-right,
///    performing pairwise resolution at each step.
///    b. Compare the computed resolvent against the claimed clause.
///    c. Reject if they don't match (prevents malicious result fabrication).
pub(crate) fn check_resolution(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    premises: &[SmtStepId],
    pivot: Option<SmtTermId>,
    derived_clauses: &[Option<Vec<SmtTermId>>],
) -> StepVerdict {
    // Need at least one premise for resolution.
    if premises.is_empty() {
        return StepVerdict {
            step_id,
            trust_level: StepTrustLevel::Trusted,
            checker: CHECKER_NAME,
            detail: Some("resolution with no premises".to_string()),
        };
    }

    // Collect all premise clauses (keep them separated for premise tracking).
    let mut premise_clauses: Vec<Vec<SmtTermId>> = Vec::with_capacity(premises.len());
    for &pid in premises {
        let idx = pid.0 as usize;
        if idx >= derived_clauses.len() {
            return StepVerdict {
                step_id,
                trust_level: StepTrustLevel::Trusted,
                checker: CHECKER_NAME,
                detail: Some(format!("premise {} out of range", pid.0)),
            };
        }
        match &derived_clauses[idx] {
            Some(c) => premise_clauses.push(c.clone()),
            None => {
                return StepVerdict {
                    step_id,
                    trust_level: StepTrustLevel::Trusted,
                    checker: CHECKER_NAME,
                    detail: Some(format!("premise {} has no clause", pid.0)),
                };
            }
        }
    }

    // If we have exactly 2 premises and a pivot, do binary resolution check.
    if let Some(pivot_lit) = pivot {
        if premises.len() == 2 {
            return check_binary_resolution(
                dag,
                step_id,
                clause,
                premises,
                pivot_lit,
                derived_clauses,
            );
        }
    }

    // Also handle 2 premises without explicit pivot (e.g., Alethe resolution/th_resolution).
    if premises.len() == 2 && pivot.is_none() {
        // Try to find the pivot by searching for complementary literals.
        if let Some(found_pivot) =
            find_complementary_pivot(dag, &premise_clauses[0], &premise_clauses[1])
        {
            return check_binary_resolution(
                dag,
                step_id,
                clause,
                premises,
                found_pivot,
                derived_clauses,
            );
        }
    }

    // Multi-premise chain resolution.
    //
    // SOUNDNESS-CRITICAL: We compute the resolvent independently by performing
    // sequential pairwise resolution steps, then compare the computed result
    // against the claimed clause. We NEVER use the claimed clause to guide
    // the computation — doing so would let a malicious prover claim an arbitrary
    // result (e.g. the empty clause) and have the checker accept it.
    //
    // Algorithm: fold premises left-to-right. At each step, find ALL complementary
    // pivots between the accumulator and the next premise, try resolving on each
    // one, and collect all reachable resolvents. When there are multiple pivot
    // choices (rare in practice, common in tautological clauses), we must explore
    // all to avoid rejecting valid proofs due to wrong pivot selection.
    //
    // Soundness argument: every candidate resolvent is genuinely derivable from
    // the premises by a sequence of valid resolution steps. We accept if and
    // only if the claimed clause matches one of these genuine resolvents.

    // Build sorted expected clause for comparison.
    let mut expected_sorted = clause.to_vec();
    expected_sorted.sort();
    expected_sorted.dedup();

    // Collect all valid resolvents via iterative fold with pivot branching.
    // Start with the first premise clause as the initial set of accumulators.
    let mut candidates: Vec<Vec<SmtTermId>> = vec![premise_clauses[0].clone()];

    for next_premise in &premise_clauses[1..] {
        let mut next_candidates: Vec<Vec<SmtTermId>> = Vec::new();

        for acc in &candidates {
            // Find ALL complementary pivot pairs between accumulator and next premise.
            let pivots = find_all_complementary_pivot_pairs(dag, acc, next_premise);

            if pivots.is_empty() {
                // No pivot found for this accumulator path — dead end.
                continue;
            }

            for (lit_acc, lit_next) in &pivots {
                // Resolve: (acc \ {pivot}) ∪ (next \ {neg_pivot})
                let mut new_acc: Vec<SmtTermId> = Vec::new();
                for &lit in acc {
                    if lit == *lit_acc || dag.are_complementary(lit, *lit_next) {
                        continue;
                    }
                    if !new_acc.contains(&lit) {
                        new_acc.push(lit);
                    }
                }
                for &lit in next_premise.iter() {
                    if lit == *lit_next || dag.are_complementary(lit, *lit_acc) {
                        continue;
                    }
                    if !new_acc.contains(&lit) {
                        new_acc.push(lit);
                    }
                }
                // Deduplicate this candidate before adding to avoid combinatorial blowup.
                new_acc.sort();
                new_acc.dedup();
                if !next_candidates.contains(&new_acc) {
                    next_candidates.push(new_acc);
                }
            }
        }

        if next_candidates.is_empty() {
            // No valid resolution path found at this fold step.
            return StepVerdict {
                step_id,
                trust_level: StepTrustLevel::Trusted,
                checker: CHECKER_NAME,
                detail: Some(
                    "chain resolution: no complementary pivot found between \
                     accumulator and next premise"
                        .to_string(),
                ),
            };
        }

        // Bound candidate count to prevent exponential blowup on pathological inputs.
        // 64 candidates is generous for real proofs (typically 1-2 pivots per step).
        const MAX_CANDIDATES: usize = 64;
        if next_candidates.len() > MAX_CANDIDATES {
            next_candidates.truncate(MAX_CANDIDATES);
        }

        candidates = next_candidates;
    }

    // Check if any computed resolvent matches the claimed clause.
    for candidate in &candidates {
        if *candidate == expected_sorted {
            // Check for tautological resolvent (contains both x and not(x)).
            let is_tautology = candidate.iter().any(|&lit_a| {
                candidate
                    .iter()
                    .any(|&lit_b| lit_a != lit_b && dag.are_complementary(lit_a, lit_b))
            });

            return StepVerdict {
                step_id,
                trust_level: StepTrustLevel::KernelVerified,
                checker: CHECKER_NAME,
                detail: if is_tautology {
                    Some("resolvent is tautological".to_string())
                } else {
                    None
                },
            };
        }
    }

    // No computed resolvent matches the claimed clause.
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(format!(
            "resolution result mismatch: no pivot sequence produces the claimed clause \
             ({} candidates explored, claimed {} literals)",
            candidates.len(),
            expected_sorted.len()
        )),
    }
}

/// Find a complementary literal between two clauses.
///
/// Returns the positive literal (or the first of the pair) if found.
fn find_complementary_pivot(
    dag: &SmtProofDag,
    c1: &[SmtTermId],
    c2: &[SmtTermId],
) -> Option<SmtTermId> {
    for &l1 in c1 {
        for &l2 in c2 {
            if dag.are_complementary(l1, l2) {
                return Some(l1);
            }
        }
    }
    None
}

/// Find ALL complementary pivot pairs between two clauses.
///
/// Returns all `(lit_from_c1, lit_from_c2)` pairs where the two literals are
/// complementary. When there are multiple complementary pairs (e.g., clauses
/// share multiple variables), different pivot choices lead to different valid
/// resolvents. Chain resolution must explore all choices to avoid rejecting
/// valid proofs.
///
/// Deduplicates by the underlying variable: if `a/not_a` and `a/not_a` appear
/// from different positions in the same clause, we only return the pair once.
fn find_all_complementary_pivot_pairs(
    dag: &SmtProofDag,
    c1: &[SmtTermId],
    c2: &[SmtTermId],
) -> Vec<(SmtTermId, SmtTermId)> {
    let mut pairs: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    let mut seen_variables: Vec<(SmtTermId, SmtTermId)> = Vec::new();
    for &l1 in c1 {
        for &l2 in c2 {
            if dag.are_complementary(l1, l2) {
                // Deduplicate: check if we already have a pair with these same term IDs.
                let key = if l1 < l2 { (l1, l2) } else { (l2, l1) };
                if !seen_variables.contains(&key) {
                    seen_variables.push(key);
                    pairs.push((l1, l2));
                }
            }
        }
    }
    pairs
}

/// Binary resolution: resolve two clauses on a single pivot.
fn check_binary_resolution(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    premises: &[SmtStepId],
    pivot: SmtTermId,
    derived_clauses: &[Option<Vec<SmtTermId>>],
) -> StepVerdict {
    let c1 = match &derived_clauses[premises[0].0 as usize] {
        Some(c) => c,
        None => {
            return StepVerdict {
                step_id,
                trust_level: StepTrustLevel::Trusted,
                checker: CHECKER_NAME,
                detail: Some("first premise has no clause".to_string()),
            };
        }
    };
    let c2 = match &derived_clauses[premises[1].0 as usize] {
        Some(c) => c,
        None => {
            return StepVerdict {
                step_id,
                trust_level: StepTrustLevel::Trusted,
                checker: CHECKER_NAME,
                detail: Some("second premise has no clause".to_string()),
            };
        }
    };

    // One premise must contain the pivot, the other its negation.
    let p1_has_pivot = c1.contains(&pivot);
    let p2_has_pivot = c2.contains(&pivot);

    // Find the negated pivot in the arena.
    let neg_pivot = find_negation(dag, pivot);

    let p1_has_neg = neg_pivot.is_some_and(|np| c1.contains(&np));
    let p2_has_neg = neg_pivot.is_some_and(|np| c2.contains(&np));

    let valid_pivot = (p1_has_pivot && p2_has_neg) || (p1_has_neg && p2_has_pivot);

    if !valid_pivot {
        // Check if they're complementary by searching all literals.
        let valid_by_search = c1
            .iter()
            .any(|&l1| c2.iter().any(|&l2| dag.are_complementary(l1, l2)));
        if !valid_by_search {
            return StepVerdict {
                step_id,
                trust_level: StepTrustLevel::Trusted,
                checker: CHECKER_NAME,
                detail: Some("pivot not found in complementary position".to_string()),
            };
        }
    }

    // Build result: from C1 remove only the pivot polarity that C1 contains,
    // from C2 remove only the complementary pivot polarity that C2 contains.
    // This is critical for soundness: a tautological clause like {a, not_a, b}
    // resolved on b must keep BOTH a and not_a in the resolvent.
    //
    // Determine which literal to strip from each clause:
    // - If C1 has pivot and C2 has neg_pivot: strip pivot from C1, neg_pivot from C2
    // - If C1 has neg_pivot and C2 has pivot: strip neg_pivot from C1, pivot from C2
    // - Fallback: use DAG complementarity check per literal
    let (c1_strip, c2_strip): (Option<SmtTermId>, Option<SmtTermId>) = if let Some(np) = neg_pivot {
        if p1_has_pivot && p2_has_neg {
            (Some(pivot), Some(np))
        } else if p1_has_neg && p2_has_pivot {
            (Some(np), Some(pivot))
        } else {
            // Fallback: find complementary pair via DAG search
            let mut found = (None, None);
            'outer: for &l1 in c1 {
                for &l2 in c2 {
                    if dag.are_complementary(l1, l2) {
                        found = (Some(l1), Some(l2));
                        break 'outer;
                    }
                }
            }
            found
        }
    } else {
        // No neg_pivot found in arena; find complementary pair via DAG
        let mut found = (None, None);
        'outer2: for &l1 in c1 {
            for &l2 in c2 {
                if dag.are_complementary(l1, l2) {
                    found = (Some(l1), Some(l2));
                    break 'outer2;
                }
            }
        }
        found
    };

    let mut result: Vec<SmtTermId> = Vec::new();
    for &lit in c1 {
        if Some(lit) == c1_strip {
            continue;
        }
        if !result.contains(&lit) {
            result.push(lit);
        }
    }
    for &lit in c2 {
        if Some(lit) == c2_strip {
            continue;
        }
        if !result.contains(&lit) {
            result.push(lit);
        }
    }

    result.sort();
    let mut expected = clause.to_vec();
    expected.sort();

    if result == expected {
        StepVerdict {
            step_id,
            trust_level: StepTrustLevel::KernelVerified,
            checker: CHECKER_NAME,
            detail: None,
        }
    } else {
        // Strict match required: the claimed clause must equal the computed
        // resolvent after deduplication and sorting. Both strengthening (dropping
        // literals) and adding fabricated literals are rejected.
        StepVerdict {
            step_id,
            trust_level: StepTrustLevel::Trusted,
            checker: CHECKER_NAME,
            detail: Some(format!(
                "binary resolution result mismatch: computed {} literals, claimed {}",
                result.len(),
                expected.len()
            )),
        }
    }
}

/// Find the term ID for the negation of a given term, if it exists in the DAG.
fn find_negation(dag: &SmtProofDag, term_id: SmtTermId) -> Option<SmtTermId> {
    // Check if the term itself is a Not.
    if let Some(super::dag::SmtTerm::Not(inner)) = dag.term(term_id) {
        return Some(*inner);
    }
    // Search the arena for Not(term_id).
    for (i, t) in dag.terms.iter().enumerate() {
        if let super::dag::SmtTerm::Not(inner) = t {
            if *inner == term_id {
                return Some(SmtTermId(i as u32));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtProofStep, SmtSort, SmtTerm};

    /// Helper: build a simple DAG with two complementary unit clauses and resolve.
    fn build_simple_resolution_dag() -> (SmtProofDag, SmtStepId, Vec<Option<Vec<SmtTermId>>>) {
        let mut dag = SmtProofDag::new();

        // Terms: a, not(a)
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        // Step 0: assume {a}
        let s0 = dag.add_step(SmtProofStep::Assume(a));
        // Step 1: assume {not(a)}
        let s1 = dag.add_step(SmtProofStep::Assume(not_a));
        // Step 2: resolve on a -> empty clause
        let s2 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(a),
        });

        let derived = vec![Some(vec![a]), Some(vec![not_a]), None];
        (dag, s2, derived)
    }

    #[test]
    fn test_resolution_binary_simple_valid() {
        let (dag, step_id, derived) = build_simple_resolution_dag();

        if let Some(SmtProofStep::Resolution {
            clause,
            premises,
            pivot,
        }) = dag.step(step_id).cloned()
        {
            let verdict = check_resolution(&dag, step_id, &clause, &premises, pivot, &derived);
            assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
        } else {
            panic!("expected resolution step");
        }
    }

    #[test]
    fn test_resolution_no_premises_returns_trusted() {
        let dag = SmtProofDag::new();
        let step_id = SmtStepId(0);
        let verdict = check_resolution(&dag, step_id, &[], &[], None, &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_resolution_multi_clause() {
        let mut dag = SmtProofDag::new();

        // (a v b), (not_a v c), (not_b v not_c)
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));
        let not_c = dag.add_term(SmtTerm::Not(c));

        let _s0 = dag.add_step(SmtProofStep::Assume(a)); // placeholder
        let _s1 = dag.add_step(SmtProofStep::Assume(not_a)); // placeholder
        let _s2 = dag.add_step(SmtProofStep::Assume(b)); // placeholder

        // 3-premise chain resolution on a,b -> result should be {c, not_c}
        // which simplifies, but for test we just check the mechanism.
        let derived = vec![
            Some(vec![a, b]),         // premise 0
            Some(vec![not_a, c]),     // premise 1
            Some(vec![not_b, not_c]), // premise 2
        ];

        // Resolving s0 + s1 on a: {b, c}
        // Then {b, c} + s2 on b: {c, not_c}
        let expected_clause = vec![c, not_c];
        let step_id = SmtStepId(3);

        let verdict = check_resolution(
            &dag,
            step_id,
            &expected_clause,
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_resolution_mismatch_returns_trusted() {
        let mut dag = SmtProofDag::new();

        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a])];

        // Claim the result is empty (wrong -- should be {b}).
        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: tautological clauses
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_tautological_premise_valid() {
        // Premise 0: {a, not_a, b} (tautological clause)
        // Premise 1: {not_b}
        // Pivot: b
        // Resolvent: {a, not_a}  (still tautological, but resolution is valid)
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));

        let derived = vec![Some(vec![a, not_a, b]), Some(vec![not_b])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[a, not_a],
            &[SmtStepId(0), SmtStepId(1)],
            Some(b),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "tautological premise should resolve correctly: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: pivot appears multiple times in a premise
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_pivot_multiple_occurrences() {
        // Premise 0: {a, a, b} (a appears twice)
        // Premise 1: {not_a, c}
        // Pivot: a
        // Resolvent (after dedup): {b, c}
        // The pivot should be removed even though it appears twice in premise 0.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, a, b]), Some(vec![not_a, c])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, c],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "multi-occurrence pivot should be fully eliminated: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: chain resolution (multiple steps) producing empty clause
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_chain_to_empty() {
        // Premise 0: {a}
        // Premise 1: {not_a, b}
        // Premise 2: {not_b}
        // Chain resolution: resolve 0+1 on a => {b}, then {b}+2 on b => {}
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));

        let derived = vec![Some(vec![a]), Some(vec![not_a, b]), Some(vec![not_b])];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "chain resolution to empty clause should be valid: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: binary resolution without explicit pivot
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_binary_no_pivot_finds_complement() {
        // Premise 0: {a, b}
        // Premise 1: {not_a, c}
        // No explicit pivot — checker should find a/not_a as the pivot.
        // Result: {b, c}
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a, c])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, c],
            &[SmtStepId(0), SmtStepId(1)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "binary resolution without pivot should auto-detect: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: premises with no complementary literals
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_no_complementary_literals_rejected() {
        // Premise 0: {a}
        // Premise 1: {b}
        // No complementary pair — resolution is not applicable.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));

        let derived = vec![Some(vec![a]), Some(vec![b])];

        // Try to claim empty clause (fabricated).
        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "no complementary literals should be rejected: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: fabricated literal in the claimed clause
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_fabricated_literal_rejected() {
        // Premise 0: {a}
        // Premise 1: {not_a}
        // Claim: {b}  (fabricated — b appears in no premise)
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a]), Some(vec![not_a])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "fabricated literal should be rejected: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: resolution with empty premise clause
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_empty_premise_clause() {
        // Premise 0: {} (empty clause, already a refutation)
        // Premise 1: {a}
        // Resolving with an empty premise should yield {} (trivially).
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let _not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![]), Some(vec![a])];

        // No complementary pivot between {} and {a}, so resolution
        // can't find a valid pivot — this should be rejected for binary.
        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1)],
            None,
            &derived,
        );
        // Empty premise has nothing to resolve on — fallback to trusted.
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "resolution with empty premise and no pivot should fallback: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: single premise (no resolution partner)
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_single_premise_identity() {
        // Single premise: {a, b}
        // Claiming result: {a, b} — identity, but resolution requires 2+ premises.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));

        let derived = vec![Some(vec![a, b])];

        let step_id = SmtStepId(1);
        let verdict = check_resolution(&dag, step_id, &[a, b], &[SmtStepId(0)], None, &derived);
        // Chain resolution with 1 premise and no eliminations: {a, b} == {a, b}.
        // This is actually valid in some Alethe proof formats (identity resolution).
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "single premise identity should be accepted: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: 4-premise chain resolution
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_four_premise_chain() {
        // Premise 0: {a}
        // Premise 1: {not_a, b}
        // Premise 2: {not_b, c}
        // Premise 3: {not_c}
        // Chain: a -> b -> c -> empty
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));
        let not_c = dag.add_term(SmtTerm::Not(c));

        let derived = vec![
            Some(vec![a]),
            Some(vec![not_a, b]),
            Some(vec![not_b, c]),
            Some(vec![not_c]),
        ];

        let step_id = SmtStepId(4);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2), SmtStepId(3)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "4-premise chain to empty should be valid: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Edge case: resolution claiming wrong extra literal
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_wrong_result_extra_literal_rejected() {
        // Premise 0: {a, b}
        // Premise 1: {not_a, c}
        // Correct resolvent: {b, c}
        // Claim: {b, c, d}  — d is fabricated.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a, c])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, c, d],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "fabricated extra literal should be rejected: {:?}",
            verdict.detail
        );
    }

    // ────────────────────────────────────────────────────────────────
    // Soundness regression: tautological clause with pivot's negation
    // (Issue #3346 — binary resolution must only strip the correct
    // polarity from each parent, not both polarities from both)
    // ────────────────────────────────────────────────────────────────

    #[test]
    fn test_resolution_tautological_c1_keeps_neg_pivot() {
        // C1: {a, not_a}  (tautological, contains both a and not_a)
        // C2: {not_a, b}
        // Pivot: a
        //
        // Correct resolution:
        //   From C1: remove `a` (positive pivot) -> {not_a}
        //   From C2: remove `not_a` (negative pivot) -> {b}
        //   Resolvent: {not_a, b}
        //
        // BUG (pre-fix): stripped both `a` AND `not_a` from C1,
        //   yielding resolvent {b} — incorrectly dropping `not_a`.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, not_a]), Some(vec![not_a, b])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[not_a, b],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "tautological C1 must keep not_a in resolvent: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_resolution_tautological_c1_keeps_neg_pivot_rejects_wrong_claim() {
        // Same setup as above but claiming the WRONG (buggy) resolvent {b}.
        // The checker must REJECT this because not_a should be in the result.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, not_a]), Some(vec![not_a, b])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b], // Wrong! Missing not_a.
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "claiming resolvent without not_a must be rejected: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_resolution_tautological_c2_keeps_pos_pivot() {
        // C1: {a, b}
        // C2: {not_a, a, c}  (tautological, contains both a and not_a)
        // Pivot: a
        //
        // Correct resolution:
        //   From C1: remove `a` (positive pivot) -> {b}
        //   From C2: remove `not_a` (negative pivot) -> {a, c}
        //   Resolvent: {b, a, c}
        //
        // BUG (pre-fix): stripped both `a` AND `not_a` from C2,
        //   yielding resolvent {b, c} — incorrectly dropping `a` from C2.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a, a, c])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, a, c],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "tautological C2 must keep `a` in resolvent: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_resolution_both_tautological_different_pivot() {
        // C1: {x, not_x, a}  (tautological on x, contains pivot a)
        // C2: {y, not_y, not_a}  (tautological on y, contains neg pivot)
        // Pivot: a
        //
        // Correct resolvent: {x, not_x, y, not_y}
        // Both tautologies' complementary pairs must survive.
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Bool));
        let y = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Bool));
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let not_x = dag.add_term(SmtTerm::Not(x));
        let not_y = dag.add_term(SmtTerm::Not(y));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![x, not_x, a]), Some(vec![y, not_y, not_a])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[x, not_x, y, not_y],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "both tautological clauses must preserve non-pivot complementary pairs: {:?}",
            verdict.detail
        );
    }

    // ════════════════════════════════════════════════════════════════
    // SOUNDNESS FIX TESTS (#3345)
    // These tests verify the fix for the critical bug where the chain
    // resolution checker trusted the claimed result clause.
    // ════════════════════════════════════════════════════════════════

    #[test]
    fn test_soundness_malicious_empty_clause_claim_chain_rejected() {
        // Premise 0: {a, b}
        // Premise 1: {not_a, c}
        // Premise 2: {not_b, d}
        // True resolvent: {c, d}
        // Malicious claim: {} (empty clause)
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a, c]), Some(vec![not_b, d])];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "SOUNDNESS: malicious empty clause claim must be REJECTED: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_chain_correct_resolvent_accepted() {
        // Same premises, but claiming the correct result {c, d}.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a, c]), Some(vec![not_b, d])];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[c, d],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "correct chain resolvent should be accepted: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_malicious_empty_clause_claim_binary_rejected() {
        // Premise 0: {a, b}
        // Premise 1: {not_a}
        // Correct resolvent: {b}
        // Malicious claim: {} (empty clause)
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "SOUNDNESS: malicious empty clause on binary resolution must be REJECTED: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_missing_pivot_in_parent_chain() {
        // Premise 0: {a}
        // Premise 1: {b}  -- no complement of a
        // Premise 2: {not_a}
        // Fold left: resolve {a} with {b} -- no pivot exists. Should reject.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let _not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a]), Some(vec![b]), Some(vec![_not_a])];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "missing pivot in chain should be rejected: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_tautological_resolvent_detected() {
        // 3-premise chain that produces a tautological resolvent, forcing
        // the chain resolution path (which has tautological detection).
        //
        // Premise 0: {a, b}
        // Premise 1: {not_a, c}
        // Premise 2: {not_c, not_b}
        //
        // Fold: {a,b} + {not_a,c} on a => {b,c}
        //       {b,c} + {not_c,not_b} on c => {b,not_b} (tautological!)
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));
        let not_c = dag.add_term(SmtTerm::Not(c));

        let derived = vec![
            Some(vec![a, b]),
            Some(vec![not_a, c]),
            Some(vec![not_c, not_b]),
        ];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, not_b],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert!(
            verdict
                .detail
                .as_ref()
                .is_some_and(|d| d.contains("tautological")),
            "tautological resolvent should be flagged in detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_malicious_strengthening_chain_rejected() {
        // Premise 0: {a, b, c}
        // Premise 1: {not_a}
        // Correct resolvent: {b, c}
        // Malicious claim: {b}  (dropped c)
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, b, c]), Some(vec![not_a])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "strengthening attack must be rejected: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_malicious_strengthening_chain_multi_premise_rejected() {
        // Premise 0: {a, b}
        // Premise 1: {not_a, c}
        // Premise 2: {not_b, d}
        // Correct resolvent: {c, d}
        // Malicious claim: {c}  (dropped d)
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a, c]), Some(vec![not_b, d])];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[c],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "chain strengthening attack must be rejected: {:?}",
            verdict.detail
        );
    }

    // ════════════════════════════════════════════════════════════════
    // POLARITY PRESERVATION TESTS (#3346)
    // These tests verify that binary and chain resolution correctly
    // preserve non-pivot occurrences of the pivot variable's other
    // polarity when resolving tautological clauses.
    // ════════════════════════════════════════════════════════════════

    #[test]
    fn test_chain_tautological_accumulator_preserves_non_pivot_polarity() {
        // 3-premise chain resolution where the intermediate accumulator
        // after the first step is tautological:
        //
        // Premise 0: {a, not_a, b}  (tautological)
        // Premise 1: {not_b, c}
        // Premise 2: {not_c, d}
        //
        // Step 1: resolve {a, not_a, b} with {not_b, c} on b/not_b
        //   → {a, not_a, c}  (MUST preserve both a and not_a)
        // Step 2: resolve {a, not_a, c} with {not_c, d} on c/not_c
        //   → {a, not_a, d}
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));
        let not_c = dag.add_term(SmtTerm::Not(c));

        let derived = vec![
            Some(vec![a, not_a, b]),
            Some(vec![not_b, c]),
            Some(vec![not_c, d]),
        ];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[a, not_a, d],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "chain resolution must preserve tautological pair through intermediate steps: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_chain_tautological_wrong_claim_missing_polarity_rejected() {
        // Same setup as above, but the WRONG claim drops not_a.
        // Must be rejected.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));
        let not_c = dag.add_term(SmtTerm::Not(c));

        let derived = vec![
            Some(vec![a, not_a, b]),
            Some(vec![not_b, c]),
            Some(vec![not_c, d]),
        ];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[a, d], // Wrong! Missing not_a from the tautological premise.
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "chain resolution must reject claim missing polarity from tautological premise: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_binary_self_resolution_tautology() {
        // Self-resolution of tautological clause:
        // C1 = C2 = {a, not_a}, pivot = a
        // Resolvent: C1 \ {a} ∪ C2 \ {not_a} = {not_a} ∪ {a} = {a, not_a}
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        // Both premises point to the same clause
        let derived = vec![Some(vec![a, not_a]), Some(vec![a, not_a])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[a, not_a],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "self-resolution of tautology should yield tautology: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_binary_issue_example_a_nota_b_resolve_with_a_c() {
        // Exact example from issue #3346:
        // C1: {a, not_a, b}, C2: {a, c}
        // Pivot: a (meaning: resolve on variable `a`)
        // C1 provides ~a, C2 provides a.
        // Strip ~a from C1: {a, b}
        // Strip a from C2: {c}
        // Resolvent: {a, b, c}
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, not_a, b]), Some(vec![a, c])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[a, b, c],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "issue #3346 example must produce {{a, b, c}}, not {{b, c}}: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_binary_issue_example_wrong_claim_rejected() {
        // Same setup but claiming the BUGGY resolvent {b, c}.
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, not_a, b]), Some(vec![a, c])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, c], // Wrong! Missing `a` which should be preserved.
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "issue #3346 buggy resolvent {{b, c}} must be rejected: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_chain_pivot_var_reappears_in_later_premise() {
        // Chain where the pivot variable from an earlier step reappears
        // in a later premise, testing that non-pivot occurrences survive:
        //
        // Premise 0: {a, b}
        // Premise 1: {not_a, c}
        // Premise 2: {not_c, a}  -- `a` reappears as non-pivot
        //
        // Step 1: resolve on a/not_a → {b, c}
        // Step 2: resolve on c/not_c → {b, a}
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_c = dag.add_term(SmtTerm::Not(c));

        let derived = vec![Some(vec![a, b]), Some(vec![not_a, c]), Some(vec![not_c, a])];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, a],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "pivot variable reappearing in later premise must be preserved: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_binary_both_premises_contain_both_polarities() {
        // Both premises are tautological on the same variable:
        // C1: {a, not_a, b}, C2: {a, not_a, c}
        // Pivot: a
        // C1 has a (positive), C2 has not_a (negative).
        // Strip a from C1: {not_a, b}
        // Strip not_a from C2: {a, c}
        // Resolvent: {not_a, b, a, c} = {a, not_a, b, c}
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a, not_a, b]), Some(vec![a, not_a, c])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[a, not_a, b, c],
            &[SmtStepId(0), SmtStepId(1)],
            Some(a),
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "both tautological premises must preserve non-pivot polarities: {:?}",
            verdict.detail
        );
    }

    // ════════════════════════════════════════════════════════════════
    // AI Model EXPLOIT REGRESSION TESTS (#3345 / F1)
    // Exact exploit scenario from AI Model 3.1 Pro soundness review.
    // These test the specific attack vector where jointly satisfiable
    // premises could yield a false empty clause when the checker
    // used the claimed result to guide elimination.
    // ════════════════════════════════════════════════════════════════

    #[test]
    fn test_soundness_gemini_f1_exploit_satisfiable_premises_empty_claim_rejected() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("X".to_string(), SmtSort::Bool));
        let y = dag.add_term(SmtTerm::Var("Y".to_string(), SmtSort::Bool));
        let z = dag.add_term(SmtTerm::Var("Z".to_string(), SmtSort::Bool));
        let not_x = dag.add_term(SmtTerm::Not(x));
        let not_y = dag.add_term(SmtTerm::Not(y));
        let not_z = dag.add_term(SmtTerm::Not(z));

        let derived = vec![
            Some(vec![x, y]),
            Some(vec![not_x, z]),
            Some(vec![not_y, not_z]),
        ];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "AI Model F1 EXPLOIT: satisfiable premises must NOT produce empty clause: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_gemini_f1_correct_tautological_resolvent_accepted() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("X".to_string(), SmtSort::Bool));
        let y = dag.add_term(SmtTerm::Var("Y".to_string(), SmtSort::Bool));
        let z = dag.add_term(SmtTerm::Var("Z".to_string(), SmtSort::Bool));
        let not_x = dag.add_term(SmtTerm::Not(x));
        let not_y = dag.add_term(SmtTerm::Not(y));
        let not_z = dag.add_term(SmtTerm::Not(z));

        let derived = vec![
            Some(vec![x, y]),
            Some(vec![not_x, z]),
            Some(vec![not_y, not_z]),
        ];

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
            "correct tautological resolvent should be accepted: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_gemini_f1_alternative_tautological_resolvent_accepted() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("X".to_string(), SmtSort::Bool));
        let y = dag.add_term(SmtTerm::Var("Y".to_string(), SmtSort::Bool));
        let z = dag.add_term(SmtTerm::Var("Z".to_string(), SmtSort::Bool));
        let not_x = dag.add_term(SmtTerm::Not(x));
        let not_y = dag.add_term(SmtTerm::Not(y));
        let not_z = dag.add_term(SmtTerm::Not(z));

        let derived = vec![
            Some(vec![x, y]),
            Some(vec![not_x, z]),
            Some(vec![not_y, not_z]),
        ];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[y, not_y],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "alternative tautological resolvent should also be accepted: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_gemini_f1_partial_strengthening_rejected() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("X".to_string(), SmtSort::Bool));
        let y = dag.add_term(SmtTerm::Var("Y".to_string(), SmtSort::Bool));
        let z = dag.add_term(SmtTerm::Var("Z".to_string(), SmtSort::Bool));
        let not_x = dag.add_term(SmtTerm::Not(x));
        let not_y = dag.add_term(SmtTerm::Not(y));
        let not_z = dag.add_term(SmtTerm::Not(z));

        let derived = vec![
            Some(vec![x, y]),
            Some(vec![not_x, z]),
            Some(vec![not_y, not_z]),
        ];

        let step_id = SmtStepId(3);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[z],
            &[SmtStepId(0), SmtStepId(1), SmtStepId(2)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "strengthening tautological resolvent must be rejected: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_five_premise_satisfiable_empty_claim_rejected() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let d = dag.add_term(SmtTerm::Var("d".to_string(), SmtSort::Bool));
        let e = dag.add_term(SmtTerm::Var("e".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));
        let not_b = dag.add_term(SmtTerm::Not(b));
        let not_c = dag.add_term(SmtTerm::Not(c));
        let not_d = dag.add_term(SmtTerm::Not(d));
        let not_e = dag.add_term(SmtTerm::Not(e));

        let derived = vec![
            Some(vec![a, b]),
            Some(vec![not_a, c]),
            Some(vec![not_c, d]),
            Some(vec![not_d, e]),
            Some(vec![not_b, not_e]),
        ];

        let step_id = SmtStepId(5);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[],
            &[
                SmtStepId(0),
                SmtStepId(1),
                SmtStepId(2),
                SmtStepId(3),
                SmtStepId(4),
            ],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "5-premise satisfiable chain must NOT produce empty clause: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_soundness_fabricated_literal_in_chain_rejected() {
        let mut dag = SmtProofDag::new();
        let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Bool));
        let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Bool));
        let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Bool));
        let not_a = dag.add_term(SmtTerm::Not(a));

        let derived = vec![Some(vec![a]), Some(vec![not_a, b])];

        let step_id = SmtStepId(2);
        let verdict = check_resolution(
            &dag,
            step_id,
            &[b, c],
            &[SmtStepId(0), SmtStepId(1)],
            None,
            &derived,
        );
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::Trusted,
            "chain with fabricated literal must be rejected: {:?}",
            verdict.detail
        );
    }
}
