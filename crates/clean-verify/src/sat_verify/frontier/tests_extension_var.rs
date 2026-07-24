// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extension variable introduction and proof compression.

use super::extension_variable::*;
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Extension variable introduction
// ---------------------------------------------------------------------------

#[test]
fn test_introduce_extension_variable_basic() {
    let def = introduce_extension_variable(&[1, 2], &[3, 4], 5);
    assert_eq!(def.var, 5);
    assert_eq!(def.literal_a, 1);
    assert_eq!(def.literal_b, 3);
}

#[test]
fn test_introduce_extension_variable_negated_literals() {
    let def = introduce_extension_variable(&[-1, 2], &[-3], 10);
    assert_eq!(def.var, 10);
    assert_eq!(def.literal_a, -1);
    assert_eq!(def.literal_b, -3);
}

#[test]
fn test_introduce_extension_variable_single_literal_clauses() {
    let def = introduce_extension_variable(&[7], &[8], 9);
    assert_eq!(def.var, 9);
    assert_eq!(def.literal_a, 7);
    assert_eq!(def.literal_b, 8);
}

#[test]
#[should_panic(expected = "clause_a must be non-empty")]
fn test_introduce_extension_variable_empty_clause_a_panics() {
    let _ = introduce_extension_variable(&[], &[1], 2);
}

#[test]
#[should_panic(expected = "clause_b must be non-empty")]
fn test_introduce_extension_variable_empty_clause_b_panics() {
    let _ = introduce_extension_variable(&[1], &[], 2);
}

// ---------------------------------------------------------------------------
// Definition clause generation
// ---------------------------------------------------------------------------

#[test]
fn test_definition_clauses_basic_and_gate() {
    let def = ExtensionDef {
        var: 3,
        literal_a: 1,
        literal_b: 2,
    };
    let clauses = extension_definition_clauses(&def);

    // z <-> (a AND b) encodes as 3 clauses:
    //   (z OR NOT a OR NOT b)
    //   (NOT z OR a)
    //   (NOT z OR b)
    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0], vec![3, -1, -2]);
    assert_eq!(clauses[1], vec![-3, 1]);
    assert_eq!(clauses[2], vec![-3, 2]);
}

#[test]
fn test_definition_clauses_negated_operands() {
    // z <-> (NOT a AND NOT b)
    let def = ExtensionDef {
        var: 5,
        literal_a: -1,
        literal_b: -2,
    };
    let clauses = extension_definition_clauses(&def);

    assert_eq!(clauses.len(), 3);
    // backward: (z OR -(-1) OR -(-2)) = (z OR 1 OR 2)
    assert_eq!(clauses[0], vec![5, 1, 2]);
    // forward: (NOT z OR -1), (NOT z OR -2)
    assert_eq!(clauses[1], vec![-5, -1]);
    assert_eq!(clauses[2], vec![-5, -2]);
}

#[test]
fn test_definition_clauses_encode_iff_correctly() {
    // Verify the IFF semantics: z=T iff (a=T AND b=T).
    // For z=3, a=1, b=2:
    //   Assignment z=T, a=T, b=T should satisfy all 3 clauses.
    //   Assignment z=T, a=T, b=F should violate clause 3 (-z OR b).
    //   Assignment z=F, a=T, b=T should violate clause 1 (z OR -a OR -b).
    let def = ExtensionDef {
        var: 3,
        literal_a: 1,
        literal_b: 2,
    };
    let clauses = extension_definition_clauses(&def);

    // z=T, a=T, b=T: all satisfied.
    assert!(clause_satisfied(&clauses[0], &[3, 1, 2]));
    assert!(clause_satisfied(&clauses[1], &[3, 1, 2]));
    assert!(clause_satisfied(&clauses[2], &[3, 1, 2]));

    // z=T, a=T, b=F: clause 3 violated.
    assert!(clause_satisfied(&clauses[0], &[3, 1, -2]));
    assert!(clause_satisfied(&clauses[1], &[3, 1, -2]));
    assert!(!clause_satisfied(&clauses[2], &[3, 1, -2]));

    // z=F, a=T, b=T: clause 1 violated.
    assert!(!clause_satisfied(&clauses[0], &[-3, 1, 2]));
    assert!(clause_satisfied(&clauses[1], &[-3, 1, 2]));
    assert!(clause_satisfied(&clauses[2], &[-3, 1, 2]));

    // z=F, a=F, b=F: all satisfied.
    assert!(clause_satisfied(&clauses[0], &[-3, -1, -2]));
    assert!(clause_satisfied(&clauses[1], &[-3, -1, -2]));
    assert!(clause_satisfied(&clauses[2], &[-3, -1, -2]));
}

// ---------------------------------------------------------------------------
// Equisatisfiability preservation
// ---------------------------------------------------------------------------

#[test]
fn test_preserves_sat_simple_sat_formula() {
    // (x) AND (y) -- SAT.
    let original = vec![vec![1], vec![2]];
    let def = ExtensionDef {
        var: 3,
        literal_a: 1,
        literal_b: 2,
    };
    let def_clauses = extension_definition_clauses(&def);
    let mut extended = original.clone();
    extended.extend(def_clauses);

    assert!(verify_extension_preserves_sat(&original, &extended, &[def]));
}

#[test]
fn test_preserves_sat_unsat_formula_stays_unsat() {
    // (x) AND (-x) -- UNSAT.
    let original = vec![vec![1], vec![-1]];
    let def = ExtensionDef {
        var: 2,
        literal_a: 1,
        literal_b: 1,
    };
    let def_clauses = extension_definition_clauses(&def);
    let mut extended = original.clone();
    extended.extend(def_clauses);

    assert!(verify_extension_preserves_sat(&original, &extended, &[def]));
}

#[test]
fn test_preserves_sat_rejects_variable_collision() {
    let original = vec![vec![1, 2]];
    let def = ExtensionDef {
        var: 1, // Collides with original variable.
        literal_a: 1,
        literal_b: 2,
    };
    let def_clauses = extension_definition_clauses(&def);
    let mut extended = original.clone();
    extended.extend(def_clauses);

    assert!(!verify_extension_preserves_sat(
        &original,
        &extended,
        &[def]
    ));
}

#[test]
fn test_preserves_sat_multiple_extensions() {
    let original = vec![vec![1, 2], vec![-1, 2]];
    let def1 = ExtensionDef {
        var: 3,
        literal_a: 1,
        literal_b: 2,
    };
    let def2 = ExtensionDef {
        var: 4,
        literal_a: -1,
        literal_b: 2,
    };
    let mut extended = original.clone();
    extended.extend(extension_definition_clauses(&def1));
    extended.extend(extension_definition_clauses(&def2));

    assert!(verify_extension_preserves_sat(
        &original,
        &extended,
        &[def1, def2]
    ));
}

#[test]
fn test_preserves_sat_complex_unsat() {
    // All-pairs: (x OR y), (-x OR y), (x OR -y), (-x OR -y) -- UNSAT.
    let original = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
    let def = ExtensionDef {
        var: 3,
        literal_a: 1,
        literal_b: 2,
    };
    let mut extended = original.clone();
    extended.extend(extension_definition_clauses(&def));

    assert!(verify_extension_preserves_sat(&original, &extended, &[def]));
}

// ---------------------------------------------------------------------------
// Proof compression ratio
// ---------------------------------------------------------------------------

#[test]
fn test_compression_ratio_identity() {
    let ratio = proof_compression_ratio(100, 100);
    assert!((ratio - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_compression_ratio_compression() {
    let ratio = proof_compression_ratio(200, 100);
    assert!((ratio - 0.5).abs() < f64::EPSILON);
}

#[test]
fn test_compression_ratio_expansion() {
    let ratio = proof_compression_ratio(100, 200);
    assert!((ratio - 2.0).abs() < f64::EPSILON);
}

#[test]
fn test_compression_ratio_zero_original() {
    let ratio = proof_compression_ratio(0, 100);
    assert!(ratio.is_infinite());
}

#[test]
fn test_compression_ratio_both_zero() {
    let ratio = proof_compression_ratio(0, 0);
    // 0/0 -- our function returns INFINITY for original_size == 0.
    assert!(ratio.is_infinite());
}

// ---------------------------------------------------------------------------
// Common subexpression finding
// ---------------------------------------------------------------------------

#[test]
fn test_find_common_subexpressions_basic() {
    // Pair (1, 2) appears in both clauses.
    let clauses = vec![vec![1, 2, 3], vec![1, 2, 4]];
    let pairs = find_common_subexpressions(&clauses);
    assert!(pairs.contains(&(1, 2)));
}

#[test]
fn test_find_common_subexpressions_no_common() {
    let clauses = vec![vec![1, 2], vec![3, 4]];
    let pairs = find_common_subexpressions(&clauses);
    assert!(pairs.is_empty());
}

#[test]
fn test_find_common_subexpressions_multiple_pairs() {
    // (1,2) in clauses 0,1; (1,3) in clauses 0,2.
    let clauses = vec![vec![1, 2, 3], vec![1, 2, 4], vec![1, 3, 5]];
    let pairs = find_common_subexpressions(&clauses);
    assert!(pairs.contains(&(1, 2)));
    assert!(pairs.contains(&(1, 3)));
}

#[test]
fn test_find_common_subexpressions_single_clause() {
    // Single clause can't have pairs appearing in multiple clauses.
    let clauses = vec![vec![1, 2, 3, 4, 5]];
    let pairs = find_common_subexpressions(&clauses);
    assert!(pairs.is_empty());
}

#[test]
fn test_find_common_subexpressions_empty_input() {
    let pairs = find_common_subexpressions(&[]);
    assert!(pairs.is_empty());
}

#[test]
fn test_find_common_subexpressions_negated_literals() {
    // Pair (-1, 2) appears in both clauses.
    let clauses = vec![vec![-1, 2, 3], vec![-1, 2, 4]];
    let pairs = find_common_subexpressions(&clauses);
    assert!(pairs.contains(&(-1, 2)));
}

// ---------------------------------------------------------------------------
// Extension chain topological validation
// ---------------------------------------------------------------------------

#[test]
fn test_chain_empty_is_valid() {
    let result = verify_extension_chain(&[]);
    assert!(result.valid);
    assert!(result.topological_order.is_empty());
    assert!(result.cycles.is_empty());
}

#[test]
fn test_chain_single_def_no_deps() {
    let defs = vec![ExtensionDef {
        var: 3,
        literal_a: 1,
        literal_b: 2,
    }];
    let result = verify_extension_chain(&defs);
    assert!(result.valid);
    assert_eq!(result.topological_order, vec![3]);
}

#[test]
fn test_chain_linear_valid_order() {
    // z3 <-> (1 AND 2), ay <-> (z3 AND 1).
    // ay depends on z3, so valid order is [3, 4].
    let defs = vec![
        ExtensionDef {
            var: 3,
            literal_a: 1,
            literal_b: 2,
        },
        ExtensionDef {
            var: 4,
            literal_a: 3, // depends on z3
            literal_b: 1,
        },
    ];
    let result = verify_extension_chain(&defs);
    assert!(result.valid);
    assert_eq!(result.topological_order, vec![3, 4]);
}

#[test]
fn test_chain_cycle_detected() {
    // z3 <-> (ay AND 1), ay <-> (z3 AND 2) -- mutual dependency.
    let defs = vec![
        ExtensionDef {
            var: 3,
            literal_a: 4, // depends on ay
            literal_b: 1,
        },
        ExtensionDef {
            var: 4,
            literal_a: 3, // depends on z3
            literal_b: 2,
        },
    ];
    let result = verify_extension_chain(&defs);
    assert!(!result.valid);
    assert!(result.topological_order.is_empty());
    assert!(!result.cycles.is_empty());
    // Both 3 and 4 should be in the cycle.
    let cycle = &result.cycles[0];
    assert!(cycle.contains(&3));
    assert!(cycle.contains(&4));
}

#[test]
fn test_chain_self_reference() {
    // z3 <-> (z3 AND 1) -- self-referencing.
    let defs = vec![ExtensionDef {
        var: 3,
        literal_a: 3, // depends on self
        literal_b: 1,
    }];
    let result = verify_extension_chain(&defs);
    assert!(!result.valid);
}

#[test]
fn test_chain_parallel_independent() {
    // z3 and ay are independent.
    let defs = vec![
        ExtensionDef {
            var: 3,
            literal_a: 1,
            literal_b: 2,
        },
        ExtensionDef {
            var: 4,
            literal_a: 1,
            literal_b: 2,
        },
    ];
    let result = verify_extension_chain(&defs);
    assert!(result.valid);
    assert_eq!(result.topological_order.len(), 2);
}

// ---------------------------------------------------------------------------
// Proof size estimation
// ---------------------------------------------------------------------------

#[test]
fn test_estimate_no_extensions() {
    let clauses = vec![vec![1, 2], vec![-1, 2]];
    let est = estimate_proof_size_reduction(&clauses, &[]);
    assert_eq!(est.original_clauses, 2);
    assert_eq!(est.extended_clauses, 2);
    assert_eq!(est.new_vars, 0);
    assert!((est.estimated_reduction_factor - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_estimate_with_covering_extension() {
    // Both clauses contain (1, 2).
    let clauses = vec![vec![1, 2, 3], vec![1, 2, 4]];
    let ext = ExtensionDef {
        var: 5,
        literal_a: 1,
        literal_b: 2,
    };
    let est = estimate_proof_size_reduction(&clauses, &[ext]);
    assert_eq!(est.original_clauses, 2);
    assert_eq!(est.extended_clauses, 5); // 2 original + 3 definition
    assert_eq!(est.new_vars, 1);
    // Full coverage (2/2), so reduction factor = 0.5.
    assert!((est.estimated_reduction_factor - 0.5).abs() < f64::EPSILON);
}

#[test]
fn test_estimate_partial_coverage() {
    // Extension covers only 1 of 3 clauses.
    let clauses = vec![vec![1, 2], vec![3, 4], vec![5, 6]];
    let ext = ExtensionDef {
        var: 7,
        literal_a: 1,
        literal_b: 2,
    };
    let est = estimate_proof_size_reduction(&clauses, &[ext]);
    assert_eq!(est.original_clauses, 3);
    assert_eq!(est.new_vars, 1);
    // Coverage = 1/3, factor = 1.0 - 0.5 * (1/3) = ~0.833.
    assert!(est.estimated_reduction_factor > 0.8);
    assert!(est.estimated_reduction_factor < 0.9);
}

#[test]
fn test_estimate_empty_formula() {
    let est = estimate_proof_size_reduction(&[], &[]);
    assert_eq!(est.original_clauses, 0);
    assert_eq!(est.extended_clauses, 0);
    assert!((est.estimated_reduction_factor - 1.0).abs() < f64::EPSILON);
}

// ---------------------------------------------------------------------------
// Proof status constants
// ---------------------------------------------------------------------------

#[test]
fn test_s48_status_is_derived_pending() {
    assert_eq!(S48_EXTENSION_PRESERVES_SAT, ProofStatus::DerivedPending);
}

#[test]
fn test_s49_status_is_derived_pending() {
    assert_eq!(S49_EXTENSION_PROOF_COMPRESSION, ProofStatus::DerivedPending);
}

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

/// Check if a clause is satisfied by a set of true literals.
fn clause_satisfied(clause: &[i32], true_lits: &[i32]) -> bool {
    let set: std::collections::HashSet<i32> = true_lits.iter().copied().collect();
    clause.iter().any(|lit| set.contains(lit))
}
