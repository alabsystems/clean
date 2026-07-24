// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Extension Rule (ER) module.

use super::extension_rule::*;

// ---------------------------------------------------------------------------
// Extension variable encoding
// ---------------------------------------------------------------------------

#[test]
fn test_and_gate_extension_equisat() {
    // Variables: x=1, y=2.  Extension: z=3 defined as z <-> (x AND y).
    // Original formula: (x) AND (y) -- trivially SAT with x=T, y=T.
    let original = vec![vec![1], vec![2]];
    let ext = ExtensionVariable {
        name: 3,
        definition: vec![1, 2],
    };

    let extended = apply_extension(&original, std::slice::from_ref(&ext));

    // Extended should have original 2 clauses + 3 definition clauses.
    // Def(z <-> x AND y): (z OR -x OR -y), (-z OR x), (-z OR y).
    assert_eq!(extended.len(), 5);
    assert!(verify_extension_equisatisfiable(
        &original,
        &extended,
        &[ext]
    ));
}

#[test]
fn test_extension_unsat_formula_stays_unsat() {
    // Original: (x) AND (-x) -- UNSAT.
    let original = vec![vec![1], vec![-1]];
    let ext = ExtensionVariable {
        name: 2,
        definition: vec![1],
    };

    let extended = apply_extension(&original, std::slice::from_ref(&ext));

    // Both should be UNSAT.
    assert!(verify_extension_equisatisfiable(
        &original,
        &extended,
        &[ext]
    ));
}

#[test]
fn test_extension_preserves_sat_complex() {
    // (x1 OR x2) AND (-x1 OR x2) -- SAT when x2=T.
    let original = vec![vec![1, 2], vec![-1, 2]];
    // z=3 <-> (x1 AND x2).
    let ext = ExtensionVariable {
        name: 3,
        definition: vec![1, 2],
    };

    let extended = apply_extension(&original, std::slice::from_ref(&ext));
    assert!(verify_extension_equisatisfiable(
        &original,
        &extended,
        &[ext]
    ));
}

#[test]
fn test_extension_variable_collision_rejected() {
    // Extension variable name collides with existing variable.
    let original = vec![vec![1, 2]];
    let ext = ExtensionVariable {
        name: 1, // Collision!
        definition: vec![2],
    };

    let extended = apply_extension(&original, std::slice::from_ref(&ext));
    assert!(!verify_extension_equisatisfiable(
        &original,
        &extended,
        &[ext]
    ));
}

// ---------------------------------------------------------------------------
// Resolution steps
// ---------------------------------------------------------------------------

#[test]
fn test_er_proof_step_basic_resolution() {
    // Resolve (x OR y) with (-x OR z) on pivot x.
    // Resolvent: (y OR z).
    let resolvent = er_proof_step(&[1, 2], &[-1, 3], 1);
    assert_eq!(resolvent.len(), 2);
    assert!(resolvent.contains(&2));
    assert!(resolvent.contains(&3));
}

#[test]
fn test_er_proof_step_derives_unit() {
    // Resolve (x) with (-x OR y) on pivot x.
    // Resolvent: (y).
    let resolvent = er_proof_step(&[1], &[-1, 2], 1);
    assert_eq!(resolvent, vec![2]);
}

#[test]
fn test_er_proof_step_derives_empty() {
    // Resolve (x) with (-x) on pivot x.
    // Resolvent: empty clause (contradiction).
    let resolvent = er_proof_step(&[1], &[-1], 1);
    assert!(resolvent.is_empty());
}

#[test]
fn test_er_proof_step_deduplicates() {
    // Resolve (x OR y) with (-x OR y) on pivot x.
    // Resolvent: (y) -- no duplicates.
    let resolvent = er_proof_step(&[1, 2], &[-1, 2], 1);
    assert_eq!(resolvent, vec![2]);
}

// ---------------------------------------------------------------------------
// Resolution proof verification
// ---------------------------------------------------------------------------

#[test]
fn test_verify_resolution_proof_simple() {
    // Clauses: (x), (-x). Step: resolve 0 and 1 on pivot x=1.
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![(0, 1, 1)];
    assert!(verify_resolution_proof(&clauses, &steps));
}

#[test]
fn test_verify_resolution_proof_three_step() {
    // Clauses: (x OR y), (-x OR y), (x OR -y), (-x OR -y).
    // This is an unsatisfiable 2-variable formula.
    // Step 1: resolve 0,1 on x=1 -> (y)        [idx 4]
    // Step 2: resolve 2,3 on x=1 -> (-y)        [idx 5]
    // Step 3: resolve 4,5 on y=2 -> empty        [idx 6]
    let clauses = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
    let steps = vec![(0, 1, 1), (2, 3, 1), (4, 5, 2)];
    assert!(verify_resolution_proof(&clauses, &steps));
}

#[test]
fn test_verify_resolution_proof_invalid_index() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![(0, 5, 1)]; // Index 5 out of bounds.
    assert!(!verify_resolution_proof(&clauses, &steps));
}

#[test]
fn test_verify_resolution_proof_wrong_pivot() {
    // Pivot 2 does not appear in clause 0 = (1).
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![(0, 1, 2)];
    assert!(!verify_resolution_proof(&clauses, &steps));
}

// ---------------------------------------------------------------------------
// Extended resolution: full proof using extension variables
// ---------------------------------------------------------------------------

#[test]
fn test_extended_resolution_with_and_gate() {
    // Demonstrate ER proof with an AND-gate extension.
    // Original: (x OR y), (-x OR -y) -- SAT but not a tautology.
    // Extension: z <-> (x AND y), so z=3.
    // Extended adds: (3 OR -1 OR -2), (-3 OR 1), (-3 OR 2).
    let original = vec![vec![1, 2], vec![-1, -2]];
    let ext = ExtensionVariable {
        name: 3,
        definition: vec![1, 2],
    };
    let extended = apply_extension(&original, std::slice::from_ref(&ext));
    assert_eq!(extended.len(), 5);

    // Verify equisatisfiability.
    assert!(verify_extension_equisatisfiable(
        &original,
        &extended,
        &[ext]
    ));
}

#[test]
fn test_multiple_extensions() {
    // Two extensions on a 2-variable formula.
    let original = vec![vec![1, 2]];
    let ext1 = ExtensionVariable {
        name: 3,
        definition: vec![1, 2],
    };
    let ext2 = ExtensionVariable {
        name: 4,
        definition: vec![1],
    };

    let extended = apply_extension(&original, &[ext1.clone(), ext2.clone()]);
    // 1 original + 3 (ext1) + 2 (ext2) = 6.
    assert_eq!(extended.len(), 6);
    assert!(verify_extension_equisatisfiable(
        &original,
        &extended,
        &[ext1, ext2],
    ));
}
