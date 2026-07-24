// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the interactive Polynomial Calculus proof system builder.

use std::collections::BTreeSet;

use super::gf2_algebra::Gf2Poly;
use super::pc_proof_system::*;

// =========================================================================
// Basic construction
// =========================================================================

#[test]
fn test_proof_system_new() {
    let pc = PcProofSystem::new(vec![vec![1], vec![-1]]);
    assert_eq!(pc.num_clauses(), 2);
    assert_eq!(pc.num_derived(), 0);
    assert_eq!(pc.max_degree(), 0);
    assert!(!pc.has_contradiction());
}

#[test]
fn test_proof_system_empty_clauses() {
    let pc = PcProofSystem::new(vec![]);
    assert_eq!(pc.num_clauses(), 0);
}

// =========================================================================
// Axiom download
// =========================================================================

#[test]
fn test_axiom_download() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![-1]]);
    let a0 = pc.axiom_download(0).expect("valid clause");
    assert_eq!(a0, 0);
    assert_eq!(pc.num_derived(), 1);

    let poly = pc.get_derived(0).expect("line 0 exists");
    assert_eq!(*poly, Gf2Poly::from_clause(&[1]));
}

#[test]
fn test_axiom_download_invalid_index() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let result = pc.axiom_download(5);
    assert!(result.is_err());
}

// =========================================================================
// Derive contradiction: x AND NOT x
// =========================================================================

#[test]
fn test_derive_x_and_not_x() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![-1]]);
    let a0 = pc.axiom_download(0).expect("clause 0");
    let a1 = pc.axiom_download(1).expect("clause 1");
    let sum = pc.add(a0, a1).expect("add");
    assert!(pc.is_contradiction(sum));
    assert!(pc.has_contradiction());
    assert_eq!(pc.max_degree(), 1);
}

#[test]
fn test_finalize_x_and_not_x() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![-1]]);
    let a0 = pc.axiom_download(0).expect("clause 0");
    let a1 = pc.axiom_download(1).expect("clause 1");
    let _sum = pc.add(a0, a1).expect("add");

    let proof = pc.finalize().expect("should finalize");
    proof.verify().expect("should verify");
    assert_eq!(proof.degree(), 1);
}

// =========================================================================
// PHP(2,1)
// =========================================================================

#[test]
fn test_derive_php_2_1() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![2], vec![-1, -2]]);

    let a0 = pc.axiom_download(0).expect("pigeon 1 -> hole 1");
    let a1 = pc.axiom_download(1).expect("pigeon 2 -> hole 1");
    let a2 = pc.axiom_download(2).expect("at-most-one");

    // (1+x0) * x1 = x1 + x0*x1
    let mul = pc.mul_var(a0, 1).expect("mul by x1");
    // x0*x1 + (x1 + x0*x1) = x1
    let add1 = pc.add(a2, mul).expect("add");
    // (1+x1) + x1 = 1
    let add2 = pc.add(a1, add1).expect("add");

    assert!(pc.is_contradiction(add2));
    assert_eq!(pc.max_degree(), 2);

    let proof = pc.finalize().expect("should finalize");
    proof.verify().expect("should verify PHP(2,1)");
}

// =========================================================================
// Boolean axiom
// =========================================================================

#[test]
fn test_boolean_axiom_derives_zero() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let ba = pc.boolean_axiom(0).expect("boolean axiom");
    let poly = pc.get_derived(ba).expect("exists");
    assert!(poly.is_zero());
}

// =========================================================================
// Multiplication
// =========================================================================

#[test]
fn test_mul_var() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let a0 = pc.axiom_download(0).expect("clause 0"); // 1 + x0
    let mul = pc.mul_var(a0, 1).expect("mul by x1");
    // (1 + x0) * x1 = x1 + x0*x1
    let poly = pc.get_derived(mul).expect("exists");
    assert_eq!(poly.degree(), 2);
}

#[test]
fn test_mul_poly() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![-1]]);
    let a0 = pc.axiom_download(0).expect("clause 0"); // 1 + x0
    let a1 = pc.axiom_download(1).expect("clause 1"); // x0
    let mul = pc.mul_poly(a0, a1).expect("mul poly");
    // (1+x0)*x0 = x0 + x0^2 = x0 + x0 = 0
    let poly = pc.get_derived(mul).expect("exists");
    assert!(poly.is_zero());
}

#[test]
fn test_mul_var_invalid_index() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let result = pc.mul_var(5, 0);
    assert!(result.is_err());
}

#[test]
fn test_mul_poly_invalid_index() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let result = pc.mul_poly(0, 1);
    assert!(result.is_err());
}

// =========================================================================
// Weakening
// =========================================================================

#[test]
fn test_weaken_nonconstant() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![-1]]);
    let a0 = pc.axiom_download(0).expect("clause 0");
    let mut mono = BTreeSet::new();
    mono.insert(1u32);
    let w = pc.weaken(a0, mono).expect("weaken");
    // (1+x0) + x1 = 1 + x0 + x1
    let poly = pc.get_derived(w).expect("exists");
    assert_eq!(poly.num_terms(), 3);
}

#[test]
fn test_weaken_constant_rejected() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let a0 = pc.axiom_download(0).expect("clause 0");
    let result = pc.weaken(a0, BTreeSet::new());
    assert!(result.is_err());
}

#[test]
fn test_weaken_invalid_index() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let mut mono = BTreeSet::new();
    mono.insert(0u32);
    let result = pc.weaken(5, mono);
    assert!(result.is_err());
}

// =========================================================================
// Error cases
// =========================================================================

#[test]
fn test_add_invalid_index() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let result = pc.add(0, 1);
    assert!(result.is_err());
}

#[test]
fn test_finalize_empty_derivation() {
    let pc = PcProofSystem::new(vec![vec![1]]);
    let result = pc.finalize();
    assert!(result.is_err());
}

#[test]
fn test_finalize_no_contradiction() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let _a0 = pc.axiom_download(0).expect("clause 0");
    let result = pc.finalize();
    assert!(result.is_err());
}

// =========================================================================
// Summary
// =========================================================================

#[test]
fn test_summary_basic() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![-1]]);
    let a0 = pc.axiom_download(0).expect("clause 0");
    let a1 = pc.axiom_download(1).expect("clause 1");
    let _sum = pc.add(a0, a1).expect("add");

    let summary = pc.summary();
    assert_eq!(summary.num_steps, 3);
    assert_eq!(summary.num_axiom_downloads, 2);
    assert_eq!(summary.num_additions, 1);
    assert_eq!(summary.num_multiplications, 0);
    assert_eq!(summary.num_weakens, 0);
    assert_eq!(summary.num_boolean_axioms, 0);
    assert_eq!(summary.max_degree, 1);
    assert!(summary.has_contradiction);
    assert!(summary.last_poly_is_one);
}

#[test]
fn test_summary_php_2_1() {
    let mut pc = PcProofSystem::new(vec![vec![1], vec![2], vec![-1, -2]]);
    let a0 = pc.axiom_download(0).expect("p1");
    let a1 = pc.axiom_download(1).expect("p2");
    let a2 = pc.axiom_download(2).expect("amo");
    let mul = pc.mul_var(a0, 1).expect("mul");
    let add1 = pc.add(a2, mul).expect("add");
    let _add2 = pc.add(a1, add1).expect("add");

    let summary = pc.summary();
    assert_eq!(summary.num_axiom_downloads, 3);
    assert_eq!(summary.num_additions, 2);
    assert_eq!(summary.num_multiplications, 1);
    assert_eq!(summary.max_degree, 2);
    assert!(summary.has_contradiction);
}

// =========================================================================
// into_parts for incomplete proofs
// =========================================================================

#[test]
fn test_into_parts() {
    let mut pc = PcProofSystem::new(vec![vec![1]]);
    let _a0 = pc.axiom_download(0).expect("clause 0");
    let (steps, derived, max_deg) = pc.into_parts();
    assert_eq!(steps.len(), 1);
    assert_eq!(derived.len(), 1);
    assert_eq!(max_deg, 1);
}
