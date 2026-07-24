// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn nat_sig(name: &str, arity: u32) -> FuncSig {
    FuncSig {
        name: name.to_string(),
        arity,
        sort: Expr::const_str("Nat"),
    }
}

#[test]
fn test_generate_commutativity_candidates() {
    let sigs = vec![nat_sig("Nat.add", 2), nat_sig("Nat.mul", 2)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Commutativity], "Eq");
    assert_eq!(candidates.len(), 2);
    assert!(candidates[0].description.contains("Nat.add"));
    assert!(candidates[1].description.contains("Nat.mul"));
}

#[test]
fn test_generate_associativity_candidates() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Associativity], "Eq");
    assert_eq!(candidates.len(), 1);
    assert!(candidates[0].description.contains("associative"));
}

#[test]
fn test_generate_distributivity_requires_two_funcs() {
    let sigs = vec![nat_sig("Nat.add", 2), nat_sig("Nat.mul", 2)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Distributivity], "Eq");
    // add distributes over mul, mul distributes over add
    assert_eq!(candidates.len(), 2);
}

#[test]
fn test_distributivity_single_func_no_candidates() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Distributivity], "Eq");
    assert!(candidates.is_empty());
}

#[test]
fn test_generate_identity_candidates() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Identity], "Eq");
    assert_eq!(candidates.len(), 1);
    assert!(candidates[0].description.contains("right identity"));
}

#[test]
fn test_generate_all_patterns() {
    let sigs = vec![
        nat_sig("Nat.add", 2),
        nat_sig("Nat.mul", 2),
        nat_sig("Nat.succ", 1),
    ];
    let candidates = generate_candidates(&sigs, TermPattern::ALL, "Eq");
    // Commutativity: 2, Associativity: 2, Distributivity: 2, Identity: 2,
    // Idempotency: 2, Absorption: 2, Monotonicity: 1, Equality: 2, Ordering: 2
    assert!(
        candidates.len() >= 10,
        "got {} candidates",
        candidates.len()
    );
}

#[test]
fn test_unary_funcs_skipped_for_binary_patterns() {
    let sigs = vec![nat_sig("Nat.succ", 1)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Commutativity], "Eq");
    assert!(candidates.is_empty());
}

#[test]
fn test_enumerate_terms_depth_zero() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let terms = enumerate_terms(&sigs, 2, 0);
    assert_eq!(terms.len(), 2, "depth 0 = 2 variables");
}

#[test]
fn test_enumerate_terms_depth_one() {
    let sigs = vec![nat_sig("Nat.succ", 1)];
    let terms = enumerate_terms(&sigs, 1, 1);
    // depth 0: BVar(0)
    // depth 1: succ(BVar(0))
    assert_eq!(terms.len(), 2);
}

#[test]
fn test_enumerate_terms_binary_depth_one() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let terms = enumerate_terms(&sigs, 2, 1);
    // depth 0: BVar(0), BVar(1)  = 2 terms
    // depth 1: add(BVar(0), BVar(0)), add(BVar(0), BVar(1)),
    //          add(BVar(1), BVar(0)), add(BVar(1), BVar(1))  = 4 terms
    assert_eq!(terms.len(), 6);
}

#[test]
fn test_term_pattern_display() {
    assert_eq!(format!("{}", TermPattern::Commutativity), "commutativity");
    assert_eq!(format!("{}", TermPattern::Distributivity), "distributivity");
}

#[test]
fn test_term_pattern_min_arity() {
    assert_eq!(TermPattern::Monotonicity.min_arity(), 1);
    assert_eq!(TermPattern::Commutativity.min_arity(), 2);
}

#[test]
fn test_term_pattern_needs_second_func() {
    assert!(TermPattern::Distributivity.needs_second_func());
    assert!(TermPattern::Absorption.needs_second_func());
    assert!(!TermPattern::Commutativity.needs_second_func());
}

#[test]
fn test_monotonicity_only_unary() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Monotonicity], "Eq");
    assert!(
        candidates.is_empty(),
        "binary func should not generate monotonicity"
    );
}

#[test]
fn test_candidate_equation_has_statement() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let candidates = generate_candidates(&sigs, &[TermPattern::Commutativity], "Eq");
    assert_eq!(candidates.len(), 1);
    // Statement should be a Pi type (forall)
    let stmt_debug = format!("{:?}", candidates[0].statement);
    assert!(
        stmt_debug.contains("Pi"),
        "statement should be Pi: {stmt_debug}"
    );
}
