// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, TheoryLemmaKind};

#[test]
fn test_root_empty_clause_step_returns_last_empty_clause() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");
    let not_p = terms.mk_not(p);
    let not_q = terms.mk_not(q);

    let mut proof = Proof::new();
    let h_p = proof.add_assume(p, None);
    let h_not_p = proof.add_assume(not_p, None);
    let first_root = proof.add_resolution(vec![], p, h_p, h_not_p);
    let h_q = proof.add_assume(q, None);
    let h_not_q = proof.add_assume(not_q, None);
    let second_root = proof.add_resolution(vec![], q, h_q, h_not_q);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.root_empty_clause_step(), Some(second_root.0 as usize));
    assert_ne!(Some(first_root.0 as usize), trace.root_empty_clause_step());
}

#[test]
fn test_root_empty_clause_step_returns_none_without_empty_clause() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");

    let mut proof = Proof::new();
    let h_p = proof.add_assume(p, None);
    proof.add_rule_step(AletheRule::Or, vec![q], vec![h_p], vec![p]);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.root_empty_clause_step(), None);
}

#[test]
fn test_reachable_from_traverses_only_upstream_steps() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");
    let not_p = terms.mk_not(p);
    let not_q = terms.mk_not(q);

    let mut proof = Proof::new();
    let s0 = proof.add_assume(p, None);
    let s1 = proof.add_assume(not_p, None);
    let s2 = proof.add_assume(q, None);
    let s3 = proof.add_assume(not_q, None);
    let s4 = proof.add_resolution(vec![q], p, s0, s1);
    let s5 = proof.add_resolution(vec![q], q, s2, s3);
    let s6 = proof.add_resolution(vec![], q, s4, s5);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(
        trace.reachable_from(s6.0 as usize),
        vec![true, true, true, true, true, true, true]
    );
    assert_eq!(
        trace.reachable_from(s4.0 as usize),
        vec![true, true, false, false, true, false, false]
    );
}

#[test]
fn test_reachable_from_out_of_bounds_returns_all_false() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");

    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_assume(terms.mk_not(p), None);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.reachable_from(999), vec![false, false]);
}

#[test]
fn test_step_derives_empty_clause_matches_clause_variants() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let assume = proof.add_assume(p, None);
    let assume_not = proof.add_assume(not_p, None);
    let non_empty_resolution = proof.add_resolution(vec![p], p, assume, assume_not);
    let empty_resolution = proof.add_resolution(vec![], p, assume, assume_not);
    let empty_theory = proof.add_theory_lemma_with_kind("LRA", vec![], TheoryLemmaKind::Generic);
    let empty_step = proof.add_rule_step(AletheRule::Trust, vec![], vec![], vec![]);

    let trace = ProofTrace::new(&proof, &terms);
    assert!(!trace.step_derives_empty_clause(assume.0 as usize));
    assert!(!trace.step_derives_empty_clause(non_empty_resolution.0 as usize));
    assert!(trace.step_derives_empty_clause(empty_resolution.0 as usize));
    assert!(trace.step_derives_empty_clause(empty_theory.0 as usize));
    assert!(trace.step_derives_empty_clause(empty_step.0 as usize));
}
