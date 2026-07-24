// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct unit tests for contradiction-root selection and premise reachability.
//!
//! Part of #2891: cover `trace_rooting.rs`, where a wrong root or missed
//! premise silently drops proof steps from reconstruction.

use ay::Sort;
use ay_core::{Proof, Symbol, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

use super::tests_support::bool_var;
use crate::bridge::ay_backend::proof_reconstruct::trace::ProofTrace;

fn empty_resolution_chain() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let not_p = terms.mk_not_raw(p);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, h1, h2);

    (terms, proof)
}

#[test]
fn test_root_empty_clause_simple() {
    let (terms, proof) = empty_resolution_chain();
    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.root_empty_clause_step(), Some(2));
}

#[test]
fn test_root_empty_clause_picks_last() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);

    let mut proof = Proof::new();
    let p_pos = proof.add_assume(p, None);
    let p_neg = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, p_pos, p_neg);

    let q_pos = proof.add_assume(q, None);
    let q_neg = proof.add_assume(not_q, None);
    proof.add_resolution(vec![], q, q_pos, q_neg);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.root_empty_clause_step(), Some(5));
}

#[test]
fn test_root_empty_clause_none_when_no_empty() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let not_p = terms.mk_not_raw(p);

    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_assume(not_p, None);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.root_empty_clause_step(), None);
}

#[test]
fn test_reachable_from_linear_chain() {
    let (terms, proof) = empty_resolution_chain();
    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.reachable_from(2), vec![true, true, true]);
}

#[test]
fn test_reachable_from_diamond() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);

    let mut proof = Proof::new();
    let p_pos = proof.add_assume(p, None);
    let p_neg = proof.add_assume(not_p, None);
    let q_pos = proof.add_assume(q, None);
    let q_neg = proof.add_assume(not_q, None);

    let left = proof.add_resolution(vec![], p, p_pos, p_neg);
    let right = proof.add_resolution(vec![], q, q_pos, q_neg);
    proof.add_resolution(vec![], p, left, right);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(
        trace.reachable_from(6),
        vec![true, true, true, true, true, true, true]
    );
    assert_eq!(
        trace.reachable_from(4),
        vec![true, true, false, false, true, false, false]
    );
}

#[test]
fn test_reachable_from_unreachable_branch() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");
    let not_p = terms.mk_not_raw(p);

    let mut proof = Proof::new();
    let p_pos = proof.add_assume(p, None);
    let p_neg = proof.add_assume(not_p, None);
    proof.add_assume(q, None);
    proof.add_resolution(vec![], p, p_pos, p_neg);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.reachable_from(3), vec![true, true, false, true]);
}

#[test]
fn test_step_derives_empty_clause() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");
    let not_p = terms.mk_not_raw(p);
    let zero = terms.mk_int(BigInt::from(0));
    let le_q0 = terms.mk_app(Symbol::named("<="), vec![q, zero], Sort::Bool);

    let mut proof = Proof::new();
    let p_pos = proof.add_assume(p, None);
    let p_neg = proof.add_assume(not_p, None);
    let empty_resolution = proof.add_resolution(vec![], p, p_pos, p_neg);
    let nonempty_resolution = proof.add_resolution(vec![p], p, p_pos, p_neg);
    let empty_theory =
        proof.add_theory_lemma_with_kind("GENERIC", vec![], TheoryLemmaKind::Generic);
    let assume = proof.add_assume(le_q0, None);

    let trace = ProofTrace::new(&proof, &terms);
    assert!(trace.step_derives_empty_clause(empty_resolution.0 as usize));
    assert!(!trace.step_derives_empty_clause(nonempty_resolution.0 as usize));
    assert!(trace.step_derives_empty_clause(empty_theory.0 as usize));
    assert!(!trace.step_derives_empty_clause(assume.0 as usize));
}

#[test]
fn test_reachable_from_out_of_bounds() {
    let (terms, proof) = empty_resolution_chain();
    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.reachable_from(999), vec![false, false, false]);
}
