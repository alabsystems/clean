// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct unit tests for the raw ay proof-trace adapter.
//!
//! Part of #2891: provide direct coverage for `trace.rs`, the only
//! proof-reconstruction module that matches raw ay_core proof payload types.

use ay::Sort;
use ay_core::{AletheRule, FarkasAnnotation, Proof, Symbol, TermId, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};

use super::tests_support::bool_var;
use super::trace::{ConstantView, ProofTrace, RuleView, StepView, TermView, TheoryLemmaView};

fn int_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

#[test]
fn test_trace_step_view_assume() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");

    let mut proof = Proof::new();
    proof.add_assume(p, None);

    let trace = ProofTrace::new(&proof, &terms);
    match trace.step(0) {
        StepView::Assume(term_id) => assert_eq!(term_id, p),
        other => panic!("expected Assume step, got {:?}", other),
    }
}

#[test]
fn test_trace_step_view_resolution() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let not_p = terms.mk_not_raw(p);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, h1, h2);

    let trace = ProofTrace::new(&proof, &terms);
    match trace.step(2) {
        StepView::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => {
            assert!(
                clause.is_empty(),
                "expected empty resolvent, got {:?}",
                clause
            );
            assert_eq!(pivot, p);
            assert_eq!(clause1, h1);
            assert_eq!(clause2, h2);
        }
        other => panic!("expected Resolution step, got {:?}", other),
    }
}

#[test]
fn test_trace_step_view_theory_lemma_euf() {
    let mut terms = TermStore::new();
    let a = int_var(&mut terms, "a");
    let b = int_var(&mut terms, "b");
    let c = int_var(&mut terms, "c");
    let eq_ab = terms.mk_eq(a, b);
    let not_eq_ab = terms.mk_not_raw(eq_ab);
    let eq_ac = terms.mk_eq(a, c);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let trace = ProofTrace::new(&proof, &terms);
    match trace.step(0) {
        StepView::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            lia,
        } => {
            assert_eq!(theory, "EUF");
            assert_eq!(clause, &[not_eq_ab, eq_ac]);
            assert!(farkas.is_none(), "EUF lemma should not carry Farkas");
            assert_eq!(kind, TheoryLemmaView::EufTransitive);
            assert!(lia.is_none(), "EUF lemma should not carry LIA annotation");
        }
        other => panic!("expected TheoryLemma step, got {:?}", other),
    }
}

#[test]
fn test_trace_step_view_theory_lemma_lra_farkas() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let le_x0 = terms.mk_app(Symbol::named("<="), vec![x, zero], Sort::Bool);
    let le_x1 = terms.mk_app(Symbol::named("<="), vec![x, one], Sort::Bool);
    let not_le_x0 = terms.mk_not_raw(le_x0);
    let not_le_x1 = terms.mk_not_raw(le_x1);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_le_x0, not_le_x1],
        FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(2)]),
    );

    let trace = ProofTrace::new(&proof, &terms);
    match trace.step(0) {
        StepView::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            lia,
        } => {
            assert_eq!(theory, "LRA");
            assert_eq!(clause, &[not_le_x0, not_le_x1]);
            assert_eq!(kind, TheoryLemmaView::LraFarkas);
            assert_eq!(
                farkas,
                Some(super::trace::FarkasView {
                    coefficient_count: 2,
                    is_valid: true,
                    all_unit_coefficients: false,
                })
            );
            assert!(lia.is_none(), "LRA lemma should not carry LIA annotation");
        }
        other => panic!("expected TheoryLemma step, got {:?}", other),
    }
}

#[test]
fn test_trace_step_view_alethe_rule_mapping() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");

    let mut proof = Proof::new();
    let premise = proof.add_assume(p, None);
    let cases = vec![
        (
            AletheRule::ThResolution,
            RuleView::ThResolution,
            "th_resolution",
        ),
        (AletheRule::Or, RuleView::Or, "or"),
        (AletheRule::OrPos(1), RuleView::OrPos, "or_pos"),
        (AletheRule::OrNeg, RuleView::OrNeg, "or_neg"),
        (AletheRule::EquivPos1, RuleView::EquivPos1, "equiv_pos1"),
        (AletheRule::EquivPos2, RuleView::EquivPos2, "equiv_pos2"),
        (AletheRule::EquivNeg1, RuleView::EquivNeg1, "equiv_neg1"),
        (AletheRule::EquivNeg2, RuleView::EquivNeg2, "equiv_neg2"),
        (AletheRule::AndPos(3), RuleView::AndPos(3), "and_pos"),
        (AletheRule::AndNeg, RuleView::AndNeg, "and_neg"),
        (AletheRule::Trust, RuleView::Trust, "trust"),
        (AletheRule::Hole, RuleView::Hole, "hole"),
    ];

    for (rule, expected, rule_name) in cases {
        let step_id = proof.add_rule_step(rule, vec![p], vec![premise], vec![p]);
        match trace_step(&proof, &terms, step_id.0 as usize) {
            StepView::Step {
                rule,
                rule_name: actual_name,
                clause,
                premises,
                args,
            } => {
                assert_eq!(rule, expected);
                assert_eq!(actual_name, rule_name);
                assert_eq!(clause, &[p]);
                assert_eq!(premises, &[premise]);
                assert_eq!(args, &[p]);
            }
            other => panic!("expected Step variant, got {:?}", other),
        }
    }
}

#[test]
fn test_trace_term_view_named_app() {
    let mut terms = TermStore::new();
    let a = bool_var(&mut terms, "a");
    let b = bool_var(&mut terms, "b");
    let app = terms.mk_app(Symbol::named("f"), vec![a, b], Sort::Bool);

    let trace = ProofTrace::without_proof(&terms);
    match trace.term(app) {
        TermView::NamedApp { name, args } => {
            assert_eq!(name, "f");
            assert_eq!(args, &[a, b]);
        }
        other => panic!("expected NamedApp, got {:?}", other),
    }
}

#[test]
fn test_trace_flatten_or_nested() {
    let mut terms = TermStore::new();
    let a = bool_var(&mut terms, "a");
    let b = bool_var(&mut terms, "b");
    let c = bool_var(&mut terms, "c");
    let nested = terms.mk_app(Symbol::named("or"), vec![b, c], Sort::Bool);
    let root = terms.mk_app(Symbol::named("or"), vec![a, nested], Sort::Bool);

    let trace = ProofTrace::without_proof(&terms);
    assert_eq!(trace.flatten_or(root), vec![a, b, c]);
    assert_eq!(trace.flatten_or(a), vec![a]);
}

#[test]
fn test_trace_is_negation_pair() {
    let mut terms = TermStore::new();
    let p = bool_var(&mut terms, "p");
    let q = bool_var(&mut terms, "q");
    let not_p = terms.mk_not_raw(p);

    let trace = ProofTrace::without_proof(&terms);
    assert!(trace.is_negation_pair(p, not_p));
    assert!(trace.is_negation_pair(not_p, p));
    assert!(!trace.is_negation_pair(p, q));
}

#[test]
fn test_trace_as_equality() {
    let mut terms = TermStore::new();
    let a = int_var(&mut terms, "a");
    let b = int_var(&mut terms, "b");
    let eq_ab = terms.mk_eq(a, b);
    let p = bool_var(&mut terms, "p");

    let trace = ProofTrace::without_proof(&terms);
    assert_eq!(trace.as_equality(eq_ab), Some((a, b)));
    assert_eq!(trace.as_equality(p), None);
}

#[test]
fn test_trace_as_constant_variants() {
    let mut terms = TermStore::new();
    let bool_term = terms.mk_bool(true);
    let int_term = terms.mk_int(BigInt::from(7));
    let rational_value = BigRational::new(BigInt::from(3), BigInt::from(2));
    let rational_term = terms.mk_rational(rational_value.clone());
    let string_term = terms.mk_string("clean".to_string());

    let trace = ProofTrace::without_proof(&terms);
    match trace.as_constant(bool_term) {
        Some(ConstantView::Bool(value)) => assert!(value),
        other => panic!("expected Bool constant, got {:?}", other),
    }
    match trace.as_constant(int_term) {
        Some(ConstantView::Int(value)) => assert_eq!(value, &BigInt::from(7)),
        other => panic!("expected Int constant, got {:?}", other),
    }
    match trace.as_constant(rational_term) {
        Some(ConstantView::Rational(value)) => assert_eq!(value.0, rational_value),
        other => panic!("expected Rational constant, got {:?}", other),
    }
    match trace.as_constant(string_term) {
        Some(ConstantView::String(value)) => assert_eq!(value, "clean"),
        other => panic!("expected String constant, got {:?}", other),
    }
}

#[test]
fn test_trace_step_out_of_bounds_returns_unknown() {
    let terms = TermStore::new();
    let trace = ProofTrace::without_proof(&terms);
    assert!(matches!(trace.step(999), StepView::Unknown));
}

#[test]
fn test_trace_without_proof_has_zero_steps() {
    let terms = TermStore::new();
    let trace = ProofTrace::without_proof(&terms);
    assert_eq!(trace.step_count(), 0);
}

#[test]
fn test_trace_clause_of_assume_flattens_or() {
    let mut terms = TermStore::new();
    let a = bool_var(&mut terms, "a");
    let b = bool_var(&mut terms, "b");
    let c = bool_var(&mut terms, "c");
    let nested = terms.mk_app(Symbol::named("or"), vec![b, c], Sort::Bool);
    let root = terms.mk_app(Symbol::named("or"), vec![a, nested], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(root, None);
    proof.add_assume(a, None);

    let trace = ProofTrace::new(&proof, &terms);
    assert_eq!(trace.clause_of_step(0), vec![a, b, c]);
    assert_eq!(trace.clause_of_step(1), vec![a]);
}

fn trace_step<'a>(proof: &'a Proof, terms: &'a TermStore, idx: usize) -> StepView<'a> {
    ProofTrace::new(proof, terms).step(idx)
}
