// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cdcl::{Lit, Var};
use crate::egraph::Symbol;
use crate::smt::{
    SmtTerm, TermId, TheoryCheckResult, TheoryLemmaRequest, TheoryLiteral, TheorySolver,
};

fn make_lit(var_idx: u32, positive: bool) -> Lit {
    let var = Var::new(var_idx);
    if positive {
        Lit::pos(var)
    } else {
        Lit::neg(var)
    }
}

#[test]
fn test_non_array_disequality_does_not_queue_extensionality_request() {
    let mut theory = ArrayTheory::new();
    theory.set_terms(vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ]);

    let result = theory.assert_literal(
        make_lit(0, false),
        &TheoryLiteral::Neq(TermId(0), TermId(1)),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert!(
        theory.drain_lemma_requests().is_empty(),
        "plain disequalities between non-array terms must not request extensionality"
    );
}

#[test]
fn test_array_disequality_queues_one_canonical_extensionality_request() {
    let mut theory = ArrayTheory::new();
    theory.set_terms(vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3
        SmtTerm::Const(Symbol::new("b")), // 4
    ]);

    let diseq_reason = make_lit(1, false);
    let result = theory.assert_literal(diseq_reason, &TheoryLiteral::Neq(TermId(3), TermId(4)));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    assert_eq!(
        theory.pending_extensionality_set.len(),
        1,
        "the canonical array pair should be deduplicated immediately"
    );

    assert_eq!(
        theory.drain_lemma_requests(),
        vec![TheoryLemmaRequest::ArrayExtensionality {
            lhs: TermId(3),
            rhs: TermId(4),
            diseq_reason,
        }],
    );
    assert!(
        theory.drain_lemma_requests().is_empty(),
        "draining should empty the queue while leaving the dedup set in place"
    );
}

#[test]
fn test_array_peer_closure_is_order_independent_for_extensionality() {
    let mut theory = ArrayTheory::new();
    theory.set_terms(vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3
        SmtTerm::Const(Symbol::new("b")), // 4
        SmtTerm::Const(Symbol::new("c")), // 5
    ]);

    let diseq_reason = make_lit(2, false);
    let diseq_result =
        theory.assert_literal(diseq_reason, &TheoryLiteral::Neq(TermId(4), TermId(5)));
    assert!(matches!(diseq_result, TheoryCheckResult::Consistent));
    assert!(
        theory.drain_lemma_requests().is_empty(),
        "before any array-typed peer is discovered, b != c should stay non-array"
    );

    let eq_result =
        theory.assert_literal(make_lit(3, true), &TheoryLiteral::Eq(TermId(3), TermId(4)));
    assert!(matches!(eq_result, TheoryCheckResult::Consistent));

    assert_eq!(
        theory.drain_lemma_requests(),
        vec![TheoryLemmaRequest::ArrayExtensionality {
            lhs: TermId(4),
            rhs: TermId(5),
            diseq_reason,
        }],
        "discovering b as array-typed later must retroactively expose the pending b != c request"
    );
}

#[test]
fn test_backtrack_clears_pending_extensionality_requests_and_dedup() {
    let mut theory = ArrayTheory::new();
    theory.set_terms(vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3
        SmtTerm::Const(Symbol::new("b")), // 4
    ]);

    theory.push();
    let result = theory.assert_literal(
        make_lit(4, false),
        &TheoryLiteral::Neq(TermId(3), TermId(4)),
    );
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert_eq!(theory.pending_extensionality.len(), 1);
    assert_eq!(theory.pending_extensionality_set.len(), 1);

    theory.backtrack(0);

    assert!(
        theory.pending_extensionality.is_empty(),
        "backtrack must clear queued lemma requests"
    );
    assert!(
        theory.pending_extensionality_set.is_empty(),
        "backtrack must clear queued-request dedup state"
    );
    assert!(
        theory.drain_lemma_requests().is_empty(),
        "no stale extensionality request should survive backtrack"
    );
}
