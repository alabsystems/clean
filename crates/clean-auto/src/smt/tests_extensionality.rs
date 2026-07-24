// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cdcl::Lit;
use crate::egraph::Symbol;
use crate::theories::arrays::ArrayTheory;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};

struct SyncTrackingTheory {
    set_terms_calls: Arc<AtomicU32>,
    internalize_calls: Arc<AtomicU32>,
}

impl TheorySolver for SyncTrackingTheory {
    fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, _level: u32) {}

    fn push(&mut self) {}

    fn name(&self) -> &'static str {
        "SyncTrackingTheory"
    }

    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {
        self.set_terms_calls.fetch_add(1, Ordering::Relaxed);
    }

    fn internalize_atom(&mut self, _theory_lit: &TheoryLiteral) {
        self.internalize_calls.fetch_add(1, Ordering::Relaxed);
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

struct SnapshotTrackingTheory {
    snapshots: Arc<Mutex<Vec<Arc<[SmtTerm]>>>>,
}

impl TheorySolver for SnapshotTrackingTheory {
    fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, _level: u32) {}

    fn push(&mut self) {}

    fn name(&self) -> &'static str {
        "SnapshotTrackingTheory"
    }

    fn set_terms(&mut self, terms: Arc<[SmtTerm]>) {
        self.snapshots
            .lock()
            .expect("snapshot tracking mutex should not be poisoned")
            .push(terms);
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

fn witness_terms(smt: &SmtSolver) -> Vec<TermId> {
    smt.terms()
        .iter()
        .enumerate()
        .filter_map(|(idx, term)| match term {
            SmtTerm::Const(name) if name.name().starts_with("array_ext_witness_") => {
                Some(TermId(idx as u32))
            }
            _ => None,
        })
        .collect()
}

#[test]
fn test_array_extensionality_emission_adds_witness_terms_and_learned_clause() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ArrayTheory::new()));

    let base = smt.const_term("base");
    let idx = smt.const_term("idx");
    let value = smt.const_term("value");
    let other = smt.const_term("other");
    let stored = smt.store_term(base, idx, value);
    let _ = smt.assert_neq(stored, other);

    let terms_before = smt.terms().len();
    let stats_before = smt.stats();
    assert_eq!(stats_before.sat_learned_clauses, 0);

    match smt.solve() {
        SmtResult::Sat(_) => {}
        other => panic!("expected SAT after lazy extensionality lemma insertion, got {other:?}"),
    }

    let stats_after = smt.stats();
    assert_eq!(
        smt.terms().len(),
        terms_before + 3,
        "one request should create exactly one witness constant and two select terms"
    );
    assert_eq!(
        stats_after.num_clauses,
        stats_before.num_clauses + 1,
        "the extensionality request should add exactly one learned clause"
    );
    assert_eq!(
        stats_after.sat_learned_clauses,
        stats_before.sat_learned_clauses + 1,
        "the extensionality lemma must go through the learned/theory clause path"
    );

    let witness_terms = witness_terms(&smt);
    assert_eq!(
        witness_terms.len(),
        1,
        "expected exactly one extensionality witness constant"
    );
    let witness = witness_terms[0];
    let witness_selects = smt
        .terms()
        .iter()
        .filter(|term| {
            matches!(
                term,
                SmtTerm::App(name, args)
                    if name == &Symbol::new("select") && args.len() == 2 && args[1] == witness
            )
        })
        .count();
    assert_eq!(
        witness_selects, 2,
        "the emitted lemma must materialize select(lhs, witness) and select(rhs, witness)"
    );
}

#[test]
fn test_array_extensionality_restart_resyncs_theories() {
    let mut smt = SmtSolver::new();
    let array_idx = smt.add_theory(Box::new(ArrayTheory::new()));

    let set_terms_calls = Arc::new(AtomicU32::new(0));
    let internalize_calls = Arc::new(AtomicU32::new(0));
    smt.add_theory(Box::new(SyncTrackingTheory {
        set_terms_calls: Arc::clone(&set_terms_calls),
        internalize_calls: Arc::clone(&internalize_calls),
    }));

    let base = smt.const_term("base");
    let idx = smt.const_term("idx");
    let value = smt.const_term("value");
    let other = smt.const_term("other");
    let stored = smt.store_term(base, idx, value);
    let _ = smt.assert_neq(stored, other);

    match smt.solve() {
        SmtResult::Sat(_) => {}
        other => panic!("expected SAT after extensionality restart/resync, got {other:?}"),
    }

    assert!(
        set_terms_calls.load(Ordering::Relaxed) >= 2,
        "restart path should resync theories by calling set_terms again after lemma emission"
    );
    assert!(
        internalize_calls.load(Ordering::Relaxed) >= 3,
        "resync should re-internalize the original disequality atom plus the fresh witness-select atom"
    );

    let arrays = smt
        .get_theory_typed::<ArrayTheory>(array_idx)
        .expect("ArrayTheory should remain accessible after solve");
    assert_eq!(
        arrays.stats().num_selects,
        2,
        "after restart/resync, ArrayTheory should see the two fresh witness select terms"
    );
}

#[test]
fn test_array_extensionality_repeated_solve_does_not_duplicate_witness_or_clause() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ArrayTheory::new()));

    let base = smt.const_term("base");
    let idx = smt.const_term("idx");
    let value = smt.const_term("value");
    let other = smt.const_term("other");
    let stored = smt.store_term(base, idx, value);
    let _ = smt.assert_neq(stored, other);

    assert!(matches!(smt.solve(), SmtResult::Sat(_)));
    let terms_after_first = smt.terms().len();
    let stats_after_first = smt.stats();
    let witnesses_after_first = witness_terms(&smt).len();

    assert!(matches!(smt.solve(), SmtResult::Sat(_)));
    let stats_after_second = smt.stats();

    assert_eq!(
        smt.terms().len(),
        terms_after_first,
        "solver-side emitted-pair dedup must block duplicate witness terms on repeated solve()"
    );
    assert_eq!(
        witness_terms(&smt).len(),
        witnesses_after_first,
        "the same canonical pair must not create a second witness constant"
    );
    assert_eq!(
        stats_after_second.num_clauses, stats_after_first.num_clauses,
        "re-solving the same instance must not duplicate the learned extensionality clause"
    );
    assert_eq!(
        stats_after_second.sat_learned_clauses, stats_after_first.sat_learned_clauses,
        "re-solving the same instance must not inflate learned-clause accounting"
    );
}

#[test]
fn test_repeated_solve_skips_theory_resync_until_terms_change() {
    let mut smt = SmtSolver::new();
    let snapshots = Arc::new(Mutex::new(Vec::new()));
    smt.add_theory(Box::new(SnapshotTrackingTheory {
        snapshots: Arc::clone(&snapshots),
    }));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let _ = smt.assert_eq(a, b);

    assert!(matches!(smt.solve(), SmtResult::Sat(_)));
    assert!(matches!(smt.solve(), SmtResult::Sat(_)));

    let c = smt.const_term("c");
    let _ = smt.assert_eq(a, c);
    assert!(matches!(smt.solve(), SmtResult::Sat(_)));

    let snapshots = snapshots
        .lock()
        .expect("snapshot tracking mutex should not be poisoned");
    assert_eq!(
        snapshots.len(),
        2,
        "repeated solve() without new terms or atoms should reuse the existing theory baseline"
    );
    assert!(
        !Arc::ptr_eq(&snapshots[0], &snapshots[1]),
        "interning a new term must invalidate the cached shared term snapshot"
    );
    assert_eq!(
        snapshots[0].len(),
        2,
        "the initial snapshot should contain the two original constants"
    );
    assert_eq!(
        snapshots[1].len(),
        3,
        "after interning a new constant, the rebuilt snapshot should expose the larger term set"
    );
}

#[test]
fn test_repeated_solve_incrementally_internalizes_new_atoms() {
    let mut smt = SmtSolver::new();
    let set_terms_calls = Arc::new(AtomicU32::new(0));
    let internalize_calls = Arc::new(AtomicU32::new(0));
    smt.add_theory(Box::new(SyncTrackingTheory {
        set_terms_calls: Arc::clone(&set_terms_calls),
        internalize_calls: Arc::clone(&internalize_calls),
    }));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let _ = smt.assert_eq(a, b);

    assert!(matches!(smt.solve(), SmtResult::Sat(_)));
    assert_eq!(
        set_terms_calls.load(Ordering::Relaxed),
        1,
        "initial solve should sync terms once"
    );
    assert_eq!(
        internalize_calls.load(Ordering::Relaxed),
        1,
        "initial solve should internalize the first registered atom"
    );

    let _ = smt.assert_eq(b, c);
    assert!(matches!(smt.solve(), SmtResult::Sat(_)));

    assert_eq!(
        set_terms_calls.load(Ordering::Relaxed),
        1,
        "adding an atom without term growth should not rerun set_terms"
    );
    assert_eq!(
        internalize_calls.load(Ordering::Relaxed),
        2,
        "second solve should internalize only the newly registered atom"
    );
}

#[test]
fn test_mutable_theory_access_forces_full_resync() {
    let mut smt = SmtSolver::new();
    let set_terms_calls = Arc::new(AtomicU32::new(0));
    let internalize_calls = Arc::new(AtomicU32::new(0));
    smt.add_theory(Box::new(SyncTrackingTheory {
        set_terms_calls: Arc::clone(&set_terms_calls),
        internalize_calls: Arc::clone(&internalize_calls),
    }));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let _ = smt.assert_eq(a, b);

    assert!(matches!(smt.solve(), SmtResult::Sat(_)));
    assert_eq!(set_terms_calls.load(Ordering::Relaxed), 1);
    assert_eq!(internalize_calls.load(Ordering::Relaxed), 1);

    let theory = smt
        .get_theory_mut(0)
        .expect("tracking theory should stay registered");
    assert_eq!(theory.name(), "SyncTrackingTheory");

    assert!(matches!(smt.solve(), SmtResult::Sat(_)));
    assert_eq!(
        set_terms_calls.load(Ordering::Relaxed),
        2,
        "mutable theory access should invalidate the cached structural baseline"
    );
    assert_eq!(
        internalize_calls.load(Ordering::Relaxed),
        2,
        "dirty mutable access should replay atom internalization on the next solve"
    );
}
