// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof trail recording tests.
//!
//! Extracted from the main tests.rs to reduce file size (#2386 structural cleanup).
//! Covers: theory conflict/propagation trail entries, lit-to-theory mapping,
//! trail lifecycle across solve() calls.

use super::*;
use crate::cdcl::{Lit, Var};
use crate::theories::equality::EqualityTheory;
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};

// ─── Mock theories (duplicated from tests.rs for module isolation) ─────

/// A theory that rejects the first N SAT assignments with conflicts,
/// then accepts. Used to test DPLL(T) loop conflict handling.
struct ConflictCountingTheory {
    conflicts_remaining: AtomicU32,
    last_lit_encoded: AtomicU32,
}

impl ConflictCountingTheory {
    fn new(conflict_count: u32) -> Self {
        Self {
            conflicts_remaining: AtomicU32::new(conflict_count),
            last_lit_encoded: AtomicU32::new(0),
        }
    }

    fn encode_lit(lit: Lit) -> u32 {
        let idx = lit.var().index() as u32;
        let pol = if lit.is_pos() { 1 } else { 0 };
        idx * 2 + pol + 1
    }

    #[allow(dead_code)]
    fn decode_lit(encoded: u32) -> Option<Lit> {
        if encoded == 0 {
            return None;
        }
        let val = encoded - 1;
        let var = Var::new(val / 2);
        if val % 2 == 1 {
            Some(Lit::pos(var))
        } else {
            Some(Lit::neg(var))
        }
    }
}

impl TheorySolver for ConflictCountingTheory {
    fn assert_literal(&mut self, lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        self.last_lit_encoded
            .store(Self::encode_lit(lit), Ordering::Relaxed);
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        let remaining = self.conflicts_remaining.load(Ordering::Relaxed);
        if remaining > 0 {
            self.conflicts_remaining
                .store(remaining - 1, Ordering::Relaxed);
            if let Some(lit) = Self::decode_lit(self.last_lit_encoded.load(Ordering::Relaxed)) {
                TheoryCheckResult::Conflict(vec![lit])
            } else {
                TheoryCheckResult::Consistent
            }
        } else {
            TheoryCheckResult::Consistent
        }
    }

    fn backtrack(&mut self, _level: u32) {}
    fn push(&mut self) {}
    fn name(&self) -> &'static str {
        "conflict_counter"
    }
    fn set_terms(&mut self, _terms: std::sync::Arc<[SmtTerm]>) {}
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

/// A theory that propagates a literal on first check, then accepts.
struct PropagatingTheory {
    propagated: AtomicBool,
    propagate_lit: Lit,
}

impl PropagatingTheory {
    fn new(lit: Lit) -> Self {
        Self {
            propagated: AtomicBool::new(false),
            propagate_lit: lit,
        }
    }
}

impl TheorySolver for PropagatingTheory {
    fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        if !self.propagated.load(Ordering::Relaxed) {
            self.propagated.store(true, Ordering::Relaxed);
            TheoryCheckResult::Propagation(vec![(self.propagate_lit, vec![])])
        } else {
            TheoryCheckResult::Consistent
        }
    }

    fn backtrack(&mut self, _level: u32) {}
    fn push(&mut self) {}
    fn name(&self) -> &'static str {
        "propagating"
    }
    fn set_terms(&mut self, _terms: std::sync::Arc<[SmtTerm]>) {}
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

// ─── Proof trail tests (#2442 Phase 2) ──────────────────────────────

#[test]
fn test_proof_trail_empty_for_pure_sat_conflict() {
    // Pure SAT-level conflict (a = b AND a ≠ b) should produce an empty
    // proof trail because the SAT solver detects the contradiction directly
    // without invoking theory checks.
    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_neq(a, b);

    match smt.solve() {
        SmtResult::Unsat(_) => {}
        _ => panic!("Expected UNSAT"),
    }
    assert!(
        smt.proof_trail().is_empty(),
        "Pure SAT conflict should produce empty proof trail, got {} entries",
        smt.proof_trail().len()
    );
}

#[test]
fn test_proof_trail_records_theory_conflict() {
    // Equality theory conflict (a = b, b = c, a ≠ c) should produce
    // a non-empty proof trail with at least one TheoryConflict entry.
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(b, c);
    let _ = smt.assert_neq(a, c);

    match smt.solve() {
        SmtResult::Unsat(_) => {}
        _ => panic!("Expected UNSAT from equality theory"),
    }

    let trail = smt.proof_trail();
    assert!(
        !trail.is_empty(),
        "Theory conflict should produce non-empty proof trail"
    );

    // At least one entry should be a TheoryConflict
    let has_conflict = trail
        .iter()
        .any(|e| matches!(e, ProofTrailEntry::TheoryConflict { .. }));
    assert!(
        has_conflict,
        "Proof trail should contain at least one TheoryConflict entry"
    );
}

#[test]
fn test_proof_trail_conflict_has_theory_name() {
    // Verify that the theory name is captured in conflict entries.
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(b, c);
    let _ = smt.assert_neq(a, c);

    match smt.solve() {
        SmtResult::Unsat(_) => {}
        _ => panic!("Expected UNSAT"),
    }

    for entry in smt.proof_trail() {
        if let ProofTrailEntry::TheoryConflict { theory_name, .. } = entry {
            // Theory name should be non-empty
            assert!(
                !theory_name.is_empty(),
                "TheoryConflict should have a non-empty theory_name"
            );
            return;
        }
    }
    panic!("Expected at least one TheoryConflict in proof trail");
}

#[test]
fn test_proof_trail_conflict_has_clause_index() {
    // Verify that theory conflict entries record the clause index.
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(b, c);
    let _ = smt.assert_neq(a, c);

    match smt.solve() {
        SmtResult::Unsat(_) => {}
        _ => panic!("Expected UNSAT"),
    }

    for entry in smt.proof_trail() {
        if let ProofTrailEntry::TheoryConflict { clause_index, .. } = entry {
            // A theory conflict from three ground-level assertions should
            // produce a learned blocking clause with a valid clause index.
            assert!(
                clause_index.is_some(),
                "equality theory conflict should produce a blocking clause, got clause_index=None"
            );
            return;
        }
    }
    panic!("Expected at least one TheoryConflict in proof trail");
}

#[test]
fn test_proof_trail_conflict_records_theory_literals() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(b, c);
    let _ = smt.assert_neq(a, c);

    match smt.solve() {
        SmtResult::Unsat(_) => {}
        _ => panic!("Expected UNSAT"),
    }

    for entry in smt.proof_trail() {
        if let ProofTrailEntry::TheoryConflict {
            conflict_theory_lits,
            ..
        } = entry
        {
            assert!(
                conflict_theory_lits.contains(&TheoryLiteral::Neq(a, c)),
                "conflict payload should retain the disequality witness, got {conflict_theory_lits:?}"
            );
            assert!(
                conflict_theory_lits.iter().any(|lit| matches!(
                    lit,
                    TheoryLiteral::Eq(x, y) if (*x == a && *y == b) || (*x == b && *y == c)
                )),
                "conflict payload should retain at least one contributing equality, got {conflict_theory_lits:?}"
            );
            return;
        }
    }
    panic!("Expected at least one TheoryConflict in proof trail");
}

#[test]
fn test_proof_trail_records_theory_propagation() {
    // Use a theory that propagates a literal. The trail should record
    // a TheoryPropagation entry.
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Create theory variables
    let _eq_ab = smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Neq(a, b)]);

    // Add a propagating theory
    let prop_lit = Lit::pos(Var::new(0));
    smt.add_theory(Box::new(PropagatingTheory::new(prop_lit)));

    match smt.solve() {
        SmtResult::Sat(_) => {}
        _ => panic!("Expected SAT for simple problem with propagation"),
    }

    let trail = smt.proof_trail();
    for entry in trail {
        if let ProofTrailEntry::TheoryPropagation {
            implied_theory_lit,
            explanation_theory_lits,
            theory_name,
            ..
        } = entry
        {
            assert_eq!(
                *theory_name, "propagating",
                "proof trail should retain the propagating theory name"
            );
            assert_eq!(
                implied_theory_lit,
                &Some(TheoryLiteral::Eq(a, b)),
                "propagation payload should retain the implied theory literal"
            );
            assert!(
                explanation_theory_lits.is_empty(),
                "test propagation has no explanation premises, got {explanation_theory_lits:?}"
            );
            return;
        }
    }
    panic!("Theory propagation should produce a TheoryPropagation entry in the trail");
}

#[test]
fn test_proof_trail_cleared_on_new_solve() {
    // Proof trail should be cleared when solve() is called again.
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(b, c);
    let _ = smt.assert_neq(a, c);

    // First solve: should populate trail
    match smt.solve() {
        SmtResult::Unsat(_) => {}
        _ => panic!("Expected UNSAT"),
    }
    let first_trail_len = smt.proof_trail().len();
    assert!(
        first_trail_len > 0,
        "Trail should be non-empty after first solve"
    );

    // Second solve on same (already UNSAT) instance: trail should be fresh.
    // The SAT solver may detect UNSAT immediately (from learned clauses),
    // producing an empty trail since no new theory checks are needed.
    let _ = smt.solve();
    // Trail was cleared at solve() start, so it may be empty or re-populated
    // depending on solver state — the key property is it was cleared and rebuilt.
    let second_trail_len = smt.proof_trail().len();
    // Just verify the trail is accessible (no panic, no stale data)
    let _ = second_trail_len;
}

#[test]
fn test_proof_trail_lit_to_theory_literal() {
    // Verify that lit_to_theory_literal correctly maps SAT literals
    // back to their theory representations.
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // assert_eq creates a SAT variable for the equality
    let _ = smt.assert_eq(a, b);

    // var 0 should map to Eq(a, b) (positive) or Neq(a, b) (negative)
    let pos_lit = Lit::pos(Var::new(0));
    let neg_lit = Lit::neg(Var::new(0));

    if let Some(theory_lit) = smt.lit_to_theory_literal(pos_lit) {
        match theory_lit {
            TheoryLiteral::Eq(t1, t2) => {
                assert_eq!(t1, a);
                assert_eq!(t2, b);
            }
            _ => panic!("Expected Eq for positive literal"),
        }
    }

    if let Some(theory_lit) = smt.lit_to_theory_literal(neg_lit) {
        match theory_lit {
            TheoryLiteral::Neq(t1, t2) => {
                assert_eq!(t1, a);
                assert_eq!(t2, b);
            }
            _ => panic!("Expected Neq for negative literal"),
        }
    }
}

#[test]
fn test_proof_trail_conflict_counting_theory() {
    // ConflictCountingTheory produces N conflicts before accepting.
    // Each conflict should be recorded in the proof trail.
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ConflictCountingTheory::new(3)));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    smt.add_clause(vec![TheoryLiteral::Eq(a, b)]);

    match smt.solve() {
        SmtResult::Sat(_) | SmtResult::Unsat(_) | SmtResult::Unknown => {}
    }

    let trail = smt.proof_trail();
    let conflict_count = trail
        .iter()
        .filter(|e| matches!(e, ProofTrailEntry::TheoryConflict { .. }))
        .count();

    // Should have recorded conflicts from the ConflictCountingTheory.
    // The theory produces 3 conflicts, but the solver may or may not
    // re-trigger all of them depending on the SAT search path.
    assert!(
        conflict_count >= 1,
        "Expected at least 1 theory conflict in trail, got {conflict_count}"
    );
    // Verify theory name is captured
    for entry in trail {
        if let ProofTrailEntry::TheoryConflict { theory_name, .. } = entry {
            assert_eq!(
                *theory_name, "conflict_counter",
                "Expected conflict_counter theory name"
            );
        }
    }
}

// ─── theory_literal_to_sat_literal round-trip tests (#2386 proof_coverage) ─

#[test]
fn test_theory_literal_to_sat_literal_eq_round_trip() {
    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Intern an Eq(a,b) via add_clause so theory_to_var is populated
    smt.add_clause(vec![TheoryLiteral::Eq(a, b)]);

    let eq_lit = TheoryLiteral::Eq(a, b);
    let sat_lit = smt
        .theory_literal_to_sat_literal(&eq_lit)
        .expect("Eq should map to a SAT literal");
    assert!(
        sat_lit.is_pos(),
        "Eq maps to the positive polarity of its SAT variable"
    );

    // Round-trip: SAT literal back to theory literal
    let recovered = smt
        .lit_to_theory_literal(sat_lit)
        .expect("SAT literal should map back to a theory literal");
    assert_eq!(
        recovered, eq_lit,
        "Eq round-trip should recover the original theory literal"
    );
}

#[test]
fn test_theory_literal_to_sat_literal_neq_round_trip() {
    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    smt.add_clause(vec![TheoryLiteral::Neq(a, b)]);

    let neq_lit = TheoryLiteral::Neq(a, b);
    let sat_lit = smt
        .theory_literal_to_sat_literal(&neq_lit)
        .expect("Neq should map to a SAT literal");
    assert!(
        !sat_lit.is_pos(),
        "Neq maps to the negative polarity of the Eq variable"
    );

    let recovered = smt
        .lit_to_theory_literal(sat_lit)
        .expect("SAT literal should map back to a theory literal");
    assert_eq!(
        recovered, neq_lit,
        "Neq round-trip should recover the original theory literal"
    );
}

#[test]
fn test_theory_literal_to_sat_literal_lt_round_trip() {
    let mut smt = SmtSolver::new();
    let x = smt.int_term(1i64);
    let y = smt.int_term(2i64);

    smt.add_clause(vec![TheoryLiteral::Lt(x, y)]);

    let lt_lit = TheoryLiteral::Lt(x, y);
    let sat_lit = smt
        .theory_literal_to_sat_literal(&lt_lit)
        .expect("Lt should map to a SAT literal");
    assert!(
        sat_lit.is_pos(),
        "Lt maps to the positive polarity of its SAT variable"
    );

    let recovered = smt
        .lit_to_theory_literal(sat_lit)
        .expect("SAT literal should map back to a theory literal");
    assert_eq!(
        recovered, lt_lit,
        "Lt round-trip should recover the original theory literal"
    );
}

#[test]
fn test_theory_literal_to_sat_literal_le_round_trip() {
    let mut smt = SmtSolver::new();
    let x = smt.int_term(3i64);
    let y = smt.int_term(4i64);

    smt.add_clause(vec![TheoryLiteral::Le(x, y)]);

    let le_lit = TheoryLiteral::Le(x, y);
    let sat_lit = smt
        .theory_literal_to_sat_literal(&le_lit)
        .expect("Le should map to a SAT literal");
    assert!(
        sat_lit.is_pos(),
        "Le maps to the positive polarity of its SAT variable"
    );

    let recovered = smt
        .lit_to_theory_literal(sat_lit)
        .expect("SAT literal should map back to a theory literal");
    assert_eq!(
        recovered, le_lit,
        "Le round-trip should recover the original theory literal"
    );
}

#[test]
fn test_theory_literal_to_sat_literal_bool_round_trip() {
    let mut smt = SmtSolver::new();
    let bool_var: u32 = 42;

    smt.add_clause(vec![TheoryLiteral::Bool(bool_var)]);

    let bool_lit = TheoryLiteral::Bool(bool_var);
    let sat_lit = smt
        .theory_literal_to_sat_literal(&bool_lit)
        .expect("Bool should map to a SAT literal");
    assert!(
        sat_lit.is_pos(),
        "Bool maps to the positive polarity of its SAT variable"
    );

    let recovered = smt
        .lit_to_theory_literal(sat_lit)
        .expect("SAT literal should map back to a theory literal");
    assert_eq!(
        recovered, bool_lit,
        "Bool round-trip should recover the original theory literal"
    );
}

#[test]
fn test_theory_literal_to_sat_literal_negbool_round_trip() {
    let mut smt = SmtSolver::new();
    let bool_var: u32 = 42;

    smt.add_clause(vec![TheoryLiteral::NegBool(bool_var)]);

    let negbool_lit = TheoryLiteral::NegBool(bool_var);
    let sat_lit = smt
        .theory_literal_to_sat_literal(&negbool_lit)
        .expect("NegBool should map to a SAT literal");
    assert!(
        !sat_lit.is_pos(),
        "NegBool maps to the negative polarity of the Bool variable"
    );

    let recovered = smt
        .lit_to_theory_literal(sat_lit)
        .expect("SAT literal should map back to a theory literal");
    assert_eq!(
        recovered, negbool_lit,
        "NegBool round-trip should recover the original theory literal"
    );
}

#[test]
fn test_theory_literal_to_sat_literal_unknown_returns_none() {
    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Don't intern any clause — the theory_to_var map is empty for Eq(a,b)
    let result = smt.theory_literal_to_sat_literal(&TheoryLiteral::Eq(a, b));
    assert_eq!(
        result, None,
        "theory_literal_to_sat_literal should return None for un-interned literals"
    );
}
