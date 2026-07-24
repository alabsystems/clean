// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Level-0 reset soundness tests for ArrayTheory (#2386, #2625).
//!
//! After #2386 the DPLL(T) loop no longer calls `push()` before assertions, so
//! theories operate permanently at level 0. The default `TheorySolver::reset()`
//! delegates to `backtrack(0)`, which is a no-op when `self.level == 0`.
//! ArrayTheory's explicit `reset()` override must clear all assertion-derived
//! state despite the level being zero.

use super::*;
use crate::cdcl::{Lit, Var};
use crate::egraph::Symbol;
use crate::smt::{SmtTerm, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver};

fn make_array_terms() -> Vec<SmtTerm> {
    // a: array, i: index, v: value, store(a,i,v): result, select(a,i): result
    vec![
        SmtTerm::Const(Symbol::new("a")), // 0
        SmtTerm::Const(Symbol::new("i")), // 1
        SmtTerm::Const(Symbol::new("v")), // 2
        SmtTerm::App(Symbol::new("store"), vec![TermId(0), TermId(1), TermId(2)]), // 3: store(a, i, v)
        SmtTerm::App(Symbol::new("select"), vec![TermId(0), TermId(1)]), // 4: select(a, i)
        SmtTerm::Const(Symbol::new("b")),                                // 5: another array
    ]
}

/// Asserts a level-0 equality and disequality into the theory.
fn assert_at_level0(theory: &mut ArrayTheory) {
    let lit_eq = Lit::pos(Var::new(10));
    let lit_neq = Lit::pos(Var::new(11));

    // Assert a = b (equality)
    let result = theory.assert_literal(lit_eq, &TheoryLiteral::Eq(TermId(0), TermId(5)));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "level-0 equality assertion should be consistent"
    );

    // Assert store(a,i,v) != select(a,i) (disequality)
    let result = theory.assert_literal(lit_neq, &TheoryLiteral::Neq(TermId(3), TermId(4)));
    assert!(
        matches!(result, TheoryCheckResult::Consistent),
        "level-0 disequality assertion should be consistent"
    );
}

/// Core invariant check: all assertion-derived state must be cleared.
/// Uses only pub(super)-visible fields and collect_statistics().
fn assert_reset_clears_assertion_state(theory: &ArrayTheory) {
    assert!(
        theory.equalities.is_empty(),
        "equalities must be empty after reset"
    );
    assert!(
        theory.disequalities.is_empty(),
        "disequalities must be empty after reset"
    );
    assert!(
        theory.pending_equalities.is_empty(),
        "pending_equalities must be empty after reset"
    );
    assert!(
        theory.pending_extensionality.is_empty(),
        "pending_extensionality must be empty after reset"
    );
    assert!(
        theory.pending_extensionality_set.is_empty(),
        "pending_extensionality_set must be empty after reset"
    );

    // Verify through statistics that assertion counts are zero
    let stats: std::collections::HashMap<_, _> = theory.collect_statistics().into_iter().collect();
    assert_eq!(
        stats.get("array_equalities").copied(),
        Some(0),
        "array_equalities stat must be zero after reset"
    );
    assert_eq!(
        stats.get("array_disequalities").copied(),
        Some(0),
        "array_disequalities stat must be zero after reset"
    );
    assert_eq!(
        stats.get("array_pending_equalities").copied(),
        Some(0),
        "array_pending_equalities stat must be zero after reset"
    );
}

/// Structural state from set_terms/analyze_terms must survive reset.
fn assert_reset_preserves_structural_state(theory: &ArrayTheory) {
    assert!(
        !theory.selects.is_empty(),
        "selects should survive reset (structural state from analyze_terms)"
    );
    assert!(
        !theory.stores.is_empty(),
        "stores should survive reset (structural state from analyze_terms)"
    );

    let stats: std::collections::HashMap<_, _> = theory.collect_statistics().into_iter().collect();
    assert!(
        stats.get("array_selects").copied().unwrap_or(0) > 0,
        "array_selects stat should be non-zero after reset (structural)"
    );
    assert!(
        stats.get("array_stores").copied().unwrap_or(0) > 0,
        "array_stores stat should be non-zero after reset (structural)"
    );
}

/// Primary soundness test: reset() clears assertion state at level 0.
///
/// After #2386 the DPLL(T) loop never calls push(), so assertions happen at
/// level 0. The explicit reset() override must clear all assertion-derived
/// state. The default `backtrack(0)` would be a no-op here — this test catches
/// any regression to the default delegation.
#[test]
fn test_array_reset_clears_level0_assertion_state() {
    let mut theory = ArrayTheory::new();
    theory.set_terms(make_array_terms());

    // Assert at level 0 (no push)
    assert_at_level0(&mut theory);

    // Verify assertion state exists before reset
    assert!(
        !theory.equalities.is_empty(),
        "precondition: equalities should be populated before reset"
    );
    assert!(
        !theory.disequalities.is_empty(),
        "precondition: disequalities should be populated before reset"
    );

    theory.reset();

    assert_reset_clears_assertion_state(&theory);
    assert_reset_preserves_structural_state(&theory);
}

/// After reset, re-asserting the same equalities must succeed.
/// Structural state from `set_terms`/`analyze_terms` must persist so
/// the same select/store analysis is available for the next solve cycle.
#[test]
fn test_array_reset_supports_reuse_after_level0_cycle() {
    let mut theory = ArrayTheory::new();
    theory.set_terms(make_array_terms());

    // First cycle
    assert_at_level0(&mut theory);
    theory.reset();

    // Second cycle — must work identically
    assert_at_level0(&mut theory);

    assert!(
        !theory.equalities.is_empty(),
        "re-asserted equalities should be present after second cycle"
    );

    theory.reset();
    assert_reset_clears_assertion_state(&theory);
    assert_reset_preserves_structural_state(&theory);
}

/// soft_reset() delegates to reset() and must also clear level-0 state.
/// This mirrors the actual DPLL(T) call path after #2386.
#[test]
fn test_array_soft_reset_clears_level0_assertion_state() {
    let mut theory = ArrayTheory::new();
    theory.set_terms(make_array_terms());

    assert_at_level0(&mut theory);

    assert!(
        !theory.equalities.is_empty(),
        "precondition: equalities should be populated before soft_reset"
    );

    theory.soft_reset();

    assert_reset_clears_assertion_state(&theory);
    assert_reset_preserves_structural_state(&theory);
}
