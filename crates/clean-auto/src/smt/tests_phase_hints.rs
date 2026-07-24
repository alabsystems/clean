// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{SmtResult, SmtSolver, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver};
use crate::cdcl::{Lit, Var};
use crate::smt::SmtTerm;
use crate::theories::arithmetic::ArithmeticTheory;
use crate::theories::equality::EqualityTheory;
use std::sync::Arc;

struct HintTheory {
    hinted_lit: TheoryLiteral,
    phase: bool,
}

impl TheorySolver for HintTheory {
    fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, _level: u32) {}

    fn push(&mut self) {}

    fn name(&self) -> &'static str {
        "HintTheory"
    }

    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

    fn suggest_phase(&self, theory_lit: &TheoryLiteral) -> Option<bool> {
        (theory_lit == &self.hinted_lit).then_some(self.phase)
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

struct ConflictHintTheory {
    hinted_lit: TheoryLiteral,
    phase: bool,
}

impl TheorySolver for ConflictHintTheory {
    fn assert_literal(&mut self, lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        if lit.is_pos() && theory_lit == &self.hinted_lit {
            TheoryCheckResult::Conflict(vec![lit])
        } else {
            TheoryCheckResult::Consistent
        }
    }

    fn check(&self) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, _level: u32) {}

    fn push(&mut self) {}

    fn name(&self) -> &'static str {
        "ConflictHintTheory"
    }

    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

    fn suggest_phase(&self, theory_lit: &TheoryLiteral) -> Option<bool> {
        (theory_lit == &self.hinted_lit).then_some(self.phase)
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

#[test]
fn test_theory_phase_hints_seed_sat_phase_on_consensus() {
    let hinted_lit = TheoryLiteral::Bool(7);
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(HintTheory {
        hinted_lit: hinted_lit.clone(),
        phase: false,
    }));
    smt.add_clause(vec![hinted_lit.clone()]);

    smt.apply_theory_phase_hints();

    assert_eq!(smt.phase_hint_for_literal(&hinted_lit), Some(false));
}

#[test]
fn test_theory_phase_hints_ignore_conflicting_suggestions_forward_order() {
    let hinted_lit = TheoryLiteral::Bool(9);
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(HintTheory {
        hinted_lit: hinted_lit.clone(),
        phase: true,
    }));
    smt.add_theory(Box::new(HintTheory {
        hinted_lit: hinted_lit.clone(),
        phase: false,
    }));
    smt.add_clause(vec![hinted_lit.clone()]);

    smt.apply_theory_phase_hints();

    assert_eq!(smt.phase_hint_for_literal(&hinted_lit), Some(true));
}

#[test]
fn test_theory_phase_hints_ignore_conflicting_suggestions_reverse_order() {
    let hinted_lit = TheoryLiteral::Bool(11);
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(HintTheory {
        hinted_lit: hinted_lit.clone(),
        phase: false,
    }));
    smt.add_theory(Box::new(HintTheory {
        hinted_lit: hinted_lit.clone(),
        phase: true,
    }));
    smt.add_clause(vec![hinted_lit.clone()]);

    smt.apply_theory_phase_hints();

    assert_eq!(smt.phase_hint_for_literal(&hinted_lit), Some(true));
}

#[test]
fn test_solve_conflict_path_applies_theory_phase_hints() {
    let hinted_lit = TheoryLiteral::Bool(13);
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ConflictHintTheory {
        hinted_lit: hinted_lit.clone(),
        phase: false,
    }));
    smt.add_clause(vec![hinted_lit.clone()]);

    assert!(
        matches!(smt.solve(), SmtResult::Unsat(_)),
        "the theory conflict should make the unit-asserted atom UNSAT"
    );
    assert_eq!(smt.phase_hint_for_literal(&hinted_lit), Some(false));
}

#[test]
fn test_equality_theory_suggest_phase_tracks_equalities_and_disequalities() {
    let a = TermId(0);
    let b = TermId(1);

    let mut eq = EqualityTheory::new();
    assert_eq!(eq.suggest_phase(&TheoryLiteral::Eq(a, b)), None);

    let lit_eq = Lit::pos(Var::new(0));
    assert!(matches!(
        eq.assert_literal(lit_eq, &TheoryLiteral::Eq(a, b)),
        TheoryCheckResult::Consistent
    ));
    assert_eq!(eq.suggest_phase(&TheoryLiteral::Eq(a, b)), Some(true));

    let mut diseq_only = EqualityTheory::new();
    let lit_neq = Lit::pos(Var::new(1));
    assert!(matches!(
        diseq_only.assert_literal(lit_neq, &TheoryLiteral::Neq(a, b)),
        TheoryCheckResult::Consistent
    ));
    assert_eq!(
        diseq_only.suggest_phase(&TheoryLiteral::Eq(a, b)),
        Some(false)
    );
}

#[test]
fn test_arithmetic_theory_suggest_phase_uses_current_assignment() {
    let a = TermId(0);
    let b = TermId(1);
    let lit = Lit::pos(Var::new(0));

    let mut arith = ArithmeticTheory::new();
    assert!(matches!(
        arith.assert_literal(lit, &TheoryLiteral::Le(a, b)),
        TheoryCheckResult::Consistent
    ));

    assert_eq!(arith.suggest_phase(&TheoryLiteral::Le(a, b)), Some(true));
    assert_eq!(arith.suggest_phase(&TheoryLiteral::Lt(a, b)), Some(false));
    assert_eq!(arith.suggest_phase(&TheoryLiteral::Eq(a, b)), Some(true));
}
