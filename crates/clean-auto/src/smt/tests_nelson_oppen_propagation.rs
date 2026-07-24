// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nelson-Oppen propagation contract tests (#2366).
//!
//! Focuses on real-theory propagation outcomes:
//! - forwarded equality causing an arithmetic contradiction
//! - arithmetic Le-squeeze equality feeding back into EUF

use super::*;
use crate::theories::equality::EqualityTheory;

fn proof_trail_summary(smt: &SmtSolver) -> Vec<String> {
    smt.proof_trail()
        .iter()
        .map(|entry| match entry {
            ProofTrailEntry::TheoryConflict { theory_name, .. } => {
                format!("Conflict({theory_name})")
            }
            ProofTrailEntry::TheoryPropagation { theory_name, .. } => {
                format!("Propagation({theory_name})")
            }
        })
        .collect()
}

fn forwarding_conflict_payload(
    smt: &SmtSolver,
) -> (&[crate::cdcl::Lit], &[TheoryLiteral], Option<u32>) {
    let trail_summary = proof_trail_summary(smt);
    let Some((conflict_lits, conflict_theory_lits, clause_index)) =
        smt.proof_trail().iter().find_map(|entry| match entry {
            ProofTrailEntry::TheoryConflict {
                theory_name: "forwarding",
                conflict_lits,
                conflict_theory_lits,
                clause_index,
            } => Some((
                conflict_lits.as_slice(),
                conflict_theory_lits.as_slice(),
                *clause_index,
            )),
            _ => None,
        })
    else {
        panic!(
            "Expected a TheoryConflict from 'forwarding' in the proof trail, \
             but only found: {:?}",
            trail_summary
        );
    };
    (conflict_lits, conflict_theory_lits, clause_index)
}

fn assert_forwarding_conflict_matches_premises(
    smt: &SmtSolver,
    conflict_lits: &[crate::cdcl::Lit],
    conflict_theory_lits: &[TheoryLiteral],
    expected_theory_lits: &[TheoryLiteral],
) {
    let expected_conflict_lits: Vec<_> = expected_theory_lits
        .iter()
        .map(|theory_lit| {
            smt.theory_literal_to_sat_literal(theory_lit)
                .unwrap_or_else(|| {
                    panic!("missing SAT literal for expected theory lit {theory_lit:?}")
                })
        })
        .collect();
    assert_eq!(
        conflict_lits.len(),
        expected_conflict_lits.len(),
        "resolved forwarding conflict should contain exactly the original premises, got SAT lits {conflict_lits:?} and theory lits {conflict_theory_lits:?}"
    );
    for expected_lit in &expected_conflict_lits {
        assert!(
            conflict_lits.contains(expected_lit),
            "resolved forwarding conflict should contain SAT literal {expected_lit:?}; got {conflict_lits:?}"
        );
    }
    assert_eq!(
        conflict_theory_lits.len(),
        expected_theory_lits.len(),
        "resolved forwarding conflict should expose exactly the original theory premises, got {conflict_theory_lits:?}"
    );
    for expected_theory_lit in expected_theory_lits {
        assert!(
            conflict_theory_lits.contains(expected_theory_lit),
            "resolved forwarding conflict should contain theory literal {expected_theory_lit:?}; got {conflict_theory_lits:?}"
        );
    }
}

/// Verify that forward_equality_deductions returns a conflict when
/// a forwarded equality causes a theory contradiction.
///
/// This exercises the conflict return path in propagation.rs:182
/// which was previously untested in isolation.
#[test]
fn test_forward_equality_deductions_surfaces_theory_conflict() {
    use crate::theories::arithmetic::ArithmeticTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // a = b (EUF) combined with a < b (arithmetic) should produce UNSAT:
    // If a = b then a < b becomes a < a which is contradictory.
    // The conflict arises when EUF's equality a = b is forwarded to
    // ArithmeticTheory which already has the a < b constraint.
    let _ = smt.assert_eq(a, b);
    smt.add_clause(vec![TheoryLiteral::Lt(a, b)]);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: a = b ∧ a < b → a < a → UNSAT.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT for a = b ∧ a < b — this requires a < a. \
                 Equality forwarding to arithmetic may not propagate conflicts."
            );
        }
        SmtResult::Unknown => {
            // Acceptable for incomplete solver.
        }
    }
}

/// Verify that forwarding conflict resolution produces a direct conflict
/// clause instead of requiring a second DPLL(T) iteration (#2386).
///
/// Setup: a = b, f(a) = c, f(b) = d (EUF) + c < d (arithmetic).
/// EUF deduces c = d via congruence (a=b → f(a)=f(b), with f(a)=c and
/// f(b)=d → c=d). This deduced equality is forwarded to arithmetic, which
/// detects a conflict with c < d. The proof trail should contain a
/// TheoryConflict from "forwarding" — proving the CDCL solver learned
/// from the conflict in one iteration via resolution.
///
/// Previous versions used direct encodings (a=b + a<b, or Le-squeeze +
/// x≠c) but those either get caught during model assertion (both literals
/// in the SAT model) or produce propagations without a forwarding conflict
/// (EUF's assert_shared_equality doesn't check asserted disequalities).
/// The congruence-based setup forces the equality to be DEDUCED by EUF and
/// forwarded to arithmetic, where the Lt constraint triggers a real
/// forwarding conflict.
#[test]
fn test_forwarding_conflict_resolution_produces_direct_conflict() {
    use crate::theories::arithmetic::ArithmeticTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");
    let f_a = smt.app_term("f", vec![a]);
    let f_b = smt.app_term("f", vec![b]);

    // EUF: a = b → congruence → f(a) = f(b). With f(a) = c, f(b) = d → c = d (deduced).
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(f_a, c);
    let _ = smt.assert_eq(f_b, d);
    // Arithmetic: c < d — contradicts the deduced c = d.
    smt.add_clause(vec![TheoryLiteral::Lt(c, d)]);

    let result = smt.solve();
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "Expected UNSAT: congruence deduces c = d, contradicts c < d"
    );

    let (conflict_lits, conflict_theory_lits, clause_index) = forwarding_conflict_payload(&smt);
    assert!(
        clause_index.is_some(),
        "Forwarding conflict should learn a blocking clause, got clause_index=None"
    );

    let expected_theory_lits = [
        TheoryLiteral::Eq(a, b),
        TheoryLiteral::Eq(f_a, c),
        TheoryLiteral::Eq(f_b, d),
        TheoryLiteral::Lt(c, d),
    ];
    assert_forwarding_conflict_matches_premises(
        &smt,
        conflict_lits,
        conflict_theory_lits,
        &expected_theory_lits,
    );
}

/// Opposite-polarity references to a freshly created forwarding atom must not
/// produce a direct forwarding conflict.
///
/// Setup:
/// - `DeducingTheory` emits a shared equality with no pre-existing SAT atom
/// - `OppositePolarityConflictTheory` reports a forwarding conflict using the
///   negated reason literal (`!reason`)
///
/// The negated literal has no SAT clause behind it yet, so
/// `resolve_forwarding_conflict` must fail closed and fall back to the
/// two-iteration path:
/// 1. record a `TheoryPropagation` from the deducing theory
/// 2. sync the new atom and let the next iteration produce a normal theory
///    conflict during `assert_literal`
#[test]
fn test_forwarding_conflict_resolution_rejects_unsynced_opposite_polarity() {
    use std::any::Any;
    use std::sync::Arc;

    struct DeducingTheory {
        pair: (TermId, TermId),
        emitted: bool,
    }

    impl TheorySolver for DeducingTheory {
        fn assert_literal(
            &mut self,
            _lit: crate::cdcl::Lit,
            _theory_lit: &TheoryLiteral,
        ) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "Deducer"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<crate::cdcl::Lit>)> {
            if self.emitted {
                Vec::new()
            } else {
                self.emitted = true;
                vec![(self.pair.0, self.pair.1, vec![])]
            }
        }

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    struct OppositePolarityConflictTheory {
        target: (TermId, TermId),
    }

    impl TheorySolver for OppositePolarityConflictTheory {
        fn assert_literal(
            &mut self,
            lit: crate::cdcl::Lit,
            theory_lit: &TheoryLiteral,
        ) -> TheoryCheckResult {
            match theory_lit {
                TheoryLiteral::Eq(lhs, rhs)
                    if (*lhs, *rhs) == self.target || (*rhs, *lhs) == self.target =>
                {
                    TheoryCheckResult::Conflict(vec![lit])
                }
                _ => TheoryCheckResult::Consistent,
            }
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "OppositePolarity"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn assert_shared_equality(
            &mut self,
            t1: TermId,
            t2: TermId,
            reason: crate::cdcl::Lit,
        ) -> TheoryCheckResult {
            if (t1, t2) == self.target || (t2, t1) == self.target {
                TheoryCheckResult::Conflict(vec![reason.not()])
            } else {
                TheoryCheckResult::Consistent
            }
        }

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    smt.add_theory(Box::new(DeducingTheory {
        pair: (a, b),
        emitted: false,
    }));
    smt.add_theory(Box::new(OppositePolarityConflictTheory { target: (a, b) }));

    let result = smt.solve();
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "expected UNSAT after the fallback iteration replays the propagated equality as a real SAT literal"
    );
    assert!(
        smt.proof_trail().iter().any(|entry| matches!(
            entry,
            ProofTrailEntry::TheoryPropagation {
                theory_name: "Deducer",
                ..
            }
        )),
        "the initial forwarding-created equality should still be recorded as a propagation"
    );
    assert!(
        smt.proof_trail().iter().any(|entry| matches!(
            entry,
            ProofTrailEntry::TheoryConflict {
                theory_name: "OppositePolarity",
                ..
            }
        )),
        "after the atom is synced, the next iteration should surface a normal theory conflict"
    );
    assert!(
        !smt.proof_trail().iter().any(|entry| matches!(
            entry,
            ProofTrailEntry::TheoryConflict {
                theory_name: "forwarding",
                ..
            }
        )),
        "an unsynced opposite-polarity forwarding literal must not be treated as a direct forwarding conflict"
    );
}

/// Verify that Nelson-Oppen propagation handles Le+Le squeeze → equality.
///
/// x ≤ c, c ≤ x forces x = c in arithmetic. If this equality is not
/// propagated back to EUF, congruence reasoning is incomplete.
/// This test uses a tighter setup than test_nelson_oppen_arithmetic_to_euf_equality:
/// single variable, single constant, disequality contradiction.
#[test]
fn test_nelson_oppen_le_squeeze_propagates_equality() {
    use crate::theories::arithmetic::ArithmeticTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let x = smt.const_term("x");
    let c = smt.const_term("c");

    // x ≤ c ∧ c ≤ x → x = c (arithmetic)
    smt.add_clause(vec![TheoryLiteral::Le(x, c)]);
    smt.add_clause(vec![TheoryLiteral::Le(c, x)]);

    // x ≠ c → contradicts x = c
    let _ = smt.assert_neq(x, c);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: x ≤ c ∧ c ≤ x → x = c, contradicts x ≠ c.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT for x ≤ c, c ≤ x, x ≠ c — arithmetic squeeze \
                 forces x = c which contradicts x ≠ c. \
                 Le-squeeze equality propagation may be broken (#2364)."
            );
        }
        SmtResult::Unknown => {
            // Acceptable for incomplete solver.
        }
    }
}
