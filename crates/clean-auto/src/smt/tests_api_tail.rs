// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cdcl::{Lit, Var};
use crate::egraph::Symbol;
use crate::theories::{
    arithmetic::ArithmeticTheory, arrays::ArrayTheory, equality::EqualityTheory,
};
use std::any::Any;
use std::collections::HashSet;
use std::sync::Arc;

#[test]
fn test_smt_stats() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let _ = smt.assert_eq(a, b);

    let stats = smt.stats();
    assert_eq!(stats.num_terms, 2);
    assert!(stats.num_vars >= 1);
    assert_eq!(stats.sat_propagations, 0);
    assert_eq!(stats.theory_check_calls, 0);
    assert_eq!(stats.theory_conflicts, 0);
    assert_eq!(stats.theory_propagated_literals, 0);
    assert_eq!(stats.theory_unknowns, 0);
    assert!(
        stats.theory_stats.is_empty(),
        "plain SMT stats should not report per-theory counters without theories"
    );
}

#[test]
fn test_smt_stats_collect_theory_counters() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(ArrayTheory::new()));
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let arr = smt.const_term("arr");
    let idx = smt.const_term("idx");
    let val = smt.const_term("val");
    let store = smt.store_term(arr, idx, val);
    let _read = smt.select_term(store, idx);
    let _ = smt.assert_eq(a, b);

    match smt.solve() {
        SmtResult::Sat(_) => {}
        other => panic!("expected SAT for simple multi-theory statistics probe, got {other:?}"),
    }

    let stats = smt.stats();
    assert!(
        stats
            .theory_stats
            .windows(2)
            .all(|window| window[0].0 <= window[1].0),
        "theory statistics should have deterministic key ordering"
    );

    let stat = |name: &'static str| {
        stats
            .theory_stats
            .iter()
            .find_map(|(key, value)| (*key == name).then_some(*value))
            .unwrap_or_else(|| panic!("missing theory stat {name}"))
    };

    assert!(
        stat("arith_vars") >= 2,
        "arithmetic stats should reflect internalized terms"
    );
    assert!(
        stat("array_selects") >= 1 && stat("array_stores") >= 1,
        "array stats should reflect the registered select/store terms"
    );
    assert!(
        stat("euf_terms") >= 2,
        "EUF stats should reflect internalized terms"
    );
}

#[test]
fn test_smt_theory_typed_accessors_coverage() {
    let mut smt = SmtSolver::new();
    let eq_idx = smt.add_theory(Box::new(EqualityTheory::new()));

    let theory = smt
        .get_theory(eq_idx)
        .expect("get_theory should find registered theory");
    assert_eq!(
        theory.name(),
        "EUF",
        "registered theory should be EqualityTheory"
    );
    assert!(
        smt.get_theory(eq_idx + 1).is_none(),
        "out-of-range index should return None"
    );

    let theory_mut: &mut dyn TheorySolver = smt
        .get_theory_mut(eq_idx)
        .expect("get_theory_mut should find registered theory");
    assert_eq!(theory_mut.name(), "EUF");
    assert!(
        smt.get_theory_mut(eq_idx + 1).is_none(),
        "out-of-range index should return None"
    );

    let typed = smt
        .get_theory_typed::<EqualityTheory>(eq_idx)
        .expect("get_theory_typed should find registered EqualityTheory");
    assert_eq!(typed.name(), "EUF");
    assert!(
        smt.get_theory_typed::<EqualityTheory>(eq_idx + 1).is_none(),
        "out-of-range typed index should return None"
    );

    let typed_mut = smt
        .get_theory_typed_mut::<EqualityTheory>(eq_idx)
        .expect("get_theory_typed_mut should find registered EqualityTheory");
    assert_eq!(typed_mut.name(), "EUF");
    assert!(
        smt.get_theory_typed_mut::<EqualityTheory>(eq_idx + 1)
            .is_none(),
        "out-of-range typed_mut index should return None"
    );

    assert!(
        smt.get_theory_typed::<ArithmeticTheory>(eq_idx).is_none(),
        "wrong type downcast (ArithmeticTheory at EqualityTheory index) should return None"
    );
}

/// Verify that `internalize_atom` pre-registers E-graph nodes before
/// the DPLL(T) assertion loop (#2386). After `solve()`, every TermId
/// referenced by a registered TheoryLiteral must report an E-class through
/// the public EqualityTheory query API — even terms that only appear in
/// disequalities (which don't force assert_equality).
#[test]
fn test_internalize_atom_preregisters_euf_terms() {
    let mut smt = SmtSolver::new();
    let eq_idx = smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let fa = smt.app_term("f", vec![a]);

    // a = b forces both a, b into the E-graph via assert_equality.
    let _ = smt.assert_eq(a, b);
    // c ≠ f(a) — without internalize_atom, c and f(a) would only be
    // built into the E-graph lazily during assert_disequality.
    let _ = smt.assert_neq(c, fa);

    let result = smt.solve();
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected SAT for consistent a=b, c≠f(a)"
    );

    let euf = smt
        .get_theory_typed::<EqualityTheory>(eq_idx)
        .expect("EqualityTheory should be accessible after solve");

    // All four term IDs must be in the E-graph after internalize_atom.
    for (tid, name) in [(a, "a"), (b, "b"), (c, "c"), (fa, "f(a)")] {
        assert!(
            euf.get_eclass(tid).is_some(),
            "term {name} (id={tid:?}) should be pre-registered in E-graph by internalize_atom"
        );
    }
}

/// Fresh theory atoms created by propagation must be synced back through
/// `internalize_atom` before the next outer DPLL(T) iteration (#2386).
///
/// Without that re-sync, the next assert loop can hit a theory that assumes
/// all registered atoms were pre-internalized, turning a valid propagation-only
/// problem into a spurious UNSAT.
#[test]
fn test_propagation_resyncs_new_theory_atoms_before_next_iteration() {
    struct DeducingTheory {
        pair: (TermId, TermId),
        emitted: bool,
    }

    impl TheorySolver for DeducingTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "DeducingTheory"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
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

    struct NeedsInternalizeTheory {
        target: TheoryLiteral,
        internalized: HashSet<TheoryLiteral>,
    }

    impl TheorySolver for NeedsInternalizeTheory {
        fn assert_literal(&mut self, lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            if theory_lit == &self.target && !self.internalized.contains(theory_lit) {
                return TheoryCheckResult::Conflict(vec![lit]);
            }
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "NeedsInternalizeTheory"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn internalize_atom(&mut self, theory_lit: &TheoryLiteral) {
            self.internalized.insert(theory_lit.clone());
        }

        fn assert_shared_equality(
            &mut self,
            _t1: TermId,
            _t2: TermId,
            _reason: Lit,
        ) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
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
    let target = TheoryLiteral::Eq(a, b);

    smt.add_theory(Box::new(DeducingTheory {
        pair: (a, b),
        emitted: false,
    }));
    smt.add_theory(Box::new(NeedsInternalizeTheory {
        target,
        internalized: HashSet::new(),
    }));

    match smt.solve() {
        SmtResult::Sat(model) => {
            assert!(
                model.equalities.contains(&(a, b)) || model.equalities.contains(&(b, a)),
                "propagation-created equality should remain asserted after the resync"
            );
        }
        other => {
            panic!(
                "expected SAT after propagation-created atoms are re-internalized, got {other:?}"
            );
        }
    }
}

/// Model-true deduced equalities (which reuse an existing SAT variable and
/// skip propagation) must not create unsynced atoms, so the Conflict arm's
/// debug assertion holds (#2386).
///
/// Setup: assert a = b as a unit clause (model-true). A `DeducingTheory`
/// surfaces (a, b) during Nelson-Oppen, but since the var already exists and
/// is model-true, `convert_deduced_to_propagations` skips the propagation
/// push. A `ConflictOnCheckTheory` then returns Conflict from `check()`,
/// triggering the Conflict arm. The sync invariant holds because no new
/// atoms were created — only existing vars were looked up.
#[test]
fn test_model_true_deduction_skips_propagation_conflict_arm_safe() {
    use std::sync::Arc;

    struct ModelTrueDeducingTheory {
        pair: (TermId, TermId),
        emitted: bool,
    }

    impl TheorySolver for ModelTrueDeducingTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }
        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }
        fn backtrack(&mut self, _level: u32) {}
        fn push(&mut self) {}
        fn name(&self) -> &'static str {
            "ModelTrueDeducingTheory"
        }
        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}
        fn prepare_deduced_equalities(&mut self) {
            // Reset the emission flag so the deduction is produced each iteration.
            // In a real theory this would come from model-based reasoning.
            self.emitted = false;
        }
        fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
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

    /// Theory that returns Consistent from `assert_literal` but Conflict
    /// from `check()`, using the last-seen assertion literal as the conflict
    /// clause. This exercises the Conflict arm after Nelson-Oppen has run.
    struct ConflictOnCheckTheory {
        conflict_lit: Option<Lit>,
    }

    impl TheorySolver for ConflictOnCheckTheory {
        fn assert_literal(&mut self, lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            self.conflict_lit = Some(lit);
            TheoryCheckResult::Consistent
        }
        fn check(&self) -> TheoryCheckResult {
            if let Some(lit) = self.conflict_lit {
                TheoryCheckResult::Conflict(vec![lit])
            } else {
                TheoryCheckResult::Consistent
            }
        }
        fn backtrack(&mut self, _level: u32) {}
        fn push(&mut self) {}
        fn name(&self) -> &'static str {
            "ConflictOnCheckTheory"
        }
        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}
        fn reset(&mut self) {
            self.conflict_lit = None;
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

    // Force a = b true in the model via unit clause. This creates the
    // SAT variable for Eq(a, b) before solve().
    let _ = smt.assert_eq(a, b);

    smt.add_theory(Box::new(ModelTrueDeducingTheory {
        pair: (a, b),
        emitted: false,
    }));
    smt.add_theory(Box::new(ConflictOnCheckTheory { conflict_lit: None }));

    // The DPLL(T) loop should:
    // 1. Find SAT model with a=b true
    // 2. Assert to theories (Consistent from both)
    // 3. N-O fixpoint: deduction (a,b) → existing var, model-true → skip
    // 4. theory.check(): ConflictOnCheckTheory returns Conflict
    // 5. Conflict arm fires; debug_assert checks sync invariant (no new atoms)
    // 6. Blocking clause added → next iteration → UNSAT
    let result = smt.solve();
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "expected UNSAT: unit clause a=b + always-conflicting check theory"
    );
}

/// Verify that `assert_eq` followed by a conflicting `assert_neq` returns
/// `None` from the second call, exposing immediate-UNSAT feedback (#2319).
#[test]
fn test_assert_eq_neq_immediate_conflict_feedback() {
    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // First assertion: a = b — should succeed.
    let cref = smt.assert_eq(a, b);
    assert!(cref.is_some(), "first unit clause should succeed");

    // Conflicting assertion: a ≠ b — immediate UNSAT at SAT level.
    let cref2 = smt.assert_neq(a, b);
    assert!(
        cref2.is_none(),
        "conflicting unit clause should return None (immediate UNSAT)"
    );
}

/// Verify that `EqualityTheory::are_equal` is callable through `&self`
/// after explicit internalization, and that congruence still works (#2319).
#[test]
fn test_are_equal_read_only_with_explicit_internalization() {
    let mut eq = EqualityTheory::new();

    let terms = vec![
        SmtTerm::Const(Symbol::new("x")),
        SmtTerm::Const(Symbol::new("y")),
        SmtTerm::App(Symbol::new("h"), vec![TermId(0)]),
        SmtTerm::App(Symbol::new("h"), vec![TermId(1)]),
    ];
    eq.set_terms(terms);

    let x = TermId(0);
    let y = TermId(1);
    let hx = TermId(2);
    let hy = TermId(3);

    eq.internalize_term(x);
    eq.internalize_term(y);
    eq.internalize_term(hx);
    eq.internalize_term(hy);

    let eq_ref: &EqualityTheory = &eq;
    assert!(!eq_ref.are_equal(hx, hy));

    let lit = Lit::pos(Var::new(0));
    let result = eq.assert_literal(lit, &TheoryLiteral::Eq(x, y));
    assert!(matches!(result, TheoryCheckResult::Consistent));

    let eq_ref: &EqualityTheory = &eq;
    assert!(eq_ref.are_equal(hx, hy));
}
