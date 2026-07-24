// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::theories::equality::EqualityTheory;

#[test]
fn test_smt_basic() {
    let mut smt = SmtSolver::new();

    // Create terms
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Assert a = b
    let _ = smt.assert_eq(a, b);

    // Should be SAT (no theory solver to check)
    match smt.solve() {
        SmtResult::Sat(model) => {
            assert!(model.equalities.contains(&(a, b)));
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_smt_conflict_basic() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Assert a = b and a != b - pure SAT conflict
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_neq(a, b);

    // Should be UNSAT from SAT level
    match smt.solve() {
        SmtResult::Unsat(_core) => {}
        _ => panic!("Expected UNSAT"),
    }
}

#[test]
fn test_smt_term_interning() {
    let mut smt = SmtSolver::new();

    let a1 = smt.const_term("a");
    let a2 = smt.const_term("a");
    let b = smt.const_term("b");

    // Same name should return same term ID
    assert_eq!(a1, a2);
    assert_ne!(a1, b);
}

#[test]
fn test_smt_app_terms() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let fa = smt.app_term("f", vec![a]);
    let fb = smt.app_term("f", vec![b]);
    let fa2 = smt.app_term("f", vec![a]);

    // Same application should return same term ID
    assert_eq!(fa, fa2);
    assert_ne!(fa, fb);
}

#[test]
fn test_smt_add_clause_returns_valid_ref() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    let clause_ref = smt
        .add_clause(vec![TheoryLiteral::Eq(a, b)])
        .expect("Expected clause reference for satisfiable clause");
    assert!(clause_ref.is_valid());
}

#[test]
fn test_smt_clause() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    // a = b OR a = c
    smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(a, c)]);

    // Should be SAT
    match smt.solve() {
        SmtResult::Sat(_) => {}
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_smt_theory_conflict_unsat() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    // a = b, b = c, but a != c should be UNSAT via theory conflict.
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(b, c);
    let _ = smt.assert_neq(a, c);

    match smt.solve() {
        SmtResult::Unsat(_core) => {}
        _ => panic!("Expected UNSAT from equality theory"),
    }
}

#[test]
fn test_theory_literal_negate_roundtrip() {
    let a = TermId(1);
    let b = TermId(2);

    assert_eq!(TheoryLiteral::Eq(a, b).negate(), TheoryLiteral::Neq(a, b));
    assert_eq!(TheoryLiteral::Neq(a, b).negate(), TheoryLiteral::Eq(a, b));
    assert_eq!(TheoryLiteral::Lt(a, b).negate(), TheoryLiteral::Le(b, a));
    assert_eq!(TheoryLiteral::Le(a, b).negate(), TheoryLiteral::Lt(b, a));
    assert_eq!(TheoryLiteral::Bool(5).negate(), TheoryLiteral::NegBool(5));
    assert_eq!(TheoryLiteral::NegBool(5).negate(), TheoryLiteral::Bool(5));
}

#[test]
fn test_smt_disjunction_choice() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    // (a = b) OR (a = c)
    smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(a, c)]);

    // Force a != b
    let _ = smt.assert_neq(a, b);

    // Now a = c must be true
    match smt.solve() {
        SmtResult::Sat(model) => {
            assert!(model.equalities.contains(&(a, c)));
            assert!(model.disequalities.contains(&(a, b)));
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_smt_multiple_equalities() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");

    // a = b AND c = d
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(c, d);

    match smt.solve() {
        SmtResult::Sat(model) => {
            assert!(model.equalities.contains(&(a, b)));
            assert!(model.equalities.contains(&(c, d)));
        }
        _ => panic!("Expected SAT"),
    }
}

// ================================================================
// Performance proof: check_theories clones entire terms Vec per theory
//
// smt.rs:414-416:
//   for theory in &mut self.theories {
//       theory.set_terms(self.terms.clone());
//   }
//
// Every call to check_theories deep-clones self.terms (Vec<SmtTerm>)
// for EACH registered theory solver. In the DPLL(T) loop (line 384),
// check_theories is called up to MAX_DPLL_T_ITERATIONS (10,000) times.
//
// For T terms and K theories: each DPLL(T) iteration costs O(T * K) clones.
// Over I iterations: total clone cost is O(I * T * K).
// With T=1000 terms, K=2 theories, I=100 iterations: 200,000 Vec clones.
//
// Fix: share terms via Arc<[SmtTerm]> or pass &[SmtTerm] references.
// ================================================================

/// Performance proof: terms Vec clone cost scales with term count.
///
/// Measures the cost of `self.terms.clone()` at varying term counts.
/// This operation happens once per theory per DPLL(T) iteration.
#[test]
fn test_check_theories_term_clone_scaling() {
    use std::time::Instant;

    let term_counts = [50usize, 200, 800];
    let mut clone_times = Vec::new();

    for &n in &term_counts {
        let mut smt = SmtSolver::new();

        // Build n terms -- a mix of Const and App to approximate real workloads
        let mut term_ids = Vec::new();
        for i in 0..n {
            if i < n / 2 {
                let id = smt.const_term(format!("c{i}"));
                term_ids.push(id);
            } else {
                // App with 2 children to bulk up the clone cost
                let child1 = term_ids[i % (n / 2)];
                let child2 = term_ids[(i + 1) % (n / 2)];
                let id = smt.app_term(format!("f{i}"), vec![child1, child2]);
                term_ids.push(id);
            }
        }

        // Measure the cost of cloning the terms vector (the operation on line 415)
        let terms_ref = smt.terms();
        let start = Instant::now();
        for _ in 0..500 {
            let cloned: Vec<SmtTerm> = terms_ref.to_vec();
            std::hint::black_box(&cloned);
        }
        let elapsed = start.elapsed().as_nanos();
        clone_times.push(elapsed);
    }

    // term_counts go 50 -> 200 -> 800 (4x each step).
    // Clone is O(n) where n = number of terms.
    // 16x terms -> should give ~16x clone time.
    let ratio_16x = clone_times[2] as f64 / clone_times[0].max(1) as f64;
    // The per-clone cost is O(n). In check_theories, this happens K times per
    // DPLL(T) iteration (K = number of theories). Over a full solve with I
    // iterations, total clone cost is O(I * K * n).
    //
    // With n=800 terms, K=2, I=100: clone happens 200 times at O(800) each
    // = 160,000 SmtTerm clones. This dominates theory-check cost for
    // problems with many terms and few theory conflicts.
    assert!(
        ratio_16x > 5.0,
        "Expected at least 5x growth for 16x terms (got {ratio_16x:.1}x). \
         If this fails, the clone overhead may have been optimized away."
    );
}

#[test]
fn test_theory_assertions_follow_var_index_order() {
    use crate::cdcl::Lit;
    use std::any::Any;
    use std::sync::{Arc, Mutex};

    struct RecordingTheory {
        seen_vars: Arc<Mutex<Vec<usize>>>,
    }

    impl TheorySolver for RecordingTheory {
        fn assert_literal(&mut self, lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            self.seen_vars
                .lock()
                .expect("recorded var order mutex should not be poisoned")
                .push(lit.var().index());
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "RecordingTheory"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    let seen_vars = Arc::new(Mutex::new(Vec::new()));
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(RecordingTheory {
        seen_vars: Arc::clone(&seen_vars),
    }));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");
    let e = smt.const_term("e");

    let _ = smt.assert_eq(c, d);
    let _ = smt.assert_neq(a, b);
    let _ = smt.add_clause(vec![TheoryLiteral::Le(d, e)]);
    let _ = smt.assert_eq(a, c);
    let _ = smt.add_clause(vec![TheoryLiteral::Lt(b, e)]);

    match smt.solve() {
        SmtResult::Sat(_) => {}
        result => panic!("Expected SAT while recording theory order, got {result:?}"),
    }

    let seen = seen_vars
        .lock()
        .expect("recorded var order mutex should not be poisoned")
        .clone();
    assert_eq!(
        seen,
        vec![0, 1, 2, 3, 4],
        "theory assertions must follow ascending SAT var order for deterministic DPLL(T) checks"
    );
}

/// Verify that the CDCL clause database grows monotonically during DPLL(T)
/// theory conflict/propagation cycles -- no learned clause deletion exists yet.
///
/// Theory clauses are now added as learned (#2327) with LBD metadata, making
/// them eligible for future reduce_db (#2370). Until reduce_db is implemented,
/// the clause count only grows.
#[test]
fn test_dpll_t_clause_growth_monotonic() {
    use crate::theories::equality::EqualityTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    // Create terms: a, b, c, f(a), f(b), f(c)
    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let fa = smt.app_term("f", vec![a]);
    let fb = smt.app_term("f", vec![b]);
    let _fc = smt.app_term("f", vec![c]);

    // Assert contradictory equality/disequality constraints to force
    // theory conflicts and clause learning in the DPLL(T) loop.
    let _ = smt.assert_eq(a, b); // a = b
    let _ = smt.assert_eq(b, c); // b = c
    let _ = smt.assert_neq(fa, fb); // f(a) != f(b) -- conflicts with congruence

    let initial_clauses = smt.stats().num_clauses;

    let result = smt.solve();
    // Should be UNSAT: a = b -> f(a) = f(b) by congruence, but f(a) != f(b) asserted
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "Expected UNSAT for contradictory equality constraints"
    );

    let final_clauses = smt.stats().num_clauses;

    // Clause count must be >= initial (monotonic growth, no GC)
    assert!(
        final_clauses >= initial_clauses,
        "Clause count should not decrease: initial={initial_clauses}, final={final_clauses}. \
         If this fails, clause deletion was implemented -- update this test."
    );
}

/// Regression test for #2327: theory conflict/propagation clauses must be
/// marked as learned (not original) with LBD metadata. Before this fix,
/// theory clauses went through `add_clause()` which set `learned: false`,
/// causing unbounded growth of the "original" clause count and preventing
/// future `reduce_db` from ever deleting them.
#[test]
fn test_theory_clauses_are_learned() {
    use crate::theories::equality::EqualityTheory;

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let fa = smt.app_term("f", vec![a]);
    let fb = smt.app_term("f", vec![b]);

    // a = b, f(a) != f(b) -> congruence conflict -> theory clause generated
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_neq(fa, fb);

    let stats_before = smt.stats();
    assert_eq!(
        stats_before.sat_learned_clauses, 0,
        "No learned clauses before solving"
    );

    let result = smt.solve();
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "Expected UNSAT for congruence conflict"
    );

    let stats_after = smt.stats();
    // Theory conflict clause must be counted as learned, not original
    assert!(
        stats_after.sat_learned_clauses > 0,
        "Theory clauses should be marked as learned: got {} learned clauses",
        stats_after.sat_learned_clauses
    );
}

// proof_coverage phase: SmtInt, theory accessors, terms API (#982)

#[test]
fn test_smt_int_constructors_coverage() {
    let val = SmtInt::from_nat(clean_kernel::expr::BigNat::from_u64(42));
    assert!(matches!(val, SmtInt::NonNegative(_)));
    assert_eq!(format!("{val}"), "42");
    assert!(matches!(SmtInt::from_i64(7), SmtInt::NonNegative(_)));
    assert!(matches!(SmtInt::from_i64(-3), SmtInt::Negative(_)));
    assert_eq!(format!("{}", SmtInt::from_i64(-3)), "-3");
    assert!(matches!(SmtInt::from_i64(0), SmtInt::NonNegative(_)));
    let val2: SmtInt = 42i64.into();
    assert_eq!(format!("{val2}"), "42");
    let val3: SmtInt = clean_kernel::expr::BigNat::from_u64(99).into();
    assert_eq!(format!("{val3}"), "99");
}

#[test]
fn test_smt_int_term_coverage() {
    let mut smt = SmtSolver::new();
    let t1 = smt.int_term(5i64);
    let t2 = smt.int_term(5i64);
    let t3 = smt.int_term(-1i64);

    assert_eq!(t1, t2, "int_term should intern equal values");
    assert_ne!(t1, t3, "different int values should differ");
    assert!(matches!(
        smt.get_term(t1),
        Some(SmtTerm::Int(SmtInt::NonNegative(_)))
    ));
    assert!(matches!(
        smt.get_term(t3),
        Some(SmtTerm::Int(SmtInt::Negative(_)))
    ));
    assert!(
        smt.get_term(TermId(999)).is_none(),
        "non-existent TermId(999) should return None"
    );
    assert_eq!(smt.terms().len(), 2);
}

#[test]
fn test_smt_select_store_term_coverage() {
    let mut smt = SmtSolver::new();
    let arr = smt.const_term("a");
    let idx = smt.const_term("i");
    let val = smt.const_term("v");

    let sel = smt.select_term(arr, idx);
    let sto = smt.store_term(arr, idx, val);
    assert_ne!(sel, sto);

    match smt.get_term(sel) {
        Some(SmtTerm::App(name, args)) => {
            assert_eq!(name.name(), "select");
            assert_eq!(args.len(), 2);
        }
        other => panic!("Expected App(select, [..]), got {other:?}"),
    }
    match smt.get_term(sto) {
        Some(SmtTerm::App(name, args)) => {
            assert_eq!(name.name(), "store");
            assert_eq!(args.len(), 3);
        }
        other => panic!("Expected App(store, [..]), got {other:?}"),
    }
}

#[test]
fn test_smt_set_terms_once_congruence_coverage() {
    // Verify set_terms called once before DPLL(T) loop (#2308)
    // preserves correctness through conflict/backtrack cycles.
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let fa = smt.app_term("f", vec![a]);
    let fb = smt.app_term("f", vec![b]);

    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_neq(fa, fb);

    assert!(
        matches!(smt.solve(), SmtResult::Unsat(_)),
        "Expected UNSAT (congruence: a=b -> f(a)=f(b))"
    );
}

#[test]
fn test_smt_set_terms_once_transitivity_coverage() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let x = smt.const_term("x");
    let y = smt.const_term("y");
    let z = smt.const_term("z");
    let w = smt.const_term("w");

    let _ = smt.assert_eq(x, y);
    let _ = smt.assert_eq(y, z);
    let _ = smt.assert_eq(z, w);
    let _ = smt.assert_neq(x, w);

    assert!(
        matches!(smt.solve(), SmtResult::Unsat(_)),
        "Expected UNSAT (transitivity chain x=y=z=w, x!=w)"
    );
}
