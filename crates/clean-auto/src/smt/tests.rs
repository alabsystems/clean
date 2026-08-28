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
// Regression guard: check_theories must not deep-clone the terms Vec
// per theory per DPLL(T) iteration (#2308).
//
// Pre-fix, `check_theories` ran `theory.set_terms(self.terms.clone())`
// for each of K theories on every one of up to MAX_DPLL_T_ITERATIONS
// rounds: O(I * K * n) SmtTerm clones for n terms. The fix shares one
// `Arc<[SmtTerm]>` snapshot (`shared_terms_for_theories`), rebuilt only
// when a new term is interned, so the deep-copy count is O(1) per term-set
// version regardless of K, I or n.
//
// This used to be a wall-clock microbenchmark of `Vec::to_vec` at 50 vs
// 800 terms asserting a >5x ratio. That measured the std library, not the
// solver, and flaked under parallel load (1/2266 runs on 2026-08-20: a
// preempted 50-term timing inflated the denominator). The property is now
// measured by counting the work directly: the number of distinct term-slice
// allocations handed to theories, which is deterministic.
// ================================================================

/// Every theory, on every resync round, must receive the *same* shared
/// `Arc<[SmtTerm]>` allocation: exactly one O(n) copy per term-set version.
#[test]
fn test_check_theories_term_clone_scaling() {
    use crate::cdcl::Lit;
    use std::any::Any;
    use std::sync::{Arc, Mutex};

    struct SnapshotRecordingTheory {
        snapshots: Arc<Mutex<Vec<Arc<[SmtTerm]>>>>,
    }

    impl TheorySolver for SnapshotRecordingTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "SnapshotRecordingTheory"
        }

        fn set_terms(&mut self, terms: Arc<[SmtTerm]>) {
            self.snapshots
                .lock()
                .expect("snapshot mutex should not be poisoned")
                .push(terms);
        }

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    /// Number of distinct heap allocations among the recorded snapshots.
    /// Pre-#2308 this equals the number of `set_terms` calls (K * rounds);
    /// post-fix it equals the number of term-set versions.
    fn distinct_allocations(snapshots: &[Arc<[SmtTerm]>]) -> usize {
        let mut seen: Vec<&Arc<[SmtTerm]>> = Vec::new();
        for snapshot in snapshots {
            if !seen.iter().any(|s| Arc::ptr_eq(s, snapshot)) {
                seen.push(snapshot);
            }
        }
        seen.len()
    }

    const THEORIES: usize = 2;
    const RESYNC_ROUNDS: usize = 4;
    const TERM_COUNT: usize = 800;

    let mut smt = SmtSolver::new();
    let snapshots = Arc::new(Mutex::new(Vec::new()));
    for _ in 0..THEORIES {
        smt.add_theory(Box::new(SnapshotRecordingTheory {
            snapshots: Arc::clone(&snapshots),
        }));
    }

    // Build n terms -- a mix of Const and App to approximate real workloads.
    let mut term_ids = Vec::new();
    for i in 0..TERM_COUNT {
        if i < TERM_COUNT / 2 {
            term_ids.push(smt.const_term(format!("c{i}")));
        } else {
            let child1 = term_ids[i % (TERM_COUNT / 2)];
            let child2 = term_ids[(i + 1) % (TERM_COUNT / 2)];
            term_ids.push(smt.app_term(format!("f{i}"), vec![child1, child2]));
        }
    }
    let _ = smt.assert_eq(term_ids[0], term_ids[1]);

    // Each round: force a full theory resync (mutable theory access marks the
    // sync state dirty) and solve, so set_terms fires K times per round.
    for _ in 0..RESYNC_ROUNDS {
        let theory = smt
            .get_theory_mut(0)
            .expect("recording theory should stay registered");
        assert_eq!(theory.name(), "SnapshotRecordingTheory");
        assert!(matches!(smt.solve(), SmtResult::Sat(_)));
    }

    let recorded = snapshots
        .lock()
        .expect("snapshot mutex should not be poisoned")
        .clone();
    assert_eq!(
        recorded.len(),
        THEORIES * RESYNC_ROUNDS,
        "every theory should be resynced on every round"
    );
    assert!(
        recorded.iter().all(|s| s.len() == TERM_COUNT),
        "each snapshot should expose the full term set"
    );
    assert_eq!(
        distinct_allocations(&recorded),
        1,
        "an unchanged term set must be deep-copied exactly once across {THEORIES} theories x \
         {RESYNC_ROUNDS} resyncs; more allocations means check_theories is cloning the \
         terms Vec per theory again (#2308)"
    );

    // Interning one new term is the only event that may trigger a fresh copy,
    // and again it must be shared by every theory.
    let extra = smt.const_term("c_extra");
    let _ = smt.assert_eq(extra, term_ids[0]);
    assert!(matches!(smt.solve(), SmtResult::Sat(_)));

    let recorded = snapshots
        .lock()
        .expect("snapshot mutex should not be poisoned")
        .clone();
    assert_eq!(recorded.len(), THEORIES * (RESYNC_ROUNDS + 1));
    assert_eq!(
        distinct_allocations(&recorded),
        2,
        "a term-set change should rebuild the shared snapshot exactly once"
    );
    let (old, new) = recorded.split_at(THEORIES * RESYNC_ROUNDS);
    assert!(new.iter().all(|s| s.len() == TERM_COUNT + 1));
    assert!(new.iter().all(|s| !Arc::ptr_eq(s, &old[0])));
    assert!(new.iter().all(|s| Arc::ptr_eq(s, &new[0])));
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
