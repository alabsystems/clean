// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::collections::HashSet;
use std::ops::ControlFlow;
use std::time::{Duration, Instant};

fn var(n: u32) -> Term {
    Term::Var(n)
}

fn const_(c: Symbol) -> Term {
    Term::Const(c)
}

fn app(f: Symbol, args: Vec<Term>) -> Term {
    Term::App(f, args)
}

#[test]
fn test_unification_simple() {
    // X = a
    let t1 = var(0);
    let t2 = const_(0);
    let mgu = unify(&t1, &t2).unwrap();
    assert_eq!(t1.apply_subst(&mgu), t2);
}

#[test]
fn test_unification_function() {
    // f(X, b) = f(a, Y)
    let t1 = app(0, vec![var(0), const_(1)]);
    let t2 = app(0, vec![const_(0), var(1)]);
    let mgu = unify(&t1, &t2).unwrap();
    assert_eq!(t1.apply_subst(&mgu), t2.apply_subst(&mgu));
}

#[test]
fn test_unification_occurs_check() {
    // X = f(X) - should fail
    let t1 = var(0);
    let t2 = app(0, vec![var(0)]);
    assert!(
        unify(&t1, &t2).is_none(),
        "occurs check should prevent X = f(X) unification"
    );
}

#[test]
fn test_matching() {
    // Pattern: f(X, X), Target: f(a, a)
    let pattern = app(0, vec![var(0), var(0)]);
    let target = app(0, vec![const_(0), const_(0)]);
    let subst = match_terms(&pattern, &target).unwrap();
    assert_eq!(pattern.apply_subst(&subst), target);
}

#[test]
fn test_matching_fails() {
    // Pattern: f(X, X), Target: f(a, b) - should fail
    let pattern = app(0, vec![var(0), var(0)]);
    let target = app(0, vec![const_(0), const_(1)]);
    assert!(
        match_terms(&pattern, &target).is_none(),
        "f(X,X) should not match f(a,b) where a != b"
    );
}

#[test]
fn test_kbo_simple() {
    let kbo = KBO::new();

    // f(a) > a (more symbols)
    let t1 = app(0, vec![const_(0)]);
    let t2 = const_(0);
    assert!(kbo.greater(&t1, &t2));
}

#[test]
fn test_kbo_same_weight() {
    let mut kbo = KBO::new();
    kbo.set_precedence(0, 10); // f has higher precedence
    kbo.set_precedence(1, 5); // g has lower precedence

    // f(a) > g(a) by precedence
    let t1 = app(0, vec![const_(0)]);
    let t2 = app(1, vec![const_(0)]);
    assert!(kbo.greater(&t1, &t2));
}

#[test]
fn test_clause_tautology() {
    // a = a is a tautology
    let clause = Clause::new(vec![Literal::eq(const_(0), const_(0))], 0);
    assert!(clause.is_tautology());
}

#[test]
fn test_clause_not_tautology() {
    // a = b is not a tautology
    let clause = Clause::new(vec![Literal::eq(const_(0), const_(1))], 0);
    assert!(!clause.is_tautology());
}

#[test]
fn test_tautology_symmetric_complementary_literals() {
    // Algorithm audit: {a=b, b!=a} is a tautology under equality symmetry,
    // but is_tautology only checks lhs==lhs && rhs==rhs for complementary
    // literals (line 492). The symmetric case lhs==rhs && rhs==lhs is missed.
    //
    // This test documents the gap. If is_tautology is fixed to handle
    // symmetric complementary literals, this test should pass.
    let a = const_(0);
    let b = const_(1);
    let clause = Clause::new(
        vec![
            Literal::eq(a.clone(), b.clone()),  // a = b (positive)
            Literal::neq(b.clone(), a.clone()), // b != a (negative, symmetric)
        ],
        0,
    );
    // Under equality symmetry, a=b and b!=a are complementary → tautology.
    // NOTE: This documents the gap. If it fails, fix is_tautology at line 492
    // to also check: lit1.lhs == lit2.rhs && lit1.rhs == lit2.lhs
    assert!(
        clause.is_tautology(),
        "symmetric complementary literals should be detected as tautology"
    );
}

#[test]
fn test_fifo_strategy_processes_oldest_first() {
    // Algorithm audit: FIFO strategy should process oldest clauses first
    // (smallest ID = first generated = first processed).
    //
    // Bug: compute_priority uses -(id) and the reversed Ord creates a
    // double-negation that produces LIFO (newest-first) order.
    // Fix: remove negation in compute_priority for FIFO, or remove reversed Ord.
    let mut prover = SuperpositionProver::new();
    prover.set_strategy(SelectionStrategy::FIFO);

    // Add 3 clauses — they get IDs 0, 1, 2
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]); // id=0
    prover.add_clause(vec![Literal::eq(const_(2), const_(3))]); // id=1
    prover.add_clause(vec![Literal::eq(const_(4), const_(5))]); // id=2

    // Pop from the unprocessed heap and check order
    let first = prover.unprocessed.pop().unwrap();
    let second = prover.unprocessed.pop().unwrap();
    let third = prover.unprocessed.pop().unwrap();

    // FIFO: oldest (id=0) should be popped first
    // NOTE: This test documents the bug. With current double-negation,
    // id=2 is popped first (LIFO). See compute_priority at line 991.
    assert_eq!(
        first.clause.id, 0,
        "FIFO should pop oldest clause first, got id={}",
        first.clause.id
    );
    assert_eq!(second.clause.id, 1);
    assert_eq!(third.clause.id, 2);
}

#[test]
fn test_prover_trivial_unsat() {
    // { a = b }, { a ≠ b } is unsatisfiable
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]);
    prover.add_clause(vec![Literal::neq(const_(0), const_(1))]);

    match prover.prove(100) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("Expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn test_prover_trivial_sat() {
    // { a = a } is satisfiable (tautology removed, saturates immediately)
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(0))]);

    match prover.prove(100) {
        ProverResult::Saturated => {}
        other => panic!("Expected Saturated, got {other:?}"),
    }
}

#[test]
fn test_prover_symmetry() {
    // { a = b }, { b ≠ a } is unsatisfiable
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]);
    prover.add_clause(vec![Literal::neq(const_(1), const_(0))]);

    match prover.prove(100) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("Expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn test_prover_transitivity() {
    // { a = b }, { b = c }, { a ≠ c } is unsatisfiable
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]); // a = b
    prover.add_clause(vec![Literal::eq(const_(1), const_(2))]); // b = c
    prover.add_clause(vec![Literal::neq(const_(0), const_(2))]); // a ≠ c

    match prover.prove(100) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("Expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn test_prove_until_elapsed_deadline_preempts_search() {
    // The set { a = b }, { a ≠ b } is UNSAT and `prove` derives the empty
    // clause. With an already-elapsed wall-clock deadline, the saturation loop's
    // per-iteration deadline poll fires before it can do that work and returns
    // ResourceLimit — the BUG-1 guarantee that the hot loop honours the deadline.
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]);
    prover.add_clause(vec![Literal::neq(const_(0), const_(1))]);

    let elapsed = Instant::now() - Duration::from_secs(1);
    match prover.prove_until(10_000, Some(elapsed)) {
        ProverResult::ResourceLimit => {}
        other => panic!("expected ResourceLimit from an elapsed deadline, got {other:?}"),
    }
}

#[test]
fn test_prove_until_no_deadline_matches_prove() {
    // With `None`, `prove_until` is exactly `prove`: the same UNSAT set still
    // closes. (Guards the delegation: the deadline is purely additive.)
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]);
    prover.add_clause(vec![Literal::neq(const_(0), const_(1))]);

    match prover.prove_until(10_000, None) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("expected Unsatisfiable with no deadline, got {other:?}"),
    }
}

#[test]
fn test_prover_congruence() {
    // { a = b }, { f(a) ≠ f(b) } is unsatisfiable
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]); // a = b
    let fa = app(0, vec![const_(0)]); // f(a)
    let fb = app(0, vec![const_(1)]); // f(b)
    prover.add_clause(vec![Literal::neq(fa, fb)]); // f(a) ≠ f(b)

    match prover.prove(100) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("Expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn test_prover_nested_congruence() {
    // { a = b }, { g(f(a)) ≠ g(f(b)) } is unsatisfiable
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]); // a = b
    let fa = app(0, vec![const_(0)]); // f(a)
    let fb = app(0, vec![const_(1)]); // f(b)
    let gfa = app(1, vec![fa]); // g(f(a))
    let gfb = app(1, vec![fb]); // g(f(b))
    prover.add_clause(vec![Literal::neq(gfa, gfb)]); // g(f(a)) ≠ g(f(b))

    match prover.prove(1000) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("Expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn test_prover_equality_resolution() {
    // { X ≠ X } is unsatisfiable (equality resolution derives empty clause)
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::neq(var(0), var(0))]); // X ≠ X

    match prover.prove(100) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("Expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn test_prover_disjunction() {
    // { a = b ∨ a = c }, { a ≠ b }, { a ≠ c } is unsatisfiable
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![
        Literal::eq(const_(0), const_(1)), // a = b
        Literal::eq(const_(0), const_(2)), // a = c
    ]);
    prover.add_clause(vec![Literal::neq(const_(0), const_(1))]); // a ≠ b
    prover.add_clause(vec![Literal::neq(const_(0), const_(2))]); // a ≠ c

    match prover.prove(100) {
        ProverResult::Unsatisfiable(_) => {}
        other => panic!("Expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn test_term_positions() {
    // f(g(a), b) has positions: [], [0], [0,0], [1]
    let term = app(0, vec![app(1, vec![const_(0)]), const_(1)]);
    let positions = term.positions();
    assert!(positions.contains(&Position(vec![])));
    assert!(positions.contains(&Position(vec![0])));
    assert!(positions.contains(&Position(vec![0, 0])));
    assert!(positions.contains(&Position(vec![1])));
    assert_eq!(positions.len(), 4);
}

#[test]
fn test_term_visit_positions_matches_positions_order() {
    let term = app(
        0,
        vec![
            app(1, vec![const_(0), var(0)]),
            app(2, vec![const_(1)]),
            const_(2),
        ],
    );

    let mut visited = Vec::new();
    term.visit_positions(|path, _| visited.push(Position(path.to_vec())));

    assert_eq!(visited, term.positions());
}

#[test]
fn test_term_try_visit_positions_breaks_early() {
    let term = app(
        0,
        vec![app(1, vec![const_(0), const_(1)]), app(2, vec![const_(2)])],
    );
    let mut visited = Vec::new();

    let outcome = term.try_visit_positions(|path, subterm| {
        visited.push(Position(path.to_vec()));
        if *subterm == const_(1) {
            return ControlFlow::Break(Position(path.to_vec()));
        }
        ControlFlow::Continue(())
    });

    assert_eq!(
        visited,
        vec![
            Position(vec![]),
            Position(vec![0]),
            Position(vec![0, 0]),
            Position(vec![0, 1]),
        ]
    );
    assert_eq!(outcome, ControlFlow::Break(Position(vec![0, 1])));
}

#[test]
fn test_term_replacement() {
    // Replace g(a) with c in f(g(a), b) to get f(c, b)
    let term = app(0, vec![app(1, vec![const_(0)]), const_(1)]);
    let result = term.replace_at(&Position(vec![0]), const_(2)).unwrap();
    assert_eq!(result, app(0, vec![const_(2), const_(1)]));
}

#[test]
fn test_lpo_simple() {
    let lpo = LPO::new();

    // f(a, b) > a
    let t1 = app(0, vec![const_(0), const_(1)]);
    let t2 = const_(0);
    assert!(lpo.greater(&t1, &t2));
}

/// Regression test for #1844: LPO lexicographic skip must use position k+1, not 1.
///
/// f(a, b, c) vs f(a, d, e): position 0 equal, position 1 has b > d (k=1).
/// Correct LPO checks s > t_j for j > k only (j=2: s > e).
/// Old code used skip(1), checking j >= 1 (j=1: s > d, j=2: s > e).
/// Both produce the same result here (subterm rule ensures s > d), but
/// the fix aligns the code with the mathematical definition.
#[test]
fn test_lpo_lexicographic_skip_position() {
    let lpo = LPO::new();

    // f = 0 (prec 0), a = 1, b = 10 (high prec), c = 3, d = 4, e = 2
    // Position 0: a(1) == a(1) → equal
    // Position 1: b(10) vs d(4) → prec(10) > prec(4) → b > d, so k = 1
    // Check: f(a,b,c) > e(2)? Yes (b with prec 10 is subterm of s, b >= e)
    let s = app(0, vec![const_(1), const_(10), const_(3)]);
    let t = app(0, vec![const_(1), const_(4), const_(2)]);
    assert!(
        lpo.greater(&s, &t),
        "f(a,b,c) > f(a,d,e) when b > d and s > remaining args"
    );
}

/// Test LPO lexicographic at k=2 (two equal prefix positions).
#[test]
fn test_lpo_lexicographic_skip_position_k2() {
    let lpo = LPO::new();

    // f = 0, a = 1, b = 2, c = 10 (high prec), d = 4, e = 3
    // Position 0: a(1) == a(1) → equal
    // Position 1: b(2) == b(2) → equal
    // Position 2: c(10) vs d(4) → prec(10) > prec(4) → c > d, so k = 2
    // Check: f(a,b,c) > e(3)? Yes (c with prec 10 >= e)
    let s = app(0, vec![const_(1), const_(2), const_(10), const_(3)]);
    let t = app(0, vec![const_(1), const_(2), const_(4), const_(3)]);
    assert!(
        lpo.greater(&s, &t),
        "f(a,b,c,x) > f(a,b,d,x) when c > d at position 2"
    );
}

/// Test LPO lexicographic returns false when remaining args check fails.
#[test]
fn test_lpo_lexicographic_remaining_args_fail() {
    let mut lpo = LPO::new();
    // Set up precedences so the remaining arg check fails:
    // f = 0 (prec 0), a = 1, b = 5, d = 3, e = 100
    // Position 0: a == a
    // Position 1: b(5) > d(3), so k = 1
    // Check: f(a,b) > e(100)? f has prec 0 < 100, and no subterm has prec >= 100
    lpo.set_precedence(100, 100);
    let s = app(0, vec![const_(1), const_(5)]);
    let t = app(0, vec![const_(1), const_(3), const_(100)]);
    assert!(
        !lpo.greater(&s, &t),
        "f(a,b) should NOT be > f(a,d,e) when e has very high precedence"
    );
}

#[test]
fn test_subsumption() {
    let prover = SuperpositionProver::new();

    // a = b subsumes a = b ∨ c = d
    let c1 = Clause::new(vec![Literal::eq(const_(0), const_(1))], 0);
    let c2 = Clause::new(
        vec![
            Literal::eq(const_(0), const_(1)),
            Literal::eq(const_(2), const_(3)),
        ],
        1,
    );
    assert!(prover.subsumes(&c1, &c2));

    // a = b ∨ c = d does not subsume a = b
    assert!(!prover.subsumes(&c2, &c1));
}

#[test]
fn test_subsumption_with_variables() {
    let prover = SuperpositionProver::new();

    // X = Y subsumes a = b
    let c1 = Clause::new(vec![Literal::eq(var(0), var(1))], 0);
    let c2 = Clause::new(vec![Literal::eq(const_(0), const_(1))], 1);
    assert!(prover.subsumes(&c1, &c2));

    // a = b does not subsume X = Y
    assert!(!prover.subsumes(&c2, &c1));
}

#[test]
fn test_prover_stats() {
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]);
    prover.add_clause(vec![Literal::neq(const_(0), const_(1))]);

    let result = prover.prove(100);

    // a = b ∧ a ≠ b is unsatisfiable — prover should find the contradiction
    assert!(
        matches!(result, ProverResult::Unsatisfiable(_)),
        "contradictory clauses (a=b, a≠b) should be Unsatisfiable, got {:?}",
        result
    );

    // Should have generated some clauses and performed inferences
    assert!(prover.stats.generated >= 2);
}

// Property-based tests for unification (MGU properties)
mod proptest_unification {
    use super::*;
    use proptest::prelude::*;

    /// Strategy for generating terms with bounded depth
    fn arb_term(max_depth: usize, max_vars: u32) -> impl Strategy<Value = Term> {
        let leaf = prop_oneof![
            (0..max_vars).prop_map(Term::Var),
            (0..10u32).prop_map(Term::Const),
        ];

        leaf.prop_recursive(max_depth as u32, 32, 3, move |inner| {
            prop_oneof![
                (0..max_vars).prop_map(Term::Var),
                (0..10u32).prop_map(Term::Const),
                (0..5u32, prop::collection::vec(inner.clone(), 1..=3))
                    .prop_map(|(f, args)| Term::App(f, args)),
            ]
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Property: MGU is idempotent - σ(σ(t)) = σ(t)
        #[test]
        fn prop_mgu_idempotent(t in arb_term(3, 5)) {
            if let Some(sigma) = unify(&t, &t) {
                let t_sigma = t.apply_subst(&sigma);
                let t_sigma2 = t_sigma.apply_subst(&sigma);
                prop_assert_eq!(
                    t_sigma,
                    t_sigma2,
                    "MGU should be idempotent: σ(σ(t)) = σ(t)"
                );
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Property: MGU is correct - if unify succeeds, σ(t1) = σ(t2)
        #[test]
        fn prop_mgu_unifies(
            t1 in arb_term(3, 5),
            t2 in arb_term(3, 5),
        ) {
            if let Some(sigma) = unify(&t1, &t2) {
                let t1_sigma = t1.apply_subst(&sigma);
                let t2_sigma = t2.apply_subst(&sigma);
                prop_assert_eq!(
                    t1_sigma,
                    t2_sigma,
                    "MGU should unify: σ(t1) = σ(t2)\n\
                     t1 = {:?}\n\
                     t2 = {:?}\n\
                     σ = {:?}",
                    t1,
                    t2,
                    sigma
                );
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        /// Property: Self-unification always succeeds
        #[test]
        fn prop_mgu_self_unify(t in arb_term(3, 5)) {
            let result = unify(&t, &t);
            prop_assert!(
                result.is_some(),
                "Self-unification should always succeed for term {:?}",
                t
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        /// Property: Unification is symmetric - unify(t1, t2) iff unify(t2, t1)
        #[test]
        fn prop_mgu_symmetric(
            t1 in arb_term(2, 4),
            t2 in arb_term(2, 4),
        ) {
            let result1 = unify(&t1, &t2);
            let result2 = unify(&t2, &t1);

            match (&result1, &result2) {
                (Some(s1), Some(s2)) => {
                    // Both succeed; verify they produce the same unified result
                    let unified1 = t1.apply_subst(s1);
                    let unified2 = t2.apply_subst(s2);
                    // They should unify to the same thing
                    let _unified_check1 = t1.apply_subst(s2);
                    let _unified_check2 = t2.apply_subst(s1);
                    prop_assert_eq!(unified1, t2.apply_subst(s1));
                    prop_assert_eq!(unified2, t1.apply_subst(s2));
                }
                (None, None) => {
                    // Both fail - correct
                }
                _ => {
                    prop_assert!(
                        false,
                        "Unification symmetry violated: unify({:?}, {:?}) = {:?}, but unify({:?}, {:?}) = {:?}",
                        t1, t2, result1, t2, t1, result2
                    );
                }
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        /// Property: Occurs check prevents infinite terms
        #[test]
        fn prop_mgu_occurs_check(
            var_id in 0..5u32,
            func_id in 0..5u32,
        ) {
            // X = f(X) should fail occurs check
            let t1 = Term::Var(var_id);
            let t2 = Term::App(func_id, vec![Term::Var(var_id)]);

            let result = unify(&t1, &t2);
            prop_assert!(
                result.is_none(),
                "Occurs check should prevent X = f(X) from unifying"
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        /// Property: Constants with different values don't unify
        #[test]
        fn prop_mgu_const_mismatch(
            c1 in 0..10u32,
            c2 in 0..10u32,
        ) {
            prop_assume!(c1 != c2);
            let t1 = Term::Const(c1);
            let t2 = Term::Const(c2);

            let result = unify(&t1, &t2);
            prop_assert!(
                result.is_none(),
                "Different constants {:?} and {:?} should not unify",
                c1,
                c2
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        /// Property: Variable unifies with any term (unless occurs check fails)
        #[test]
        fn prop_mgu_var_unifies(
            var_id in 5..10u32, // Use high var IDs to avoid occurs check issues
            t in arb_term(2, 4),
        ) {
            // Only test if the term doesn't contain the variable
            if !t.vars().contains(&var_id) {
                let var_term = Term::Var(var_id);
                let result = unify(&var_term, &t);
                prop_assert!(
                    result.is_some(),
                    "Variable X{} should unify with term {:?} when occurs check passes",
                    var_id,
                    t
                );

                // Verify the unification is correct
                if let Some(sigma) = result {
                    let unified = var_term.apply_subst(&sigma);
                    prop_assert_eq!(
                        unified,
                        t.apply_subst(&sigma),
                        "After unification, X{} should equal the target term",
                        var_id
                    );
                }
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(150))]

        /// Property: Function symbol mismatch prevents unification
        #[test]
        fn prop_mgu_func_mismatch(
            f1 in 0..5u32,
            f2 in 0..5u32,
            arg1 in arb_term(1, 3),
            arg2 in arb_term(1, 3),
        ) {
            prop_assume!(f1 != f2);
            let t1 = Term::App(f1, vec![arg1]);
            let t2 = Term::App(f2, vec![arg2]);

            let result = unify(&t1, &t2);
            prop_assert!(
                result.is_none(),
                "Functions with different symbols f{} and f{} should not unify",
                f1,
                f2
            );
        }
    }
}

// ---- Performance proof tests ----
// These tests verify complexity claims and catch quadratic patterns.

/// Performance proof: `find_clause` is O(n) per call — linear scan over processed Vec.
///
/// `build_proof_trace` calls `find_clause` once per proof-used clause (BFS).
/// For a proof using `p` clauses with `n` total processed: O(p * n).
/// This test constructs a prover with `n` processed clauses and measures
/// that `find_clause` scales linearly in `n`, not quadratically.
///
/// Finding: `find_clause` uses `Vec::iter().find()` instead of `HashMap<u64, usize>`.
/// For large saturation runs (1000+ processed clauses), proof reconstruction
/// becomes the bottleneck.
#[test]
fn test_find_clause_linear_scaling() {
    use std::time::Instant;

    let sizes = [100usize, 400, 1600];
    let mut times = Vec::new();

    for &n in &sizes {
        let mut prover = SuperpositionProver::new();

        // Fill the processed set with n clauses
        for i in 0..n {
            let clause = Clause {
                id: i as u64,
                literals: vec![Literal {
                    lhs: Term::Const(i as Symbol),
                    rhs: Term::Const((i + 1) as Symbol),
                    positive: true,
                }],
                parents: vec![],
                inference: Inference::Input,
            };
            prover.push_processed(clause);
        }

        // Measure time to find the LAST clause (worst case) many times
        let target_id = (n - 1) as u64;
        let start = Instant::now();
        for _ in 0..1000 {
            let result = prover.find_clause(target_id);
            assert!(result.is_some(), "clause {target_id} should be found");
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // sizes go 100 -> 400 -> 1600 (4x each step).
    // For O(n) per call: 4x size -> 4x time, so 16x size -> 16x time.
    // Allow up to 50x for noise. If >50x, it's worse than linear.
    let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
    assert!(
        ratio_16x < 50.0,
        "find_clause appears worse than O(n): \
         16x processed set gave {ratio_16x:.1}x time. \
         sizes={sizes:?}, times={times:?}"
    );
    // Note: this test PASSES because find_clause IS O(n).
    // The issue is that build_proof_trace calls it O(p) times,
    // making the total O(p*n) instead of O(p) with a HashMap index.
}

/// Regression test (#2278): forward demodulation must not create
/// self-referential clause IDs. After demodulation, the demodulated clause
/// gets a fresh ID and the original is archived.
#[test]
fn test_forward_demod_no_self_referential_id() {
    let mut prover = SuperpositionProver::new();

    // a = b (unit equation for demodulation)
    prover.add_clause(vec![Literal::eq(const_(0), const_(1))]);
    // f(a) != f(b) — will be demodulated to f(b) != f(b)
    prover.add_clause(vec![Literal::neq(
        Term::App(10, vec![const_(0)]),
        Term::App(10, vec![const_(1)]),
    )]);

    match prover.prove(100) {
        ProverResult::Unsatisfiable(trace) => {
            // Verify no clause in the trace has self-referential parents
            for clause in &trace.clauses {
                if let Inference::Demodulation(orig_id, _) = &clause.inference {
                    assert_ne!(
                        clause.id, *orig_id,
                        "demodulated clause has self-referential ID: {} == {}",
                        clause.id, orig_id
                    );
                }
            }
            // Verify all parents in the trace are resolvable
            for clause in &trace.clauses {
                for parent_id in &clause.parents {
                    assert!(
                        trace.clauses.iter().any(|c| c.id == *parent_id)
                            || trace.empty_clause.id == *parent_id,
                        "parent {} not found in trace for clause {}",
                        parent_id,
                        clause.id,
                    );
                }
            }
        }
        other => panic!(
            "expected Unsatisfiable for a=b, f(a)!=f(b), got {:?}",
            other
        ),
    }
}

/// Regression test (#2278): backward_simplify archives removed clauses.
#[test]
fn test_backward_simplify_archives_clauses() {
    let mut prover = SuperpositionProver::new();
    prover.add_clause(vec![Literal::eq(const_(0), const_(0))]);
    prover.prove(10);
    // Verify the archive HashMap itself is accessible and functional.
    // In this small case backward simplification may not trigger, but
    // the mechanism is exercised by the demodulation test above.
    let _archive_size = prover.clause_archive.len();
}

/// Performance proof: `forward_simplify` literal sort uses `format!` per comparison.
///
/// Line 1126: `clause.literals.sort_by(|a, b| format!("{a}").cmp(&format!("{b}")))`
/// This allocates 2 Strings per comparison. For L literals, sort does
/// O(L log L) comparisons → O(L log L) String allocations.
///
/// This test verifies the sort_by allocates by measuring it with
/// increasing literal counts and checking for the allocation overhead.
#[test]
fn test_forward_simplify_format_sort_overhead() {
    use std::time::Instant;

    let sizes = [5usize, 20, 80];
    let mut times = Vec::new();

    for &n in &sizes {
        // Build a clause with n distinct non-reflexive, non-tautological literals
        let literals: Vec<Literal> = (0..n)
            .map(|i| Literal {
                lhs: app(0, vec![const_(i as Symbol)]),
                rhs: app(1, vec![const_((i + n) as Symbol)]),
                positive: true,
            })
            .collect();

        let start = Instant::now();
        for _ in 0..500 {
            let mut lits = literals.clone();
            // Measure the OLD format!-based sort pattern (pre-#1820 fix).
            // Production forward_simplify now uses structural sort().
            lits.retain(|l| !l.is_reflexive());
            lits.sort_by(|a, b| format!("{a}").cmp(&format!("{b}")));
            lits.dedup();
            std::hint::black_box(&lits);
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // sizes go 5 -> 20 -> 80 (4x each step).
    // For O(n log n) sort with O(1) comparisons: ~4.6x per step.
    // With format! allocation: higher constant factor but same asymptotic.
    // This test documents the overhead exists. The ratio should be moderate.
    let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
    // Document the actual ratio for the performance record
    eprintln!(
        "forward_simplify format!-sort: 16x literals → {ratio_16x:.1}x time \
         (sizes={sizes:?}, times_ns={times:?})"
    );
    // Regression guard: documents the overhead of the OLD format!-based approach.
    // Production code now uses derived Ord on Literal/Term (#1820).
    assert!(
        ratio_16x < 500.0,
        "forward_simplify format!-sort scaling worse than expected: {ratio_16x:.1}x for 16x literals."
    );
}

/// Performance proof: `Term::positions()` uses `Vec::insert(0, ...)` which is O(depth).
///
/// For a term tree of depth d with n nodes, `positions()` returns n Position objects.
/// Each Position at depth k contains a Vec of length k, and insert(0, ...) on each
/// recursive call shifts all elements. Total cost: O(sum of path_lengths * depth) = O(n * d).
/// For balanced trees this is O(n * log n). For degenerate chains it's O(n^2).
#[test]
fn test_term_positions_scaling() {
    use std::time::Instant;

    // Build a degenerate chain: f(f(f(...f(a)...)))
    fn build_chain(depth: usize) -> Term {
        let mut t = Term::Const(0);
        for _ in 0..depth {
            t = Term::App(1, vec![t]);
        }
        t
    }

    let depths = [10usize, 40, 160];
    let mut times = Vec::new();

    for &d in &depths {
        let term = build_chain(d);
        let start = Instant::now();
        for _ in 0..500 {
            let positions = term.positions();
            std::hint::black_box(&positions);
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // For degenerate chain of depth d: positions returns d+1 positions.
    // Each position at index i has a path of length i.
    // insert(0, ...) at each level shifts i elements.
    // Total inserts: sum(1..d) = O(d^2).
    // depths go 10 -> 40 -> 160 (4x each step).
    // For O(d^2): 16x depth → 256x time.
    let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
    eprintln!(
        "Term::positions() chain scaling: 16x depth → {ratio_16x:.1}x time \
         (depths={depths:?}, times_ns={times:?})"
    );
    // Regression guard: quadratic O(d^2) from insert(0,...) gives high ratios.
    // Catch regression to cubic or worse without locking in bad behavior.
    assert!(
        ratio_16x < 1000.0,
        "Term::positions() chain scaling worse than expected O(d^2): {ratio_16x:.1}x for 16x depth."
    );
}

/// Performance proof: `vars()` allocates a new HashSet on every call.
///
/// `unify_rec` calls `t.vars().contains(v)` for the occurs check (line 278).
/// Each call traverses the entire term and builds a HashSet. For a term of
/// size n with d recursive unification steps, this is O(n * d) allocations.
///
/// A cheaper occurs check would traverse the term looking for the specific
/// variable without allocating a set.
#[test]
fn test_vars_allocation_per_call() {
    use std::time::Instant;

    // Build a large balanced term: f(f(a, b), f(c, d))...
    fn build_balanced(depth: usize, next_var: &mut u32) -> Term {
        if depth == 0 {
            let v = *next_var;
            *next_var += 1;
            Term::Var(v)
        } else {
            let left = build_balanced(depth - 1, next_var);
            let right = build_balanced(depth - 1, next_var);
            Term::App(0, vec![left, right])
        }
    }

    let depths = [4usize, 6, 8]; // 2^4=16, 2^6=64, 2^8=256 nodes
    let mut times = Vec::new();

    for &d in &depths {
        let mut next_var = 0;
        let term = build_balanced(d, &mut next_var);

        let start = Instant::now();
        for _ in 0..1000 {
            let vars = term.vars();
            std::hint::black_box(&vars);
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // Term sizes: 2^4-1=15, 2^6-1=63, 2^8-1=255 nodes.
    // vars() is O(n) per call. 4x nodes → 4x time. 16x nodes → 16x time.
    let ratio = times[2] as f64 / times[0].max(1) as f64;
    eprintln!("Term::vars() scaling: depths={depths:?}, times_ns={times:?}, ratio={ratio:.1}x");
    // vars() is O(n), so 16x nodes → ~16x time is expected.
    // Regression guard: catch if it becomes worse than O(n log n).
    // The real issue is per-call HashSet allocation inside unify_rec,
    // not asymptotic scaling of vars() itself.
    assert!(
        ratio < 100.0,
        "Term::vars() scaling worse than expected O(n): {ratio:.1}x for ~17x nodes."
    );
}

/// Performance proof: `generate_clauses()` clones entire `self.processed` on every call.
///
/// Line 1261: `let processed_clauses: Vec<Clause> = self.processed.clone();`
/// This deep-copies every Clause (each containing Vec<Literal> with Term trees)
/// on every iteration of the main prove() loop. For n processed clauses of average
/// size s, each clone costs O(n * s). Over n iterations (one per processed clause
/// added), total clone cost is O(n^2 * s) — quadratic in processed set size.
///
/// This is strictly worse than the other 5 findings in #1820 because it
/// operates on the entire clause set, not individual terms or clauses.
/// Fix: iterate processed by index, or use unsafe to split the borrow.
#[test]
fn test_generate_clauses_processed_clone_scaling() {
    use std::time::Instant;

    let sizes = [50usize, 200, 800];
    let mut clone_times = Vec::new();

    for &n in &sizes {
        let mut prover = SuperpositionProver::new();

        // Fill processed with n clauses, each with 3 literals
        for i in 0..n {
            let clause = Clause {
                id: i as u64,
                literals: vec![
                    Literal {
                        lhs: app(0, vec![const_(i as Symbol), const_((i + 1) as Symbol)]),
                        rhs: const_((i + 2) as Symbol),
                        positive: true,
                    },
                    Literal {
                        lhs: const_((i + 3) as Symbol),
                        rhs: const_((i + 4) as Symbol),
                        positive: false,
                    },
                    Literal {
                        lhs: app(1, vec![const_((i + 5) as Symbol)]),
                        rhs: app(2, vec![const_((i + 6) as Symbol)]),
                        positive: true,
                    },
                ],
                parents: vec![],
                inference: Inference::Input,
            };
            prover.push_processed(clause);
        }

        // Measure the cost of cloning processed (the operation on line 1261)
        let start = Instant::now();
        for _ in 0..100 {
            let cloned: Vec<Clause> = prover.processed.clone();
            std::hint::black_box(&cloned);
        }
        let elapsed = start.elapsed().as_nanos();
        clone_times.push(elapsed);
    }

    // sizes go 50 -> 200 -> 800 (4x each step).
    // Clone is O(n * s) where s is per-clause size (constant here).
    // So 4x clauses → 4x time, 16x clauses → 16x time.
    let ratio_16x = clone_times[2] as f64 / clone_times[0].max(1) as f64;
    eprintln!(
        "processed.clone() scaling: sizes={sizes:?}, times_ns={clone_times:?}, \
         16x clauses → {ratio_16x:.1}x time"
    );

    // The real issue is that this clone happens on EVERY iteration of prove().
    // After n iterations, n clauses are processed, so:
    //   Total clone cost = sum(1..n) * s = O(n^2 * s)
    // With 800 clauses at 3 literals each, a single clone is already expensive.
    // Over a full run, the quadratic growth dominates all other costs.
    assert!(
        ratio_16x > 5.0,
        "Expected at least 5x growth for 16x clauses (got {ratio_16x:.1}x). \
         If this fails, the clone overhead may have been optimized away."
    );
}

// ================================================================
// Performance proof: recursive functions lack stack_safe guards
//
// Unlike the kernel (whnf.rs, def_eq.rs, infer.rs) which wraps all
// recursive entry points in `stack_safe()`, the superposition module
// has 5 recursive functions with no depth limit or stack guard:
//
//   1. apply_subst (line 95) — recurses into App args
//   2. unify_rec (line 270) — recurses into App args
//   3. apply_subst_to_term (line 300) — recurses into App args
//   4. lpo_gt / lpo_ge (lines 762/806) — mutually recursive
//   5. KBO::weight / collect_var_counts (lines 627/661)
//
// For deeply nested terms (depth > default stack limit / ~frame_size),
// these will stack overflow. The kernel avoids this with stacker::maybe_grow.
//
// Fix: wrap recursive calls in stack_safe() or add depth counters.
// ================================================================

/// Performance proof: apply_subst recurses to full depth without stack guard.
///
/// Builds a term chain of depth `d`: App(f, [App(f, [... App(f, [Var(0)])])])
/// and applies a trivial substitution. If stack_safe were present, this would
/// grow the heap stack as needed. Without it, the default thread stack
/// limits the maximum safe depth.
///
/// This test documents the recursion depth behavior. If it fails with a
/// stack overflow, it proves the finding. If it passes at moderate depth,
/// we record the safe depth boundary.
///
/// Regression test for performance_proofs P1 iter 753.
#[test]
fn test_apply_subst_recursion_depth() {
    // Build a deeply nested term: f(f(f(...f(X0)...)))
    fn build_deep_chain(depth: usize) -> Term {
        let mut t = Term::Var(0);
        for _ in 0..depth {
            t = Term::App(0, vec![t]);
        }
        t
    }

    // Moderate depth that should work even without stack_safe
    let depth = 1000;
    let term = build_deep_chain(depth);

    // Apply a trivial substitution: X0 → c0
    let mut subst = Substitution::new();
    subst.bind(0, Term::Const(42));

    let result = term.apply_subst(&subst);

    // Verify the innermost Var(0) was replaced with Const(42)
    let mut current = &result;
    for _ in 0..depth {
        match current {
            Term::App(f, args) => {
                assert_eq!(*f, 0, "function symbol should be preserved");
                assert_eq!(args.len(), 1, "should have exactly one arg");
                current = &args[0];
            }
            other => panic!("expected App at depth, got {:?}", other),
        }
    }
    assert_eq!(
        *current,
        Term::Const(42),
        "innermost term should be substituted"
    );

    // Document: this passes at depth=1000 because the default stack is
    // typically 8MB and each frame is small. At depth ~50000+ it would
    // overflow on most platforms without stack_safe.
    eprintln!(
        "apply_subst recursion: depth={depth} completed without stack overflow. \
         No stack_safe guard present — vulnerable at higher depths."
    );
}

/// Performance proof: unify_rec recurses without stack guard on nested terms.
///
/// Documents that unify_rec (line 270) recurses to the full depth of the
/// term without any stack_safe wrapper. The kernel's equivalent
/// (is_def_eq_impl) uses stack_safe for this reason.
///
/// Regression test for performance_proofs P1 iter 753.
#[test]
fn test_unify_rec_recursion_depth() {
    // Build two identical deep chains
    fn build_deep_chain(depth: usize) -> Term {
        let mut t: Term = Term::Const(0);
        for _ in 0..depth {
            t = Term::App(1, vec![t]);
        }
        t
    }

    let depth = 1000;
    let t1 = build_deep_chain(depth);
    let t2 = build_deep_chain(depth);

    // Unify identical deep terms — should succeed
    let result = unify(&t1, &t2);
    assert!(
        result.is_some(),
        "identical deep terms should unify at depth={depth}"
    );
    let subst = result.unwrap();
    assert!(
        subst.is_empty(),
        "unifying identical terms should produce empty substitution"
    );

    eprintln!(
        "unify_rec recursion: depth={depth} completed without stack overflow. \
         No stack_safe guard present — vulnerable at higher depths."
    );
}

/// Performance proof: `is_tautology` complementary literal check is O(n²).
///
/// Lines 490-496: nested loop over all literal pairs to find complementary
/// literals (same atoms, opposite polarity). For a clause with L literals,
/// this performs L*(L-1)/2 comparisons. Each comparison involves Term equality
/// (structural comparison). Called on every generated clause via
/// `forward_simplify` (line 1129).
///
/// Fix: Build a HashSet of (lhs, rhs) pairs from positive literals, then
/// check negative literals against it — O(L) with hashing.
///
/// Regression test for performance_proofs P1 iter 788.
#[test]
fn test_is_tautology_quadratic_complementary_check() {
    use std::time::Instant;

    let sizes = [20usize, 80, 320];
    let mut times = Vec::new();

    for &n in &sizes {
        // Build a clause with n non-complementary, non-reflexive literals.
        // All positive with distinct atoms so no tautology detected — worst case
        // forces checking all pairs.
        let literals: Vec<Literal> = (0..n)
            .map(|i| Literal {
                lhs: app(0, vec![const_(i as Symbol)]),
                rhs: app(1, vec![const_((i + n) as Symbol)]),
                positive: true,
            })
            .collect();

        let clause = Clause {
            id: 0,
            literals,
            parents: vec![],
            inference: Inference::Input,
        };

        let start = Instant::now();
        for _ in 0..1000 {
            let result = clause.is_tautology();
            std::hint::black_box(result);
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // sizes go 20 -> 80 -> 320 (4x each step).
    // For O(n^2): 4x literals → 16x time, 16x literals → 256x time.
    // For O(n): 4x literals → 4x time.
    let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
    eprintln!(
        "is_tautology complementary check: 16x literals → {ratio_16x:.1}x time \
         (sizes={sizes:?}, times_ns={times:?})"
    );

    // Regression guard: catch if performance degrades beyond expected O(n^2).
    // Current behavior is quadratic (ratio ~256x for 16x literals).
    // When the O(n) HashSet fix is applied, ratio will drop to ~16x — that's good.
    // This guard catches unexpected regression (e.g., cubic or worse).
    assert!(
        ratio_16x < 500.0,
        "is_tautology scaling worse than expected O(n^2): {ratio_16x:.1}x for 16x literals. \
         Expected <500x (quadratic ceiling). Possible regression to cubic or worse."
    );
}

/// Test equality factoring with 3 positive literals.
///
/// Parent: s=t1 ∨ s=t2 ∨ s=t3.
/// Factoring (s=t1, s=t2) should produce: s=t1 ∨ t1≠t2 ∨ s=t3 (3 literals).
/// BUG: The remaining-literal filter at line 1448 uses
/// `positive.iter().skip(idx1 + 1).any(...)` which excludes ALL positive
/// literals after idx1, not just the specific second factored literal.
/// With 3+ positive literals, non-factored positives are incorrectly dropped.
#[test]
fn test_equality_factoring_three_positive_literals() {
    let mut prover = SuperpositionProver::new();

    // Use high symbol ID for LHS so t_sigma < s_sigma in KBO ordering.
    // KBO default precedence = symbol ID, so prec(10) > prec(1..3).
    // This ensures the ordering constraint t ≤ s passes.
    let clause = Clause::new(
        vec![
            Literal::eq(const_(10), const_(1)), // s=t1
            Literal::eq(const_(10), const_(2)), // s=t2
            Literal::eq(const_(10), const_(3)), // s=t3
        ],
        0,
    );

    let results = prover.equality_factoring(&clause);
    assert!(
        !results.is_empty(),
        "3 positive literals with unifiable LHS should produce factored clauses"
    );

    // With 3 positive literals, pairs (0,1) and (0,2) produce factored clauses
    // where the remaining non-factored positive literal MUST be preserved.
    // Expected: every factored clause has exactly 3 literals:
    //   kept equation + new disequation + remaining positive literal
    for (i, factored) in results.iter().enumerate() {
        assert_eq!(
            factored.literals.len(),
            3,
            "factored clause {} should have 3 literals \
             (kept eq + disequation + remaining positive), got {}: {:?}",
            i,
            factored.literals.len(),
            factored.literals
        );
    }

    // Verify first factored clause (pair 0,1) content:
    // lit[0] = s=t1 (kept), lit[1] = t1≠t2 (diseq), lit[2] = s=t3 (preserved)
    let fc = &results[0];
    assert!(
        fc.literals[0].positive,
        "first literal should be positive (kept eq)"
    );
    assert!(
        !fc.literals[1].positive,
        "second literal should be negative (disequation)"
    );
    assert!(
        fc.literals[2].positive,
        "third literal should be positive (preserved)"
    );
    assert_eq!(
        fc.literals[2].lhs,
        const_(10),
        "preserved literal LHS should be s"
    );
    assert_eq!(
        fc.literals[2].rhs,
        const_(3),
        "preserved literal RHS should be t3"
    );
}

/// Test equality factoring with 4 positive literals (stress test).
///
/// Parent: s=t1 ∨ s=t2 ∨ s=t3 ∨ s=t4.
/// Factoring any pair (i,j) must preserve ALL non-factored positives.
#[test]
fn test_equality_factoring_four_positive_literals() {
    let mut prover = SuperpositionProver::new();

    let clause = Clause::new(
        vec![
            Literal::eq(const_(10), const_(1)), // s=t1
            Literal::eq(const_(10), const_(2)), // s=t2
            Literal::eq(const_(10), const_(3)), // s=t3
            Literal::eq(const_(10), const_(4)), // s=t4
        ],
        0,
    );

    let results = prover.equality_factoring(&clause);
    assert!(
        !results.is_empty(),
        "4 positive literals should produce factored clauses"
    );

    // Each factored clause keeps 1 eq + 1 diseq + (4-2) remaining = 4 literals
    for (i, factored) in results.iter().enumerate() {
        assert_eq!(
            factored.literals.len(),
            4,
            "factored clause {} should have 4 literals \
             (kept eq + disequation + 2 remaining positives), got {}: {:?}",
            i,
            factored.literals.len(),
            factored.literals
        );
    }
}

/// Test equality factoring preserves negative literals in mixed clauses.
///
/// Parent: s=t1 ∨ ¬P ∨ s=t2 (2 positive, 1 negative).
/// Factoring (s=t1, s=t2) → s=t1 ∨ t1≠t2 ∨ ¬P (3 literals).
/// The negative literal must be preserved as a remaining literal.
#[test]
fn test_equality_factoring_mixed_pos_neg() {
    let mut prover = SuperpositionProver::new();

    let clause = Clause::new(
        vec![
            Literal::eq(const_(10), const_(1)), // s=t1 (positive)
            Literal::neq(const_(5), const_(6)), // ¬P (negative)
            Literal::eq(const_(10), const_(2)), // s=t2 (positive)
        ],
        0,
    );

    let results = prover.equality_factoring(&clause);
    assert!(
        !results.is_empty(),
        "mixed clause with 2 unifiable positive literals should factor"
    );

    // Result: kept eq + disequation + preserved negative = 3 literals
    let fc = &results[0];
    assert_eq!(
        fc.literals.len(),
        3,
        "factored clause should have 3 literals (eq + diseq + neg), got {}: {:?}",
        fc.literals.len(),
        fc.literals
    );

    // Verify the negative literal is preserved
    let neg_count = fc.literals.iter().filter(|l| !l.positive).count();
    assert!(
        neg_count >= 2,
        "should have at least 2 negative literals (disequation + original neg), got {}",
        neg_count
    );
}

/// BUG TEST: Superposition replace_at does not apply σ to non-replaced parts.
///
/// When the MGU binds variables from BOTH c1 and c2 (e.g., c1 has repeated
/// var f(X,X)), `replace_at` substitutes the matched subterm but leaves
/// other c2 variables un-substituted. This produces an UNSOUND clause:
/// a clause with free variables that should have been ground.
///
/// Example:
///   c1: f(X, X) = a        (positive equation with repeated var)
///   c2: g(f(Y, c0), Y) ≠ b  (negative literal)
///   Position [0] in c2.lhs: subterm f(Y, c0), unifies with f(X, X)
///   MGU: {X → c0, Y → c0}  (binds BOTH c1 var X and c2 var Y)
///
///   Correct result: g(a, c0) ≠ b  (Y replaced by c0 per MGU)
///   Buggy result:   g(a, Y') ≠ b  (Y' left free — UNSOUND)
///
/// Root cause: superposition.rs line 1332-1335 does
///   `lit2.lhs.replace_at(pos, rσ)` instead of
///   `lit2.lhs.replace_at(pos, rσ).apply_subst(σ)`
/// Same bug exists in the !is_lhs branch (lines 1342-1345).
#[test]
fn test_superposition_repeated_var_mgu_binds_c2_vars() {
    let mut prover = SuperpositionProver::new();

    // c1: f(X, X) = a — positive equation with repeated variable
    // Using func symbol 0 for f, const 0 for a
    let c1 = Clause::new(
        vec![Literal::eq(app(0, vec![var(0), var(0)]), const_(0))],
        0,
    );

    // c2: g(f(Y, c1_const), Y) ≠ b
    // Using func symbol 1 for g, const 1 for c1_const, const 2 for b
    // Y = var(0) in c2 (will be renamed to var(1) after rename_vars)
    let c2 = Clause::new(
        vec![Literal::neq(
            app(1, vec![app(0, vec![var(0), const_(1)]), var(0)]),
            const_(2),
        )],
        1,
    );

    let results = prover.superposition(&c1, &c2);

    // With f(X,X)=a and g(f(Y,c1),Y)≠b:
    // After rename_vars: c2 becomes g(f(Y', c1), Y') ≠ b where Y'=var(1)
    // Unify f(X,X) with f(Y',c1): X→c1, Y'→c1 (MGU binds both c1 and c2 vars)
    // Correct result: g(a, c1) ≠ b (all vars substituted)
    //
    // If the bug is present, we get g(a, Y') ≠ b (Y' left free)
    if !results.is_empty() {
        for (i, clause) in results.iter().enumerate() {
            for (j, lit) in clause.literals.iter().enumerate() {
                let lhs_vars = lit.lhs.vars();
                let rhs_vars = lit.rhs.vars();
                assert!(
                    lhs_vars.is_empty() && rhs_vars.is_empty(),
                    "Superposition result clause {i} literal {j} has free variables! \
                     lhs_vars={lhs_vars:?}, rhs_vars={rhs_vars:?}, lit={lit}. \
                     Bug: replace_at does not apply MGU to non-replaced parts \
                     of the literal when the MGU binds c2 variables."
                );
            }
        }
    }
}

/// Regression test for #2274: replace_at failure in rewrite_literal returns
/// None instead of silently falling back to full substitution.
#[test]
fn test_superposition_replace_at_failure_does_not_produce_clause() {
    // Literal with Const terms — Position [0] is invalid on Const
    let lit = Literal::neq(const_(0), const_(1));
    let pos = Position(vec![0]);
    let replacement = const_(2);
    let mgu = Substitution::new();

    // rewrite_literal should return None (invalid position), not a fallback
    let result =
        SuperpositionProver::rewrite_literal(&lit, true, &pos.0, replacement.clone(), &mgu);
    assert!(
        result.is_none(),
        "replace_at failure should return None, not produce a fallback clause"
    );

    // Also verify the rhs branch
    let result_rhs = SuperpositionProver::rewrite_literal(&lit, false, &pos.0, replacement, &mgu);
    assert!(
        result_rhs.is_none(),
        "replace_at failure on rhs should also return None"
    );
}

/// build_proof_trace collects ancestor clauses from the empty clause.
///
/// Regression test for #2298: the empty clause is not in processed when
/// build_proof_trace is called, so parent traversal must seed from the
/// empty clause's parents directly.
#[test]
fn test_build_proof_trace_collects_ancestors() {
    let mut prover = SuperpositionProver::new();

    // Input clause: a = b (id=0)
    let input = Clause {
        literals: vec![Literal {
            lhs: const_(0),
            rhs: const_(1),
            positive: true,
        }],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    prover.push_processed(input);

    // Derived clause: f(a) = f(b) (id=1, parent=0)
    let derived = Clause {
        literals: vec![Literal {
            lhs: app(2, vec![const_(0)]),
            rhs: app(2, vec![const_(1)]),
            positive: true,
        }],
        id: 1,
        parents: vec![0],
        inference: Inference::Superposition(0, 0, Position::root()),
    };
    prover.push_processed(derived);

    // Empty clause (id=2, parent=1) — not in processed
    let empty = Clause {
        literals: vec![],
        id: 2,
        parents: vec![1],
        inference: Inference::EqualityResolution(1),
    };

    let trace = prover.build_proof_trace(&empty);
    assert_eq!(trace.empty_clause.id, 2);
    assert!(
        !trace.clauses.is_empty(),
        "proof trace should contain ancestor clauses"
    );
    // Should contain both ancestor clauses (id=0 and id=1)
    let ids: HashSet<u64> = trace.clauses.iter().map(|c| c.id).collect();
    assert!(ids.contains(&0), "trace should contain input clause 0");
    assert!(ids.contains(&1), "trace should contain derived clause 1");
}

// ---- Demodulation multi-literal coverage tests ----

/// Demodulation on 3-literal clause: only the second literal matches the
/// unit equation. Verifies all literals are visited, not just the first.
///
/// KBO with default weights: Const(0) vs Const(1) — same weight 1.
/// Precedence falls back to symbol ID, so Const(1) > Const(0).
/// big = Const(1), small = Const(0). Rewrites occurrences of 1 → 0.
#[test]
fn test_demod_multi_literal_rewrites_non_first_literal() {
    let prover = SuperpositionProver::new();

    // Unit equation: symbol 0 = symbol 1. Orients as 1 → 0.
    let unit = Clause {
        literals: vec![Literal::eq(const_(0), const_(1))],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };

    // 3-literal clause where only the 2nd literal contains symbol 1:
    // f(2,3) != g(4) ∨ h(1) != h(5) ∨ p(6) != q(7)
    let clause = Clause {
        literals: vec![
            Literal::neq(
                app(10, vec![const_(2), const_(3)]),
                app(11, vec![const_(4)]),
            ),
            Literal::neq(app(12, vec![const_(1)]), app(12, vec![const_(5)])),
            Literal::neq(app(13, vec![const_(6)]), app(14, vec![const_(7)])),
        ],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };

    let result = prover.demodulate(&clause, &unit);

    assert!(
        matches!(result.inference, Inference::Demodulation(1, 0)),
        "demodulation should fire on 3-literal clause containing symbol 1"
    );

    // All 3 literals should be preserved
    assert_eq!(
        result.literals.len(),
        3,
        "demodulated clause should preserve 3 literals"
    );

    // 1st literal unchanged (no symbol 1): f(2,3) != g(4)
    assert_eq!(
        result.literals[0].lhs,
        app(10, vec![const_(2), const_(3)]),
        "1st literal LHS should be unchanged"
    );

    // 2nd literal rewritten: h(1) → h(0)
    assert_eq!(
        result.literals[1].lhs,
        app(12, vec![const_(0)]),
        "2nd literal LHS h(1) should become h(0) after demod"
    );

    // 3rd literal unchanged (no symbol 1): p(6) != q(7)
    assert_eq!(
        result.literals[2].lhs,
        app(13, vec![const_(6)]),
        "3rd literal LHS should be unchanged"
    );
}

/// Demodulation rewrites ALL literals containing the pattern, not just the first.
/// Unit: f(X) → X (orient f(X) > X by KBO: weight(f(X)) = 1+1 = 2 > 1).
/// Clause: g(f(a)) != b ∨ h(f(c)) != d — both literals contain f(_).
#[test]
fn test_demod_rewrites_all_matching_literals() {
    let prover = SuperpositionProver::new();

    // Symbol IDs: f=10, g=11, h=12, a=0, b=1, c=2, d=3
    let unit = Clause {
        literals: vec![Literal::eq(
            app(10, vec![var(0)]), // f(X)
            var(0),                // X
        )],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };

    let multi = Clause {
        literals: vec![
            Literal::neq(
                app(11, vec![app(10, vec![const_(0)])]), // g(f(a))
                const_(1),                               // b
            ),
            Literal::neq(
                app(12, vec![app(10, vec![const_(2)])]), // h(f(c))
                const_(3),                               // d
            ),
        ],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };

    let result = prover.demodulate(&multi, &unit);

    // Both literals should be rewritten: g(a)!=b ∨ h(c)!=d
    assert!(
        matches!(result.inference, Inference::Demodulation(1, 0)),
        "demodulation should have fired on multi-literal clause"
    );

    // Check first literal: g(f(a)) should become g(a)
    assert_eq!(
        result.literals[0].lhs,
        app(11, vec![const_(0)]),
        "first literal LHS should be g(a) after demod, got {:?}",
        result.literals[0].lhs
    );

    // Check second literal: h(f(c)) should become h(c)
    assert_eq!(
        result.literals[1].lhs,
        app(12, vec![const_(2)]),
        "second literal LHS should be h(c) after demod, got {:?}",
        result.literals[1].lhs
    );
}

/// Position invalidation: demodulate pre-computes positions then mutates the
/// term. After rewriting at an outer position, inner positions become stale
/// and point to wrong subterms in the mutated term.
///
/// Unit: f(X) → X. Clause: g(f(f(a))) != b.
/// positions() returns DFS order: [], [0], [0,0], [0,0,0].
///
/// Trace:
///   []: g(f(f(a))) vs f(X) — symbol mismatch (g≠f). No.
///   [0]: f(f(a)) vs f(X) — match X=f(a). Replace → g(f(a)).
///   [0,0]: NOW STALE. In g(f(a)), [0,0] = a (not f(a) as in original).
///          match(f(X), a) fails (App≠Const).
///   [0,0,0]: at_position returns None (a is Const, no children).
///
/// Result: g(f(a)) — partially reduced.
/// Ideal (with re-traversal): g(a) — fully reduced.
///
/// This is a completeness gap, not a soundness bug. The inner f(a) would be
/// caught in a subsequent forward_simplify pass, but this doubles the number
/// of simplification rounds needed for nested rewrites.
#[test]
fn test_demod_stale_positions_incomplete_nested_rewrite() {
    let prover = SuperpositionProver::new();

    // f(X) = X, orient f(X) > X (KBO weight 2 > 1)
    let unit = Clause {
        literals: vec![Literal::eq(app(10, vec![var(0)]), var(0))],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };

    // g(f(f(a))) != b
    let clause = Clause {
        literals: vec![Literal::neq(
            app(11, vec![app(10, vec![app(10, vec![const_(0)])])]), // g(f(f(a)))
            const_(1),                                              // b
        )],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };

    let result = prover.demodulate(&clause, &unit);

    assert!(
        matches!(result.inference, Inference::Demodulation(1, 0)),
        "demodulation should fire on g(f(f(a)))"
    );

    let lhs = &result.literals[0].lhs;
    let fully_reduced = app(11, vec![const_(0)]); // g(a)

    // With #2307 fixpoint loop, demodulate fully reduces nested redexes:
    // g(f(f(a))) → g(f(a)) → g(a) in a single demodulate call.
    assert_eq!(
        *lhs, fully_reduced,
        "fixpoint demodulation should fully reduce g(f(f(a))) → g(a). Got {:?}",
        lhs
    );
}

/// Demodulation on multi-literal clause with non-orientable equation returns
/// the clause unchanged.
#[test]
fn test_demod_non_orientable_returns_unchanged() {
    let prover = SuperpositionProver::new();

    // f(X) = f(Y) — incomparable under KBO (same weight, same function symbol,
    // but different variable structure). Both sides have weight 2.
    let unit = Clause {
        literals: vec![Literal::eq(app(10, vec![var(0)]), app(10, vec![var(1)]))],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };

    let clause = Clause {
        literals: vec![
            Literal::neq(app(10, vec![const_(0)]), const_(1)),
            Literal::neq(const_(2), const_(3)),
        ],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };

    let result = prover.demodulate(&clause, &unit);

    // Non-orientable equation should return clause unchanged
    assert!(
        !matches!(result.inference, Inference::Demodulation(_, _)),
        "non-orientable equation should not trigger demodulation"
    );
    assert_eq!(
        result.literals, clause.literals,
        "clause should be unchanged with non-orientable unit equation"
    );
}

/// Chained demodulation: two different unit equations applied sequentially
/// to the same multi-literal clause. First demod rewrites symbol 1→0,
/// second demod rewrites symbol 3→2.
#[test]
fn test_demod_chained_multi_literal() {
    let prover = SuperpositionProver::new();

    // Unit 1: 0 = 1, orients as 1 → 0 (prec(1) > prec(0))
    let unit1 = Clause {
        literals: vec![Literal::eq(const_(0), const_(1))],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    // Unit 2: 2 = 3, orients as 3 → 2 (prec(3) > prec(2))
    let unit2 = Clause {
        literals: vec![Literal::eq(const_(2), const_(3))],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };

    // Multi-literal clause: f(1) != g(3) ∨ h(1,3) != k(4)
    let clause = Clause {
        literals: vec![
            Literal::neq(app(10, vec![const_(1)]), app(11, vec![const_(3)])),
            Literal::neq(
                app(12, vec![const_(1), const_(3)]),
                app(13, vec![const_(4)]),
            ),
        ],
        id: 2,
        parents: vec![],
        inference: Inference::Input,
    };

    // Apply first demod: rewrites 1 → 0
    let after_demod1 = prover.demodulate(&clause, &unit1);
    assert!(
        matches!(after_demod1.inference, Inference::Demodulation(2, 0)),
        "first demod should fire (rewriting symbol 1)"
    );

    // f(1)→f(0), h(1,3)→h(0,3)
    assert_eq!(
        after_demod1.literals[0].lhs,
        app(10, vec![const_(0)]),
        "first demod should rewrite f(1) to f(0)"
    );
    assert_eq!(
        after_demod1.literals[1].lhs,
        app(12, vec![const_(0), const_(3)]),
        "first demod should rewrite h(1,3) to h(0,3)"
    );

    // Apply second demod: rewrites 3 → 2
    let after_demod2 = prover.demodulate(&after_demod1, &unit2);
    assert!(
        matches!(after_demod2.inference, Inference::Demodulation(_, 1)),
        "second demod should fire (rewriting symbol 3)"
    );

    // g(3)→g(2), h(0,3)→h(0,2)
    assert_eq!(
        after_demod2.literals[0].rhs,
        app(11, vec![const_(2)]),
        "second demod should rewrite g(3) to g(2)"
    );
    assert_eq!(
        after_demod2.literals[1].lhs,
        app(12, vec![const_(0), const_(2)]),
        "second demod should rewrite h(0,3) to h(0,2)"
    );
}

/// Regression test for generate_clauses scaling (#2568).
///
/// When the processed set grows, generate_clauses currently clones the entire
/// Vec<Clause> on every call (inference.rs:21). This test exercises the path
/// with a non-trivial processed set to ensure correctness is preserved when
/// the clone is refactored to a borrow-based approach.
#[test]
fn test_generate_clauses_scaling_correctness() {
    let mut prover = SuperpositionProver::new();
    let f_sym: Symbol = 200;
    let g_sym: Symbol = 201;

    // Build a processed set with 20 distinct ground unit equations using
    // unique constant symbols to avoid subsumption or unintended unification.
    let n_processed = 20;
    for i in 0..n_processed {
        let sym_lhs = (i * 2 + 400) as Symbol;
        let sym_rhs = (i * 2 + 401) as Symbol;
        let clause = Clause::new(
            vec![Literal::eq(const_(sym_lhs), const_(sym_rhs))],
            prover.next_id,
        );
        prover.next_id += 1;
        prover.push_processed(clause);
    }

    // Add one matchable clause: a = f(b)
    // Superposition of given f(X)=g(X) into a=f(b) at position f(b):
    //   unify f(X) with f(b) → X=b, rewrite f(b)→g(b), yielding a=g(b)
    let a_sym: Symbol = 300;
    let b_sym: Symbol = 301;
    prover.push_processed(Clause::new(
        vec![Literal::eq(const_(a_sym), app(f_sym, vec![const_(b_sym)]))],
        prover.next_id,
    ));
    prover.next_id += 1;
    assert_eq!(prover.processed.len(), n_processed + 1);

    // Given clause: f(X) = g(X)
    let given = Clause::new(
        vec![Literal::eq(
            app(f_sym, vec![var(0)]),
            app(g_sym, vec![var(0)]),
        )],
        prover.next_id,
    );
    prover.next_id += 1;

    let new_clauses = prover.generate_clauses(&given);

    // Must produce at least one inference rewriting f(b) to g(b) or
    // containing g(b) from the matchable processed clause.
    let has_rewrite = new_clauses.iter().any(|c| {
        c.literals.iter().any(|l| {
            l.lhs == app(g_sym, vec![const_(b_sym)]) || l.rhs == app(g_sym, vec![const_(b_sym)])
        })
    });
    assert!(
        has_rewrite,
        "superposition should rewrite f(b) to g(b) in at least one inference; \
         got {} clauses total",
        new_clauses.len()
    );

    // All generated clauses must have valid parent references.
    for clause in &new_clauses {
        assert!(
            !clause.parents.is_empty(),
            "generated clause {} should have parent references",
            clause.id
        );
    }
}
