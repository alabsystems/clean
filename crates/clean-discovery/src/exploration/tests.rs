// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::exploration_patterns::FuncSig;
use clean_kernel::{BinderInfo, Level};

fn nat_sig(name: &str, arity: u32) -> FuncSig {
    FuncSig {
        name: name.to_string(),
        arity,
        sort: Expr::const_str("Nat"),
    }
}

/// Build `@Eq Nat lhs rhs`.
fn mk_eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), lhs, rhs],
    )
}

/// Wrap `body` in `n` `forall (_ : Nat),` binders.
fn forall_nat(n: u32, body: Expr) -> Expr {
    let mut stmt = body;
    for _ in 0..n {
        stmt = Expr::pi(BinderInfo::Default, Expr::const_str("Nat"), stmt);
    }
    stmt
}

#[test]
fn test_exploration_config_default() {
    let config = ExplorationConfig::default();
    assert_eq!(config.max_depth, 3);
    assert_eq!(config.max_terms, 1000);
    assert_eq!(config.counterexample_samples, 100);
    assert_eq!(config.eq_const, "Eq");
}

#[test]
fn test_exploration_state_dedup() {
    let mut state = ExplorationState::new();
    let stmt = Expr::prop();
    assert!(!state.is_known(&stmt));

    state.add_lemma(DiscoveredLemma {
        statement: stmt.clone(),
        description: "test".to_string(),
        pattern: TermPattern::Equality,
        func_names: vec!["f".to_string()],
        depth: 0,
    });
    assert!(state.is_known(&stmt));
    assert_eq!(state.known_lemmas.len(), 1);
}

#[test]
fn test_counterexample_filter_rejects_idempotent_add() {
    let filter = CounterexampleFilter::new(100);
    let candidate = CandidateEquation {
        pattern: TermPattern::Idempotency,
        statement: Expr::prop(),
        description: "Nat.add is idempotent".to_string(),
        func_names: vec!["Nat.add".to_string()],
    };
    assert!(
        !filter.survives(&candidate),
        "add(a,a) = a should be rejected"
    );
}

#[test]
fn test_counterexample_filter_allows_commutativity() {
    let filter = CounterexampleFilter::new(100);
    let candidate = CandidateEquation {
        pattern: TermPattern::Commutativity,
        statement: Expr::prop(),
        description: "Nat.add is commutative".to_string(),
        func_names: vec!["Nat.add".to_string()],
    };
    assert!(
        filter.survives(&candidate),
        "add commutativity should survive"
    );
}

#[test]
fn test_counterexample_filter_rejects_wrong_distributivity() {
    let filter = CounterexampleFilter::new(100);
    let candidate = CandidateEquation {
        pattern: TermPattern::Distributivity,
        statement: Expr::prop(),
        description: "add distributes over mul".to_string(),
        func_names: vec!["Nat.add".to_string(), "Nat.mul".to_string()],
    };
    assert!(
        !filter.survives(&candidate),
        "add over mul should be rejected"
    );
}

#[test]
fn test_counterexample_filter_allows_correct_distributivity() {
    let filter = CounterexampleFilter::new(100);
    let candidate = CandidateEquation {
        pattern: TermPattern::Distributivity,
        statement: Expr::prop(),
        description: "mul distributes over add".to_string(),
        func_names: vec!["Nat.mul".to_string(), "Nat.add".to_string()],
    };
    assert!(filter.survives(&candidate), "mul over add should survive");
}

#[test]
fn test_counterexample_filter_identity_add() {
    let filter = CounterexampleFilter::new(100);
    let add_identity = CandidateEquation {
        pattern: TermPattern::Identity,
        statement: Expr::prop(),
        description: "Nat.add has right identity 0".to_string(),
        func_names: vec!["Nat.add".to_string()],
    };
    assert!(filter.survives(&add_identity));

    let mul_identity = CandidateEquation {
        pattern: TermPattern::Identity,
        statement: Expr::prop(),
        description: "Nat.mul has right identity 0".to_string(),
        func_names: vec!["Nat.mul".to_string()],
    };
    assert!(
        !filter.survives(&mul_identity),
        "mul identity with 0 should be rejected"
    );
}

#[test]
fn test_pattern_generator_basic() {
    let sigs = vec![nat_sig("Nat.add", 2), nat_sig("Nat.mul", 2)];
    let generator = PatternGenerator::new(
        sigs,
        vec![TermPattern::Commutativity, TermPattern::Associativity],
        "Eq",
    );
    let candidates = generator.generate();
    // 2 funcs * 2 patterns = 4
    assert_eq!(candidates.len(), 4);
}

#[test]
fn test_exploration_runner_creation_empty_sigs() {
    let config = ExplorationConfig::default();
    let result = ExplorationRunner::new(vec![], config);
    assert!(result.is_err());
}

#[test]
fn test_exploration_runner_creation_empty_patterns() {
    let config = ExplorationConfig {
        pattern_types: vec![],
        ..ExplorationConfig::default()
    };
    let result = ExplorationRunner::new(vec![nat_sig("Nat.add", 2)], config);
    assert!(result.is_err());
}

#[test]
fn test_exploration_runner_runs_without_panic() {
    let config = ExplorationConfig {
        max_depth: 1,
        max_terms: 50,
        pattern_types: vec![TermPattern::Equality],
        timeout: Duration::from_secs(5),
        counterexample_samples: 10,
        eq_const: "Eq".to_string(),
        num_threads: Some(1),
    };
    let sigs = vec![nat_sig("Nat.add", 2)];
    let mut runner = ExplorationRunner::new(sigs, config).expect("runner creation should succeed");
    let result = runner.run();
    assert!(result.explored_count > 0);
    assert_eq!(result.iterations_completed, 1);
}

#[test]
fn test_exploration_full_loop_nat_theory() {
    let config = ExplorationConfig {
        max_depth: 2,
        max_terms: 100,
        pattern_types: vec![
            TermPattern::Commutativity,
            TermPattern::Associativity,
            TermPattern::Equality,
        ],
        timeout: Duration::from_secs(10),
        counterexample_samples: 50,
        eq_const: "Eq".to_string(),
        num_threads: Some(1),
    };
    let sigs = vec![nat_sig("Nat.add", 2), nat_sig("Nat.mul", 2)];
    let mut runner = ExplorationRunner::new(sigs, config).expect("runner creation should succeed");
    let result = runner.run();

    assert!(result.explored_count > 0, "should explore some candidates");
    assert!(
        result.survived_filter_count > 0,
        "some candidates should survive filtering"
    );
    assert_eq!(result.iterations_completed, 2);
}

#[test]
fn test_exploration_timeout_respected() {
    // Use Duration::ZERO to guarantee the timeout fires immediately.
    let config = ExplorationConfig {
        max_depth: 1000,
        max_terms: 10,
        pattern_types: vec![TermPattern::Equality],
        timeout: Duration::ZERO,
        counterexample_samples: 1,
        eq_const: "Eq".to_string(),
        num_threads: Some(1),
    };
    let sigs = vec![nat_sig("Nat.add", 2)];
    let mut runner = ExplorationRunner::new(sigs, config).expect("runner creation should succeed");
    let result = runner.run();

    assert!(
        result.iterations_completed < 1000,
        "timeout should stop exploration early, got {} iterations",
        result.iterations_completed,
    );
}

#[test]
fn test_exploration_state_default() {
    let state = ExplorationState::default();
    assert!(state.known_lemmas.is_empty());
    assert!(state.known_lemma_reprs.is_empty());
    assert_eq!(state.exploration_depth, 0);
}

#[test]
fn test_filter_batch_returns_subset() {
    let filter = CounterexampleFilter::new(10);
    let candidates = vec![
        CandidateEquation {
            pattern: TermPattern::Commutativity,
            statement: Expr::prop(),
            description: "comm".to_string(),
            func_names: vec!["Nat.add".to_string()],
        },
        CandidateEquation {
            pattern: TermPattern::Idempotency,
            statement: Expr::prop(),
            description: "idem".to_string(),
            func_names: vec!["Nat.add".to_string()],
        },
    ];
    let survivors = filter.filter_batch(&candidates);
    assert_eq!(survivors.len(), 1, "idempotent add should be filtered out");
    assert_eq!(survivors[0].pattern, TermPattern::Commutativity);
}

#[test]
fn test_exploration_with_env() {
    let env = Environment::new();
    let config = ExplorationConfig {
        max_depth: 1,
        max_terms: 10,
        pattern_types: vec![TermPattern::Equality],
        timeout: Duration::from_secs(5),
        eq_const: "Eq".to_string(),
        num_threads: Some(1),
        ..ExplorationConfig::default()
    };
    let sigs = vec![nat_sig("Nat.add", 2)];
    let runner = ExplorationRunner::with_env(env, sigs, config);
    assert!(runner.is_ok());
}

#[test]
fn test_pattern_generator_add_signatures() {
    let sigs = vec![nat_sig("Nat.add", 2)];
    let mut generator = PatternGenerator::new(sigs, vec![TermPattern::Commutativity], "Eq");
    let before = generator.generate().len();
    generator.add_signatures(vec![nat_sig("Nat.mul", 2)]);
    let after = generator.generate().len();
    assert!(
        after > before,
        "adding signatures should produce more candidates"
    );
}

// --- Computational counterexample evaluation (real Nat statements) ---

/// Build a real `forall a b, add(a,b) = add(b,a)` candidate. Under 2 binders:
/// a = BVar(1), b = BVar(0).
fn real_add_commutativity() -> CandidateEquation {
    let add = |x, y| Expr::apps(Expr::const_str("Nat.add"), [x, y]);
    let body = mk_eq_nat(
        add(Expr::bvar(1), Expr::bvar(0)),
        add(Expr::bvar(0), Expr::bvar(1)),
    );
    CandidateEquation {
        pattern: TermPattern::Commutativity,
        statement: forall_nat(2, body),
        description: "Nat.add is commutative".to_string(),
        func_names: vec!["Nat.add".to_string()],
    }
}

/// Build a real (false) `forall a, add(a,a) = a` candidate.
fn real_add_idempotency() -> CandidateEquation {
    let add = |x, y| Expr::apps(Expr::const_str("Nat.add"), [x, y]);
    let body = mk_eq_nat(add(Expr::bvar(0), Expr::bvar(0)), Expr::bvar(0));
    CandidateEquation {
        pattern: TermPattern::Idempotency,
        statement: forall_nat(1, body),
        description: "Nat.add is idempotent".to_string(),
        func_names: vec!["Nat.add".to_string()],
    }
}

#[test]
fn test_survives_real_commutativity_no_counterexample() {
    let filter = CounterexampleFilter::new(100);
    assert!(
        filter.survives(&real_add_commutativity()),
        "add commutativity (a+b == b+a) has no counterexample and must survive"
    );
}

#[test]
fn test_survives_real_idempotent_add_rejected_by_counterexample() {
    let filter = CounterexampleFilter::new(100);
    assert!(
        !filter.survives(&real_add_idempotency()),
        "add idempotency (a+a == a) is false (a=1: 2 != 1) and must be rejected"
    );
}

#[test]
fn test_survives_non_nat_falls_back_to_heuristic() {
    // Statement is Prop (not an Eq), so the evaluator is inconclusive and the
    // structural heuristic decides — preserving prior behavior.
    let filter = CounterexampleFilter::new(100);
    let idempotent_max = CandidateEquation {
        pattern: TermPattern::Idempotency,
        statement: Expr::prop(),
        description: "max is idempotent".to_string(),
        func_names: vec!["Nat.max".to_string()],
    };
    assert!(
        filter.survives(&idempotent_max),
        "max idempotency must survive via the fallback heuristic"
    );

    let idempotent_add_stub = CandidateEquation {
        pattern: TermPattern::Idempotency,
        statement: Expr::prop(),
        description: "add is idempotent".to_string(),
        func_names: vec!["Nat.add".to_string()],
    };
    assert!(
        !filter.survives(&idempotent_add_stub),
        "with a non-evaluable statement, the heuristic still rejects idempotent add"
    );
}

#[test]
fn test_survives_overflow_does_not_reject() {
    // forall a, mul(a, a) = mul(a, a): trivially true, and large samples may
    // overflow u64. Overflow/inconclusive samples must NEVER reject, so this
    // self-equation survives.
    let filter = CounterexampleFilter::new(100);
    let mul = |x, y| Expr::apps(Expr::const_str("Nat.mul"), [x, y]);
    let body = mk_eq_nat(
        mul(Expr::bvar(0), Expr::bvar(0)),
        mul(Expr::bvar(0), Expr::bvar(0)),
    );
    let candidate = CandidateEquation {
        pattern: TermPattern::Equality,
        statement: forall_nat(1, body),
        description: "mul(a,a) equals itself".to_string(),
        func_names: vec!["Nat.mul".to_string()],
    };
    assert!(
        filter.survives(&candidate),
        "a self-equation must survive even when some samples overflow"
    );
}

#[test]
fn test_survives_deterministic_same_candidate_same_verdict() {
    let filter = CounterexampleFilter::new(100);
    let comm = real_add_commutativity();
    let idem = real_add_idempotency();
    assert_eq!(
        filter.survives(&comm),
        filter.survives(&comm),
        "commutativity verdict must be deterministic across runs"
    );
    assert_eq!(
        filter.survives(&idem),
        filter.survives(&idem),
        "idempotency verdict must be deterministic across runs"
    );
    // And the two verdicts are distinct, confirming the evaluator drives them.
    assert!(filter.survives(&comm));
    assert!(!filter.survives(&idem));
}
