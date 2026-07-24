// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for batch parallel dispatch, aggregation, and types.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::{Environment, Expr, Level, Name};

fn setup_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }
    env
}

fn make_nat_eq(lhs: &Expr, rhs: &Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

#[test]
fn test_dispatch_empty_batch() {
    let env = setup_env();
    let config = BatchConfig::new();
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &[]);

    assert_eq!(result.results.len(), 0);
    assert_eq!(result.stats.total, 0);
    assert_eq!(result.stats.proved, 0);
}

#[test]
fn test_dispatch_single_reflexive_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_nat_eq(&a, &a);

    let queries = vec![BatchQuery::new(QueryId(0), goal, 5_000)];
    let config = BatchConfig::new();
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &queries);

    assert_eq!(result.results.len(), 1);
    assert_eq!(
        result.results[0].status,
        BatchQueryStatus::Proved,
        "a = a should be proved, got: {:?}",
        result.results[0].reason
    );
    assert_eq!(result.results[0].query_id, QueryId(0));
    assert!(result.results[0].proof_term.is_some());
    assert_eq!(result.stats.proved, 1);
    assert_eq!(result.stats.total, 1);
}

#[test]
fn test_dispatch_multiple_goals_parallel() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let queries = vec![
        BatchQuery::new(QueryId(0), make_nat_eq(&a, &a), 5_000),
        BatchQuery::new(QueryId(1), make_nat_eq(&b, &b), 5_000),
        BatchQuery::new(QueryId(2), make_nat_eq(&c, &c), 5_000),
    ];

    let config = BatchConfig::new().with_max_parallel(2);
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &queries);

    assert_eq!(result.results.len(), 3);
    for (i, r) in result.results.iter().enumerate() {
        assert_eq!(r.query_id, QueryId(i as u64));
        assert_eq!(
            r.status,
            BatchQueryStatus::Proved,
            "goal {i} should be proved, got: {:?}",
            r.reason
        );
    }
    assert_eq!(result.stats.proved, 3);
    assert_eq!(result.stats.total, 3);
}

#[test]
fn test_dispatch_timeout_handling() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_nat_eq(&a, &a);

    // Zero timeout should produce a timeout result.
    let queries = vec![BatchQuery::new(QueryId(42), goal, 0)];
    let config = BatchConfig::new();
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &queries);

    assert_eq!(result.results.len(), 1);
    assert_eq!(result.results[0].status, BatchQueryStatus::Timeout);
    assert_eq!(result.results[0].query_id, QueryId(42));
    assert!(result.results[0].reason.is_some());
}

#[test]
fn test_dispatch_priority_ordering() {
    // Priority affects dispatch order but not result order.
    // Results should always match the input query order.
    let env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let queries = vec![
        BatchQuery::new(QueryId(0), make_nat_eq(&a, &a), 5_000).with_priority(1),
        BatchQuery::new(QueryId(1), make_nat_eq(&a, &a), 5_000).with_priority(100),
        BatchQuery::new(QueryId(2), make_nat_eq(&a, &a), 5_000).with_priority(50),
    ];

    let config = BatchConfig::new().with_max_parallel(1);
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &queries);

    // Results are in input order regardless of priority.
    assert_eq!(result.results[0].query_id, QueryId(0));
    assert_eq!(result.results[1].query_id, QueryId(1));
    assert_eq!(result.results[2].query_id, QueryId(2));
    assert_eq!(result.stats.proved, 3);
}

#[test]
fn test_dispatch_with_shared_axioms() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Goal: a = b (not provable without hypothesis).
    // Shared axiom: a = b (makes it provable).
    let goal = make_nat_eq(&a, &b);
    let axiom = make_nat_eq(&a, &b);

    let queries = vec![BatchQuery::new(QueryId(0), goal, 5_000)];
    let config = BatchConfig::new().with_shared_axioms(vec![axiom]);
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &queries);

    assert_eq!(result.results.len(), 1);
    assert_eq!(
        result.results[0].status,
        BatchQueryStatus::Proved,
        "a = b with shared axiom a = b should be proved, got: {:?}",
        result.results[0].reason
    );
}

#[test]
fn test_dispatch_with_per_query_hypotheses() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let goal = make_nat_eq(&a, &b);
    let hypothesis = make_nat_eq(&a, &b);

    let queries = vec![BatchQuery::new(QueryId(0), goal, 5_000).with_hypotheses(vec![hypothesis])];
    let config = BatchConfig::new();
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &queries);

    assert_eq!(result.results.len(), 1);
    assert_eq!(
        result.results[0].status,
        BatchQueryStatus::Proved,
        "a = b with hypothesis a = b should be proved, got: {:?}",
        result.results[0].reason
    );
}

#[test]
fn test_dispatch_mixed_provable_and_unprovable() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let queries = vec![
        BatchQuery::new(QueryId(0), make_nat_eq(&a, &a), 5_000), // provable
        BatchQuery::new(QueryId(1), make_nat_eq(&a, &b), 5_000), // not provable
    ];

    let config = BatchConfig::new();
    let dispatcher = BatchDispatcher::new(config);
    let result = dispatcher.dispatch(&env, &queries);

    assert_eq!(result.results.len(), 2);
    assert_eq!(result.results[0].status, BatchQueryStatus::Proved);
    // a = b without hypotheses should be disproved or unknown.
    assert!(
        matches!(
            result.results[1].status,
            BatchQueryStatus::Disproved | BatchQueryStatus::Unknown
        ),
        "a = b should be disproved or unknown, got: {:?}",
        result.results[1].status
    );
    assert_eq!(result.stats.proved, 1);
    assert_eq!(result.stats.total, 2);
}

// --- Aggregator tests ---

#[test]
fn test_aggregator_summarize_empty() {
    let aggregator = BatchAggregator::new(vec![], 0);
    let stats = aggregator.summarize();
    assert_eq!(stats.total, 0);
    assert_eq!(stats.proved, 0);
    assert_eq!(stats.queries_per_second(), 0.0);
    assert_eq!(stats.prove_rate(), 0.0);
}

#[test]
fn test_aggregator_summarize_mixed() {
    let results = vec![
        BatchResult::proved(
            QueryId(0),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
        BatchResult::disproved(QueryId(1), 200_000),
        BatchResult::timeout(QueryId(2), 300_000, "timed out".to_string()),
        BatchResult::unknown(QueryId(3), 150_000, "unknown".to_string()),
        BatchResult::error(QueryId(4), 50_000, "error".to_string()),
    ];

    let aggregator = BatchAggregator::new(results, 1_000_000_000);
    let stats = aggregator.summarize();

    assert_eq!(stats.total, 5);
    assert_eq!(stats.proved, 1);
    assert_eq!(stats.disproved, 1);
    assert_eq!(stats.timeout, 1);
    assert_eq!(stats.unknown, 1);
    assert_eq!(stats.error, 1);
    assert!((stats.queries_per_second() - 5.0).abs() < 0.001);
    assert!((stats.prove_rate() - 0.2).abs() < 0.001);
}

#[test]
fn test_aggregator_group_by_status() {
    let results = vec![
        BatchResult::proved(
            QueryId(0),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
        BatchResult::proved(
            QueryId(1),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
        BatchResult::timeout(QueryId(2), 300_000, "timed out".to_string()),
    ];

    let aggregator = BatchAggregator::new(results, 0);
    let groups = aggregator.group_by_status();

    assert_eq!(groups.proved, vec![QueryId(0), QueryId(1)]);
    assert_eq!(groups.timeout, vec![QueryId(2)]);
    assert!(groups.disproved.is_empty());
    assert!(groups.unknown.is_empty());
    assert!(groups.error.is_empty());
}

#[test]
fn test_aggregator_retryable_ids() {
    let results = vec![
        BatchResult::proved(
            QueryId(0),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
        BatchResult::timeout(QueryId(1), 300_000, "timed out".to_string()),
        BatchResult::unknown(QueryId(2), 150_000, "unknown".to_string()),
        BatchResult::error(QueryId(3), 50_000, "error".to_string()),
    ];

    let aggregator = BatchAggregator::new(results, 0);
    let retryable = aggregator.retryable_ids();

    // Timeout and unknown are retryable; error is not.
    assert_eq!(retryable, vec![QueryId(1), QueryId(2)]);
}

#[test]
fn test_aggregator_error_ids() {
    let results = vec![
        BatchResult::proved(
            QueryId(0),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
        BatchResult::error(QueryId(1), 50_000, "error".to_string()),
    ];

    let aggregator = BatchAggregator::new(results, 0);
    assert_eq!(aggregator.error_ids(), vec![QueryId(1)]);
}

#[test]
fn test_aggregator_avg_time_ns() {
    let results = vec![
        BatchResult::proved(
            QueryId(0),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
        BatchResult::proved(
            QueryId(1),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            300_000,
        ),
    ];

    let aggregator = BatchAggregator::new(results, 0);
    assert_eq!(aggregator.avg_time_ns(), 200_000);
}

#[test]
fn test_aggregator_proved_ids() {
    let results = vec![
        BatchResult::proved(
            QueryId(5),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
        BatchResult::disproved(QueryId(6), 200_000),
        BatchResult::proved(
            QueryId(7),
            crate::ProofResult::new(Expr::prop(), "test", 0, None),
            100_000,
        ),
    ];

    let aggregator = BatchAggregator::new(results, 0);
    assert_eq!(aggregator.proved_ids(), vec![QueryId(5), QueryId(7)]);
}

// --- Types tests ---

#[test]
fn test_batch_config_builder() {
    let config = BatchConfig::new()
        .with_max_parallel(4)
        .with_default_timeout_ms(10_000)
        .with_shared_axioms(vec![Expr::prop()]);

    assert_eq!(config.max_parallel, Some(4));
    assert_eq!(config.default_timeout_ms, 10_000);
    assert_eq!(config.shared_axioms.len(), 1);
}

#[test]
fn test_batch_config_max_parallel_minimum() {
    let config = BatchConfig::new().with_max_parallel(0);
    assert_eq!(
        config.max_parallel,
        Some(1),
        "max_parallel should clamp to 1"
    );
}

#[test]
fn test_batch_query_builder() {
    let query = BatchQuery::new(QueryId(99), Expr::prop(), 3_000)
        .with_priority(42)
        .with_hypotheses(vec![Expr::prop()]);

    assert_eq!(query.query_id, QueryId(99));
    assert_eq!(query.timeout_ms, 3_000);
    assert_eq!(query.priority, 42);
    assert_eq!(query.hypotheses.len(), 1);
}

#[test]
fn test_batch_stats_throughput() {
    let stats = BatchStats {
        total: 100,
        proved: 80,
        disproved: 10,
        timeout: 5,
        unknown: 3,
        error: 2,
        total_time_ns: 2_000_000_000, // 2 seconds
    };

    assert!((stats.queries_per_second() - 50.0).abs() < 0.001);
    assert!((stats.prove_rate() - 0.8).abs() < 0.001);
}

#[test]
fn test_query_id_ordering() {
    assert!(QueryId(0) < QueryId(1));
    assert_eq!(QueryId(5), QueryId(5));
}
