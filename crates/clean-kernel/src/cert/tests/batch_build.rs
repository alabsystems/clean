// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::cert::*;
use crate::env::Environment;
use crate::level::Level;

fn empty_env() -> Environment {
    Environment::new()
}

fn sort_input(id: impl Into<String>) -> BatchBuildInput {
    BatchBuildInput::new(id, |builder| builder.sort(Level::zero()))
}

fn invalid_input(id: impl Into<String>) -> BatchBuildInput {
    BatchBuildInput::new(id, |builder| builder.bvar(0))
}

#[test]
fn test_batch_build_single_success() {
    let env = empty_env();
    let inputs = vec![sort_input("prop_type")];

    let results = batch_build_verify_sequential(&env, inputs);
    assert_eq!(results.len(), 1);
    assert!(results[0].success);
    let _cert = results[0]
        .cert
        .as_ref()
        .expect("successful build should have cert");
    let _ct = results[0]
        .computed_type
        .as_ref()
        .expect("successful build should have computed_type");
}

#[test]
fn test_batch_build_single_failure() {
    let env = empty_env();
    let results = batch_build_verify_sequential(&env, vec![invalid_input("invalid_bvar")]);
    assert_eq!(results.len(), 1);
    assert!(!results[0].success);
    let _err = results[0]
        .error
        .as_ref()
        .expect("failed build should have error");
}

#[test]
fn test_batch_build_mixed_success_failure() {
    let env = empty_env();
    let inputs = vec![
        sort_input("valid_prop"),
        invalid_input("invalid"),
        BatchBuildInput::new("valid_type1", |builder| {
            builder.sort(Level::succ(Level::zero()))
        }),
    ];

    let results = batch_build_verify_sequential(&env, inputs);
    assert_eq!(results.len(), 3);
    assert!(results[0].success);
    assert!(!results[1].success);
    assert!(results[2].success);
}

#[test]
fn test_batch_build_with_stats() {
    let env = empty_env();
    let inputs = vec![sort_input("valid"), invalid_input("invalid")];

    let (results, stats) = batch_build_verify_sequential_with_stats(&env, inputs);
    assert_eq!(results.len(), 2);
    assert_eq!(stats.total, 2);
    assert_eq!(stats.successful, 1);
    assert_eq!(stats.failed, 1);
}

#[test]
fn test_batch_build_parallel() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..100).map(|i| sort_input(format!("item_{i}"))).collect();

    let results = batch_build_verify(&env, inputs);
    assert_eq!(results.len(), 100);
    assert!(results.iter().all(|r| r.success));
}

#[test]
fn test_batch_build_verify_with_threads() {
    let env = empty_env();

    let inputs: Vec<BatchBuildInput> = (0..50).map(|i| sort_input(format!("item_{i}"))).collect();
    let results = batch_build_verify_with_threads(&env, inputs, 2);
    assert_eq!(results.len(), 50);
    assert!(results.iter().all(|r| r.success));

    let inputs_single: Vec<BatchBuildInput> =
        (0..50).map(|i| sort_input(format!("single_{i}"))).collect();
    let results_single = batch_build_verify_with_threads(&env, inputs_single, 1);
    assert_eq!(results_single.len(), 50);
    assert!(results_single.iter().all(|r| r.success));
}

#[test]
fn test_batch_build_verify_with_stats_threads() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..25).map(|i| sort_input(format!("item_{i}"))).collect();

    let (results, stats) = batch_build_verify_with_stats_threads(&env, inputs, 2);
    assert_eq!(results.len(), 25);
    assert!(results.iter().all(|r| r.success));
    assert_eq!(stats.total, 25);
    assert_eq!(stats.successful, 25);
    assert_eq!(stats.failed, 0);
}

#[test]
fn test_batch_build_verify_with_stats_progress() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..20).map(|i| sort_input(format!("item_{i}"))).collect();

    let callback_count = AtomicUsize::new(0);
    let (results, stats) = batch_build_verify_with_stats_progress(&env, inputs, 2, |_result| {
        callback_count.fetch_add(1, Ordering::Relaxed);
    });

    assert_eq!(results.len(), 20);
    assert!(results.iter().all(|r| r.success));
    assert_eq!(stats.total, 20);
    assert_eq!(callback_count.load(Ordering::Relaxed), 20);
}

#[test]
fn test_batch_build_verify_with_stats_progress_zero_threads() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..10).map(|i| sort_input(format!("item_{i}"))).collect();

    let (results, stats) = batch_build_verify_with_stats_progress(&env, inputs, 0, |_result| {});

    assert_eq!(results.len(), 10);
    assert_eq!(stats.total, 10);
}

#[test]
fn test_batch_build_verify_with_threads_mixed_results() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..10)
        .map(|i| {
            if i % 2 == 0 {
                sort_input(format!("valid_{i}"))
            } else {
                invalid_input(format!("invalid_{i}"))
            }
        })
        .collect();

    let results = batch_build_verify_with_threads(&env, inputs, 2);
    assert_eq!(results.len(), 10);

    let successes = results.iter().filter(|r| r.success).count();
    let failures = results.iter().filter(|r| !r.success).count();
    assert_eq!(successes, 5, "Expected 5 successes (even indices)");
    assert_eq!(failures, 5, "Expected 5 failures (odd indices)");

    for result in results.iter().filter(|r| !r.success) {
        assert!(
            result.error.is_some(),
            "Failed results should have error message"
        );
    }
}

#[test]
fn test_contract_order_and_id_preservation() {
    let env = empty_env();
    let ids: Vec<String> = (0..20).map(|i| format!("unique_id_{i:03}")).collect();
    let inputs: Vec<BatchBuildInput> = ids.iter().map(|id| sort_input(id.clone())).collect();

    let results = batch_build_verify(&env, inputs);
    assert_eq!(
        results.len(),
        ids.len(),
        "Result count must match input count"
    );
    for (i, (result, expected_id)) in results.iter().zip(ids.iter()).enumerate() {
        assert_eq!(
            &result.id, expected_id,
            "Result {} ID mismatch: expected '{}', got '{}'",
            i, expected_id, result.id
        );
    }
}

#[test]
fn test_contract_order_and_id_preservation_sequential() {
    let env = empty_env();
    let ids: Vec<String> = (0..15).map(|i| format!("seq_id_{i:02}")).collect();
    let inputs: Vec<BatchBuildInput> = ids.iter().map(|id| sort_input(id.clone())).collect();

    let results = batch_build_verify_sequential(&env, inputs);
    assert_eq!(results.len(), ids.len());
    for (result, expected_id) in results.iter().zip(ids.iter()) {
        assert_eq!(&result.id, expected_id);
    }
}

#[test]
fn test_contract_order_and_id_preservation_with_threads() {
    let env = empty_env();
    let ids: Vec<String> = (0..30).map(|i| format!("thread_id_{i:03}")).collect();

    let inputs_1: Vec<BatchBuildInput> = ids.iter().map(|id| sort_input(id.clone())).collect();
    let results_1 = batch_build_verify_with_threads(&env, inputs_1, 1);
    for (result, expected_id) in results_1.iter().zip(ids.iter()) {
        assert_eq!(&result.id, expected_id, "1-thread: ID mismatch");
    }

    let inputs_4: Vec<BatchBuildInput> = ids.iter().map(|id| sort_input(id.clone())).collect();
    let results_4 = batch_build_verify_with_threads(&env, inputs_4, 4);
    for (result, expected_id) in results_4.iter().zip(ids.iter()) {
        assert_eq!(&result.id, expected_id, "4-thread: ID mismatch");
    }
}

#[test]
fn test_contract_parallel_sequential_equivalence() {
    let env = empty_env();

    fn make_inputs(n: usize) -> Vec<BatchBuildInput> {
        (0..n)
            .map(|i| {
                let id = format!("equiv_{i:02}");
                if i % 3 == 0 {
                    invalid_input(id)
                } else {
                    sort_input(id)
                }
            })
            .collect()
    }

    let parallel_results = batch_build_verify(&env, make_inputs(30));
    let sequential_results = batch_build_verify_sequential(&env, make_inputs(30));

    assert_eq!(parallel_results.len(), sequential_results.len());
    for (par, seq) in parallel_results.iter().zip(sequential_results.iter()) {
        assert_eq!(
            par.id, seq.id,
            "ID mismatch between parallel and sequential"
        );
        assert_eq!(
            par.success, seq.success,
            "Success mismatch for ID '{}': parallel={}, sequential={}",
            par.id, par.success, seq.success
        );
    }
}

#[test]
fn test_contract_stats_total_invariant() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..25)
        .map(|i| {
            if i % 2 == 0 {
                sort_input(format!("valid_{i}"))
            } else {
                invalid_input(format!("invalid_{i}"))
            }
        })
        .collect();

    let (results, stats) = batch_build_verify_with_stats(&env, inputs);

    assert_eq!(
        stats.total,
        results.len(),
        "stats.total ({}) != results.len() ({})",
        stats.total,
        results.len()
    );
    assert_eq!(
        stats.successful + stats.failed,
        stats.total,
        "successful ({}) + failed ({}) != total ({})",
        stats.successful,
        stats.failed,
        stats.total
    );

    let actual_success = results.iter().filter(|r| r.success).count();
    let actual_fail = results.iter().filter(|r| !r.success).count();
    assert_eq!(stats.successful, actual_success);
    assert_eq!(stats.failed, actual_fail);
}

#[test]
fn test_contract_stats_total_invariant_sequential() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..10).map(|i| sort_input(format!("item_{i}"))).collect();

    let (results, stats) = batch_build_verify_sequential_with_stats(&env, inputs);
    assert_eq!(stats.total, results.len());
    assert_eq!(stats.successful + stats.failed, stats.total);
    assert_eq!(stats.successful, 10);
    assert_eq!(stats.failed, 0);
}

#[test]
fn test_contract_stats_min_max_bounds() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..20).map(|i| sort_input(format!("item_{i}"))).collect();

    let (results, stats) = batch_build_verify_with_stats(&env, inputs);

    for result in &results {
        assert!(
            result.time_us >= stats.min_time_us,
            "result time {} < stats.min_time_us {}",
            result.time_us,
            stats.min_time_us
        );
        assert!(
            result.time_us <= stats.max_time_us,
            "result time {} > stats.max_time_us {}",
            result.time_us,
            stats.max_time_us
        );
    }

    assert!(
        stats.min_time_us <= stats.max_time_us,
        "min_time_us ({}) > max_time_us ({})",
        stats.min_time_us,
        stats.max_time_us
    );
}

#[test]
fn test_contract_empty_input_stats() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = vec![];

    let (results, stats) = batch_build_verify_with_stats(&env, inputs);
    assert_eq!(results.len(), 0);
    assert_eq!(stats.total, 0);
    assert_eq!(stats.successful, 0);
    assert_eq!(stats.failed, 0);
    assert_eq!(stats.min_time_us, 0);
}

#[test]
fn test_contract_thread_count_equivalence() {
    let env = empty_env();

    fn make_inputs(n: usize) -> Vec<BatchBuildInput> {
        (0..n)
            .map(|i| {
                let id = format!("thread_equiv_{i:02}");
                if i % 4 == 0 {
                    invalid_input(id)
                } else {
                    sort_input(id)
                }
            })
            .collect()
    }

    let results_default = batch_build_verify(&env, make_inputs(24));
    let results_1_thread = batch_build_verify_with_threads(&env, make_inputs(24), 1);
    let results_2_threads = batch_build_verify_with_threads(&env, make_inputs(24), 2);
    let results_4_threads = batch_build_verify_with_threads(&env, make_inputs(24), 4);

    assert_eq!(results_default.len(), 24);
    assert_eq!(results_1_thread.len(), 24);
    assert_eq!(results_2_threads.len(), 24);
    assert_eq!(results_4_threads.len(), 24);

    for i in 0..24 {
        let expected_id = format!("thread_equiv_{i:02}");
        let expected_success = i % 4 != 0;

        assert_eq!(results_default[i].id, expected_id);
        assert_eq!(results_1_thread[i].id, expected_id);
        assert_eq!(results_2_threads[i].id, expected_id);
        assert_eq!(results_4_threads[i].id, expected_id);

        assert_eq!(results_default[i].success, expected_success);
        assert_eq!(results_1_thread[i].success, expected_success);
        assert_eq!(results_2_threads[i].success, expected_success);
        assert_eq!(results_4_threads[i].success, expected_success);
    }
}

#[test]
fn test_contract_determinism() {
    let env = empty_env();

    fn make_inputs() -> Vec<BatchBuildInput> {
        (0..15)
            .map(|i| {
                let id = format!("det_{i:02}");
                if i % 5 == 0 {
                    invalid_input(id)
                } else {
                    sort_input(id)
                }
            })
            .collect()
    }

    let run1 = batch_build_verify(&env, make_inputs());
    let run2 = batch_build_verify(&env, make_inputs());
    let run3 = batch_build_verify(&env, make_inputs());

    for i in 0..15 {
        assert_eq!(run1[i].id, run2[i].id);
        assert_eq!(run2[i].id, run3[i].id);
        assert_eq!(run1[i].success, run2[i].success);
        assert_eq!(run2[i].success, run3[i].success);
    }
}
