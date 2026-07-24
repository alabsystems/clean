// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch certificate verification tests

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::mode::CleanMode;

fn empty_env() -> Environment {
    Environment::new()
}

#[test]
fn test_batch_verify_empty() {
    let env = empty_env();
    let inputs: Vec<BatchVerifyInput> = vec![];
    let results = batch_verify(&env, inputs);
    assert!(results.is_empty());
}

#[test]
fn test_batch_verify_single() {
    let env = empty_env();
    let level = Level::zero();
    let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let inputs = vec![BatchVerifyInput::new("test1", cert, expr)];
    let results = batch_verify(&env, inputs);

    assert_eq!(results.len(), 1);
    assert!(results[0].success);
    assert_eq!(results[0].id, "test1");
    let _vt = results[0]
        .verified_type
        .as_ref()
        .expect("successful verification should have verified_type");
}

#[test]
fn test_batch_verify_uses_environment_mode() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let interval = Expr::from_kind(ExprKind::CubicalInterval);
    let inputs = vec![BatchVerifyInput::new(
        "cubical_interval",
        ProofCert::CubicalInterval,
        interval,
    )];

    let results = batch_verify(&env, inputs);

    assert_eq!(results.len(), 1);
    assert!(results[0].success);
    assert_eq!(results[0].id, "cubical_interval");
    assert_eq!(
        results[0].verified_type.as_ref(),
        Some(&Expr::sort(Level::succ(Level::zero())))
    );
}

#[test]
fn test_batch_verify_multiple_success() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..10)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(format!("cert_{i}"), cert, expr)
        })
        .collect();

    let results = batch_verify(&env, inputs);

    assert_eq!(results.len(), 10);
    for (i, result) in results.iter().enumerate() {
        assert!(result.success, "Failed at index {i}");
        assert_eq!(result.id, format!("cert_{i}"));
    }
}

#[test]
fn test_batch_verify_with_failures() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..5)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            if i % 2 == 0 {
                // Valid certificate
                let cert = ProofCert::Sort {
                    level: level.clone(),
                };
                BatchVerifyInput::new(format!("valid_{i}"), cert, expr)
            } else {
                // Invalid certificate (level mismatch)
                let cert = ProofCert::Sort {
                    level: Level::succ(Level::zero()),
                };
                BatchVerifyInput::new(format!("invalid_{i}"), cert, expr)
            }
        })
        .collect();

    let results = batch_verify(&env, inputs);

    assert_eq!(results.len(), 5);
    assert!(results[0].success); // valid_0
    assert!(!results[1].success); // invalid_1
    assert!(results[2].success); // valid_2
    assert!(!results[3].success); // invalid_3
    assert!(results[4].success); // valid_4
}

#[test]
fn test_batch_verify_with_stats() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..100)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(format!("{i}"), cert, expr)
        })
        .collect();

    let (results, stats) = batch_verify_with_stats(&env, inputs);

    assert_eq!(results.len(), 100);
    assert_eq!(stats.total, 100);
    assert_eq!(stats.successful, 100);
    assert_eq!(stats.failed, 0);
    assert!(stats.wall_time_us > 0 || stats.total == 0);
    println!("Batch stats: {stats}");
}

#[test]
fn test_batch_verify_sequential() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..10)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(format!("{i}"), cert, expr)
        })
        .collect();

    let results = batch_verify_sequential(&env, inputs);

    assert_eq!(results.len(), 10);
    for result in &results {
        assert!(result.success);
    }
}

#[test]
fn test_batch_verify_sequential_with_stats() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..50)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(format!("{i}"), cert, expr)
        })
        .collect();

    let (results, stats) = batch_verify_sequential_with_stats(&env, inputs);

    assert_eq!(results.len(), 50);
    assert_eq!(stats.total, 50);
    assert_eq!(stats.successful, 50);
    assert_eq!(stats.failed, 0);
    // Sequential should have speedup close to 1.0
    println!("Sequential stats: {stats}");
}

#[test]
fn test_batch_verify_with_threads() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..20)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(format!("{i}"), cert, expr)
        })
        .collect();

    // Test with 2 threads
    let results = batch_verify_with_threads(&env, inputs.clone(), 2);
    assert_eq!(results.len(), 20);
    for result in &results {
        assert!(result.success);
    }

    // Test with 1 thread (essentially sequential)
    let results_single = batch_verify_with_threads(&env, inputs, 1);
    assert_eq!(results_single.len(), 20);
}

#[test]
fn test_batch_verify_with_stats_threads() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..10)
        .map(|i| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(format!("{i}"), cert, expr)
        })
        .collect();

    let (results, stats) = batch_verify_with_stats_threads(&env, inputs, 2);

    // Must return all results
    assert_eq!(
        results.len(),
        10,
        "batch_verify_with_stats_threads must return all inputs"
    );
    for result in &results {
        assert!(result.success);
    }

    // Stats must be populated
    assert_eq!(stats.total, 10);
    assert_eq!(stats.successful, 10);
    assert_eq!(stats.failed, 0);
}

#[test]
fn test_batch_verify_with_stats_progress_invokes_callback() {
    use std::sync::{Arc, Mutex};

    let env = empty_env();
    let level = Level::zero();
    let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    for threads in [0usize, 2usize] {
        let inputs = vec![
            BatchVerifyInput::new("a", cert.clone(), expr.clone()),
            BatchVerifyInput::new("b", cert.clone(), expr.clone()),
        ];

        let seen: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
        let seen_cb = Arc::clone(&seen);

        let (results, stats) = batch_verify_with_stats_progress(
            &env,
            inputs,
            threads,
            move |result: &BatchVerifyResult| {
                let mut guard = seen_cb.lock().unwrap();
                guard.push(result.id.clone());
            },
        );

        assert_eq!(results.len(), 2);
        assert_eq!(stats.total, 2);

        let mut ids = seen.lock().unwrap();
        ids.sort();
        assert_eq!(*ids, vec!["a".to_string(), "b".to_string()]);
    }
}

#[test]
fn test_batch_verify_complex_certs() {
    let env = empty_env();

    // Create complex certificates - use nested Sort with varying levels
    // (Pi types require more complex setup with the environment)
    let inputs: Vec<BatchVerifyInput> = (0..10)
        .map(|i| {
            // Create different universe levels
            let mut level = Level::zero();
            for _ in 0..(i % 3) {
                level = Level::succ(level);
            }
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };

            BatchVerifyInput::new(format!("sort_{i}"), cert, expr)
        })
        .collect();

    let (results, stats) = batch_verify_with_stats(&env, inputs);

    assert_eq!(results.len(), 10);
    assert_eq!(stats.successful, 10);
    for result in &results {
        assert!(result.success, "Failed: {:?}", result.error);
    }
}

#[test]
fn test_batch_verify_stats_display() {
    let stats = BatchVerifyStats {
        total: 100,
        successful: 95,
        failed: 5,
        wall_time_us: 1000,
        sum_verify_time_us: 4000,
        min_time_us: 10,
        max_time_us: 100,
        speedup: 4.0,
    };

    let display = format!("{stats}");
    assert!(display.contains("100"));
    assert!(display.contains("95"));
    assert!(display.contains('5'));
    assert!(display.contains("4.00x"));
}

#[test]
fn test_batch_verify_result_accessors() {
    let success_result = BatchVerifyResult::success(
        "test".to_string(),
        Expr::from_kind(ExprKind::Sort(Level::zero())),
        100,
    );
    assert!(success_result.success);
    let _vt = success_result
        .verified_type
        .as_ref()
        .expect("success result should have verified_type");
    assert!(
        success_result.error.is_none(),
        "success result should have no error, got {:?}",
        success_result.error
    );
    assert_eq!(success_result.time_us, 100);

    let failure_result =
        BatchVerifyResult::failure("test2".to_string(), "Some error".to_string(), 50);
    assert!(!failure_result.success);
    assert!(
        failure_result.verified_type.is_none(),
        "failure result should have no verified_type, got {:?}",
        failure_result.verified_type
    );
    let _err = failure_result
        .error
        .as_ref()
        .expect("failure result should have error");
    assert_eq!(failure_result.time_us, 50);
}

#[test]
fn test_batch_verify_input_new() {
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };
    let expr = Expr::from_kind(ExprKind::Sort(level));

    let input = BatchVerifyInput::new("my_id", cert.clone(), expr.clone());
    assert_eq!(input.id, "my_id");
    assert_eq!(input.cert, cert);
    assert_eq!(input.expr, expr);

    // Test with String id
    let input2 = BatchVerifyInput::new(String::from("string_id"), cert, expr);
    assert_eq!(input2.id, "string_id");
}

#[test]
fn test_batch_verify_preserves_order() {
    let env = empty_env();

    // Create inputs with specific IDs
    let inputs: Vec<BatchVerifyInput> = vec!["z", "a", "m", "b", "y"]
        .into_iter()
        .map(|id| {
            let level = Level::zero();
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(id, cert, expr)
        })
        .collect();

    let results = batch_verify(&env, inputs);

    // Results should be in the same order as inputs
    assert_eq!(results[0].id, "z");
    assert_eq!(results[1].id, "a");
    assert_eq!(results[2].id, "m");
    assert_eq!(results[3].id, "b");
    assert_eq!(results[4].id, "y");
}

#[test]
fn test_batch_verify_parallel_vs_sequential_same_results() {
    let env = empty_env();

    let inputs: Vec<BatchVerifyInput> = (0..50)
        .map(|i| {
            let level = if i % 3 == 0 {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            };
            let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
            let cert = ProofCert::Sort {
                level: level.clone(),
            };
            BatchVerifyInput::new(format!("{i}"), cert, expr)
        })
        .collect();

    let parallel_results = batch_verify(&env, inputs.clone());
    let sequential_results = batch_verify_sequential(&env, inputs);

    // Same number of results
    assert_eq!(parallel_results.len(), sequential_results.len());

    // Same success/failure outcomes
    for (p, s) in parallel_results.iter().zip(sequential_results.iter()) {
        assert_eq!(p.id, s.id);
        assert_eq!(p.success, s.success);
        if p.success {
            assert_eq!(p.verified_type, s.verified_type);
        }
    }
}

// ========================================================================
// Classical mode certificate roundtrip tests
// ========================================================================
