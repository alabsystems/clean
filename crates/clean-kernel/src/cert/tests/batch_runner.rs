// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::cert::*;
use crate::env::Environment;
use crate::level::Level;

fn empty_env() -> Environment {
    Environment::new()
}

fn make_verify_inputs(env: &Environment, n: usize) -> Vec<BatchVerifyInput> {
    (0..n)
        .map(|i| {
            let mut builder = CertBuilder::new(env);
            let node = builder.sort(Level::zero()).unwrap();
            let cert = builder.finish(node).unwrap();
            BatchVerifyInput::new(format!("item_{i}"), cert, crate::expr::Expr::prop())
        })
        .collect()
}

fn make_build_inputs(n: usize) -> Vec<BatchBuildInput> {
    (0..n)
        .map(|i| BatchBuildInput::new(format!("item_{i}"), |b| b.sort(Level::zero())))
        .collect()
}

#[test]
fn test_batch_verifier_basic() {
    let env = empty_env();
    let inputs = make_verify_inputs(&env, 1);

    let results = BatchVerifier::new(&env, inputs).run();
    assert_eq!(results.len(), 1);
    assert!(results[0].success);
}

#[test]
fn test_batch_verifier_sequential() {
    let env = empty_env();
    let inputs = make_verify_inputs(&env, 5);

    let results = BatchVerifier::new(&env, inputs).sequential().run();
    assert_eq!(results.len(), 5);
    assert!(results.iter().all(|r| r.success));
}

#[test]
fn test_batch_verifier_with_progress() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let env = empty_env();
    let inputs = make_verify_inputs(&env, 5);

    let callback_count = AtomicUsize::new(0);
    let results = BatchVerifier::new(&env, inputs)
        .with_progress(|_| {
            callback_count.fetch_add(1, Ordering::Relaxed);
        })
        .run();

    assert_eq!(results.len(), 5);
    assert_eq!(callback_count.load(Ordering::Relaxed), 5);
}

#[test]
fn test_batch_build_verifier_basic() {
    let env = empty_env();
    let mut inputs = make_build_inputs(1);
    let results = BatchBuildVerifier::new(&env, vec![inputs.remove(0)]).run();
    assert_eq!(results.len(), 1);
    assert!(results[0].success);
}

#[test]
fn test_batch_build_verifier_sequential() {
    let env = empty_env();
    let inputs = make_build_inputs(10);

    let results = BatchBuildVerifier::new(&env, inputs).sequential().run();
    assert_eq!(results.len(), 10);
    assert!(results.iter().all(|r| r.success));
}

#[test]
fn test_batch_build_verifier_with_threads() {
    let env = empty_env();
    let inputs = make_build_inputs(20);

    let results = BatchBuildVerifier::new(&env, inputs).with_threads(4).run();
    assert_eq!(results.len(), 20);
    assert!(results.iter().all(|r| r.success));
}

#[test]
fn test_batch_build_verifier_with_stats() {
    let env = empty_env();
    let inputs: Vec<BatchBuildInput> = (0..5)
        .map(|i| {
            if i % 2 == 0 {
                BatchBuildInput::new(format!("valid_{i}"), |b| b.sort(Level::zero()))
            } else {
                BatchBuildInput::new(format!("invalid_{i}"), |b| b.bvar(0))
            }
        })
        .collect();

    let (results, stats) = BatchBuildVerifier::new(&env, inputs)
        .sequential()
        .with_stats()
        .run_with_stats();
    assert_eq!(results.len(), 5);
    assert_eq!(stats.total, 5);
    assert_eq!(stats.successful, 3);
    assert_eq!(stats.failed, 2);
}

#[test]
fn test_batch_build_verifier_with_progress() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let env = empty_env();
    let inputs = make_build_inputs(10);

    let callback_count = AtomicUsize::new(0);
    let (results, stats) = BatchBuildVerifier::new(&env, inputs)
        .with_threads(2)
        .with_progress(|_| {
            callback_count.fetch_add(1, Ordering::Relaxed);
        })
        .run_with_stats();

    assert_eq!(results.len(), 10);
    assert_eq!(stats.total, 10);
    assert_eq!(callback_count.load(Ordering::Relaxed), 10);
}

#[test]
fn test_batch_build_verifier_with_progress_run_only() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let env = empty_env();
    let inputs = make_build_inputs(5);

    let callback_count = AtomicUsize::new(0);
    let results = BatchBuildVerifier::new(&env, inputs)
        .with_progress(|_| {
            callback_count.fetch_add(1, Ordering::Relaxed);
        })
        .run();

    assert_eq!(results.len(), 5);
    assert!(results.iter().all(|r| r.success));
    assert_eq!(callback_count.load(Ordering::Relaxed), 5);
}
