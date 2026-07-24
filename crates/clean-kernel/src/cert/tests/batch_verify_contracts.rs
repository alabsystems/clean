// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::cert::*;
use crate::env::Environment;
use crate::level::Level;

fn empty_env() -> Environment {
    Environment::new()
}

fn make_verify_inputs(env: &Environment, n: usize, prefix: &str) -> Vec<BatchVerifyInput> {
    (0..n)
        .map(|i| {
            let mut builder = CertBuilder::new(env);
            let node = builder.sort(Level::zero()).unwrap();
            let cert = builder.finish(node).unwrap();
            BatchVerifyInput::new(format!("{prefix}_{i:02}"), cert, crate::expr::Expr::prop())
        })
        .collect()
}

#[test]
fn test_contract_batch_verify_order_and_id() {
    let env = empty_env();
    let ids: Vec<String> = (0..10).map(|i| format!("verify_id_{i:02}")).collect();
    let inputs: Vec<BatchVerifyInput> = ids
        .iter()
        .map(|id| {
            let mut builder = CertBuilder::new(&env);
            let node = builder.sort(Level::zero()).unwrap();
            let cert = builder.finish(node).unwrap();
            BatchVerifyInput::new(id.clone(), cert, crate::expr::Expr::prop())
        })
        .collect();

    let results = batch_verify(&env, inputs);
    assert_eq!(results.len(), ids.len());
    for (result, expected_id) in results.iter().zip(ids.iter()) {
        assert_eq!(&result.id, expected_id);
    }
}

#[test]
fn test_contract_batch_verify_parallel_sequential_equivalence() {
    let env = empty_env();
    let par_results = batch_verify(&env, make_verify_inputs(&env, 15, "verify_equiv"));
    let seq_results = batch_verify_sequential(&env, make_verify_inputs(&env, 15, "verify_equiv"));

    assert_eq!(par_results.len(), seq_results.len());
    for (par, seq) in par_results.iter().zip(seq_results.iter()) {
        assert_eq!(par.id, seq.id);
        assert_eq!(par.success, seq.success);
    }
}

#[test]
fn test_contract_batch_verify_stats_total() {
    let env = empty_env();
    let inputs = make_verify_inputs(&env, 8, "item");

    let (results, stats) = batch_verify_with_stats(&env, inputs);
    assert_eq!(stats.total, results.len());
    assert_eq!(stats.successful + stats.failed, stats.total);
}

#[test]
fn test_contract_batch_verify_thread_equivalence() {
    let env = empty_env();
    let results_default = batch_verify(&env, make_verify_inputs(&env, 12, "verify_thread"));
    let results_1 =
        batch_verify_with_threads(&env, make_verify_inputs(&env, 12, "verify_thread"), 1);
    let results_4 =
        batch_verify_with_threads(&env, make_verify_inputs(&env, 12, "verify_thread"), 4);

    for i in 0..12 {
        let expected_id = format!("verify_thread_{i:02}");
        assert_eq!(results_default[i].id, expected_id);
        assert_eq!(results_1[i].id, expected_id);
        assert_eq!(results_4[i].id, expected_id);
        assert_eq!(results_default[i].success, results_1[i].success);
        assert_eq!(results_1[i].success, results_4[i].success);
    }
}
