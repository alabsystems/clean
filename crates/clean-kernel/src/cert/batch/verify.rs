// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::{fmt, sync::Arc, time::Instant};

use rayon::prelude::*;

use crate::cert::types::ProofCert;
use crate::cert::verifier::CertVerifier;
use crate::env::Environment;
use crate::expr::Expr;

use super::common::{micros_to_u64, with_stats, with_thread_pool};

/// Input for batch verification: a certificate paired with its expression.
#[derive(Debug, Clone)]
pub struct BatchVerifyInput {
    pub id: String,
    pub cert: ProofCert,
    pub expr: Expr,
}

impl BatchVerifyInput {
    pub fn new(id: impl Into<String>, cert: ProofCert, expr: Expr) -> Self {
        Self {
            id: id.into(),
            cert,
            expr,
        }
    }
}

/// Result of verifying a single certificate in a batch.
#[derive(Debug, Clone)]
pub struct BatchVerifyResult {
    pub id: String,
    pub success: bool,
    pub verified_type: Option<Expr>,
    pub error: Option<String>,
    pub time_us: u64,
}

impl BatchVerifyResult {
    pub(crate) fn success(id: String, ty: Expr, time_us: u64) -> Self {
        Self {
            id,
            success: true,
            verified_type: Some(ty),
            error: None,
            time_us,
        }
    }

    pub(crate) fn failure(id: String, error: String, time_us: u64) -> Self {
        Self {
            id,
            success: false,
            verified_type: None,
            error: Some(error),
            time_us,
        }
    }
}

/// Statistics for batch verification.
#[derive(Debug, Clone, Default)]
pub struct BatchVerifyStats {
    pub total: usize,
    pub successful: usize,
    pub failed: usize,
    pub wall_time_us: u64,
    pub sum_verify_time_us: u64,
    pub min_time_us: u64,
    pub max_time_us: u64,
    pub speedup: f64,
}

impl fmt::Display for BatchVerifyStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BatchVerifyStats {{ total: {}, success: {}, failed: {}, wall_time: {}µs, sum_time: {}µs, min: {}µs, max: {}µs, speedup: {:.2}x }}",
            self.total,
            self.successful,
            self.failed,
            self.wall_time_us,
            self.sum_verify_time_us,
            self.min_time_us,
            self.max_time_us,
            self.speedup
        )
    }
}

fn compute_batch_stats(results: &[BatchVerifyResult], wall_time_us: u64) -> BatchVerifyStats {
    let total = results.len();
    let mut successful = 0usize;
    let mut failed = 0usize;
    let mut sum_verify_time_us = 0u64;
    let mut min_time_us = u64::MAX;
    let mut max_time_us = 0u64;

    for result in results {
        sum_verify_time_us += result.time_us;
        min_time_us = min_time_us.min(result.time_us);
        max_time_us = max_time_us.max(result.time_us);
        if result.success {
            successful += 1;
        } else {
            failed += 1;
        }
    }

    if total == 0 {
        min_time_us = 0;
    }

    let speedup = if wall_time_us > 0 {
        sum_verify_time_us as f64 / wall_time_us as f64
    } else {
        1.0
    };

    BatchVerifyStats {
        total,
        successful,
        failed,
        wall_time_us,
        sum_verify_time_us,
        min_time_us,
        max_time_us,
        speedup,
    }
}

fn verify_one(env: &Environment, input: BatchVerifyInput) -> BatchVerifyResult {
    let start = Instant::now();
    let mut verifier = CertVerifier::with_mode(env, env.mode());
    match verifier.verify(&input.cert, &input.expr) {
        Ok(ty) => {
            BatchVerifyResult::success(input.id, ty, micros_to_u64(start.elapsed().as_micros()))
        }
        Err(error) => BatchVerifyResult::failure(
            input.id,
            error.to_string(),
            micros_to_u64(start.elapsed().as_micros()),
        ),
    }
}

fn verify_parallel(env: &Environment, inputs: Vec<BatchVerifyInput>) -> Vec<BatchVerifyResult> {
    inputs
        .into_par_iter()
        .map(|input| verify_one(env, input))
        .collect()
}

fn verify_parallel_with_callback<F>(
    env: &Environment,
    inputs: Vec<BatchVerifyInput>,
    callback: Arc<F>,
) -> Vec<BatchVerifyResult>
where
    F: Fn(&BatchVerifyResult) + Send + Sync,
{
    inputs
        .into_par_iter()
        .map(|input| {
            let result = verify_one(env, input);
            callback(&result);
            result
        })
        .collect()
}

pub fn batch_verify(env: &Environment, inputs: Vec<BatchVerifyInput>) -> Vec<BatchVerifyResult> {
    verify_parallel(env, inputs)
}

pub fn batch_verify_with_stats(
    env: &Environment,
    inputs: Vec<BatchVerifyInput>,
) -> (Vec<BatchVerifyResult>, BatchVerifyStats) {
    with_stats(|| batch_verify(env, inputs), compute_batch_stats)
}

pub fn batch_verify_sequential(
    env: &Environment,
    inputs: Vec<BatchVerifyInput>,
) -> Vec<BatchVerifyResult> {
    inputs
        .into_iter()
        .map(|input| verify_one(env, input))
        .collect()
}

pub fn batch_verify_sequential_with_stats(
    env: &Environment,
    inputs: Vec<BatchVerifyInput>,
) -> (Vec<BatchVerifyResult>, BatchVerifyStats) {
    with_stats(|| batch_verify_sequential(env, inputs), compute_batch_stats)
}

pub fn batch_verify_with_threads(
    env: &Environment,
    inputs: Vec<BatchVerifyInput>,
    num_threads: usize,
) -> Vec<BatchVerifyResult> {
    with_thread_pool(num_threads, || verify_parallel(env, inputs))
}

pub fn batch_verify_with_stats_threads(
    env: &Environment,
    inputs: Vec<BatchVerifyInput>,
    num_threads: usize,
) -> (Vec<BatchVerifyResult>, BatchVerifyStats) {
    with_stats(
        || batch_verify_with_threads(env, inputs, num_threads),
        compute_batch_stats,
    )
}

pub fn batch_verify_with_stats_progress<F>(
    env: &Environment,
    inputs: Vec<BatchVerifyInput>,
    threads: usize,
    on_result: F,
) -> (Vec<BatchVerifyResult>, BatchVerifyStats)
where
    F: Fn(&BatchVerifyResult) + Send + Sync,
{
    let callback = Arc::new(on_result);
    with_stats(
        || {
            if threads > 0 {
                let callback = Arc::clone(&callback);
                with_thread_pool(threads, || {
                    verify_parallel_with_callback(env, inputs, callback)
                })
            } else {
                verify_parallel_with_callback(env, inputs, callback)
            }
        },
        compute_batch_stats,
    )
}
