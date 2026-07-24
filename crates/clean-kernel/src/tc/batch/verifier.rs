// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BatchVerifier: high-throughput batch verifier for AI workloads.

use super::{compute_stats, BatchCheckResult, BatchCheckStats, BatchConfig};
use crate::env::Environment;
use crate::expr::Expr;
use crate::mode::CleanMode;
use crate::tc::{TcCaches, TypeChecker, TypeError};
use rayon::prelude::*;
use std::sync::atomic::{AtomicBool, Ordering};

/// High-throughput batch verifier for AI workloads
///
/// This verifier is optimized for checking millions of candidate expressions
/// efficiently. It amortizes setup costs and supports parallel execution.
pub struct BatchVerifier<'env> {
    env: &'env Environment,
    config: BatchConfig,
}

impl<'env> BatchVerifier<'env> {
    /// Create a new batch verifier with default configuration
    ///
    /// # Contract
    ///
    /// ENSURES: Verifier uses default threshold/thread settings
    /// ENSURES: Verifier inherits `env.mode()`
    pub fn new(env: &'env Environment) -> Self {
        Self::with_config(env, BatchConfig::default())
    }

    /// Create with custom configuration
    ///
    /// # Contract
    ///
    /// ENSURES: Verifier uses the provided `config` settings
    /// ENSURES: `config.mode == None` preserves `env.mode()`
    /// ENSURES: `config.mode == Some(mode)` explicitly overrides `env.mode()`
    pub fn with_config(env: &'env Environment, config: BatchConfig) -> Self {
        Self { env, config }
    }

    #[inline]
    fn effective_mode(&self) -> CleanMode {
        self.config.mode.unwrap_or(self.env.mode())
    }

    /// Check if a single expression is well-typed
    ///
    /// Returns the inferred type on success.
    ///
    /// # Contract
    ///
    /// ENSURES: `Ok(ty)` iff `expr` is well-typed, `ty` is its inferred type
    /// ENSURES: `Err(_)` iff `expr` has a type error
    #[inline]
    pub fn check_one(&self, expr: &Expr) -> Result<Expr, TypeError> {
        let tc = TypeChecker::with_mode(self.env, self.effective_mode());
        tc.infer_type(expr)
    }

    /// Check multiple expressions, returning results for each
    ///
    /// Results are in the same order as input expressions.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.len() == exprs.len()`
    /// ENSURES: `result[i].valid == check_one(&exprs[i]).is_ok()` for all i
    pub fn batch_check(&self, exprs: &[Expr]) -> Vec<BatchCheckResult> {
        if exprs.len() < self.config.parallel_threshold {
            self.batch_check_sequential(exprs)
        } else {
            self.batch_check_parallel(exprs)
        }
    }

    /// Check multiple expressions sequentially with cross-expression cache sharing.
    ///
    /// Reuses TypeChecker caches across expressions so that WHNF reductions,
    /// definitional equality results, and equivalence classes computed for one
    /// expression benefit subsequent expressions in the same batch.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.len() == exprs.len()`
    /// ENSURES: Results are in same order as input
    pub fn batch_check_sequential(&self, exprs: &[Expr]) -> Vec<BatchCheckResult> {
        self.check_chunk_with_shared_caches(exprs)
    }

    /// Check multiple expressions in parallel using rayon with per-chunk cache sharing.
    ///
    /// Partitions expressions into chunks (one per thread). Within each chunk,
    /// TypeChecker caches are reused across expressions. This avoids the overhead
    /// of creating fresh empty caches per expression while keeping threads independent.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.len() == exprs.len()`
    /// ENSURES: Results are in same order as input (order-preserving parallel iteration)
    pub fn batch_check_parallel(&self, exprs: &[Expr]) -> Vec<BatchCheckResult> {
        let num_threads = self
            .config
            .num_threads
            .unwrap_or_else(rayon::current_num_threads);
        let chunk_size = std::cmp::max(1, exprs.len() / num_threads.max(1));
        self.run_parallel(|| {
            let chunk_results: Vec<Vec<BatchCheckResult>> = exprs
                .par_chunks(chunk_size)
                .map(|chunk| self.check_chunk_with_shared_caches(chunk))
                .collect();
            chunk_results.into_iter().flatten().collect()
        })
    }

    /// Run a parallel operation using the configured thread pool.
    ///
    /// If `num_threads` is set, creates a dedicated thread pool with that many threads.
    /// Otherwise, uses the global rayon pool.
    ///
    /// # Contract
    ///
    /// ENSURES: Result is computed using parallelism
    /// ENSURES: If `config.num_threads.is_some()`, uses dedicated thread pool
    fn run_parallel<T: Send, F: FnOnce() -> T + Send>(&self, f: F) -> T {
        if let Some(threads) = self.config.num_threads {
            match rayon::ThreadPoolBuilder::new().num_threads(threads).build() {
                Ok(pool) => pool.install(f),
                Err(_) => {
                    // Fall back to global rayon pool on thread pool creation failure
                    // (e.g., resource exhaustion, OS thread limits).
                    f()
                }
            }
        } else {
            f()
        }
    }

    /// Check expressions with statistics
    ///
    /// # Contract
    ///
    /// ENSURES: `result.0.len() == exprs.len()`
    /// ENSURES: `result.1.total == exprs.len()`
    /// ENSURES: `result.1.valid + result.1.invalid == result.1.total`
    /// ENSURES: `result.1.wall_time_ns` reflects actual elapsed wall-clock time
    pub fn batch_check_with_stats(
        &self,
        exprs: &[Expr],
    ) -> (Vec<BatchCheckResult>, BatchCheckStats) {
        let wall_start = std::time::Instant::now();
        let results = self.batch_check(exprs);
        let wall_time_ns = wall_start.elapsed().as_nanos() as u64;

        let stats = compute_stats(&results, wall_time_ns);
        (results, stats)
    }

    /// Stream verification with callback and cross-expression cache sharing.
    ///
    /// Calls `on_result` for each expression. Returns early if callback returns `false`.
    /// This is useful for processing results as they complete without storing all results.
    ///
    /// # Contract
    ///
    /// ENSURES: `on_result` called at most once per expression in `exprs`
    /// ENSURES: Iteration stops when `on_result` returns `false`
    pub fn stream_check<F>(&self, exprs: impl Iterator<Item = Expr>, mut on_result: F)
    where
        F: FnMut(&Expr, &BatchCheckResult) -> bool,
    {
        let mut caches = TcCaches::default();
        for expr in exprs {
            let result = self.check_single_with_caches(&expr, &mut caches);
            if !on_result(&expr, &result) {
                break;
            }
        }
    }

    /// Stream verification with early termination on first valid expression.
    ///
    /// Calls `on_valid` for each valid expression. Returns early if callback returns `false`.
    /// Invalid expressions are silently skipped. Shares TypeChecker caches across
    /// expressions for amortized reduction costs.
    ///
    /// # Contract
    ///
    /// ENSURES: `on_valid` called only for well-typed expressions
    /// ENSURES: Iteration stops when `on_valid` returns `false`
    pub fn stream_valid<F>(&self, exprs: impl Iterator<Item = Expr>, mut on_valid: F)
    where
        F: FnMut(&Expr, &Expr) -> bool, // (expr, type) -> continue?
    {
        let mut caches = TcCaches::default();
        for expr in exprs {
            let tc = TypeChecker::with_mode_and_caches(self.env, self.effective_mode(), caches);
            let result = tc.infer_type(&expr);
            caches = tc.take_caches();
            if let Ok(ty) = result {
                if !on_valid(&expr, &ty) {
                    break;
                }
            }
        }
    }

    /// Find the first valid expression (common AI pattern).
    ///
    /// Returns the first expression that type-checks along with its inferred type.
    /// This is the most common AI use case: generate candidates, find first valid.
    /// Shares TypeChecker caches across expressions so that failed candidates
    /// still contribute cached reductions for subsequent candidates.
    ///
    /// # Contract
    ///
    /// ENSURES: `Some((expr, ty))` iff at least one expression in `exprs` is well-typed
    /// ENSURES: `None` iff no expression in `exprs` is well-typed
    /// ENSURES: If `Some`, `expr` is the first well-typed expression in iteration order
    pub fn find_first_valid(&self, exprs: impl Iterator<Item = Expr>) -> Option<(Expr, Expr)> {
        let mut caches = TcCaches::default();
        for expr in exprs {
            let tc = TypeChecker::with_mode_and_caches(self.env, self.effective_mode(), caches);
            let result = tc.infer_type(&expr);
            caches = tc.take_caches();
            if let Ok(ty) = result {
                return Some((expr, ty));
            }
        }
        None
    }

    /// Find any valid expression in parallel (not necessarily first in order)
    ///
    /// Processes expressions in parallel with early termination when a valid one is found.
    /// Returns a valid expression and its type. Due to parallel execution, this may not
    /// be the first valid expression in the input order - use `find_first_valid` for
    /// deterministic ordering.
    ///
    /// # Contract
    ///
    /// ENSURES: `Some((expr, ty))` iff at least one expression in `exprs` is well-typed
    /// ENSURES: `None` iff no expression in `exprs` is well-typed
    /// ENSURES: If `Some`, `expr` is some (not necessarily first) well-typed expression
    pub fn find_first_valid_parallel(&self, exprs: &[Expr]) -> Option<(Expr, Expr)> {
        let found = AtomicBool::new(false);
        let num_threads = self
            .config
            .num_threads
            .unwrap_or_else(rayon::current_num_threads);
        let chunk_size = std::cmp::max(1, exprs.len() / num_threads.max(1));
        self.run_parallel(|| {
            exprs.par_chunks(chunk_size).find_map_any(|chunk| {
                let mut caches = TcCaches::default();
                for e in chunk {
                    if found.load(Ordering::Relaxed) {
                        return None;
                    }
                    let tc = TypeChecker::with_mode_and_caches(
                        self.env,
                        self.effective_mode(),
                        std::mem::take(&mut caches),
                    );
                    let result = tc.infer_type(e);
                    caches = tc.take_caches();
                    if let Ok(ty) = result {
                        found.store(true, Ordering::Relaxed);
                        return Some((e.clone(), ty));
                    }
                }
                None
            })
        })
    }

    /// Count valid expressions without storing results.
    ///
    /// More memory-efficient than `batch_check` when you only need the count.
    /// Shares TypeChecker caches across expressions (sequential) or per-chunk
    /// (parallel) for amortized reduction costs.
    ///
    /// # Contract
    ///
    /// ENSURES: `result == exprs.iter().filter(|e| check_one(e).is_ok()).count()`
    pub fn count_valid(&self, exprs: &[Expr]) -> usize {
        if exprs.len() < self.config.parallel_threshold {
            let mut caches = TcCaches::default();
            exprs
                .iter()
                .filter(|e| self.check_single_with_caches(e, &mut caches).valid)
                .count()
        } else {
            let num_threads = self
                .config
                .num_threads
                .unwrap_or_else(rayon::current_num_threads);
            let chunk_size = std::cmp::max(1, exprs.len() / num_threads.max(1));
            self.run_parallel(|| {
                exprs
                    .par_chunks(chunk_size)
                    .map(|chunk| {
                        let mut caches = TcCaches::default();
                        chunk
                            .iter()
                            .filter(|e| self.check_single_with_caches(e, &mut caches).valid)
                            .count()
                    })
                    .sum()
            })
        }
    }

    /// Get indices of valid expressions.
    ///
    /// Returns indices into the input slice for expressions that type-check.
    /// Shares TypeChecker caches across expressions (sequential) or per-chunk
    /// (parallel) for amortized reduction costs.
    ///
    /// # Contract
    ///
    /// ENSURES: All indices in result are in range `[0, exprs.len())`
    /// ENSURES: `exprs[i]` is well-typed for all `i` in result
    /// ENSURES: Indices are in ascending order
    pub fn valid_indices(&self, exprs: &[Expr]) -> Vec<usize> {
        if exprs.len() < self.config.parallel_threshold {
            let mut caches = TcCaches::default();
            exprs
                .iter()
                .enumerate()
                .filter_map(|(i, e)| {
                    self.check_single_with_caches(e, &mut caches)
                        .valid
                        .then_some(i)
                })
                .collect()
        } else {
            let num_threads = self
                .config
                .num_threads
                .unwrap_or_else(rayon::current_num_threads);
            let chunk_size = std::cmp::max(1, exprs.len() / num_threads.max(1));
            let mut indices: Vec<usize> = self.run_parallel(|| {
                exprs
                    .par_chunks(chunk_size)
                    .enumerate()
                    .flat_map(|(chunk_idx, chunk)| {
                        let base = chunk_idx * chunk_size;
                        let mut caches = TcCaches::default();
                        chunk
                            .iter()
                            .enumerate()
                            .filter_map(|(i, e)| {
                                self.check_single_with_caches(e, &mut caches)
                                    .valid
                                    .then_some(base + i)
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect()
            });
            // par_chunks preserves chunk order within each chunk, but chunks
            // may interleave in the flat_map; sort to fulfill contract.
            indices.sort_unstable();
            indices
        }
    }

    /// Convert a type inference result to a batch check result.
    pub(super) fn infer_result_to_batch_result(
        result: Result<Expr, TypeError>,
        time_ns: u64,
    ) -> BatchCheckResult {
        match result {
            Ok(ty) => BatchCheckResult::success(ty, time_ns),
            Err(e) => BatchCheckResult::failure(e.to_string(), time_ns),
        }
    }

    /// Internal: check a single expression with timing, reusing shared caches.
    ///
    /// Creates a TypeChecker with pre-populated caches, runs type inference,
    /// then extracts the updated caches back for the next call. This amortizes
    /// the cost of WHNF and def_eq computations across multiple expressions.
    pub(super) fn check_single_with_caches(
        &self,
        expr: &Expr,
        caches: &mut TcCaches,
    ) -> BatchCheckResult {
        let start = std::time::Instant::now();
        let tc = TypeChecker::with_mode_and_caches(
            self.env,
            self.effective_mode(),
            std::mem::take(caches),
        );
        let result = tc.infer_type(expr);
        *caches = tc.take_caches();
        Self::infer_result_to_batch_result(result, start.elapsed().as_nanos() as u64)
    }

    /// Internal: check a chunk of expressions sequentially with shared caches.
    ///
    /// Used by both `batch_check_sequential` and `batch_check_parallel` (per-chunk).
    fn check_chunk_with_shared_caches(&self, exprs: &[Expr]) -> Vec<BatchCheckResult> {
        let mut caches = TcCaches::default();
        exprs
            .iter()
            .map(|e| self.check_single_with_caches(e, &mut caches))
            .collect()
    }
}
