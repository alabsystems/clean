// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parallel type-checking and enhanced error reporting for batch verification.
//!
//! Provides `typecheck_constants_parallel` which fans out constant type-checking
//! across a rayon thread pool, and `ErrorSummary` / `ExtendedBatchSummary` for
//! categorized error reporting.

use crate::verify_batch::{
    build_summary_with_mode, error_category, BatchSummary, ModuleResult, ValidationMode,
};
use clean_kernel::env::Environment;
use clean_kernel::expr::Expr;
use clean_kernel::tc::{TypeChecker, DEFAULT_HEARTBEAT_LIMIT};
use rayon::prelude::*;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Duration;

// -- Parallel type checking ---------------------------------------------------

/// Collect all `(name, &type_expr)` pairs from the environment in `target_names`.
///
/// WS1: the type `Expr` is borrowed by reference from the (immutable, longer-lived)
/// `&Environment` rather than deep-cloned up front. `&Expr` is `Send + Sync`, so
/// the references can be fanned out across the rayon pool directly.
fn collect_checkable_constants<'env>(
    env: &'env Environment,
    target_names: &BTreeSet<String>,
) -> Vec<(String, &'env Expr)> {
    let mut items = Vec::new();
    for ci in env.constants() {
        let name = ci.name.to_string();
        if target_names.contains(&name) {
            items.push((name, &ci.type_));
        }
    }
    for ind in env.inductives() {
        let name = ind.name.to_string();
        if target_names.contains(&name) {
            items.push((name, &ind.type_));
        }
    }
    for ctor in env.constructors() {
        let name = ctor.name.to_string();
        if target_names.contains(&name) {
            items.push((name, &ctor.type_));
        }
    }
    for rec in env.recursors() {
        let name = rec.name.to_string();
        if target_names.contains(&name) {
            items.push((name, &rec.type_));
        }
    }
    items
}

/// Build a per-worker, cache-enabled `TypeChecker` over an immutable env.
///
/// WS1 SOUNDNESS: the type cache is sound only while the `Environment` is fixed
/// for the checker's lifetime. In batch re-validation `env` is frozen (we
/// re-check already-registered constants against it and never mutate it), so a
/// reused cache-enabled checker bound to that single `&Environment` is sound.
/// `map_init` builds one of these per rayon worker and reuses it across the
/// items that worker processes, so `whnf`/`def_eq`/`infer` results for shared
/// library subterms are computed once and reused.
fn new_cached_worker(env: &Environment, max_heartbeats: u32) -> TypeChecker<'_> {
    let mut tc = TypeChecker::new(env);
    tc.enable_type_cache_pub();
    // SOUNDNESS: the heartbeat is a resource budget only (0 = unlimited). On
    // exhaustion the kernel conservatively REJECTS (whnf returns a less-reduced
    // but def-eq term; is_def_eq returns false), so raising/disabling it cannot
    // make an ill-typed constant pass — it only lets compute-heavy VALID
    // constants finish instead of aborting with HeartbeatExceeded.
    tc.set_heartbeat_limit(max_heartbeats);
    tc
}

/// Type-check constants in parallel using rayon.
///
/// Uses one long-lived, cache-enabled `TypeChecker` per rayon worker (via
/// `map_init`) rather than allocating a fresh checker per declaration.
/// `TypeChecker` is not `Sync` due to internal `RefCell` caches, but each
/// worker owns its checker and `Environment` is `Sync`.
///
/// Returns (pass_count, fail_count, errors) matching `typecheck_constants`.
pub fn typecheck_constants_parallel(
    env: &Environment,
    target_names: &BTreeSet<String>,
    num_threads: usize,
) -> (usize, usize, BTreeMap<String, String>) {
    let items = collect_checkable_constants(env, target_names);
    if items.is_empty() {
        return (0, 0, BTreeMap::new());
    }

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads.max(1))
        .thread_name(|idx| format!("tc-worker-{idx}"))
        .build()
        .expect("invariant: rayon thread pool creation should succeed");

    let results: Vec<(String, Result<(), String>)> = pool.install(|| {
        items
            .par_iter()
            .map_init(
                || new_cached_worker(env, DEFAULT_HEARTBEAT_LIMIT),
                |tc, (name, type_expr)| {
                    // Clean context per declaration so a prior erroring check
                    // (early return before its ctx_pop) cannot leak binders.
                    tc.reset_local_context();
                    // Refill the per-constant heartbeat budget: the long-lived
                    // worker checker shares one counter, so without this the
                    // budget drains cumulatively and later constants spuriously
                    // HeartbeatExceeded. Pure resource reset — no soundness effect.
                    tc.reset_heartbeat();
                    let result = tc
                        .infer_type(type_expr)
                        .map(|_| ())
                        .map_err(|e| format!("{e:?}"));
                    (name.clone(), result)
                },
            )
            .collect()
    });

    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut errors = BTreeMap::new();
    for (name, result) in results {
        match result {
            Ok(()) => pass += 1,
            Err(e) => {
                fail += 1;
                errors.insert(name, e);
            }
        }
    }
    (pass, fail, errors)
}

/// Collect `(name, &type, &value)` for constants that have values.
/// Only `ConstantInfo` has values; inductives/constructors/recursors do not.
///
/// WS1: type and value `Expr`s are borrowed from the immutable `&Environment`
/// rather than deep-cloned up front.
fn collect_checkable_values<'env>(
    env: &'env Environment,
    target_names: &BTreeSet<String>,
) -> Vec<(String, &'env Expr, &'env Expr)> {
    let mut items = Vec::new();
    for ci in env.constants() {
        let name = ci.name.to_string();
        if target_names.contains(&name) {
            if let Some(val) = &ci.value {
                items.push((name, &ci.type_, val));
            }
        }
    }
    items
}

/// Full `add_decl`-equivalent validation in parallel: `infer_sort` on types +
/// `check_type` on values, with `infer_only=false`.
///
/// Phase 1 runs `infer_sort` on all types in parallel.
/// Phase 2 runs `check_type` on all values in parallel (skipping any that
/// failed in phase 1).
///
/// Part of #3232
///
/// `max_heartbeats` is the per-check reduction/inference step budget applied to
/// every worker's kernel (`0` = unlimited). It is a pure RESOURCE limit, NOT a
/// soundness gate — see `new_cached_worker` / `typecheck_constants_full`.
pub fn typecheck_constants_full_parallel(
    env: &Environment,
    target_names: &BTreeSet<String>,
    num_threads: usize,
    max_heartbeats: u32,
) -> (usize, usize, BTreeMap<String, String>) {
    let type_items = collect_checkable_constants(env, target_names);
    if type_items.is_empty() {
        return (0, 0, BTreeMap::new());
    }

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads.max(1))
        .thread_name(|idx| format!("tc-full-{idx}"))
        .build()
        .expect("invariant: rayon thread pool creation should succeed");

    // Phase 1: infer_sort on all types (one cache-enabled checker per worker)
    let sort_results: Vec<(String, Result<(), String>)> = pool.install(|| {
        type_items
            .par_iter()
            .map_init(
                || new_cached_worker(env, max_heartbeats),
                |tc, (name, type_expr)| {
                    tc.reset_local_context();
                    // Per-constant heartbeat refill (see infer_type path above):
                    // the shared worker counter must restart for each constant
                    // or the budget drains across the batch. No soundness effect.
                    tc.reset_heartbeat();
                    let result = tc
                        .infer_sort(type_expr)
                        .map(|_| ())
                        .map_err(|e| format!("infer_sort: {e:?}"));
                    (name.clone(), result)
                },
            )
            .collect()
    });

    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut errors = BTreeMap::new();
    for (name, result) in sort_results {
        match result {
            Ok(()) => pass += 1,
            Err(e) => {
                fail += 1;
                errors.insert(name, e);
            }
        }
    }

    // Phase 2: check_type on values (only for constants that passed phase 1)
    let value_items = collect_checkable_values(env, target_names);
    if !value_items.is_empty() {
        let phase1_errors = &errors;
        let value_results: Vec<(String, Result<(), String>)> = pool.install(|| {
            value_items
                .par_iter()
                .filter(|(name, _, _)| !phase1_errors.contains_key(name))
                .map_init(
                    || new_cached_worker(env, max_heartbeats),
                    |tc, (name, type_expr, val_expr)| {
                        tc.reset_local_context();
                        // Per-constant heartbeat refill (see infer_type path):
                        // restart the shared worker counter for each value check.
                        // No soundness effect — heartbeat is a resource budget.
                        tc.reset_heartbeat();
                        let result = tc
                            .check_type(val_expr, type_expr)
                            .map(|_| ())
                            .map_err(|e| format!("check_type: {e:?}"));
                        (name.clone(), result)
                    },
                )
                .collect()
        });

        for (name, result) in value_results {
            if let Err(e) = result {
                // Demote from pass to fail
                pass = pass.saturating_sub(1);
                fail += 1;
                errors.insert(name, e);
            }
        }
    }

    (pass, fail, errors)
}

// -- Enhanced error summary ---------------------------------------------------

/// Detailed breakdown of errors by category, with example constant names.
#[derive(Debug, Clone, Serialize)]
pub struct ErrorSummary {
    /// Total number of errors across all categories.
    pub total_errors: usize,
    /// Errors grouped by category (using `error_category` classifier).
    pub by_category: BTreeMap<String, CategoryDetail>,
}

/// Detail for a single error category.
#[derive(Debug, Clone, Serialize)]
pub struct CategoryDetail {
    /// How many errors fall into this category.
    pub count: usize,
    /// Up to 5 example constant names that triggered this error.
    pub examples: Vec<String>,
}

/// Build an `ErrorSummary` from a map of constant_name -> error_message.
pub fn build_error_summary(tc_errors: &BTreeMap<String, String>) -> ErrorSummary {
    let mut by_category: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();
    for (name, err_msg) in tc_errors {
        let cat = error_category(err_msg);
        let entry = by_category.entry(cat).or_insert_with(|| (0, Vec::new()));
        entry.0 += 1;
        if entry.1.len() < 5 {
            entry.1.push(name.clone());
        }
    }
    let by_category = by_category
        .into_iter()
        .map(|(cat, (count, examples))| (cat, CategoryDetail { count, examples }))
        .collect();
    ErrorSummary {
        total_errors: tc_errors.len(),
        by_category,
    }
}

/// Extended batch summary that includes detailed error breakdown.
#[derive(Debug, Clone, Serialize)]
pub struct ExtendedBatchSummary {
    /// The standard batch summary.
    #[serde(flatten)]
    pub summary: BatchSummary,
    /// Detailed error breakdown (only present when there are errors).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_details: Option<ErrorSummary>,
}

/// Build an extended summary with categorized error details, honestly stamping
/// the [`ValidationMode`] that produced the pass/fail numbers.
pub fn build_extended_summary_with_mode(
    root: &Path,
    total_files: usize,
    processed_files: usize,
    results: Vec<ModuleResult>,
    elapsed: Duration,
    mode: ValidationMode,
) -> ExtendedBatchSummary {
    let mut all_errors = BTreeMap::new();
    for r in &results {
        for (name, err) in &r.tc_errors {
            all_errors.insert(name.clone(), err.clone());
        }
    }
    let error_details = if all_errors.is_empty() {
        None
    } else {
        Some(build_error_summary(&all_errors))
    };
    let summary =
        build_summary_with_mode(root, total_files, processed_files, results, elapsed, mode);
    ExtendedBatchSummary {
        summary,
        error_details,
    }
}

/// Back-compat shim labelling the summary as TYPE-ONLY (`InferOnly`). Prefer
/// [`build_extended_summary_with_mode`] when the full re-check may have run.
pub fn build_extended_summary(
    root: &Path,
    total_files: usize,
    processed_files: usize,
    results: Vec<ModuleResult>,
    elapsed: Duration,
) -> ExtendedBatchSummary {
    build_extended_summary_with_mode(
        root,
        total_files,
        processed_files,
        results,
        elapsed,
        ValidationMode::InferOnly,
    )
}
