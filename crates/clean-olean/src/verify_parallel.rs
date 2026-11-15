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
#[cfg(feature = "cli")]
use clean_kernel::expr::Expr;
#[cfg(feature = "cli")]
use clean_kernel::tc::{TypeChecker, DEFAULT_HEARTBEAT_LIMIT};
#[cfg(feature = "cli")]
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
#[cfg(feature = "cli")]
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
#[cfg(feature = "cli")]
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
#[cfg(feature = "cli")]
pub(crate) fn typecheck_constants_parallel(
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

/// Full LOCAL consistency checking in parallel, with one verdict per exact
/// typed declaration. Every represented registry type is checked, followed by
/// the constant's value if its types checked, in `KernelTheory::Lean`. The
/// kernel checks run concurrently; their verdicts are then combined in Lean's
/// replay order (`verify_batch_full::replay_check::parallel`), so the result
/// equals [`crate::verify_batch_full::typecheck_constants_full`]'s: a target
/// that mentions itself, sits on a dependency cycle, is `unsafe`, or uses a
/// refused target fails. Non-target constants remain assumed.
pub fn typecheck_constants_full_parallel(
    env: &Environment,
    target_names: &BTreeSet<String>,
    num_threads: usize,
    max_heartbeats: u32,
) -> (usize, usize, BTreeMap<String, String>) {
    typecheck_constants_full_parallel_in_run(
        env,
        target_names,
        &BTreeSet::new(),
        &BTreeMap::new(),
        num_threads,
        max_heartbeats,
    )
}

/// [`typecheck_constants_full_parallel`] for one module of a multi-module
/// run: `not_admitted` holds every declaration an earlier module of the run
/// refused, and a target that mentions one is refused; `already_declared`
/// holds the module's declarations whose name the environment held before the
/// module was loaded (see
/// [`crate::verify_batch_full::typecheck_constants_full_streaming_in_run`]).
pub(crate) fn typecheck_constants_full_parallel_in_run(
    env: &Environment,
    target_names: &BTreeSet<String>,
    not_admitted: &BTreeSet<String>,
    already_declared: &BTreeMap<String, String>,
    num_threads: usize,
    max_heartbeats: u32,
) -> (usize, usize, BTreeMap<String, String>) {
    use crate::verify_batch_full::local_roster;
    let pool = match rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads.max(1))
        .thread_name(|idx| format!("tc-full-{idx}"))
        .build()
    {
        Ok(pool) => pool,
        Err(error) => {
            let roster = local_roster::resolve_targets(env, target_names);
            let checks = roster
                .declarations
                .keys()
                .map(|name| {
                    (
                        name.clone(),
                        vec![format!("local checker worker creation failed: {error}")],
                    )
                })
                .collect();
            return roster.finish(&checks);
        }
    };
    let prerequisites = BTreeSet::new();
    let scope = crate::verify_batch_full::ReplayScope {
        prerequisites: &prerequisites,
        not_admitted,
        already_declared,
    };
    crate::verify_batch_full::replay_check::parallel(
        env,
        target_names,
        &scope,
        &pool,
        max_heartbeats,
    )
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
pub(crate) fn build_error_summary(tc_errors: &BTreeMap<String, String>) -> ErrorSummary {
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
