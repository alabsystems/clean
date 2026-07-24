// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime for `clean olean verify-batch`.
//!
//! All helpers in this module were ported 1:1 from the legacy standalone
//! `verify_olean_batch` binary so the unified CLI preserves byte-identical
//! behaviour. The three top-level entry points (cumulative / parallel
//! cumulative / isolated) are dispatched by [`run_verify_batch`] based on
//! the resolved [`ResolvedArgs`].

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use tracing::{info, warn};

use clean_kernel::env::Environment;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;

use crate::verify_batch::{
    build_dependency_order, build_summary, build_summary_with_mode, collect_new_env_names,
    discover_olean_files, emit_summary, module_name_from_path, preload_init_with_snapshot,
    relative_display, verify_one_isolated, verify_one_module_load_shared,
    verify_one_module_with_mode_shared, ModuleResult, ValidationMode,
};
use crate::verify_cache::{
    file_content_hash, is_module_cached, load_cache, save_cache, update_cache_entry,
};
use crate::verify_parallel::{
    build_extended_summary_with_mode, typecheck_constants_full_parallel,
    typecheck_constants_parallel,
};
use crate::verify_report::{build_verification_report, write_report_to_file};
use crate::{default_search_paths, load_module_with_deps, LoadSummary};

use super::{OleanCliError, VerifyBatchArgs};

/// Normalised form of [`VerifyBatchArgs`] after validation and default-path
/// resolution. Mirrors the old binary's `CliArgs` struct so the copied runner
/// helpers keep working byte-for-byte.
#[derive(Debug)]
pub(super) struct ResolvedArgs {
    root: PathBuf,
    search_paths: Vec<PathBuf>,
    json_output: bool,
    json_report: Option<PathBuf>,
    limit: Option<usize>,
    isolated: bool,
    load_only: bool,
    parallel: usize,
    cache_file: Option<PathBuf>,
    full_validation: bool,
    /// Resolved kernel heartbeat budget for the full-validation re-check.
    /// `0` = unlimited. Defaults to `DEFAULT_HEARTBEAT_LIMIT` when the flag is
    /// omitted, preserving the historical behaviour exactly.
    max_heartbeats: u32,
    /// Directory for the `.clean-cache` Init snapshot (opt-in). `None` ⇒ the
    /// legacy full Init pre-load with no snapshot read/write.
    cache_dir: Option<PathBuf>,
    /// Streaming proof-value elision policy for `--full-validation`. `None`
    /// (default) preserves the eager, full-resident behaviour exactly.
    elide_proof_values: clean_kernel::env::ProofValueElision,
}

pub(super) fn resolve_args(args: VerifyBatchArgs) -> Result<ResolvedArgs, OleanCliError> {
    if args.parallel == 0 {
        return Err(OleanCliError::InvalidParallel);
    }
    if !args.olean_dir.is_dir() {
        return Err(OleanCliError::NotADirectory(args.olean_dir.clone()));
    }
    let root = args.olean_dir.clone();
    let mut search_paths = default_search_paths();
    search_paths.extend(args.init_paths);
    search_paths.push(root.clone());
    Ok(ResolvedArgs {
        root,
        search_paths,
        json_output: args.json,
        json_report: args.json_report,
        limit: args.limit,
        isolated: args.isolated,
        load_only: args.load_only,
        parallel: args.parallel,
        cache_file: args.cache_file,
        full_validation: args.full_validation,
        // Omitted flag => preserve the historical hardcoded default exactly.
        // `--max-heartbeats 0` opts into unlimited.
        max_heartbeats: args.max_heartbeats.unwrap_or(DEFAULT_HEARTBEAT_LIMIT),
        cache_dir: args.cache_dir,
        elide_proof_values: args.stream_elide_proof_values.into(),
    })
}

/// Top-level dispatcher: validates args, spawns the legacy 1 GiB-stack
/// worker thread, and picks the isolated / parallel / serial cumulative path.
pub(super) fn run_verify_batch(args: VerifyBatchArgs) -> Result<(), OleanCliError> {
    let resolved = resolve_args(args)?;
    // The original binary spawned a 1 GiB-stack thread to avoid kernel-stack
    // exhaustion during deep recursion in very large module DAGs. Preserve
    // that here so `clean olean verify-batch` matches the legacy behaviour.
    let handle = std::thread::Builder::new()
        .name("verify-batch".to_owned())
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || {
            if resolved.isolated {
                run_isolated_verification(&resolved);
            } else if resolved.parallel > 1 {
                run_cumulative_parallel(&resolved);
            } else {
                run_cumulative_verification(&resolved);
            }
        })
        .expect("invariant: thread spawn should succeed");
    handle.join().expect("verification thread panicked");
    Ok(())
}

// -- Logging helpers ----------------------------------------------------------

fn log_module_result(idx: usize, total: usize, r: &ModuleResult, json: bool) {
    if json {
        return;
    }
    let status = if !r.load_ok {
        "LOAD_ERR"
    } else if r.tc_fail > 0 {
        "TC_FAIL"
    } else if r.tc_pass > 0 {
        "OK"
    } else {
        "LOADED"
    };
    info!(
        idx = idx + 1,
        total,
        status,
        module = r.module_name,
        elapsed_ms = r.elapsed_ms,
        tc_pass = r.tc_pass,
        tc_fail = r.tc_fail,
        added = r.constants_added,
        skipped = r.constants_skipped,
        "module"
    );
}

fn report_progress(idx: usize, total: usize, start: &Instant, last: &mut Instant) {
    if last.elapsed() > Duration::from_secs(60) {
        let elapsed = start.elapsed();
        let rate = (idx + 1) as f64 / elapsed.as_secs_f64();
        let remaining = (total - idx - 1) as f64 / rate;
        info!(
            done = idx + 1,
            total,
            rate_per_sec = format!("{rate:.1}"),
            eta_secs = format!("{remaining:.0}"),
            "progress"
        );
        *last = Instant::now();
    }
}

fn append_parse_failures(
    results: &mut Vec<ModuleResult>,
    failures: &[(PathBuf, String)],
    root: &Path,
) {
    for (path, err) in failures {
        results.push(ModuleResult {
            path: relative_display(path, root),
            module_name: module_name_from_path(path, root),
            load_ok: false,
            constants_added: 0,
            constants_skipped: 0,
            tc_pass: 0,
            tc_fail: 0,
            elapsed_ms: 0,
            load_error: Some(err.clone()),
            tc_errors: BTreeMap::new(),
        });
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_final_summary(
    root: &Path,
    total_files: usize,
    processed: usize,
    results: Vec<ModuleResult>,
    elapsed: Duration,
    json_output: bool,
    json_report_path: Option<&Path>,
    mode: ValidationMode,
) {
    if json_output {
        let ext =
            build_extended_summary_with_mode(root, total_files, processed, results, elapsed, mode);
        if let Some(report_path) = json_report_path {
            let report = build_verification_report(&ext.summary, ext.error_details.as_ref());
            if let Err(e) = write_report_to_file(&report, report_path) {
                warn!(err = %e, path = %report_path.display(), "failed to write JSON report");
            } else {
                info!(path = %report_path.display(), "wrote verification report");
            }
        }
        let out = serde_json::to_string_pretty(&ext)
            .expect("invariant: ExtendedBatchSummary is always serializable");
        use std::io::Write;
        std::io::stdout()
            .write_all(out.as_bytes())
            .expect("invariant: stdout write should not fail");
        std::io::stdout().write_all(b"\n").ok();
    } else {
        let summary = build_summary_with_mode(root, total_files, processed, results, elapsed, mode);
        if let Some(report_path) = json_report_path {
            let report = build_verification_report(&summary, None);
            if let Err(e) = write_report_to_file(&report, report_path) {
                warn!(err = %e, path = %report_path.display(), "failed to write JSON report");
            } else {
                info!(path = %report_path.display(), "wrote verification report");
            }
        }
        emit_summary(&summary, false);
    }
}

// -- Cumulative verification --------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn process_cached_module(
    env: &mut Environment,
    module_name: &str,
    rel_path: &str,
    desc_path: &Path,
    args: &ResolvedArgs,
    known_names: &mut HashSet<String>,
    visited: &mut hashbrown::HashSet<String>,
    cache: &mut Option<crate::verify_cache::VerificationCache>,
    cache_hits: &mut usize,
) -> ModuleResult {
    let file_hash = if cache.is_some() {
        std::fs::read(desc_path).ok().map(|b| file_content_hash(&b))
    } else {
        None
    };

    let skip_tc = match (&*cache, &file_hash) {
        (Some(c), Some(hash)) => is_module_cached(c, module_name, hash),
        _ => false,
    };
    if skip_tc && !args.load_only {
        *cache_hits += 1;
    }

    let effective_load_only = args.load_only || skip_tc;
    let mode = run_mode(args);
    let mut result = verify_one_module_with_mode_shared(
        env,
        module_name,
        rel_path,
        &args.search_paths,
        known_names,
        effective_load_only,
        mode,
        args.max_heartbeats,
        args.elide_proof_values,
        visited,
    );

    if skip_tc && result.load_ok {
        if let (Some(c), Some(ref hash)) = (&*cache, &file_hash) {
            if let Some(names) = crate::verify_cache::cached_constant_names(c, module_name, hash) {
                result.tc_pass = names.len();
                result.tc_fail = 0;
            }
        }
    }

    if let (Some(ref mut c), Some(ref hash)) = (cache, &file_hash) {
        if result.load_ok && !args.load_only {
            let verified: Vec<String> = if skip_tc {
                c.entries
                    .get(module_name)
                    .map(|e| e.verified_constants.clone())
                    .unwrap_or_default()
            } else {
                Vec::new()
            };
            update_cache_entry(c, module_name, hash, verified, result.tc_fail);
        }
    }
    result
}

fn run_cumulative_verification(args: &ResolvedArgs) {
    let olean_files = discover_olean_files(&args.root);
    let total_files = olean_files.len();
    info!(total = total_files, dir = %args.root.display(), "discovered .olean files");

    let (ordered_modules, parse_failures) = build_dependency_order(&olean_files, &args.root);
    let process_count = args
        .limit
        .map_or(ordered_modules.len(), |m| m.min(ordered_modules.len()));

    let mut env = Environment::default();
    preload_init_with_snapshot(
        &mut env,
        &args.root,
        &args.search_paths,
        args.cache_dir.as_deref(),
        args.full_validation,
        args.max_heartbeats,
        args.elide_proof_values,
    );

    let mut cache = args.cache_file.as_ref().map(|p| load_cache(p));
    let mut cache_hits = 0usize;
    let overall_start = Instant::now();
    let mut results: Vec<ModuleResult> = Vec::with_capacity(process_count);
    let mut last_progress = Instant::now();
    let mut known_names: HashSet<String> = HashSet::new();
    collect_new_env_names(&env, &mut known_names);
    // One `visited` set shared across ALL modules on the load-only fast path: in
    // dependency order each module's already-loaded imports short-circuit before
    // any `.olean` re-read, turning O(modules × closure) re-parsing into O(union)
    // (~4x faster on the v4.30 stdlib). See `load_module_with_deps_shared`.
    let mut shared_visited: hashbrown::HashSet<String> = hashbrown::HashSet::new();

    for (idx, desc) in ordered_modules.iter().take(process_count).enumerate() {
        let rel_path = relative_display(&desc.path, &args.root);
        let result = if args.load_only {
            verify_one_module_load_shared(
                &mut env,
                &desc.module_name,
                &rel_path,
                &args.search_paths,
                &mut shared_visited,
            )
        } else {
            process_cached_module(
                &mut env,
                &desc.module_name,
                &rel_path,
                &desc.path,
                args,
                &mut known_names,
                &mut shared_visited,
                &mut cache,
                &mut cache_hits,
            )
        };
        log_module_result(idx, process_count, &result, args.json_output);
        report_progress(idx, process_count, &overall_start, &mut last_progress);
        results.push(result);
    }

    // Load-only fast path defers no-confusion regeneration to ONE pass over the
    // complete environment (per-module regeneration on a partial env mis-generates
    // aux constants — see `import::tests::diag_full_shared_vs_perloop`). Count the
    // constants it produces via an environment-size delta — one O(env) pass, NOT a
    // per-module `collect_new_env_names` scan — so `constants_total` includes them.
    if args.load_only {
        let env_total = |e: &Environment| -> usize {
            e.constants().count()
                + e.inductives().count()
                + e.constructors().count()
                + e.recursors().count()
        };
        let before = env_total(&env);
        env.regenerate_missing_no_confusion();
        env.ensure_native_reducers();
        let regenerated = env_total(&env).saturating_sub(before);
        if regenerated > 0 {
            results.push(ModuleResult {
                path: "<final-regenerate>".to_string(),
                module_name: "<final-regenerate>".to_string(),
                load_ok: true,
                constants_added: regenerated,
                constants_skipped: 0,
                tc_pass: 0,
                tc_fail: 0,
                elapsed_ms: 0,
                load_error: None,
                tc_errors: BTreeMap::new(),
            });
        }
    }

    if cache_hits > 0 {
        info!(cache_hits, "modules skipped via incremental cache");
    }
    if let (Some(ref c), Some(ref path)) = (&cache, &args.cache_file) {
        if let Err(e) = save_cache(c, path) {
            warn!(err = %e, "failed to save verification cache");
        }
    }

    append_parse_failures(&mut results, &parse_failures, &args.root);
    emit_final_summary(
        &args.root,
        total_files,
        process_count,
        results,
        overall_start.elapsed(),
        args.json_output,
        args.json_report.as_deref(),
        run_mode(args),
    );
}

/// The honest [`ValidationMode`] this run executed: `Full` (add_decl-equivalent
/// `check_type` on proof values) iff `--full-validation` was passed, else the
/// type-only `InferOnly` fast path.
fn run_mode(args: &ResolvedArgs) -> ValidationMode {
    if args.full_validation {
        ValidationMode::Full
    } else {
        ValidationMode::InferOnly
    }
}

// -- Parallel-aware cumulative verification -----------------------------------

fn load_and_tc_parallel(
    env: &mut Environment,
    module_name: &str,
    rel_path: &str,
    search_paths: &[PathBuf],
    known_names: &mut HashSet<String>,
    load_only: bool,
    num_threads: usize,
    mode: ValidationMode,
    max_heartbeats: u32,
) -> ModuleResult {
    let start = Instant::now();
    let load_result: Result<Vec<LoadSummary>, _> =
        load_module_with_deps(env, module_name, search_paths);
    let load_elapsed = start.elapsed();

    match load_result {
        Ok(summaries) => {
            let new_names = collect_new_env_names(env, known_names);
            let added = new_names.len();
            let skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();
            let (tc_pass, tc_fail, tc_errors) = if load_only {
                (0, 0, BTreeMap::new())
            } else {
                match mode {
                    ValidationMode::InferOnly => {
                        typecheck_constants_parallel(env, &new_names, num_threads)
                    }
                    ValidationMode::Full => typecheck_constants_full_parallel(
                        env,
                        &new_names,
                        num_threads,
                        max_heartbeats,
                    ),
                }
            };
            ModuleResult {
                path: rel_path.to_owned(),
                module_name: module_name.to_owned(),
                load_ok: true,
                constants_added: added,
                constants_skipped: skipped,
                tc_pass,
                tc_fail,
                elapsed_ms: load_elapsed.as_millis() as u64,
                load_error: None,
                tc_errors,
            }
        }
        Err(e) => ModuleResult {
            path: rel_path.to_owned(),
            module_name: module_name.to_owned(),
            load_ok: false,
            constants_added: 0,
            constants_skipped: 0,
            tc_pass: 0,
            tc_fail: 0,
            elapsed_ms: load_elapsed.as_millis() as u64,
            load_error: Some(format!("{e}")),
            tc_errors: BTreeMap::new(),
        },
    }
}

fn run_cumulative_parallel(args: &ResolvedArgs) {
    let olean_files = discover_olean_files(&args.root);
    let total_files = olean_files.len();
    info!(total = total_files, threads = args.parallel,
          dir = %args.root.display(), "parallel mode");

    let (ordered_modules, parse_failures) = build_dependency_order(&olean_files, &args.root);
    let process_count = args
        .limit
        .map_or(ordered_modules.len(), |m| m.min(ordered_modules.len()));

    let mut env = Environment::default();
    preload_init_with_snapshot(
        &mut env,
        &args.root,
        &args.search_paths,
        args.cache_dir.as_deref(),
        args.full_validation,
        args.max_heartbeats,
        args.elide_proof_values,
    );

    let overall_start = Instant::now();
    let mut results: Vec<ModuleResult> = Vec::with_capacity(process_count);
    let mut last_progress = Instant::now();
    let mut known_names: HashSet<String> = HashSet::new();
    collect_new_env_names(&env, &mut known_names);

    for (idx, desc) in ordered_modules.iter().take(process_count).enumerate() {
        let rel_path = relative_display(&desc.path, &args.root);
        let mode = run_mode(args);
        let result = load_and_tc_parallel(
            &mut env,
            &desc.module_name,
            &rel_path,
            &args.search_paths,
            &mut known_names,
            args.load_only,
            args.parallel,
            mode,
            args.max_heartbeats,
        );
        log_module_result(idx, process_count, &result, args.json_output);
        report_progress(idx, process_count, &overall_start, &mut last_progress);
        results.push(result);
    }

    append_parse_failures(&mut results, &parse_failures, &args.root);
    emit_final_summary(
        &args.root,
        total_files,
        process_count,
        results,
        overall_start.elapsed(),
        args.json_output,
        args.json_report.as_deref(),
        run_mode(args),
    );
}

// -- Isolated verification (legacy) -------------------------------------------

fn run_isolated_verification(args: &ResolvedArgs) {
    let olean_files = discover_olean_files(&args.root);
    let total_files = olean_files.len();
    let process_count = args.limit.map_or(total_files, |m| m.min(total_files));
    info!(total_files, processing = process_count,
          dir = %args.root.display(), "isolated mode");

    let overall_start = Instant::now();
    let mut results: Vec<ModuleResult> = Vec::with_capacity(process_count);
    let mut last_progress = Instant::now();

    for (idx, path) in olean_files.iter().take(process_count).enumerate() {
        let result = verify_one_isolated(path, &args.root, &args.search_paths);
        log_module_result(idx, process_count, &result, args.json_output);
        report_progress(idx, process_count, &overall_start, &mut last_progress);
        results.push(result);
    }

    let summary = build_summary(
        &args.root,
        total_files,
        process_count,
        results,
        overall_start.elapsed(),
    );
    if let Some(ref report_path) = args.json_report {
        let report = build_verification_report(&summary, None);
        if let Err(e) = write_report_to_file(&report, report_path) {
            warn!(err = %e, path = %report_path.display(), "failed to write JSON report");
        } else {
            info!(path = %report_path.display(), "wrote verification report");
        }
    }
    emit_summary(&summary, args.json_output);
}
