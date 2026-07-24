// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for batch Mathlib `.olean` verification.
//!
//! These tests are intended to run when Mathlib build artifacts are available
//! locally. If Mathlib is not present, they skip gracefully instead of failing.

use clean_kernel::env::Environment;
use clean_kernel::test_utils::{run_with_stack, LARGE_STACK};
use clean_olean::dep_graph::DependencyGraph;
use clean_olean::verify_batch::{
    build_dependency_order, build_summary, collect_new_env_names, discover_olean_files,
    module_name_from_path, preload_init_if_needed, relative_display, verify_one_module,
    BatchSummary, ModuleDesc, ModuleResult,
};
use clean_olean::verify_batch_full::typecheck_constants_full;
use clean_olean::{default_search_paths, load_module_with_deps, parse_imports_only, LoadSummary};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

const MIN_MATHLIB_OLEANS: usize = 7000;
const FIRST_MODULE_LOAD_LIMIT: usize = 100;
const DATA_SAMPLE_SIZE: usize = 50;
const FULL_BATCH_PROGRESS_EVERY: usize = 250;

struct MathlibContext {
    root: PathBuf,
    search_paths: Vec<PathBuf>,
}

#[derive(Debug, Default, Clone, Copy)]
struct LoadStats {
    module_summaries: usize,
    added_constants: usize,
    skipped_constants: usize,
    duplicate_constants: usize,
}

fn find_mathlib_root() -> Option<PathBuf> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    for ancestor in manifest_dir.ancestors() {
        let candidate = ancestor.join("data/raw/mathlib4/.lake/build/lib");
        if let Some(root) = normalize_mathlib_root_candidate(&candidate) {
            return Some(root);
        }
    }

    if let Some(root) = normalize_mathlib_root_candidate(Path::new("/tmp/mathlib4/.lake/build/lib"))
    {
        return Some(root);
    }

    if let Some(value) = std::env::var_os("MATHLIB_PATH") {
        for candidate in std::env::split_paths(&value) {
            if let Some(root) = normalize_mathlib_root_candidate(&candidate) {
                return Some(root);
            }
        }
    }

    None
}

fn normalize_mathlib_root_candidate(candidate: &Path) -> Option<PathBuf> {
    if !candidate.exists() {
        return None;
    }

    if is_mathlib_lib_root(candidate) {
        return Some(candidate.to_path_buf());
    }

    // Lake builds place artifacts under lib/lean/ in newer versions
    let lean_subdir = candidate.join("lean");
    if lean_subdir.exists() && is_mathlib_lib_root(&lean_subdir) {
        return Some(lean_subdir);
    }

    let build_lib = candidate.join(".lake/build/lib");
    if is_mathlib_lib_root(&build_lib) {
        return Some(build_lib);
    }

    // Also check .lake/build/lib/lean/ for newer lake layouts
    let build_lib_lean = candidate.join(".lake/build/lib/lean");
    if build_lib_lean.exists() && is_mathlib_lib_root(&build_lib_lean) {
        return Some(build_lib_lean);
    }

    if candidate.file_name().is_some_and(|name| name == "Mathlib")
        && candidate.join("Data/Nat/Basic.olean").exists()
    {
        return candidate.parent().map(Path::to_path_buf);
    }

    None
}

fn is_mathlib_lib_root(path: &Path) -> bool {
    path.join("Mathlib.olean").exists()
        || path.join("Mathlib/Data/Nat/Basic.olean").exists()
        || path.join("Mathlib/Data/Real/Basic.olean").exists()
}

fn find_mathlib_project_root(root: &Path) -> Option<PathBuf> {
    root.ancestors()
        .find(|ancestor| {
            ancestor.join(".lake/build/lib") == root
                || ancestor.join(".lake/build/lib/lean") == root
        })
        .map(Path::to_path_buf)
}

fn push_unique_path(paths: &mut Vec<PathBuf>, seen: &mut HashSet<PathBuf>, path: PathBuf) {
    if path.exists() && seen.insert(path.clone()) {
        paths.push(path);
    }
}

fn build_mathlib_search_paths(root: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let mut seen = HashSet::new();

    push_unique_path(&mut paths, &mut seen, root.to_path_buf());

    if let Some(project_root) = find_mathlib_project_root(root) {
        let packages_dir = project_root.join(".lake/packages");
        let mut package_paths = Vec::new();
        if let Ok(entries) = std::fs::read_dir(packages_dir) {
            for entry in entries.flatten() {
                let package_root = entry.path();
                // Check all lake layout variants: build/lib, build/lib/lean,
                // .lake/build/lib, .lake/build/lib/lean
                for base in &["build/lib", ".lake/build/lib"] {
                    let lib_path = package_root.join(base);
                    if lib_path.exists() {
                        package_paths.push(lib_path.clone());
                    }
                    let lean_path = package_root.join(format!("{base}/lean"));
                    if lean_path.exists() {
                        package_paths.push(lean_path);
                    }
                }
            }
        }
        package_paths.sort();
        package_paths.dedup();
        for path in package_paths {
            push_unique_path(&mut paths, &mut seen, path);
        }
    }

    for path in default_search_paths() {
        push_unique_path(&mut paths, &mut seen, path);
    }

    paths
}

fn mathlib_context() -> Option<MathlibContext> {
    let root = find_mathlib_root()?;
    let search_paths = build_mathlib_search_paths(&root);
    Some(MathlibContext { root, search_paths })
}

fn require_mathlib(test_name: &str) -> Option<MathlibContext> {
    match mathlib_context() {
        Some(ctx) => {
            println!("\n=== {test_name} ===");
            println!("Mathlib root: {}", ctx.root.display());
            println!("Search paths: {}", ctx.search_paths.len());
            for path in ctx.search_paths.iter().take(5) {
                println!("  {}", path.display());
            }
            if ctx.search_paths.len() > 5 {
                println!("  ...");
            }
            Some(ctx)
        }
        None => {
            eprintln!("Skipping {test_name}: Mathlib not found");
            eprintln!("Checked:");
            eprintln!("  data/raw/mathlib4/.lake/build/lib");
            eprintln!("  /tmp/mathlib4/.lake/build/lib");
            match std::env::var_os("MATHLIB_PATH") {
                Some(value) => eprintln!("  MATHLIB_PATH={}", PathBuf::from(value).display()),
                None => eprintln!("  MATHLIB_PATH is not set"),
            }
            None
        }
    }
}

fn summarize_load(summaries: &[LoadSummary]) -> LoadStats {
    LoadStats {
        module_summaries: summaries.len(),
        added_constants: summaries.iter().map(|s| s.added_constants).sum(),
        skipped_constants: summaries.iter().map(|s| s.skipped_constants.len()).sum(),
        duplicate_constants: summaries.iter().map(|s| s.duplicate_constants).sum(),
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
            tc_errors: Default::default(),
        });
    }
}

fn print_batch_summary(label: &str, summary: &BatchSummary) {
    println!("\n=== {label} ===");
    println!("  Root: {}", summary.root_dir);
    println!("  Total files: {}", summary.total_files);
    println!("  Processed files: {}", summary.processed_files);
    println!("  Load success: {}", summary.load_success);
    println!("  Load failure: {}", summary.load_failure);
    println!("  Constants added: {}", summary.total_constants);
    println!("  Constants skipped: {}", summary.total_skipped);
    println!("  Type-check pass: {}", summary.tc_pass);
    println!("  Type-check fail: {}", summary.tc_fail);
    println!("  Pass rate: {:.2}%", summary.pass_rate_pct);
    println!("  Elapsed: {:.2}s", summary.total_elapsed_secs);

    if !summary.error_categories.is_empty() {
        println!("  Error categories:");
        for (category, count) in summary.error_categories.iter().take(10) {
            println!("    {category}: {count}");
        }
    }

    let sample_failures: Vec<_> = summary
        .modules
        .iter()
        .filter(|result| !result.load_ok || result.tc_fail > 0)
        .take(10)
        .collect();
    if !sample_failures.is_empty() {
        println!("  Sample failures:");
        for failure in sample_failures {
            if !failure.load_ok {
                println!(
                    "    LOAD {}: {}",
                    failure.module_name,
                    failure
                        .load_error
                        .as_deref()
                        .unwrap_or("unknown load error")
                );
            } else {
                println!(
                    "    TC {}: {} failures ({} passes)",
                    failure.module_name, failure.tc_fail, failure.tc_pass
                );
            }
        }
    }
}

fn run_verify_batch(
    ctx: &MathlibContext,
    modules: &[(PathBuf, String)],
    load_only: bool,
    progress_every: usize,
    label: &str,
) -> (Vec<ModuleResult>, std::time::Duration) {
    let mut env = Environment::default();
    preload_init_if_needed(&mut env, &ctx.root, &ctx.search_paths);

    let mut known_names = HashSet::new();
    collect_new_env_names(&env, &mut known_names);

    let start = Instant::now();
    let mut results = Vec::with_capacity(modules.len());

    for (idx, (path, module_name)) in modules.iter().enumerate() {
        let rel_path = relative_display(path, &ctx.root);
        let result = verify_one_module(
            &mut env,
            module_name,
            &rel_path,
            &ctx.search_paths,
            &mut known_names,
            load_only,
        );

        if progress_every <= 1
            || idx == 0
            || idx + 1 == modules.len()
            || (idx + 1) % progress_every == 0
            || !result.load_ok
            || result.tc_fail > 0
        {
            println!(
                "[{}/{}] {}: load_ok={}, added={}, skipped={}, tc_pass={}, tc_fail={}, elapsed={}ms",
                idx + 1,
                modules.len(),
                result.module_name,
                result.load_ok,
                result.constants_added,
                result.constants_skipped,
                result.tc_pass,
                result.tc_fail,
                result.elapsed_ms
            );
        }

        results.push(result);
    }

    let elapsed = start.elapsed();
    println!(
        "{label}: completed {} modules in {:.2}s",
        modules.len(),
        elapsed.as_secs_f64()
    );
    (results, elapsed)
}

struct SequentialLoadResult {
    successful: usize,
    distinct_modules: HashSet<String>,
    totals: LoadStats,
    env_constants: usize,
}

fn load_modules_sequentially(
    env: &mut Environment,
    modules: &[ModuleDesc],
    search_paths: &[PathBuf],
    limit: usize,
) -> SequentialLoadResult {
    let mut successful = 0usize;
    let mut distinct_modules = HashSet::new();
    let mut totals = LoadStats::default();

    for (idx, desc) in modules.iter().take(limit).enumerate() {
        let summaries = load_module_with_deps(env, &desc.module_name, search_paths)
            .unwrap_or_else(|e| panic!("failed to load {}: {e}", desc.module_name));

        let stats = summarize_load(&summaries);
        totals.module_summaries += stats.module_summaries;
        totals.added_constants += stats.added_constants;
        totals.skipped_constants += stats.skipped_constants;
        totals.duplicate_constants += stats.duplicate_constants;

        for summary in &summaries {
            if let Some(module_name) = &summary.module_name {
                distinct_modules.insert(module_name.clone());
            }
        }

        successful += 1;
        println!(
            "[{}/{}] {}: {} summaries, {} added, {} skipped, {} dup, env={}",
            idx + 1,
            limit,
            desc.module_name,
            stats.module_summaries,
            stats.added_constants,
            stats.skipped_constants,
            stats.duplicate_constants,
            env.num_constants()
        );
    }

    SequentialLoadResult {
        successful,
        distinct_modules,
        totals,
        env_constants: env.num_constants(),
    }
}

fn sample_modules_by_prefix(
    ordered_modules: &[ModuleDesc],
    prefix: &str,
    sample_size: usize,
) -> Vec<(PathBuf, String)> {
    let matches: Vec<_> = ordered_modules
        .iter()
        .filter(|desc| desc.module_name.starts_with(prefix))
        .collect();

    if matches.len() <= sample_size {
        return matches
            .into_iter()
            .map(|desc| (desc.path.clone(), desc.module_name.clone()))
            .collect();
    }

    let mut sample = Vec::with_capacity(sample_size);
    for i in 0..sample_size {
        let idx = i * matches.len() / sample_size;
        let desc = matches[idx];
        sample.push((desc.path.clone(), desc.module_name.clone()));
    }
    sample
}

#[test]
fn test_mathlib_discover_olean_files() {
    let Some(ctx) = require_mathlib("test_mathlib_discover_olean_files") else {
        return;
    };

    let start = Instant::now();
    let olean_files = discover_olean_files(&ctx.root);
    let elapsed = start.elapsed();

    println!(
        "Discovered {} .olean files in {:?}",
        olean_files.len(),
        elapsed
    );
    for path in olean_files.iter().take(5) {
        println!("  {}", relative_display(path, &ctx.root));
    }

    assert!(
        olean_files.len() > MIN_MATHLIB_OLEANS,
        "expected > {MIN_MATHLIB_OLEANS} Mathlib .olean files, found {}",
        olean_files.len()
    );
}

#[test]
fn test_mathlib_build_dependency_order() {
    let Some(ctx) = require_mathlib("test_mathlib_build_dependency_order") else {
        return;
    };

    run_with_stack(LARGE_STACK, move || {
        let discover_start = Instant::now();
        let olean_files = discover_olean_files(&ctx.root);
        println!(
            "Discovered {} .olean files in {:?}",
            olean_files.len(),
            discover_start.elapsed()
        );

        let graph_start = Instant::now();
        let (ordered_modules, parse_failures) = build_dependency_order(&olean_files, &ctx.root);
        println!(
            "Built dependency order for {} modules with {} parse failures in {:?}",
            ordered_modules.len(),
            parse_failures.len(),
            graph_start.elapsed()
        );

        assert!(
            parse_failures.is_empty(),
            "expected no parse failures, got {}",
            parse_failures.len()
        );
        assert_eq!(
            ordered_modules.len(),
            olean_files.len(),
            "expected dependency order to cover every .olean file"
        );

        let positions: HashMap<String, usize> = ordered_modules
            .iter()
            .enumerate()
            .map(|(idx, desc)| (desc.module_name.clone(), idx))
            .collect();

        let mut dependency_edges = 0usize;
        let mut zero_internal_import_modules = 0usize;

        for (idx, desc) in ordered_modules.iter().enumerate() {
            let bytes = std::fs::read(&desc.path)
                .unwrap_or_else(|e| panic!("failed to read {}: {e}", desc.path.display()));
            let imports = parse_imports_only(&bytes).unwrap_or_else(|e| {
                panic!("failed to parse imports for {}: {e}", desc.path.display())
            });

            let mut internal_imports = 0usize;
            for import in imports {
                if let Some(&dep_idx) = positions.get(import.module_name.as_str()) {
                    dependency_edges += 1;
                    internal_imports += 1;
                    assert!(
                        dep_idx < idx,
                        "dependency order violation: {} appears before dependency {}",
                        desc.module_name,
                        import.module_name
                    );
                }
            }

            if internal_imports == 0 {
                zero_internal_import_modules += 1;
            }
        }

        println!(
            "Topological order validated: {} edges, {} root modules",
            dependency_edges, zero_internal_import_modules
        );

        assert!(
            dependency_edges > ordered_modules.len(),
            "expected a non-trivial dependency graph, got {dependency_edges} edges"
        );
    });
}

#[test]
fn test_mathlib_load_first_100_modules() {
    let Some(ctx) = require_mathlib("test_mathlib_load_first_100_modules") else {
        return;
    };

    run_with_stack(LARGE_STACK, move || {
        let olean_files = discover_olean_files(&ctx.root);
        let (ordered_modules, parse_failures) = build_dependency_order(&olean_files, &ctx.root);

        assert!(
            parse_failures.is_empty(),
            "unexpected parse failures: {}",
            parse_failures.len()
        );
        assert!(
            ordered_modules.len() >= FIRST_MODULE_LOAD_LIMIT,
            "need at least {} ordered modules, got {}",
            FIRST_MODULE_LOAD_LIMIT,
            ordered_modules.len()
        );

        let mut env = Environment::default();
        preload_init_if_needed(&mut env, &ctx.root, &ctx.search_paths);

        let start = Instant::now();
        let result = load_modules_sequentially(
            &mut env,
            &ordered_modules,
            &ctx.search_paths,
            FIRST_MODULE_LOAD_LIMIT,
        );

        println!(
            "\n=== First {} Dependency-Ordered Loads ===",
            FIRST_MODULE_LOAD_LIMIT
        );
        println!("  Successful: {}", result.successful);
        println!("  Distinct modules: {}", result.distinct_modules.len());
        println!("  Added constants: {}", result.totals.added_constants);
        println!("  Env constants: {}", result.env_constants);
        println!("  Elapsed: {:?}", start.elapsed());

        assert_eq!(
            result.successful, FIRST_MODULE_LOAD_LIMIT,
            "expected all {} modules to load",
            FIRST_MODULE_LOAD_LIMIT
        );
        assert!(
            result.distinct_modules.len() >= FIRST_MODULE_LOAD_LIMIT,
            "expected >= {} distinct modules, got {}",
            FIRST_MODULE_LOAD_LIMIT,
            result.distinct_modules.len()
        );
        assert!(
            result.env_constants > 0,
            "expected environment to contain constants"
        );
    });
}

#[test]
fn test_mathlib_verify_batch_summary() {
    let Some(ctx) = require_mathlib("test_mathlib_verify_batch_summary") else {
        return;
    };

    run_with_stack(LARGE_STACK, move || {
        let olean_files = discover_olean_files(&ctx.root);
        let (ordered_modules, parse_failures) = build_dependency_order(&olean_files, &ctx.root);
        let module_list: Vec<(PathBuf, String)> = ordered_modules
            .iter()
            .map(|desc| (desc.path.clone(), desc.module_name.clone()))
            .collect();

        let (mut results, elapsed) = run_verify_batch(
            &ctx,
            &module_list,
            true,
            FULL_BATCH_PROGRESS_EVERY,
            "Mathlib load-only batch verification",
        );
        append_parse_failures(&mut results, &parse_failures, &ctx.root);

        let summary = build_summary(
            &ctx.root,
            olean_files.len(),
            ordered_modules.len(),
            results,
            elapsed,
        );
        print_batch_summary("Mathlib Full Batch Load-Only Summary", &summary);

        assert_eq!(
            summary.total_files,
            olean_files.len(),
            "summary total_files should match discovered files"
        );
        assert_eq!(
            summary.processed_files,
            ordered_modules.len(),
            "summary processed_files should match ordered modules"
        );
        assert_eq!(
            summary.load_failure,
            parse_failures.len(),
            "expected load-only failures to be limited to dependency-graph parse failures"
        );
        assert!(
            summary.load_success > MIN_MATHLIB_OLEANS,
            "expected > {MIN_MATHLIB_OLEANS} successful module loads, got {}",
            summary.load_success
        );
        assert_eq!(summary.tc_pass, 0, "load-only run should not type-check");
        assert_eq!(summary.tc_fail, 0, "load-only run should not type-check");
    });
}

#[test]
fn test_mathlib_typecheck_sample_modules() {
    let Some(ctx) = require_mathlib("test_mathlib_typecheck_sample_modules") else {
        return;
    };

    run_with_stack(LARGE_STACK, move || {
        let olean_files = discover_olean_files(&ctx.root);
        let (ordered_modules, parse_failures) = build_dependency_order(&olean_files, &ctx.root);
        assert!(
            parse_failures.is_empty(),
            "expected no parse failures before sampling Mathlib.Data modules, got {}",
            parse_failures.len()
        );

        let sampled_modules =
            sample_modules_by_prefix(&ordered_modules, "Mathlib.Data.", DATA_SAMPLE_SIZE);
        assert!(
            sampled_modules.len() >= DATA_SAMPLE_SIZE,
            "expected at least {DATA_SAMPLE_SIZE} Mathlib.Data modules, got {}",
            sampled_modules.len()
        );

        println!("Selected Mathlib.Data sample:");
        for (_, module_name) in sampled_modules.iter().take(10) {
            println!("  {module_name}");
        }
        if sampled_modules.len() > 10 {
            println!("  ...");
        }

        let (results, elapsed) = run_verify_batch(
            &ctx,
            &sampled_modules,
            false,
            1,
            "Mathlib.Data sampled type-check batch",
        );
        let summary = build_summary(
            &ctx.root,
            sampled_modules.len(),
            sampled_modules.len(),
            results,
            elapsed,
        );
        print_batch_summary("Mathlib.Data Sample Type-Check Summary", &summary);

        assert_eq!(
            summary.load_success,
            sampled_modules.len(),
            "expected all sampled modules to load successfully"
        );
        assert!(
            summary.tc_pass > 0,
            "expected sampled modules to produce type-check activity"
        );
        assert!(
            summary.tc_pass > summary.tc_fail,
            "expected more successful than failing type-checks, got {} pass / {} fail",
            summary.tc_pass,
            summary.tc_fail
        );
    });
}

fn top_level_namespace(module_name: &str) -> String {
    module_name.split('.').take(2).collect::<Vec<_>>().join(".")
}

fn print_namespace_distribution(modules: &[ModuleDesc]) {
    let mut namespace_counts: HashMap<String, usize> = HashMap::new();
    for desc in modules {
        *namespace_counts
            .entry(top_level_namespace(&desc.module_name))
            .or_insert(0) += 1;
    }
    println!("Namespace distribution ({} modules total):", modules.len());
    let mut ns_sorted: Vec<_> = namespace_counts.iter().collect();
    ns_sorted.sort_by(|a, b| b.1.cmp(a.1));
    for (ns, count) in ns_sorted.iter().take(15) {
        println!("  {ns}: {count}");
    }
}

fn print_namespace_tc_breakdown(results: &[ModuleResult]) {
    let mut ns_tc: HashMap<String, (usize, usize)> = HashMap::new();
    for result in results {
        let ns = top_level_namespace(&result.module_name);
        let entry = ns_tc.entry(ns).or_insert((0, 0));
        entry.0 += result.tc_pass;
        entry.1 += result.tc_fail;
    }
    println!("\n=== Per-Namespace TC Breakdown ===");
    let mut ns_tc_sorted: Vec<_> = ns_tc.iter().collect();
    ns_tc_sorted.sort_by_key(|x| std::cmp::Reverse((x.1).0));
    for (ns, (pass, fail)) in ns_tc_sorted.iter().take(20) {
        let rate = if *pass + *fail > 0 {
            *pass as f64 / (*pass + *fail) as f64 * 100.0
        } else {
            100.0
        };
        println!("  {ns}: {pass} pass, {fail} fail ({rate:.4}%)");
    }
}

fn print_tc_failures(results: &[ModuleResult]) {
    let failing_modules: Vec<_> = results.iter().filter(|r| r.tc_fail > 0).collect();
    if !failing_modules.is_empty() {
        println!(
            "\n=== Modules with TC Failures ({}) ===",
            failing_modules.len()
        );
        for result in &failing_modules {
            println!(
                "  {}: {} pass, {} fail",
                result.module_name, result.tc_pass, result.tc_fail
            );
            for (name, err) in result.tc_errors.iter().take(3) {
                println!("    {name}: {err}");
            }
            if result.tc_errors.len() > 3 {
                println!("    ... and {} more", result.tc_errors.len() - 3);
            }
        }
    }
}

fn print_load_failures(results: &[ModuleResult]) {
    let load_failures: Vec<_> = results.iter().filter(|r| !r.load_ok).collect();
    if !load_failures.is_empty() {
        println!("\n=== Load Failures ({}) ===", load_failures.len());
        for result in load_failures.iter().take(20) {
            println!(
                "  {}: {}",
                result.module_name,
                result.load_error.as_deref().unwrap_or("unknown")
            );
        }
    }
}

fn print_final_verdict(summary: &BatchSummary) {
    let total_tc = summary.tc_pass + summary.tc_fail;
    let pass_rate = if total_tc > 0 {
        summary.tc_pass as f64 / total_tc as f64 * 100.0
    } else {
        100.0
    };
    println!(
        "\n=== FINAL VERDICT ===\n  Modules: {}/{}\n  TC pass: {}\n  TC fail: {}\
         \n  Pass rate: {:.6}%\n  Elapsed: {:.1}s",
        summary.load_success,
        summary.total_files,
        summary.tc_pass,
        summary.tc_fail,
        pass_rate,
        summary.total_elapsed_secs
    );
}

/// Comprehensive TC scan across ALL Mathlib namespaces.
///
/// Unlike `test_mathlib_typecheck_sample_modules` which only samples `Mathlib.Data.*`,
/// this test processes ALL modules in cumulative dependency order with type-checking
/// enabled, giving accurate pass/fail counts across the entire Mathlib tree.
///
/// The cumulative approach is critical: each module's dependencies are already in the
/// shared environment, so only newly-introduced constants need TC. This is ~10x faster
/// than isolated per-module verification.
#[test]
fn test_mathlib_typecheck_comprehensive_cumulative() {
    let Some(ctx) = require_mathlib("test_mathlib_typecheck_comprehensive_cumulative") else {
        return;
    };

    run_with_stack(LARGE_STACK, move || {
        let olean_files = discover_olean_files(&ctx.root);
        let (ordered_modules, parse_failures) = build_dependency_order(&olean_files, &ctx.root);
        assert!(
            parse_failures.is_empty(),
            "expected no parse failures, got {}",
            parse_failures.len()
        );

        print_namespace_distribution(&ordered_modules);

        let module_list: Vec<(PathBuf, String)> = ordered_modules
            .iter()
            .map(|desc| (desc.path.clone(), desc.module_name.clone()))
            .collect();

        let (mut results, elapsed) = run_verify_batch(
            &ctx,
            &module_list,
            false, // TC enabled
            250,   // progress every 250 modules
            "Mathlib comprehensive cumulative TC scan",
        );
        append_parse_failures(&mut results, &parse_failures, &ctx.root);

        let summary = build_summary(
            &ctx.root,
            olean_files.len(),
            ordered_modules.len(),
            results.clone(),
            elapsed,
        );
        print_batch_summary("Mathlib Comprehensive TC Summary", &summary);
        print_namespace_tc_breakdown(&results);
        print_tc_failures(&results);
        print_load_failures(&results);

        assert!(
            summary.load_success > MIN_MATHLIB_OLEANS,
            "expected > {MIN_MATHLIB_OLEANS} successful loads, got {}",
            summary.load_success
        );
        assert!(
            summary.tc_pass > 0,
            "expected type-check activity, got 0 passes"
        );

        print_final_verdict(&summary);
    });
}

/// Reproducible, env-gated real-Mathlib **KernelVerified** regression gate.
///
/// The audit's #1 credibility gap was that the corpus-wide KV numbers
/// (~73–75%) were *measured but never committed* — nothing in the tree pinned a
/// real-Mathlib kernel-recheck. This test closes that for one module: it runs the
/// genuine `add_decl`-equivalent path — [`typecheck_constants_full`] (`infer_sort`
/// on every type **and** `check_type` on every value) — over a single Mathlib
/// module's OWN new constants (its dependency closure is loaded first and
/// excluded by the name diff), and asserts the Clean kernel rejects none.
///
/// It SKIPS cleanly (via [`require_mathlib`]) when no Mathlib tree is
/// discoverable, so CI stays green without the multi-GB corpus; point
/// `MATHLIB_PATH` at a build to actually exercise it. All thresholds are
/// env-overridable so the first real run can pin exact numbers without editing
/// code:
/// * `CLEAN_KV_TEST_MODULE`   — target module (default `Mathlib.Logic.Function.Basic`,
///   one of the two committed `kv_ratchet_slice.txt` modules → known kernel-clean).
/// * `CLEAN_KV_TEST_MIN_PASS` — non-vacuity floor on KV passes (default `1`).
/// * `CLEAN_KV_TEST_MAX_FAIL` — tolerated kernel rejections (default `0`, strict).
#[test]
fn test_mathlib_module_kv_recheck_reproducible() {
    let Some(ctx) = require_mathlib("test_mathlib_module_kv_recheck_reproducible") else {
        return;
    };
    run_with_stack(LARGE_STACK, move || {
        let target = std::env::var("CLEAN_KV_TEST_MODULE")
            .unwrap_or_else(|_| "Mathlib.Logic.Function.Basic".to_string());
        let min_pass: usize = std::env::var("CLEAN_KV_TEST_MIN_PASS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1);
        let max_fail: usize = std::env::var("CLEAN_KV_TEST_MAX_FAIL")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);

        // Resolve the target module's .olean beneath the search paths.
        let rel = format!("{}.olean", target.replace('.', "/"));
        let olean = ctx
            .search_paths
            .iter()
            .map(|p| p.join(&rel))
            .find(|p| p.is_file())
            .unwrap_or_else(|| {
                panic!("target module .olean not found for {target} (looked for {rel})")
            });

        // 1. Load the target's DIRECT imports (its dependency closure) FIRST.
        let imports: Vec<String> = {
            let bytes = std::fs::read(&olean).expect("read target .olean");
            parse_imports_only(&bytes)
                .expect("parse target imports")
                .into_iter()
                .map(|i| i.module_name)
                .collect()
        };
        let mut env = Environment::default();
        for dep in &imports {
            load_module_with_deps(&mut env, dep, &ctx.search_paths)
                .unwrap_or_else(|e| panic!("load dependency {dep}: {e}"));
        }
        // 2. Snapshot dependency names so the next diff isolates the target's OWN decls.
        let mut known: HashSet<String> = HashSet::new();
        collect_new_env_names(&env, &mut known);

        // 3. Load the target module; the newly-introduced names are exactly its own.
        load_module_with_deps(&mut env, &target, &ctx.search_paths)
            .unwrap_or_else(|e| panic!("load target {target}: {e}"));
        let own: BTreeSet<String> = collect_new_env_names(&env, &mut known);
        assert!(
            !own.is_empty(),
            "target {target} introduced no new constants (already covered by its deps?)"
        );

        // 4. Genuine kernel re-check of the module's own constants.
        let (pass, fail, errs) =
            typecheck_constants_full(&env, &own, clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT);

        println!("\n=== Mathlib KernelVerified re-check: {target} ===");
        println!("  own constants   : {}", own.len());
        println!("  KV pass         : {pass}");
        println!("  kernel-rejected : {fail}");
        for (n, e) in errs.iter().take(20) {
            println!("    REJECT {n}: {e}");
        }

        assert!(
            fail <= max_fail,
            "{target}: {fail} own constant(s) failed Clean-kernel re-check (tolerated {max_fail}); \
             first errors: {:?}",
            errs.iter().take(10).collect::<Vec<_>>()
        );
        assert!(
            pass >= min_pass,
            "{target}: only {pass} KernelVerified passes (< floor {min_pass}) — re-check was near-vacuous"
        );
    });
}

fn print_dep_graph_stats(graph: &DependencyGraph, build_time: std::time::Duration) {
    println!("\n=== Dependency Graph Stats ===");
    println!("  Build time: {:?}", build_time);
    println!("  Total modules: {}", graph.stats.total_modules);
    println!("  Total edges: {}", graph.stats.total_edges);
    println!("  Max depth: {}", graph.stats.max_depth);
    println!("  Cycle modules: {}", graph.stats.cycle_modules.len());
    println!("  Missing deps: {}", graph.stats.missing_deps.len());
    println!("  Parse failures: {}", graph.stats.parse_failures.len());
    println!("  Topo order length: {}", graph.topo_order.len());

    if !graph.stats.missing_deps.is_empty() {
        println!("  Sample missing deps (first 10):");
        for (module, dep) in graph.stats.missing_deps.iter().take(10) {
            println!("    {module} -> {dep}");
        }
    }

    let mut by_depth: Vec<_> = graph
        .walk_topo_order()
        .map(|node| (&node.module_name, node.depth))
        .collect();
    by_depth.sort_by_key(|x| std::cmp::Reverse(x.1));
    println!("  Deepest modules:");
    for (name, depth) in by_depth.iter().take(5) {
        println!("    depth={depth}: {name}");
    }
}

fn assert_dep_graph_valid(graph: &DependencyGraph, discovered_count: usize) {
    assert_eq!(
        graph.stats.total_modules,
        discovered_count - graph.stats.parse_failures.len(),
        "total_modules should match (discovered - parse_failures)"
    );
    assert!(
        graph.stats.total_modules > MIN_MATHLIB_OLEANS,
        "expected > {MIN_MATHLIB_OLEANS} modules, got {}",
        graph.stats.total_modules
    );
    assert_eq!(
        graph.topo_order.len(),
        graph.stats.total_modules,
        "topo_order should cover all modules"
    );
    assert!(
        graph.stats.total_edges > graph.stats.total_modules,
        "expected more edges than modules for a non-trivial graph"
    );
    assert!(
        graph.stats.max_depth > 5,
        "expected max_depth > 5 for Mathlib"
    );
    assert!(
        graph.stats.parse_failures.is_empty(),
        "expected no parse failures"
    );

    let walk_count = graph.walk_topo_order().count();
    assert_eq!(walk_count, graph.stats.total_modules);
    assert!(!graph.is_empty());
    assert_eq!(graph.len(), graph.stats.total_modules);

    let first_name = &graph.topo_order[0];
    let first_node = graph.get(first_name).expect("first module should exist");
    assert_eq!(&first_node.module_name, first_name);
}

#[test]
fn test_mathlib_dependency_graph_stats() {
    let Some(ctx) = require_mathlib("test_mathlib_dependency_graph_stats") else {
        return;
    };

    run_with_stack(LARGE_STACK, move || {
        let discover_start = Instant::now();
        let olean_files = discover_olean_files(&ctx.root);
        println!(
            "Discovered {} .olean files in {:?}",
            olean_files.len(),
            discover_start.elapsed()
        );

        let graph_start = Instant::now();
        let graph = DependencyGraph::build(&olean_files, &ctx.root);
        let graph_elapsed = graph_start.elapsed();

        print_dep_graph_stats(&graph, graph_elapsed);
        assert_dep_graph_valid(&graph, olean_files.len());
    });
}
