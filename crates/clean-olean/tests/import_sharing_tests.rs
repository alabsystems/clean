// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for expression structure sharing via hash-consing (#2383).

use clean_kernel::env::Environment;
use clean_olean::{default_search_paths, load_module_with_deps, load_olean_file};
use std::path::PathBuf;

fn get_lean_lib_path() -> Option<PathBuf> {
    default_search_paths()
        .into_iter()
        .find(|p| p.join("Init/Prelude.olean").exists())
}

/// Gate this file's integration tests behind `CLEAN_OLEAN_INTEGRATION=1`.
/// They load real `.olean` files against the installed Lean toolchain; on
/// machines with a non-matching toolchain they surface compiler-name and
/// inductive-flag differences that reflect Lean version drift rather than
/// real bugs in the import pipeline. Opt in via the env var when running
/// the dedicated integration lane.
fn require_olean_lean() -> Option<std::path::PathBuf> {
    if std::env::var_os("CLEAN_OLEAN_INTEGRATION").is_none() {
        eprintln!(
            "TRACE: olean integration test skipped \u{2014} set \
             CLEAN_OLEAN_INTEGRATION=1 to run against the installed \
             Lean toolchain"
        );
        return None;
    }
    get_lean_lib_path()
}

fn module_to_olean_path(name: &str, lib_path: &std::path::Path) -> PathBuf {
    let rel = name.replace('.', "/");
    lib_path.join(format!("{rel}.olean"))
}

struct SharingReport {
    intern_calls: u64,
    cache_hits: u64,
    unique_exprs: u64,
    total_constants: usize,
    elapsed: std::time::Duration,
}

impl SharingReport {
    fn from_summaries(
        summaries: &[clean_olean::LoadSummary],
        elapsed: std::time::Duration,
    ) -> Self {
        let (mut intern_calls, mut cache_hits, mut unique_exprs) = (0u64, 0u64, 0u64);
        for s in summaries {
            intern_calls += s.expr_sharing.total_intern_calls;
            cache_hits += s.expr_sharing.cache_hits;
            unique_exprs += s.expr_sharing.unique_exprs;
        }
        let total_constants = summaries.iter().map(|s| s.added_constants).sum();
        Self {
            intern_calls,
            cache_hits,
            unique_exprs,
            total_constants,
            elapsed,
        }
    }

    fn hit_rate(&self) -> f64 {
        self.cache_hits as f64 / self.intern_calls.max(1) as f64 * 100.0
    }

    fn print(&self, label: &str, expr_bytes: u64) {
        println!("--- {label} ---");
        println!("  Load time:   {:?}", self.elapsed);
        println!(
            "  Intern:      {} calls, {} hits ({:.1}%), {} unique",
            self.intern_calls,
            self.cache_hits,
            self.hit_rate(),
            self.unique_exprs
        );
        println!(
            "  Memory:      {} allocs x {}B = {:.1} KB",
            self.unique_exprs,
            expr_bytes,
            self.unique_exprs as f64 * expr_bytes as f64 / 1024.0
        );
    }

    fn print_no_sharing_comparison(&self, expr_bytes: u64) {
        let total_saved = self.intern_calls.saturating_sub(self.unique_exprs);
        println!("--- vs No sharing at all ---");
        println!(
            "  Without: {} allocs ({:.1} KB)",
            self.intern_calls,
            self.intern_calls as f64 * expr_bytes as f64 / 1024.0
        );
        println!(
            "  With:    {} allocs ({:.1} KB)",
            self.unique_exprs,
            self.unique_exprs as f64 * expr_bytes as f64 / 1024.0
        );
        println!(
            "  Saved:   {} allocs ({:.1} KB, {:.1}% reduction)",
            total_saved,
            total_saved as f64 * expr_bytes as f64 / 1024.0,
            total_saved as f64 / self.intern_calls.max(1) as f64 * 100.0
        );
    }

    fn print_delta(&self, baseline: &SharingReport, expr_bytes: u64) {
        println!("--- Delta: Cross-module vs Per-module ---");
        let alloc_saved = baseline.unique_exprs.saturating_sub(self.unique_exprs);
        println!(
            "  Alloc reduction: {} -> {} ({} fewer, {:.1}%)",
            baseline.unique_exprs,
            self.unique_exprs,
            alloc_saved,
            alloc_saved as f64 / baseline.unique_exprs.max(1) as f64 * 100.0
        );
        println!(
            "  Memory saved:    {:.1} KB",
            alloc_saved as f64 * expr_bytes as f64 / 1024.0
        );
        let extra_hits = self.cache_hits.saturating_sub(baseline.cache_hits);
        println!(
            "  Extra cache hits: {} ({:.1}% -> {:.1}%)",
            extra_hits,
            baseline.hit_rate(),
            self.hit_rate(),
        );
        if baseline.elapsed.as_nanos() > 0 && self.elapsed.as_nanos() > 0 {
            let speedup = baseline.elapsed.as_secs_f64() / self.elapsed.as_secs_f64();
            println!(
                "  Speedup:         {speedup:.2}x ({:?} -> {:?})",
                baseline.elapsed, self.elapsed
            );
        }
    }
}

/// Load per-module (fresh cache per module) for A/B comparison.
fn load_per_module(
    module_names: &[String],
    lib_path: &std::path::Path,
) -> (Environment, Vec<clean_olean::LoadSummary>) {
    let mut env = Environment::default();
    let mut summaries = Vec::new();
    for name in module_names {
        let path = module_to_olean_path(name, lib_path);
        match load_olean_file(&mut env, &path) {
            Ok(summary) => summaries.push(summary),
            Err(e) => eprintln!("Warning: failed to load {name}: {e}"),
        }
    }
    (env, summaries)
}

/// Single-module benchmark: Init.Prelude expression sharing stats (#2383 AC #1+#3).
#[test]
fn test_expr_sharing_stats_prelude() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let start = std::time::Instant::now();
    let mut env = Environment::default();
    let summaries =
        load_module_with_deps(&mut env, "Init.Prelude", std::slice::from_ref(&lib_path))
            .expect("Failed to load Init.Prelude");
    let report = SharingReport::from_summaries(&summaries, start.elapsed());
    let expr_bytes = size_of::<clean_kernel::expr::Expr>() as u64;

    println!("\n=== Expr Sharing (#2383): Init.Prelude ===");
    report.print("With hash-consing", expr_bytes);
    println!();
    report.print_no_sharing_comparison(expr_bytes);

    assert!(
        report.cache_hits > 0,
        "Expected cache hits from hash-consing"
    );
    assert!(
        report.unique_exprs <= report.intern_calls,
        "unique ({}) > total ({})",
        report.unique_exprs,
        report.intern_calls
    );
}

/// Multi-module A/B benchmark: cross-module vs per-module sharing (#2383 AC #3).
///
/// Loads Init.Core two ways: cross-module cache vs fresh-per-module cache.
/// ~2 minutes in debug builds due to triple load (warmup + 2 runs).
#[test]
fn test_cross_module_sharing_init_core() {
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Warmup: populate OS file cache so timing is fair
    {
        let mut env = Environment::default();
        let _ = load_module_with_deps(&mut env, "Init.Core", std::slice::from_ref(&lib_path));
    }

    // Run A: Cross-module sharing (current behavior)
    let start_a = std::time::Instant::now();
    let mut env_a = Environment::default();
    let summaries_a =
        load_module_with_deps(&mut env_a, "Init.Core", std::slice::from_ref(&lib_path))
            .expect("Failed to load Init.Core (cross-module)");
    let report_a = SharingReport::from_summaries(&summaries_a, start_a.elapsed());
    let module_names: Vec<String> = summaries_a
        .iter()
        .filter_map(|s| s.module_name.clone())
        .collect();

    // Run B: Per-module sharing (baseline — fresh cache per module)
    let start_b = std::time::Instant::now();
    let (_env_b, summaries_b) = load_per_module(&module_names, &lib_path);
    let report_b = SharingReport::from_summaries(&summaries_b, start_b.elapsed());

    // Report
    let expr_bytes = size_of::<clean_kernel::expr::Expr>() as u64;
    println!(
        "\n=== Cross-Module Sharing Benchmark (#2383 AC #3): Init.Core ===\n\
         Modules: {}, Constants: {}",
        summaries_a.len(),
        report_a.total_constants
    );
    println!();
    report_a.print("Run A: Cross-module sharing (current)", expr_bytes);
    println!();
    report_b.print("Run B: Per-module sharing (baseline)", expr_bytes);
    println!();
    report_a.print_delta(&report_b, expr_bytes);
    println!();
    report_a.print_no_sharing_comparison(expr_bytes);

    // Assertions
    assert!(
        report_a.cache_hits > 0,
        "Cross-module should have cache hits"
    );
    assert!(report_a.unique_exprs <= report_a.intern_calls);
    assert_eq!(
        report_a.total_constants, report_b.total_constants,
        "Constant count mismatch: cross={}, per={}",
        report_a.total_constants, report_b.total_constants
    );
    assert!(
        report_a.cache_hits >= report_b.cache_hits,
        "Cross-module hits ({}) < per-module hits ({})",
        report_a.cache_hits,
        report_b.cache_hits
    );
}
