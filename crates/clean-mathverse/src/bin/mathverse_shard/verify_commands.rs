// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_shard verify-kernel` and `verify-incremental` subcommands.
//!
//! Split from `main.rs` to keep the top-level CLI dispatcher under the
//! project-wide 500-line cap.

use std::path::{Path, PathBuf};
use std::time::Instant;

pub(crate) fn cmd_verify_kernel(args: &[String]) {
    // Sharded/streaming Lane-A path (worker `--module` / driver
    // `--corpus-sharded`). These do NOT take a positional shard-dir, so they
    // must claim the args before the legacy positional parser runs.
    if let Some(code) = crate::sharded_commands::try_cmd_sharded(args) {
        std::process::exit(code);
    }

    let opts = match parse_verify_kernel_args(args) {
        Ok(opts) => opts,
        Err(msg) => {
            eprintln!("{msg}");
            std::process::exit(1);
        }
    };

    if opts.corpus {
        cmd_verify_corpus(
            &opts.shard_dir,
            opts.emit_verified.as_deref(),
            opts.repair_levels,
            opts.elide_proofs,
        );
        return;
    }

    if opts.incremental {
        cmd_verify_incremental(&opts.shard_dir);
        return;
    }

    if opts.native {
        cmd_verify_native(&opts.shard_dir);
        return;
    }

    if opts.per_constant {
        cmd_verify_per_constant(&opts.shard_dir);
        return;
    }

    run_standard_verify_kernel(&opts.shard_dir, opts.json_output.as_deref());
}

struct VerifyKernelOpts {
    shard_dir: PathBuf,
    json_output: Option<PathBuf>,
    native: bool,
    incremental: bool,
    corpus: bool,
    per_constant: bool,
    emit_verified: Option<PathBuf>,
    repair_levels: bool,
    elide_proofs: clean_kernel::env::ProofValueElision,
}

fn parse_verify_kernel_args(args: &[String]) -> Result<VerifyKernelOpts, String> {
    let mut shard_dir: Option<PathBuf> = None;
    let mut json_output: Option<PathBuf> = None;
    let mut native = false;
    let mut incremental = false;
    let mut corpus = false;
    let mut per_constant = false;
    let mut emit_verified: Option<PathBuf> = None;
    let mut repair_levels = false;
    let mut elide_proofs = clean_kernel::env::ProofValueElision::None;

    for arg in args {
        if arg == "--native" {
            native = true;
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--corpus" {
            corpus = true;
        } else if arg == "--repair-levels" {
            repair_levels = true;
        } else if arg == "--per-constant" {
            per_constant = true;
        } else if let Some(val) = arg.strip_prefix("--elide-proofs=") {
            // Bounds resident memory for a whole-corpus pass by dropping
            // already-verified proof VALUES. `opaque` is statically sound;
            // `theorem` also drops theorem proofs and must be validated by an
            // unchanged kernel-verified count vs a non-elided run.
            elide_proofs = match val {
                "opaque" => clean_kernel::env::ProofValueElision::OpaqueOnly,
                "theorem" => clean_kernel::env::ProofValueElision::OpaqueAndTheorem,
                other => {
                    return Err(format!(
                        "Unknown --elide-proofs value '{other}' (expected 'opaque' or 'theorem')"
                    ))
                }
            };
        } else if let Some(val) = arg.strip_prefix("--json=") {
            json_output = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--emit-verified=") {
            emit_verified = Some(PathBuf::from(val));
        } else if arg.starts_with("--") {
            return Err(format!("Unknown option: {arg}"));
        } else if shard_dir.is_none() {
            shard_dir = Some(PathBuf::from(arg));
        } else {
            return Err(format!("Unexpected argument: {arg}"));
        }
    }

    let shard_dir = shard_dir.ok_or_else(|| {
        "Usage: mathverse_shard verify-kernel <shard-dir> [--json=<path>] [--incremental]\n   \
         or: mathverse_shard verify-kernel --corpus <shard-dir> [--emit-verified=<path>]\n   \
         or: mathverse_shard verify-kernel --native <shard-dir>\n   \
         or: mathverse_shard verify-kernel --per-constant <shard-dir>"
            .to_string()
    })?;

    let exclusive = [native, incremental, corpus, per_constant]
        .iter()
        .filter(|&&b| b)
        .count();
    if exclusive > 1 {
        return Err(
            "Error: --native, --incremental, --corpus, and --per-constant are mutually exclusive"
                .to_string(),
        );
    }

    if native && json_output.is_some() {
        return Err("Error: --json is not supported with --native".to_string());
    }

    if emit_verified.is_some() && !corpus {
        return Err("Error: --emit-verified=<path> requires --corpus".to_string());
    }

    if elide_proofs != clean_kernel::env::ProofValueElision::None && !corpus {
        return Err("Error: --elide-proofs=<opaque|theorem> requires --corpus".to_string());
    }

    Ok(VerifyKernelOpts {
        shard_dir,
        json_output,
        native,
        incremental,
        corpus,
        per_constant,
        emit_verified,
        repair_levels,
        elide_proofs,
    })
}

fn run_standard_verify_kernel(shard_dir: &Path, json_output: Option<&Path>) {
    use clean_mathverse::shard_verify::{
        discover_mathverse_files, verify_shard_dir_default, write_results_json,
    };

    println!("=== Mathverse Shard Kernel Verification ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }
    println!("  Found {} shard files\n", mathverse_files.len());

    let start = Instant::now();
    let report = verify_shard_dir_default(&mathverse_files);
    print_kernel_report(&report, start.elapsed());

    let default_path;
    let output_path = match json_output {
        Some(p) => p,
        None => {
            default_path = shard_dir.join("verify_results.json");
            default_path.as_path()
        }
    };
    match write_results_json(&report, output_path) {
        Ok(()) => println!("\n  Results written to: {}", output_path.display()),
        Err(e) => eprintln!("\n  Warning: {e}"),
    }
}

/// Per-constant foreign verification (`--per-constant`): kernel-checks every
/// constant in each shard individually via `verify::foreign`, reporting
/// finer-grained pass/axiom-accepted/fail/skip counts than the batch
/// `verify-kernel` path. Additive, opt-in; operates on the existing shard
/// corpus.
fn cmd_verify_per_constant(shard_dir: &Path) {
    use clean_mathverse::shard_verify::discover_mathverse_files;
    use clean_mathverse::verify::foreign::{verify_foreign_batch, BatchStats, VerifyForeignConfig};

    println!("=== Mathverse Shard Per-Constant Foreign Verification ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }
    println!("  Found {} shard files\n", mathverse_files.len());

    let start = Instant::now();
    let config = VerifyForeignConfig::default();
    let results = verify_foreign_batch(&mathverse_files, &config);
    let stats = BatchStats::from_results(&results);
    let elapsed = start.elapsed();

    println!("  Shards processed:   {}", stats.shards_processed);
    println!("  Constants total:    {}", stats.total_constants);
    println!("  Kernel-verified:    {}", stats.total_verified);
    println!("  Axiom-accepted:     {}", stats.total_axiom_accepted);
    println!("  Failed:             {}", stats.total_failed);
    println!("  Skipped:            {}", stats.total_skipped);
    println!("\n  Completed in {:.2}s", elapsed.as_secs_f64());

    if stats.total_failed > 0 {
        std::process::exit(1);
    }
}

fn cmd_verify_native(shard_dir: &Path) {
    use clean_mathverse::shard_verify::verify_native_shard_dir;

    println!("=== Mathverse Native Shard Gate ===");
    println!("  Directory: {}\n", shard_dir.display());

    let report = match verify_native_shard_dir(shard_dir) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("Error: {error}");
            std::process::exit(1);
        }
    };

    println!("  Checked {} declarations\n", report.checked);
    if report.violations.is_empty() {
        println!("  Native shard gate passed.");
        return;
    }

    for violation in &report.violations {
        eprintln!("  {}: {}", violation.name(), violation);
    }
    eprintln!("\n  {} violation(s) found", report.violations.len());
    std::process::exit(1);
}

fn print_kernel_report(
    report: &clean_mathverse::shard_verify::VerifyReport,
    elapsed: std::time::Duration,
) {
    print_kernel_shard_results(report);
    print_kernel_summary(&report.stats, elapsed);
    print_kernel_per_system(report);
}

fn print_kernel_shard_results(report: &clean_mathverse::shard_verify::VerifyReport) {
    for sr in &report.shard_results {
        let name = sr.path.file_name().unwrap_or_default().to_string_lossy();
        if let Some(ref e) = sr.error {
            eprintln!("  SKIP {name}: {e}");
        } else {
            println!(
                "  {name}: {} constants, {} verified, {} translated, {} failed",
                sr.num_constants, sr.verified, sr.translated, sr.failed,
            );
        }
    }
}

fn print_kernel_summary(
    stats: &clean_mathverse::shard_verify::VerifyStats,
    elapsed: std::time::Duration,
) {
    println!("\n=== Verification Summary ===");
    println!(
        "  Shards: {} processed, {} skipped",
        stats.shards_processed, stats.shards_skipped
    );
    println!(
        "  Constants: {} total, {} kernel-verified, {} translated",
        stats.total_constants, stats.kernel_verified, stats.translated
    );
    println!(
        "  Failed: {} reconstruct, {} type-check",
        stats.reconstruct_failed, stats.type_check_failed
    );
    println!("  Time: {:.2}s", elapsed.as_secs_f64());
    if stats.total_constants > 0 {
        let v = stats.kernel_verified as f64 / stats.total_constants as f64 * 100.0;
        let t = stats.translated as f64 / stats.total_constants as f64 * 100.0;
        println!("  Rates: {v:.1}% kernel-verified, {t:.1}% translated");
    }
}

fn print_kernel_per_system(report: &clean_mathverse::shard_verify::VerifyReport) {
    use clean_mathverse::shard_verify::source_system_name;

    println!(
        "\n=== Per-System Breakdown ===\n  {:<10} {:>8} {:>8} {:>10} {:>6}",
        "System", "Total", "Verified", "Translated", "Failed"
    );
    println!("  {}", "-".repeat(46));
    let mut systems: Vec<_> = report.per_system.values().collect();
    systems.sort_by_key(|s| std::cmp::Reverse(s.total));
    for sys in &systems {
        println!(
            "  {:<10} {:>8} {:>8} {:>10} {:>6}",
            source_system_name(sys.source_system),
            sys.total,
            sys.kernel_verified,
            sys.translated,
            sys.failed
        );
    }
}

/// Fast, kernel-free release gate: audit every shard's level-parameter windows
/// for the dedup-contiguity corruption (see [`clean_mathverse::shard_integrity`]).
/// Returns a process exit code (0 = clean, non-zero = corruption found under
/// `--strict`, or usage error). This catches — in seconds — the exact defect
/// that otherwise only surfaces as hundreds of thousands of `UndefinedLevelParam`
/// kernel-verification failures on a full corpus.
pub(crate) fn cmd_lint_levels(shard_dir: &Path, strict: bool) -> i32 {
    use clean_mathverse::shard::ShardReader;
    use clean_mathverse::shard_integrity::audit_level_param_integrity;
    use clean_mathverse::shard_verify::discover_mathverse_files;

    println!("=== Mathverse Level-Parameter Integrity Audit ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        return 1;
    }

    let mut any_corrupt = false;
    let (mut tot_with, mut tot_bad) = (0usize, 0usize);
    for path in &mathverse_files {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let reader = match ShardReader::from_file(path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("  SKIP {name}: {e}");
                continue;
            }
        };
        let report = audit_level_param_integrity(&reader);
        tot_with += report.with_params;
        tot_bad += report.corrupt;
        println!(
            "  {name}: {} with level-params, {} corrupt ({:.1}%)",
            report.with_params,
            report.corrupt,
            report.corrupt_rate() * 100.0,
        );
        if !report.is_clean() {
            any_corrupt = true;
            for c in report.sample.iter().take(5) {
                println!("      e.g. {} -> {:?}", c.constant, c.params);
            }
        }
    }

    let rate = if tot_with == 0 {
        0.0
    } else {
        tot_bad as f64 / tot_with as f64 * 100.0
    };
    println!("\n  Total: {tot_with} with level-params, {tot_bad} corrupt ({rate:.1}%)");
    if any_corrupt {
        println!(
            "  LEVEL-PARAM CORRUPTION DETECTED — this shard set must be rebuilt with a \
             contiguous level-param writer (add_string_block); see shard_integrity."
        );
        if strict {
            return 2;
        }
    } else {
        println!("  All level-parameter windows are contiguous and well-formed.");
    }
    0
}

pub(crate) fn cmd_verify_incremental(shard_dir: &Path) {
    use clean_mathverse::shard::ShardReader;
    use clean_mathverse::shard_verify::discover_mathverse_files;
    use clean_mathverse::verify::incremental::verify_shard_incremental_with_env;

    println!("=== Mathverse Shard Incremental Verification ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }
    println!("  Found {} shard files\n", mathverse_files.len());

    let start = Instant::now();
    let (mut tot, mut ver, mut fail, mut cyc, mut rec) = (0, 0, 0, 0, 0);

    for path in &mathverse_files {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let reader = match ShardReader::from_file(path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("  SKIP {name}: {e}");
                continue;
            }
        };
        // Seed the kernel prelude so universe-polymorphic + prelude-defined
        // constants resolve during re-verification. The empty-env path failed
        // ~99.67% of Lean Init constants on universe / unknown-constant errors;
        // seeding the prelude eliminates those buckets. (Cross-shard references
        // stay unresolved until a multi-shard global-topological loader exists —
        // shards are size-split, not dependency-closed.)
        let prelude = clean_kernel::Environment::try_with_prelude_for_import()
            .expect("kernel prelude environment");
        let r = verify_shard_incremental_with_env(&reader, prelude);
        println!(
            "  {name}: {} total, {} verified, {} failed, {} cycle-skipped, {:.2}s",
            r.total, r.kernel_verified, r.failed, r.cycle_skipped, r.elapsed_secs
        );
        tot += r.total;
        ver += r.kernel_verified;
        fail += r.failed;
        cyc += r.cycle_skipped;
        rec += r.reconstruct_failed;
    }

    print_incremental_summary(tot, ver, fail, cyc, rec, start.elapsed());
}

fn print_incremental_summary(
    tot: usize,
    ver: usize,
    fail: usize,
    cyc: usize,
    rec: usize,
    elapsed: std::time::Duration,
) {
    println!("\n=== Incremental Verification Summary ===");
    println!("  Total constants:      {tot}");
    println!("  Kernel verified:      {ver}");
    println!("  Failed:               {fail}");
    println!("  Cycle skipped:        {cyc}");
    println!("  Reconstruct failed:   {rec}");
    println!("  Elapsed:              {:.2}s", elapsed.as_secs_f64());
    if tot > 0 {
        println!(
            "  Verification rate:    {:.1}%",
            ver as f64 / tot as f64 * 100.0
        );
    }
}

#[path = "verify_corpus_commands.rs"]
mod corpus;

use corpus::cmd_verify_corpus;
