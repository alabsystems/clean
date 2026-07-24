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
        cmd_verify_corpus(&opts.shard_dir, opts.emit_verified.as_deref());
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
}

fn parse_verify_kernel_args(args: &[String]) -> Result<VerifyKernelOpts, String> {
    let mut shard_dir: Option<PathBuf> = None;
    let mut json_output: Option<PathBuf> = None;
    let mut native = false;
    let mut incremental = false;
    let mut corpus = false;
    let mut per_constant = false;
    let mut emit_verified: Option<PathBuf> = None;

    for arg in args {
        if arg == "--native" {
            native = true;
        } else if arg == "--incremental" {
            incremental = true;
        } else if arg == "--corpus" {
            corpus = true;
        } else if arg == "--per-constant" {
            per_constant = true;
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

    Ok(VerifyKernelOpts {
        shard_dir,
        json_output,
        native,
        incremental,
        corpus,
        per_constant,
        emit_verified,
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

/// Global, dependency-closed corpus verification (`--corpus`).
///
/// Loads EVERY discovered `.mathverse` shard into one merged `MathverseLibrary`
/// and re-verifies the whole corpus in a single prelude-seeded kernel
/// environment, in global topological order. Unlike `--incremental` (which runs
/// each shard against its own fresh prelude env), this resolves CROSS-SHARD
/// references — a constant in one shard whose type or value depends on a
/// constant defined in another — because the merged library puts every
/// dependency in one in-arena dependency graph.
fn cmd_verify_corpus(shard_dir: &Path, emit_verified: Option<&Path>) {
    use clean_mathverse::library::MathverseLibrary;
    use clean_mathverse::shard::ShardReader;
    use clean_mathverse::shard_verify::discover_mathverse_files;
    use clean_mathverse::trust::policy::TrustPolicy;
    use clean_mathverse::verify::incremental::verify_corpus_incremental_with_env;
    use clean_mathverse::verify::kernel_verified_manifest::KernelVerifiedManifest;

    println!("=== Mathverse Global Corpus Kernel Verification ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }
    println!("  Found {} shard files\n", mathverse_files.len());

    let start = Instant::now();

    // Merge every shard into one globally-indexed library.
    let mut library = MathverseLibrary::new(TrustPolicy::permissive());
    let mut loaded = 0usize;
    for path in &mathverse_files {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let reader = match ShardReader::from_file(path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("  SKIP {name}: {e}");
                continue;
            }
        };
        match library.load_shard(&reader) {
            Ok(added) => {
                loaded += 1;
                println!("  Loaded {name}: {added} constants");
            }
            Err(e) => eprintln!("  SKIP {name}: {e}"),
        }
    }
    println!(
        "\n  Merged {loaded} shards into {} constants\n",
        library.constant_count()
    );

    let prelude = clean_kernel::Environment::try_with_prelude_for_import()
        .expect("kernel prelude environment");
    let (env, report) = verify_corpus_incremental_with_env(&library, prelude);

    // BEDROCK = KernelVerified AND `axiom_deps` empty (transitive non-foundational
    // axiom closure ⊆ {propext, Quot.sound, Classical.choice}). KernelVerified
    // alone only means the value typechecked — a Definition whose body references
    // an assumed F* axiom typechecks but is NOT bedrock. This is the honest line:
    // we count only the constants that genuinely reduce to the 3 axioms.
    let bedrock: usize = report
        .kernel_verified_names
        .iter()
        .filter(|n| {
            env.axiom_deps(&clean_kernel::Name::from_string(n))
                .map(|d| d.is_empty())
                .unwrap_or(false)
        })
        .count();

    print_corpus_summary(&report, start.elapsed());
    println!(
        "  └─ of which BEDROCK:  {bedrock} (axiom_deps ⊆ propext / Quot.sound / Classical.choice)"
    );

    // Optionally record exactly which constants Clean's kernel re-verified, as a
    // non-destructive sidecar (the shards themselves are not rewritten).
    if let Some(path) = emit_verified {
        let manifest =
            KernelVerifiedManifest::from_report(&shard_dir.display().to_string(), loaded, &report);
        match manifest.write_to_file(path) {
            Ok(()) => println!(
                "\n  Wrote {} kernel-verified constant names to {}",
                manifest.kernel_verified_names.len(),
                path.display()
            ),
            Err(e) => eprintln!("\n  Warning: failed to write kernel-verified manifest: {e}"),
        }
    }

    if report.failed > 0 || report.reconstruct_failed > 0 {
        std::process::exit(1);
    }
}

fn print_corpus_summary(
    report: &clean_mathverse::verify::incremental::IncrementalVerifyReport,
    elapsed: std::time::Duration,
) {
    println!("=== Global Corpus Verification Summary ===");
    println!("  Total constants:      {}", report.total);
    println!("  Kernel verified:      {}", report.kernel_verified);
    println!("  Axiom-accepted:       {}", report.axiom_accepted);
    println!(
        "  Axiom-fallback:       {} (claimed value did NOT typecheck)",
        report.axiom_fallback
    );
    println!("  Failed:               {}", report.failed);
    println!("  Cycle skipped:        {}", report.cycle_skipped);
    println!("  Reconstruct failed:   {}", report.reconstruct_failed);
    println!("  Elapsed:              {:.2}s", elapsed.as_secs_f64());
    if report.total > 0 {
        println!(
            "  Verification rate:    {:.1}%",
            report.kernel_verified as f64 / report.total as f64 * 100.0
        );
    }
}
