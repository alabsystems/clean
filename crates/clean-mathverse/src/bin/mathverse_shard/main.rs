// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse shard build and verification CLI.
//!
//! Builds `.mathverse` shard files from Lean 4 `.olean` libraries,
//! verifies shard integrity via blake3 checksums, and runs kernel
//! verification on all constants to get actual verified counts.
//!
//! Usage:
//!   mathverse_shard build <lean-lib-dir> <output-dir> [options]
//!   mathverse_shard build-native <output-dir>
//!   mathverse_shard verify <shard-dir>
//!   mathverse_shard verify-kernel <shard-dir> [--json=<path>] [--incremental]
//!   mathverse_shard verify-kernel --corpus <shard-dir>
//!   mathverse_shard verify-kernel --native <shard-dir>
//!   mathverse_shard verify-kernel --per-constant <shard-dir>
//!   mathverse_shard verify-incremental <shard-dir>
//!   mathverse_shard coq-import --sexp-root=<dir> --out=<dir> [--library=<name>]... [--json=<path>] [--lean-faithful] [--no-stamp]
//!   mathverse_shard stamp --shard-dir=<dir> --manifest=<kernel-verified.json> [--json]
//!   mathverse_shard audit <shard-dir> [--json=<path>] [--name=<const>]
//!   mathverse_shard proof-search <shard-dir> [--goal=<name>] [--budget=<N>] [--json=<path>]

// Track B1: install mimalloc as this binary's allocator (behind `--features
// mimalloc`). `mathverse_shard verify-kernel --corpus-sharded` and the PARAGON
// in-process path both build/free large per-module reconstructions; mimalloc +
// the per-module `mi_collect` purge returns that freed memory to the OS instead
// of letting it ratchet the RSS high-water-mark. Soundness-neutral.
#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod coq_import_command;
mod native_build;
mod proof_commands;
mod sharded_commands;
mod stamp_command;
mod verify_commands;

use native_build::cmd_build_native;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;
use verify_commands::{cmd_verify_incremental, cmd_verify_kernel};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        print_usage();
        std::process::exit(1);
    }
    match args[1].as_str() {
        "build" => {
            if args.len() < 4 {
                print_build_usage();
                std::process::exit(1);
            }
            cmd_build(&args[2..]);
        }
        "build-coq" => {
            if args.len() < 4 {
                eprintln!(
                    "Usage: mathverse_shard build-coq <lean-lib-dir> <output-dir> \
                     [--coq-extract=<print-output>] [--max-file-size=N] [--verbose]"
                );
                std::process::exit(1);
            }
            cmd_build_coq(&args[2..]);
        }
        "build-native" => {
            if args.len() < 3 {
                eprintln!("Usage: mathverse_shard build-native <output-dir>");
                std::process::exit(1);
            }
            cmd_build_native(&args[2..]);
        }
        "verify" => {
            if args.len() < 3 {
                eprintln!("Usage: mathverse_shard verify <shard-dir>");
                std::process::exit(1);
            }
            cmd_verify(&args[2]);
        }
        "verify-kernel" => {
            if args.len() < 3 {
                eprintln!(
                    "Usage: mathverse_shard verify-kernel <shard-dir> [--json=<path>] [--incremental | --corpus]"
                );
                std::process::exit(1);
            }
            cmd_verify_kernel(&args[2..]);
        }
        "verify-incremental" => {
            if args.len() < 3 {
                eprintln!("Usage: mathverse_shard verify-incremental <shard-dir>");
                std::process::exit(1);
            }
            cmd_verify_incremental(Path::new(&args[2]));
        }
        "coq-import" => {
            if args.len() < 3 {
                eprintln!(
                    "Usage: mathverse_shard coq-import --sexp-root=<dir> --out=<dir> \
                     [--library=<name>]... [--json=<path>] [--lean-faithful] [--no-stamp]"
                );
                std::process::exit(1);
            }
            coq_import_command::cmd_coq_import(&args[2..]);
        }
        "stamp" => {
            if args.len() < 3 {
                eprintln!(
                    "Usage: mathverse_shard stamp --shard-dir=<dir> --manifest=<kernel-verified.json> [--json]"
                );
                std::process::exit(1);
            }
            stamp_command::cmd_stamp(&args[2..]);
        }
        "audit" => {
            if args.len() < 3 {
                eprintln!(
                    "Usage: mathverse_shard audit <shard-dir> [--json=<path>] [--name=<const>]"
                );
                std::process::exit(1);
            }
            proof_commands::cmd_audit(&args[2..]);
        }
        "proof-search" => {
            if args.len() < 3 {
                eprintln!("Usage: mathverse_shard proof-search <shard-dir> [--goal=<name>] [--budget=<N>] [--json=<path>]");
                std::process::exit(1);
            }
            proof_commands::cmd_proof_search(&args[2..]);
        }
        other => {
            eprintln!("Unknown command: {other}");
            print_usage();
            std::process::exit(1);
        }
    }
}

fn print_usage() {
    eprintln!("Usage: mathverse_shard <command> [args...]");
    eprintln!("Commands:");
    eprintln!("  build <lean-lib-dir> <output-dir> [options]");
    eprintln!("        Build .mathverse shards from .olean files");
    eprintln!("  build-coq <lean-lib-dir> <output-dir> [--coq-extract=<file>] [--verbose]");
    eprintln!("        Combined Lean 4 + Coq build; --coq-extract imports coqc -print output");
    eprintln!("  build-native <output-dir>");
    eprintln!("        Build the clean-Native shard (constructive, axiom-pure theorems");
    eprintln!("        proved inside this repo). Writes clean-native.mathverse + .json sidecar.");
    eprintln!("  verify <shard-dir>");
    eprintln!("        Verify integrity of .mathverse shards (checksum only)");
    eprintln!("  verify-kernel <shard-dir> [--json=<path>] [--incremental]");
    eprintln!("        Kernel-verify all constants in .mathverse shards");
    eprintln!("        --incremental: use shared environment with dependency ordering");
    eprintln!("  verify-kernel --corpus <shard-dir>");
    eprintln!("        Global dependency-closed re-verification: merge ALL shards into one");
    eprintln!("        library and re-verify the whole corpus in a single prelude-seeded");
    eprintln!("        kernel env in global topological order (resolves cross-shard deps)");
    eprintln!("  verify-kernel --native <shard-dir>");
    eprintln!("        Strict clean-Native gate: reject wrong source tags, sorry, axioms,");
    eprintln!("        definitions/opaques, axiom-dependent theorems, and kernel failures");
    eprintln!(
        "  verify-kernel --module <Mathlib.X.Y> --olean-root <dir>... [--emit <sidecar.json>]"
    );
    eprintln!("        WORKER (subprocess-sharding): fresh prelude env, load ONLY that module +");
    eprintln!("        its transitive dep closure, kernel-verify the module's OWN constants,");
    eprintln!("        write a non-destructive per-shard manifest, exit (OS reclaims memory).");
    eprintln!("  verify-kernel --corpus-sharded --olean-root <dir>... --out <dir> [--jobs N] [--module-list <file>]");
    eprintln!("        DRIVER: spawn one worker per module (re-exec self), bounded to N");
    eprintln!("        concurrent children, then merge all sidecars (name-union, summed");
    eprintln!(
        "        buckets) into <dir>/kernel-verified.json. Beats the 24 GiB whole-corpus OOM."
    );
    eprintln!("  verify-incremental <shard-dir>");
    eprintln!("        Incremental kernel verification with shared environment");
    eprintln!(
        "  coq-import --sexp-root=<dir> --out=<dir> [--library=<name>]... [--json=<path>] [--lean-faithful] [--no-stamp]"
    );
    eprintln!("        ONE-command Coq corpus harness: convert every <sexp-root>/<library>/*.sexp");
    eprintln!("        SerAPI dump to <out>/<library>/coq_<library>.mathverse, kernel-recheck the");
    eprintln!("        whole library corpus, write kernel-verified.json, stamp verdicts (unless");
    eprintln!("        --no-stamp), and report per-library trust distribution + BEDROCK counts");
    eprintln!("  stamp --shard-dir=<dir> --manifest=<kernel-verified.json> [--json]");
    eprintln!("        Apply an EXISTING merged kernel-verified manifest to pre-built shards");
    eprintln!("        on disk (NO re-verify). Persists the driver's full-closure verdict so a");
    eprintln!("        `clean mathverse stats` reader sees a stored KernelVerified count.");
    eprintln!("  audit <shard-dir> [--json=<path>] [--name=<const>]");
    eprintln!("        Axiom audit: classify proof quality for all declarations");
    eprintln!("        --name=<const>: audit a single declaration by name");
    eprintln!("  proof-search <shard-dir> [--goal=<name>] [--budget=<N>] [--json=<path>]");
    eprintln!("        Run proof search across loaded environment");
    eprintln!("        --goal=<name>: search for proof of a specific theorem's type");
    eprintln!("        --budget=<N>: max candidates to try (default: 10000)");
}

fn print_build_usage() {
    eprintln!("Usage: mathverse_shard build <lean-lib-dir> <output-dir> [options]");
    eprintln!("Options:");
    eprintln!("  --modules=Init,Std       Module prefixes (default: all)");
    eprintln!("  --shard-size=10000       Max constants per shard");
    eprintln!("  --max-file-size=2500000  Max .olean file size (bytes)");
    eprintln!("  --verbose                Print progress information");
}

fn cmd_build(args: &[String]) {
    use clean_mathverse::build_library::{build_lean4_library, BuildConfig};

    let lean_lib_dir = PathBuf::from(&args[0]);
    let output_dir = PathBuf::from(&args[1]);
    let opts = parse_build_opts(&args[2..]);

    if !lean_lib_dir.exists() {
        eprintln!("Error: directory not found: {}", lean_lib_dir.display());
        std::process::exit(1);
    }

    print_build_header(&lean_lib_dir, &output_dir, &opts);

    let config = BuildConfig {
        lean_lib_dir,
        output_dir: output_dir.clone(),
        modules: opts.modules,
        shard_size_limit: opts.shard_size,
        max_file_size: opts.max_file_size,
        verbose: opts.verbose,
    };

    let start = Instant::now();
    match build_lean4_library(&config) {
        Ok(result) => print_build_result(&result, &output_dir, start.elapsed()),
        Err(e) => {
            eprintln!("Build failed: {e}");
            std::process::exit(1);
        }
    }
}

/// `build-coq`: combined Lean 4 + Coq library build via
/// [`clean_mathverse::build_library::build_combined_library`]. Imports the Lean 4
/// `.olean` library, then (when `--coq-extract=<file>` is given) imports a
/// `coqc -print`-style extract through `coq::print_parser` and writes a
/// `coq_stdlib` shard. Connects the otherwise-orphaned `coq::print_parser` /
/// `coq::stdlib` capability.
fn cmd_build_coq(args: &[String]) {
    use clean_mathverse::build_library::build_combined_library;

    let lean_lib_dir = PathBuf::from(&args[0]);
    let output_dir = PathBuf::from(&args[1]);
    let mut coq_extract: Option<PathBuf> = None;
    let mut max_file_size: u64 = 2_500_000;
    let mut verbose = false;
    for arg in &args[2..] {
        if let Some(v) = arg.strip_prefix("--coq-extract=") {
            coq_extract = Some(PathBuf::from(v));
        } else if let Some(v) = arg.strip_prefix("--max-file-size=") {
            if let Ok(n) = v.parse() {
                max_file_size = n;
            }
        } else if arg == "--verbose" {
            verbose = true;
        }
    }

    if !lean_lib_dir.exists() {
        eprintln!("Error: directory not found: {}", lean_lib_dir.display());
        std::process::exit(1);
    }

    println!("=== Mathverse Combined Library Build (Lean 4 + Coq) ===");
    println!("  Lean lib dir: {}", lean_lib_dir.display());
    if let Some(ref c) = coq_extract {
        println!("  Coq extract:  {}", c.display());
    }
    println!("  Output dir:   {}\n", output_dir.display());

    match build_combined_library(
        &lean_lib_dir,
        coq_extract.as_deref(),
        &output_dir,
        max_file_size,
        verbose,
    ) {
        Ok(result) => {
            println!("  Coq constants:     {}", result.coq_constants);
            println!("  Total constants:   {}", result.total_constants);
            println!("\n  Completed in {} ms", result.elapsed_ms);
        }
        Err(e) => {
            eprintln!("Combined build failed: {e}");
            std::process::exit(1);
        }
    }
}

struct BuildOpts {
    modules: Vec<String>,
    shard_size: usize,
    max_file_size: u64,
    verbose: bool,
}

fn parse_build_opts(args: &[String]) -> BuildOpts {
    let mut opts = BuildOpts {
        modules: Vec::new(),
        shard_size: 10_000,
        max_file_size: 2_500_000,
        verbose: false,
    };
    for arg in args {
        if let Some(val) = arg.strip_prefix("--modules=") {
            opts.modules = val
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
        } else if let Some(val) = arg.strip_prefix("--shard-size=") {
            opts.shard_size = parse_or_exit(val, "--shard-size");
        } else if let Some(val) = arg.strip_prefix("--max-file-size=") {
            opts.max_file_size = parse_or_exit(val, "--max-file-size");
        } else if arg == "--verbose" {
            opts.verbose = true;
        } else {
            eprintln!("Unknown option: {arg}");
            std::process::exit(1);
        }
    }
    opts
}

fn parse_or_exit<T: std::str::FromStr>(val: &str, flag: &str) -> T {
    val.parse().unwrap_or_else(|_| {
        eprintln!("Invalid {flag} value: {val}");
        std::process::exit(1);
    })
}

fn print_build_header(lean_dir: &Path, out_dir: &Path, opts: &BuildOpts) {
    println!("=== Building Mathverse Shards ===");
    println!("  Lean lib dir: {}", lean_dir.display());
    println!("  Output dir:   {}", out_dir.display());
    if !opts.modules.is_empty() {
        println!("  Modules:      {}", opts.modules.join(", "));
    }
    println!(
        "  Shard size:   {}\n  Max file size: {}\n",
        opts.shard_size, opts.max_file_size
    );
}

fn print_build_result(
    result: &clean_mathverse::build_library::BuildResult,
    output_dir: &Path,
    elapsed: std::time::Duration,
) {
    let total_bytes = compute_dir_size(output_dir);
    println!("=== Build Complete ===");
    println!(
        "  Files discovered: {}  parsed: {}  failed: {}",
        result.total_files, result.files_parsed, result.files_failed
    );
    println!(
        "  Constants: {}  axioms: {}  with value: {}",
        result.total_constants, result.total_axioms, result.total_with_value
    );
    println!(
        "  Shards: {}  elapsed: {:.2}s  bytes: {} ({:.1} MB)",
        result.shards_written,
        elapsed.as_secs_f64(),
        total_bytes,
        total_bytes as f64 / 1_048_576.0
    );
    if !result.failed_files.is_empty() {
        println!("\n  First failures (up to 10):");
        for (path, err) in result.failed_files.iter().take(10) {
            println!("    {}: {}", path.display(), err);
        }
    }
}

fn cmd_verify(shard_dir: &str) {
    let shard_dir = Path::new(shard_dir);
    let manifest_path = shard_dir.join("manifest.json");

    println!("=== Verifying Mathverse Shards ===");
    println!("  Directory: {}", shard_dir.display());
    println!();

    if manifest_path.exists() {
        verify_with_manifest(&manifest_path, shard_dir);
    } else {
        verify_without_manifest(shard_dir);
    }
}

fn verify_without_manifest(shard_dir: &Path) {
    use clean_mathverse::manifest::verify_shard_integrity;

    println!("  No manifest.json found. Scanning for .mathverse files...");
    let mut mathverse_files = Vec::new();
    collect_mathverse_files(shard_dir, &mut mathverse_files);
    mathverse_files.sort();

    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }

    let (mut valid, mut corrupt) = (0usize, 0usize);
    let mut errors = Vec::new();

    for path in &mathverse_files {
        match verify_shard_integrity(path) {
            Ok(true) => {
                valid += 1;
                print_shard_ok(path);
            }
            Ok(false) => {
                corrupt += 1;
                errors.push(format!("{}: checksum mismatch", path.display()));
            }
            Err(e) => {
                corrupt += 1;
                errors.push(format!("{}: {e}", path.display()));
            }
        }
    }

    print_file_report(mathverse_files.len(), valid, corrupt, &errors);
    if corrupt > 0 {
        std::process::exit(1);
    }
}

fn verify_with_manifest(manifest_path: &Path, shard_dir: &Path) {
    use clean_mathverse::manifest::{verify_manifest_integrity, MathverseManifest};
    let manifest = match MathverseManifest::from_file(manifest_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error reading manifest: {e}");
            std::process::exit(1);
        }
    };
    let s = manifest.total_stats();
    println!(
        "  Manifest v{}: {} base + {} delta shards, {} constants, {} exprs\n",
        manifest.version, s.base_shards, s.delta_shards, s.total_constants, s.total_exprs
    );
    let report = verify_manifest_integrity(&manifest, shard_dir);
    print_manifest_report(&report);
    if !report.shards_corrupt.is_empty() || !report.shards_missing.is_empty() {
        std::process::exit(1);
    }
}

fn print_shard_ok(path: &Path) {
    if let Ok(r) = clean_mathverse::shard::ShardReader::from_file(path) {
        println!(
            "  OK: {} ({} constants, {} exprs)",
            path.display(),
            r.header.constant_count,
            r.header.expr_count
        );
    } else {
        println!("  OK: {} (checksum valid)", path.display());
    }
}

fn print_file_report(total: usize, valid: usize, corrupt: usize, errors: &[String]) {
    println!("\n=== Integrity Report ===");
    println!("  Files checked: {total}  valid: {valid}  corrupt: {corrupt}");
    for err in errors {
        println!("    {err}");
    }
}

fn print_manifest_report(report: &clean_mathverse::manifest::IntegrityReport) {
    println!("=== Integrity Report ===");
    println!(
        "  Shards checked: {}  valid: {}",
        report.shards_checked, report.shards_valid
    );
    for p in &report.shards_missing {
        println!("  Missing: {p}");
    }
    for p in &report.shards_corrupt {
        println!("  Corrupt: {p}");
    }
    for p in &report.shards_orphaned {
        println!("  Orphaned: {}", p.display());
    }
    if report.shards_corrupt.is_empty() && report.shards_missing.is_empty() {
        println!("  All shards OK.");
    }
}

fn collect_mathverse_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_mathverse_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "mathverse") {
                out.push(path);
            }
        }
    }
}

fn compute_dir_size(dir: &Path) -> u64 {
    let mut total = 0u64;
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                total += compute_dir_size(&path);
            } else {
                total += fs::metadata(&path).map(|m| m.len()).unwrap_or(0);
            }
        }
    }
    total
}
