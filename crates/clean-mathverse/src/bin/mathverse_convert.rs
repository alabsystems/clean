// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse Library conversion tool.
//!
//! Reads real math library files and converts them into Mathverse format,
//! producing JSON statistics and converted theorem records.
//!
//! Usage:
//!   mathverse_convert metamath <path-to-set.mm>
//!   mathverse_convert opentheory <path-to-article>
//!   mathverse_convert lean4-dir <olean-dir>  Verify+convert Lean 4 .olean directory
//!   mathverse_convert all <data-dir>         Convert all supported libraries in data dir
//!   mathverse_convert verify <shard-dir>     Kernel-verify constants in .mathverse shards

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_mathverse::export::convert_output::{
    ConvertOutputConfig, ConvertOutputWriter, OutputSummary, SystemSummary,
};
use clean_mathverse::lean4::olean::verify;
use clean_mathverse::olean_pipeline::{self, OleanPipelineConfig};
use clean_mathverse::source_refresh;
use clean_mathverse::verify::integration::{self, VerificationReport, VerifyOleanConfig};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: mathverse_convert <command> [args...]");
        eprintln!(
            "Commands: build, status, metamath, metamath-dir, lean4-dir, mathlib, all, stats, verify, refresh"
        );
        eprintln!("\nIncremental reconstruct (Phase 0):");
        eprintln!("  build [SYSTEMS...] [--out DIR] [--manifest PATH] [--force]   cached/incremental import (lane: metamath)");
        eprintln!("  status [--out DIR]                                          show the mathverse.lock.json build ledger");
        eprintln!("  update [--fetch] [--out DIR] [--manifest PATH]              rebuild only upstream-changed lanes (continuous update)");
        eprintln!("  fetch [--manifest PATH]                                     git-fetch sources and persist new SHAs");
        eprintln!("\nOptions:");
        eprintln!("  --output-dir <PATH>  Write persistent output to directory");
        eprintln!("\nRefresh subcommands:");
        eprintln!("  refresh --check                 Show stale sources");
        eprintln!("  refresh --update                Fetch updates for stale sources");
        eprintln!("  refresh --rebuild               Fetch + re-compile changed sources");
        eprintln!("  refresh --manifest <PATH>       Use custom manifest (default: data/mathverse_sources.toml)");
        std::process::exit(1);
    }

    // Parse --output-dir from anywhere in argv.
    let output_dir = parse_output_dir(&args);

    let require_arg = |usage: &str| -> &str {
        if args.len() < 3 {
            eprintln!("Usage: mathverse_convert {usage}");
            std::process::exit(1);
        }
        &args[2]
    };

    match args[1].as_str() {
        "mathlib" => cmd_mathlib(&args[2..]),
        "metamath" => convert_metamath(require_arg("metamath <path>")),
        "metamath-dir" => convert_metamath_dir(require_arg("metamath-dir <dir>")),
        "build" => cmd_build(&args[2..], output_dir.as_deref()),
        "status" => cmd_build_status(&args[2..], output_dir.as_deref()),
        "update" => cmd_update(&args[2..], output_dir.as_deref()),
        "fetch" => cmd_fetch(&args[2..]),
        "lean4-dir" => {
            let root = Path::new(require_arg("lean4-dir <olean-dir>"));
            let dir_name = root
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            if let Some(summary) = verify::verify_lean4_dir(root) {
                print_lean4_summary(&summary, &dir_name);
                write_lean4_json(root, &dir_name, &summary);
            }
        }
        "all" => convert_all(require_arg("all <data-dir>"), output_dir.as_deref()),
        "opentheory" => {
            let dir = Path::new(require_arg("opentheory <article-dir>"));
            let out = output_dir
                .clone()
                .unwrap_or_else(|| PathBuf::from("data/mathverse-shards"));
            std::fs::create_dir_all(&out).ok();
            convert_opentheory_dir(dir, &out);
        }
        "isabelle-binary" => {
            let dir = Path::new(require_arg("isabelle-binary <dir>"));
            let out = output_dir
                .clone()
                .unwrap_or_else(|| PathBuf::from("data/mathverse-shards"));
            std::fs::create_dir_all(&out).ok();
            convert_isabelle_dir(dir, &out);
        }
        "isabelle-mathlib-bridge" => {
            let isa_shard = Path::new(require_arg(
                "isabelle-mathlib-bridge <isabelle.mathverse> [mathlib-shard-dir]",
            ));
            let mathlib_dir = args.get(3).filter(|a| !a.starts_with("--")).map(Path::new);
            let out = output_dir
                .clone()
                .unwrap_or_else(|| PathBuf::from("data/mathverse-shards"));
            std::fs::create_dir_all(&out).ok();
            bridge_isabelle_mathlib(isa_shard, mathlib_dir, &out);
        }
        "stats" => show_stats(require_arg("stats <data-dir>")),
        "verify" => cmd_verify_shards(require_arg("verify <shard-dir>")),
        "verify-shard" => verify_shard_cmd(require_arg("verify-shard <path>")),
        "refresh" => cmd_refresh(&args[2..]),
        other => {
            eprintln!("Unknown command: {other}");
            std::process::exit(1);
        }
    }
}

/// Parse `--output-dir <PATH>` from the argument list.
fn parse_output_dir(args: &[String]) -> Option<PathBuf> {
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg == "--output-dir" {
            return iter.next().map(PathBuf::from);
        }
        if let Some(rest) = arg.strip_prefix("--output-dir=") {
            return Some(PathBuf::from(rest));
        }
    }
    None
}

// -- Mathlib conversion -------------------------------------------------------

/// Parse `mathlib` subcommand args into a [`MathlibBuildConfig`].
fn parse_mathlib_args(args: &[String]) -> clean_mathverse::build_mathlib::MathlibBuildConfig {
    use clean_mathverse::build_mathlib::MathlibBuildConfig;
    let mut config = MathlibBuildConfig {
        verbose: true,
        ..MathlibBuildConfig::default()
    };
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--output" | "--output-dir" => {
                i += 1;
                config.output_dir = PathBuf::from(&args[i]);
            }
            "--limit" => {
                i += 1;
                config.file_limit = args[i].parse().expect("--limit requires a number");
            }
            "--shard-size" => {
                i += 1;
                config.shard_size_limit = args[i].parse().expect("--shard-size requires a number");
            }
            "--max-file-size" => {
                i += 1;
                // 0 = no limit (import every .olean regardless of size); required
                // for full Mathlib coverage (large CategoryTheory/Tactic oleans
                // exceed the 2.5MB default and would otherwise be skipped).
                config.max_file_size = args[i].parse().expect("--max-file-size requires a number");
            }
            "--toolchain" => {
                i += 1;
                config.toolchain_lib = Some(PathBuf::from(&args[i]));
            }
            "--mathlib-root" => {
                i += 1;
                config.mathlib_olean_root = PathBuf::from(&args[i]);
            }
            "--packages-root" => {
                i += 1;
                config.packages_root = PathBuf::from(&args[i]);
            }
            other => {
                eprintln!("Unknown mathlib option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }
    config
}

fn cmd_mathlib(args: &[String]) {
    use clean_mathverse::build_mathlib::{build_mathlib_library, discover_olean_roots};

    let config = parse_mathlib_args(args);
    println!("=== Mathverse Library: Mathlib Conversion ===\n");

    let roots = discover_olean_roots(&config);
    if roots.is_empty() {
        eprintln!("Error: no .olean roots found.");
        eprintln!("Run scripts/setup_mathlib_oleans.sh first.");
        std::process::exit(1);
    }
    for (label, path) in &roots {
        println!("  root {label}: {}", path.display());
    }
    println!("  output: {}\n", config.output_dir.display());

    let start = Instant::now();
    match build_mathlib_library(&config) {
        Ok(result) => {
            print_mathlib_result(&result, &config, start.elapsed());
            write_mathlib_summary(&result, &config, start.elapsed());
        }
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    }
}

fn print_mathlib_result(
    result: &clean_mathverse::build_mathlib::MathlibBuildResult,
    config: &clean_mathverse::build_mathlib::MathlibBuildConfig,
    elapsed: std::time::Duration,
) {
    println!("\n=== Mathlib Conversion Complete ===");
    for rr in &result.root_results {
        println!(
            "  {}: {} parsed, {} constants",
            rr.label, rr.result.files_parsed, rr.result.total_constants
        );
    }
    println!("  Total constants:  {}", result.total_constants);
    println!("  Shards written:   {}", result.total_shards);
    println!("  Elapsed:          {:.2}s", elapsed.as_secs_f64());
    println!("  Output:           {}", config.output_dir.display());
}

fn write_mathlib_summary(
    result: &clean_mathverse::build_mathlib::MathlibBuildResult,
    config: &clean_mathverse::build_mathlib::MathlibBuildConfig,
    elapsed: std::time::Duration,
) {
    let roots_json: Vec<_> = result
        .root_results
        .iter()
        .map(|rr| {
            serde_json::json!({
                "label": rr.label,
                "root_dir": rr.root_dir.display().to_string(),
                "files_parsed": rr.result.files_parsed,
                "constants": rr.result.total_constants,
            })
        })
        .collect();
    let summary = serde_json::json!({
        "command": "mathverse_convert mathlib",
        "roots": roots_json,
        "total_constants": result.total_constants,
        "total_shards": result.total_shards,
        "elapsed_secs": elapsed.as_secs_f64(),
    });
    let path = config.output_dir.join("mathlib_build_summary.json");
    match fs::write(
        &path,
        serde_json::to_string_pretty(&summary).unwrap_or_default(),
    ) {
        Ok(()) => println!("  Summary: {}", path.display()),
        Err(e) => eprintln!("  Warning: could not write summary: {e}"),
    }
}

fn convert_metamath(path: &str) {
    use clean_mathverse::progverif::metamath::MetamathImporter;

    let path = Path::new(path);
    let filename = path.file_name().unwrap_or_default().to_string_lossy();
    println!("=== Converting Metamath: {filename} ===");

    let start = Instant::now();
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Error reading {}: {e}", path.display());
            return;
        }
    };
    println!(
        "  Read: {:.2}s ({:.1} MB)",
        start.elapsed().as_secs_f64(),
        text.len() as f64 / 1_048_576.0
    );

    let verify_start = Instant::now();
    let (result, vr) = match MetamathImporter::new().import_verified(&text) {
        Ok(pair) => pair,
        Err(e) => {
            eprintln!("  Parse/verify error: {e}");
            return;
        }
    };
    let verify_time = verify_start.elapsed();

    println!("  Database: {}", result.name);
    println!(
        "  Axioms: {}, Theorems: {}",
        result.axiom_count, result.vc_count
    );
    println!(
        "  RPN verified: {}, failed: {}, steps: {}",
        vr.verified, vr.failed, vr.total_steps
    );
    if vr.compressed_skipped > 0 {
        println!("  Compressed (skipped): {}", vr.compressed_skipped);
    }
    println!(
        "  Trust: {:?}, Axiom profile: {:?}",
        result.trust_level, result.axiom_profile
    );
    println!(
        "  Verify: {:.2}s, Total: {:.2}s",
        verify_time.as_secs_f64(),
        start.elapsed().as_secs_f64()
    );
    if verify_time.as_secs_f64() > 0.0 {
        println!(
            "  Throughput: {:.0} proofs/sec",
            vr.verified as f64 / verify_time.as_secs_f64()
        );
    }
    for label in vr.failed_labels.iter().take(5) {
        println!("    FAIL: {label}");
    }

    write_metamath_json(path, &filename, &result, &vr, &verify_time, &start);
    println!();
}

fn write_metamath_json(
    path: &Path,
    filename: &str,
    result: &clean_mathverse::progverif::metamath::MetamathImportResult,
    vr: &clean_mathverse::progverif::metamath::verify::VerifyResult,
    verify_time: &std::time::Duration,
    start: &Instant,
) {
    let output_path = path.with_extension("mathverse.json");
    let summary = serde_json::json!({
        "source": filename, "system": "metamath", "database_name": result.name,
        "axiom_count": result.axiom_count, "theorem_count": result.vc_count,
        "rpn_verified": vr.verified, "rpn_failed": vr.failed,
        "rpn_compressed_skipped": vr.compressed_skipped,
        "total_proof_steps": vr.total_steps,
        "trust_level": format!("{:?}", result.trust_level),
        "axiom_profile": format!("{:?}", result.axiom_profile),
        "verify_time_secs": verify_time.as_secs_f64(),
        "total_time_secs": start.elapsed().as_secs_f64(),
    });
    match fs::write(
        &output_path,
        serde_json::to_string_pretty(&summary).unwrap_or_default(),
    ) {
        Ok(()) => {
            println!("  Output: {}", output_path.display());
            // FINISH EVERYTHING: Write the .mathverse shard (#3522)
            let shard_path = output_path.with_extension("mathverse");
            println!("  Writing shard: {}", shard_path.display());
            match std::fs::read_to_string(path)
                .map_err(|e| format!("read source: {e}"))
                .and_then(|src| {
                    let db = clean_mathverse::metamath::parser::parse_mm(&src)
                        .map_err(|e| format!("parse_mm: {e:?}"))?;
                    let verified =
                        clean_mathverse::progverif::metamath::verify::verified_labels(&src);
                    Ok((db, verified))
                }) {
                Ok((stmt_importer, verified)) => {
                    if let Err(e) = clean_mathverse::metamath::shard_writer::write_mm_to_shard(
                        &stmt_importer,
                        &verified,
                        &shard_path,
                    ) {
                        eprintln!("  Error writing shard: {e}");
                    }
                }
                Err(e) => eprintln!("  Error preparing shard input: {e}"),
            }
        }
        Err(e) => eprintln!("  Warning: could not write {}: {e}", output_path.display()),
    }
}

// -- Incremental reconstruct: `build` / `status` ------------------------------
//
// Phase 0 of the reconstruct CLI (designs/2026-06-30-mathverse-reconstruct-cli.md):
// a cached, incremental `build <system>` gated by the content-addressed
// fingerprint + `mathverse.lock.json` ledger in `build_plan`. Scoped to the
// Metamath lane (git-only, RPN-verified) as the validating vertical slice; other
// systems are surfaced as DROPPED rather than silently skipped.

/// Bump when the Metamath emit logic changes, to invalidate just this lane's cache.
const METAMATH_IMPORTER_VERSION: u32 = 1;

/// Default library out-dir when neither `--out` nor `--output-dir` is given.
fn default_corpus_library() -> PathBuf {
    PathBuf::from("data/mathverse-corpus/library")
}

/// Resolve the `--out` / `--output-dir` library directory for build/status.
fn resolve_build_out(args: &[String], output_dir: Option<&Path>) -> PathBuf {
    let mut out = output_dir.map(PathBuf::from);
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--out" {
            // Only override on a present value; a trailing bare `--out` must not
            // silently discard an earlier --output-dir and fall back to the default.
            if let Some(v) = args.get(i + 1) {
                out = Some(PathBuf::from(v));
                i += 1;
            }
        }
        i += 1;
    }
    out.unwrap_or_else(default_corpus_library)
}

/// `mathverse_convert build [SYSTEMS...] [--out DIR] [--manifest PATH] [--force]`
fn cmd_build(args: &[String], output_dir: Option<&Path>) {
    use clean_mathverse::build_plan::Lockfile;

    let mut systems: Vec<String> = Vec::new();
    let mut manifest_path = PathBuf::from("data/mathverse_sources.toml");
    let mut force = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--manifest" => {
                manifest_path = args.get(i + 1).map(PathBuf::from).unwrap_or(manifest_path);
                i += 1;
            }
            "--out" | "--output-dir" => i += 1, // value consumed elsewhere
            "--force" => force = true,
            other if other.starts_with("--") => eprintln!("build: ignoring unknown flag {other}"),
            other => systems.push(other.to_string()),
        }
        i += 1;
    }
    if systems.is_empty() {
        systems.push("metamath".to_string()); // Phase 0 default lane
    }

    let out = resolve_build_out(args, output_dir);
    let manifest = match source_refresh::load_manifest(&manifest_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("build: cannot load {}: {e}", manifest_path.display());
            std::process::exit(1);
        }
    };
    if let Err(e) = std::fs::create_dir_all(out.join("delta")) {
        eprintln!("build: cannot create {}: {e}", out.join("delta").display());
        std::process::exit(1);
    }
    let lock_path = out.join("mathverse.lock.json");
    let mut lock = Lockfile::load(&lock_path).unwrap_or_default();

    println!("=== mathverse build -> {} ===", out.display());
    for system in &systems {
        match system.as_str() {
            "metamath" => build_metamath_lane(&manifest, &out, &mut lock, force),
            other => {
                eprintln!("DROPPED {other} reason=no-importer (Phase 0 lanes: metamath)");
                lock.record_dropped(other, "no-importer");
            }
        }
    }
    if let Err(e) = lock.save(&lock_path) {
        eprintln!(
            "build: failed to save lockfile {}: {e}",
            lock_path.display()
        );
        std::process::exit(1);
    }
    println!("Lockfile: {}", lock_path.display());
}

/// Build (or CACHE-HIT) the Metamath lane into `out/delta/` and pin it in the lockfile.
fn build_metamath_lane(
    manifest: &source_refresh::SourceManifest,
    out: &Path,
    lock: &mut clean_mathverse::build_plan::Lockfile,
    force: bool,
) {
    use clean_mathverse::build_plan::{self, SystemLock};

    let Some(src) = manifest
        .sources
        .iter()
        .find(|s| s.file_type == ".mm" || s.name.to_lowercase().contains("metamath"))
    else {
        eprintln!("SKIPPED metamath reason=not-in-manifest");
        return;
    };
    let clone = Path::new(&src.clone_path);

    let Some(mm_file) = find_mm_file(clone) else {
        eprintln!("SKIPPED metamath reason=no-source-at:{}", clone.display());
        return;
    };
    let file_label = mm_file
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();

    // Cache key's source identity: git HEAD, else the manifest's last-fetched SHA,
    // else a content hash of the .mm. NEVER a constant placeholder — that would serve
    // a stale shard after the source changes (resolved_source_sha's own contract).
    let source_sha = build_plan::resolved_source_sha(clone)
        .or_else(|| (!src.last_fetched_sha.is_empty()).then(|| src.last_fetched_sha.clone()))
        .unwrap_or_else(|| match fs::read(&mm_file) {
            Ok(bytes) => format!("content:{}", blake3::hash(&bytes).to_hex()),
            Err(_) => format!("nofile:{}", build_plan::now_unix()),
        });
    // Fold the chosen filename in so the fingerprint pins WHICH .mm was imported
    // (set.mm vs iset.mm vs ...) — a deterministic, reproducible build key.
    let importer_args = format!("{{\"file\":\"{file_label}\"}}");
    let fp = build_plan::fingerprint(&source_sha, METAMATH_IMPORTER_VERSION, &importer_args);

    if !force && lock.is_cache_hit("metamath", &fp, out) {
        let n = lock.systems.get("metamath").map_or(0, |e| e.decl_count);
        println!("CACHE-HIT metamath decls={n} fp={}", short_fp(&fp));
        return;
    }

    let src_text = match fs::read_to_string(&mm_file) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("SKIPPED metamath reason=read-error:{e}");
            return;
        }
    };
    let db = match clean_mathverse::metamath::parser::parse_mm(&src_text) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("SKIPPED metamath reason=parse-error:{e:?}");
            return;
        }
    };
    let verified = clean_mathverse::progverif::metamath::verify::verified_labels(&src_text);

    // Route the shard through LibraryLoader::write_shard so the library `manifest.json`
    // (the load/search index) is populated too — not just `mathverse.lock.json`.
    let loader = clean_mathverse::manifest::LibraryLoader::new(out.to_path_buf());
    if let Err(e) = loader.paths().ensure_dirs() {
        eprintln!("SKIPPED metamath reason=ensure-dirs:{e}");
        return;
    }
    let manifest_path = loader.paths().manifest_path();
    if !manifest_path.exists() {
        if let Err(e) = clean_mathverse::manifest::MathverseManifest::new().save(&manifest_path) {
            eprintln!("SKIPPED metamath reason=manifest-init:{e}");
            return;
        }
    }
    let shard_rel = "delta/metamath_0000.mathverse";
    // Force-rebuild dedup: drop any stale entry for this exact shard path before
    // re-registering (write_shard appends; it does not dedup).
    if let Ok(mut m) = clean_mathverse::manifest::MathverseManifest::load(&manifest_path) {
        if m.remove_shard(shard_rel) {
            let _ = m.save(&manifest_path);
        }
    }
    let mut writer = clean_mathverse::shard::ShardWriter::new();
    let mm_stats =
        clean_mathverse::metamath::shard_writer::write_mm_to_writer(&db, &verified, &mut writer);
    let entry = match loader.write_shard(&writer, "metamath_0000", true) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("SKIPPED metamath reason=shard-write-error:{e}");
            return;
        }
    };

    lock.record(
        "metamath",
        SystemLock {
            fingerprint: fp.clone(),
            source_sha,
            importer_version: METAMATH_IMPORTER_VERSION,
            shards: vec![entry.path],
            shard_hashes: vec![entry.content_hash],
            decl_count: mm_stats.entries_written as u64,
            trust_max: "SourceVerified".to_string(),
            built_at_unix: build_plan::now_unix(),
            closure_epoch: 0,
        },
    );
    println!(
        "BUILT metamath decls={} trust=SourceVerified shard={shard_rel} fp={}",
        mm_stats.entries_written,
        short_fp(&fp)
    );
}

/// The primary `.mm` database in a checkout: `set.mm` if present, else the
/// lexicographically-first `*.mm` (deterministic — a real set.mm repo ships
/// `iset.mm`/`nf.mm`/`ql.mm`/... and unordered FS iteration would break the
/// lockfile's reproducibility promise).
fn find_mm_file(clone: &Path) -> Option<PathBuf> {
    let set_mm = clone.join("set.mm");
    if set_mm.exists() {
        return Some(set_mm);
    }
    let mut candidates: Vec<PathBuf> = fs::read_dir(clone)
        .ok()?
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "mm"))
        .collect();
    candidates.sort();
    candidates.into_iter().next()
}

/// First 12 hex chars of a fingerprint, for compact logging.
fn short_fp(fp: &str) -> &str {
    &fp[..fp.len().min(12)]
}

/// `mathverse_convert status [--out DIR]` — print the lockfile build ledger.
fn cmd_build_status(args: &[String], output_dir: Option<&Path>) {
    use clean_mathverse::build_plan::Lockfile;

    let out = resolve_build_out(args, output_dir);
    let lock = Lockfile::load(&out.join("mathverse.lock.json")).unwrap_or_default();
    println!("=== mathverse build status ({}) ===", out.display());
    if lock.systems.is_empty() && lock.dropped.is_empty() {
        println!("  (no lockfile / nothing built)");
        return;
    }
    let mut total = 0u64;
    for (sys, e) in &lock.systems {
        println!(
            "  BUILT   {sys:<16} decls={:<8} trust={:<14} shards={} fp={}",
            e.decl_count,
            e.trust_max,
            e.shards.len(),
            short_fp(&e.fingerprint),
        );
        total += e.decl_count;
    }
    for d in &lock.dropped {
        println!("  DROPPED {:<16} reason={}", d.system, d.reason);
    }
    println!("  total decls: {total}");
}

/// Map a manifest source to its reconstruct lane key (Phase 0: metamath only).
/// Mirrors the source-finder predicate in `build_metamath_lane`.
fn lane_for_source(src: &source_refresh::SourceEntry) -> Option<&'static str> {
    if src.file_type == ".mm" || src.name.to_lowercase().contains("metamath") {
        Some("metamath")
    } else {
        None
    }
}

/// `mathverse_convert update [--fetch] [--out DIR] [--manifest PATH]` — the
/// continuous-update entrypoint: rebuild ONLY the lanes whose upstream SHA moved.
/// Unchanged systems stay a free CACHE-HIT (their lockfile entries are untouched),
/// so a scheduled daily run rebuilds only what actually changed upstream.
fn cmd_update(args: &[String], output_dir: Option<&Path>) {
    use clean_mathverse::build_plan::Lockfile;

    let do_fetch = args.iter().any(|a| a == "--fetch");
    let manifest_file = resolve_manifest_path(
        args.iter()
            .position(|a| a == "--manifest")
            .and_then(|i| args.get(i + 1))
            .map(PathBuf::from),
    );
    let out = resolve_build_out(args, output_dir);
    let mut manifest = match source_refresh::load_manifest(&manifest_file) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("update: load {}: {e}", manifest_file.display());
            std::process::exit(1);
        }
    };
    // Optionally pull latest first (mutates last_fetched_sha in place), then persist.
    if do_fetch {
        let results = source_refresh::fetch_updates(&mut manifest);
        print_fetch_results(&results);
        let _ = source_refresh::save_manifest(&manifest, &manifest_file);
    }
    let report = source_refresh::check_staleness(&manifest);
    eprint!("{}", report.format_summary());

    let _ = std::fs::create_dir_all(out.join("delta"));
    let lock_path = out.join("mathverse.lock.json");
    let mut lock = Lockfile::load(&lock_path).unwrap_or_default();

    // Rebuild every configured lane with the fingerprint cache (force=false): a lane
    // whose source SHA / importer / args is unchanged is a free CACHE-HIT; only lanes
    // whose inputs moved (e.g. --fetch pulled new commits) actually rebuild. Correct
    // whether or not we fetched — the staleness report above is informational, and is
    // the right signal to drive rebuilds is the content fingerprint, not local-vs-remote
    // (which reads equal right after a fetch).
    for src in &manifest.sources {
        match lane_for_source(src) {
            Some("metamath") => build_metamath_lane(&manifest, &out, &mut lock, false),
            Some(_) => {}
            None => eprintln!("SKIPPED {} reason=no-importer", src.name),
        }
    }
    if let Err(e) = lock.save(&lock_path) {
        eprintln!("update: save lock {}: {e}", lock_path.display());
        std::process::exit(1);
    }
    println!("Lockfile: {}", lock_path.display());
}

/// `mathverse_convert fetch [--manifest PATH]` — git-fetch every source and
/// persist the new SHAs back to the manifest (acquire only; no import).
fn cmd_fetch(args: &[String]) {
    let manifest_file = resolve_manifest_path(
        args.iter()
            .position(|a| a == "--manifest")
            .and_then(|i| args.get(i + 1))
            .map(PathBuf::from),
    );
    let mut manifest = match source_refresh::load_manifest(&manifest_file) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("fetch: load {}: {e}", manifest_file.display());
            std::process::exit(1);
        }
    };
    let results = source_refresh::fetch_updates(&mut manifest);
    print_fetch_results(&results);
    if let Err(e) = source_refresh::save_manifest(&manifest, &manifest_file) {
        eprintln!("fetch: save manifest {}: {e}", manifest_file.display());
        std::process::exit(1);
    }
}

fn convert_metamath_dir(dir: &str) {
    let dir = Path::new(dir);
    let entries: Vec<PathBuf> = match fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|ext| ext == "mm"))
            .collect(),
        Err(e) => {
            eprintln!("Error reading directory {}: {e}", dir.display());
            return;
        }
    };

    if entries.is_empty() {
        println!("No .mm files found in {}", dir.display());
        return;
    }

    println!("Found {} Metamath files", entries.len());
    for path in &entries {
        convert_metamath(&path.to_string_lossy());
    }
}

// -- convert_all with Lean 4 integration -------------------------------------

fn convert_all(data_dir: &str, output_dir: Option<&Path>) {
    let data_dir = Path::new(data_dir);
    let raw_dir = data_dir.join("raw");

    println!("=== Mathverse Library Batch Conversion ===\n");

    // Set up persistent output writer if --output-dir was provided.
    let output_config = match output_dir {
        Some(dir) => ConvertOutputConfig::with_output_dir(dir),
        None => ConvertOutputConfig::default(),
    };
    let writer = match ConvertOutputWriter::new(output_config) {
        Ok(w) => w,
        Err(e) => {
            eprintln!("Error creating output directory: {e}");
            std::process::exit(1);
        }
    };
    if writer.is_active() {
        println!(
            "  Output directory: {}\n",
            output_dir.expect("checked above").display()
        );
    }

    let mut total_kernel_verified: usize = 0;
    let mut total_declarations: usize = 0;
    let mut system_summaries: Vec<serde_json::Value> = Vec::new();
    let mut output_summary = OutputSummary::new();

    // Lean 4 .olean directories (with TC verification).
    convert_all_lean4(
        &raw_dir,
        &mut total_kernel_verified,
        &mut total_declarations,
        &mut system_summaries,
        &mut output_summary,
    );

    // Lean 4 .olean binary pipeline: produce .mathverse shards from .olean files.
    convert_all_olean_binary(
        &raw_dir,
        &writer,
        &mut total_kernel_verified,
        &mut total_declarations,
        &mut system_summaries,
        &mut output_summary,
    );

    // Metamath, OpenTheory, HOL Light, Mizar.
    convert_all_other_systems(&raw_dir);

    // Write mathverse_summary.json to data_dir (backward compat).
    write_mathverse_summary(
        data_dir,
        total_declarations,
        total_kernel_verified,
        &system_summaries,
    );

    // Write structured summary to output directory if active.
    if writer.is_active() {
        match writer.write_summary(&output_summary) {
            Ok(path) => println!("  Structured summary: {}", path.display()),
            Err(e) => eprintln!("  Warning: could not write structured summary: {e}"),
        }
    }
}

/// Discover and verify all Lean 4 .olean directories, accumulating stats.
///
/// For each directory:
/// 1. Runs kernel type-checking via `verify::verify_lean4_dir()`.
/// 2. Prints stats and writes per-directory `.mathverse.json` files.
/// 3. Produces `.mathverse` shard files with corrected `ImportConfidence` via
///    `integration::verify_and_convert_lean4_shard()`.
/// 4. Falls back gracefully to `TrustedOracle` for directories that fail.
fn convert_all_lean4(
    raw_dir: &Path,
    total_kernel_verified: &mut usize,
    total_declarations: &mut usize,
    system_summaries: &mut Vec<serde_json::Value>,
    output_summary: &mut OutputSummary,
) {
    let lean4_dirs = verify::discover_lean4_dirs(raw_dir);
    if lean4_dirs.is_empty() {
        return;
    }
    println!("--- Lean 4 .olean directories ({}) ---\n", lean4_dirs.len());

    let config = VerifyOleanConfig::default();
    let shard_output_dir = raw_dir.join("mathverse_shards");

    let mut verify_reports: Vec<VerificationReport> = Vec::new();

    for dir in &lean4_dirs {
        let dir_name = dir
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();

        // Step 1: TC verification + stats reporting (existing pipeline).
        if let Some(summary) = verify::verify_lean4_dir(dir) {
            *total_kernel_verified += summary.tc_pass;
            *total_declarations += summary.total_constants;
            print_lean4_summary(&summary, &dir_name);
            write_lean4_json(dir, &dir_name, &summary);
            system_summaries.push(serde_json::json!({
                "system": "lean4",
                "source": &dir_name,
                "total_constants": summary.total_constants,
                "kernel_verified": summary.tc_pass,
                "tc_fail": summary.tc_fail,
                "pass_rate_pct": summary.pass_rate_pct,
            }));
            output_summary.add_system(SystemSummary {
                system: "lean4".to_string(),
                source: dir_name.clone(),
                total_constants: summary.total_constants,
                kernel_verified: summary.tc_pass,
                shard_count: 1,
            });
        }

        // Step 2: Produce .mathverse shard with verification-corrected trust levels.
        match integration::verify_and_convert_lean4_shard(dir, &shard_output_dir, &config) {
            Ok(report) => {
                println!(
                    "  Shard: {} constants ({} KernelVerified, {} TrustedOracle)",
                    report.total_constants, report.kernel_verified, report.trusted_oracle
                );
                verify_reports.push(report);
            }
            Err(e) => {
                eprintln!("  Warning: shard conversion failed for {dir_name}: {e}");
            }
        }
    }

    // Print aggregate shard verification summary.
    if !verify_reports.is_empty() {
        let agg = integration::aggregate_verification_reports(&verify_reports);
        println!("\n--- Lean 4 Shard Verification Summary ---");
        println!(
            "  Directories: {}, Total constants: {}",
            agg.per_source.len(),
            agg.total_declarations
        );
        println!(
            "  KernelVerified: {} ({:.1}%), TrustedOracle: {}",
            agg.total_kernel_verified, agg.kernel_verified_pct, agg.total_trusted_oracle
        );
    }
}

/// Run the `.olean` binary pipeline to produce `.mathverse` shards from `.olean` files.
///
/// This uses `olean_bridge::convert_olean_dir_to_mathverse` (previously dead code)
/// via the `olean_pipeline` module to discover `.olean` files and generate shards
/// with full provenance tracking.
fn convert_all_olean_binary(
    raw_dir: &Path,
    writer: &ConvertOutputWriter,
    total_kernel_verified: &mut usize,
    total_declarations: &mut usize,
    system_summaries: &mut Vec<serde_json::Value>,
    output_summary: &mut OutputSummary,
) {
    let lean4_dirs = verify::discover_lean4_dirs(raw_dir);
    if lean4_dirs.is_empty() {
        return;
    }

    let shard_output_dir = raw_dir.join("mathverse_olean_shards");
    let config = OleanPipelineConfig::from_dirs(lean4_dirs, &shard_output_dir);

    println!(
        "\n--- Lean 4 .olean Binary Pipeline ({} dirs) ---\n",
        config.input_dirs.len()
    );

    match olean_pipeline::run_olean_pipeline(&config) {
        Ok(pipeline_result) => {
            // Print per-directory results.
            for dir_result in &pipeline_result.per_dir {
                let dir_name = dir_result
                    .dir
                    .file_name()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string();

                if let Some(ref conv) = dir_result.result {
                    println!(
                        "  {dir_name}: {} constants ({} verified, {} axiomatized, {} modules)",
                        conv.total_constants,
                        conv.kernel_verified,
                        conv.axiomatized,
                        conv.modules.len(),
                    );
                    if !conv.failures.is_empty() {
                        println!("    {} parse failures (skipped)", conv.failures.len());
                    }

                    // Accumulate into totals.
                    *total_declarations += conv.total_constants as usize;
                    *total_kernel_verified += conv.kernel_verified as usize;

                    system_summaries.push(serde_json::json!({
                        "system": "lean4-olean",
                        "source": dir_name,
                        "total_constants": conv.total_constants,
                        "kernel_verified": conv.kernel_verified,
                        "axiomatized": conv.axiomatized,
                        "modules": conv.modules.len(),
                    }));
                } else if let Some(ref err) = dir_result.error {
                    eprintln!("  {dir_name}: FAILED — {err}");
                }
            }

            // Print summary line.
            println!(
                "\n  Olean pipeline: {} dirs, {} shards, {} constants, {} verified, {}ms",
                pipeline_result.dirs_processed,
                pipeline_result.shards_written,
                pipeline_result.total_constants,
                pipeline_result.kernel_verified,
                pipeline_result.elapsed_ms,
            );

            // Update output summary with olean pipeline results.
            olean_pipeline::update_output_summary(output_summary, &pipeline_result);

            // Copy shards to persistent output directory if writer is active.
            if writer.is_active() {
                match olean_pipeline::write_pipeline_shards(writer, &pipeline_result) {
                    Ok(paths) => {
                        for p in &paths {
                            println!("  Shard written: {}", p.display());
                        }
                    }
                    Err(e) => {
                        eprintln!("  Warning: could not write olean shards to output dir: {e}");
                    }
                }
            }
        }
        Err(e) => {
            eprintln!("  Warning: olean binary pipeline failed: {e}");
        }
    }
}

/// Convert non-Lean 4 systems (Metamath, OpenTheory, HOL Light, Isabelle, Mizar).
fn convert_all_other_systems(raw_dir: &Path) {
    let mm_files: Vec<PathBuf> = fs::read_dir(raw_dir)
        .into_iter()
        .flat_map(|rd| rd.filter_map(|e| e.ok()).map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|ext| ext == "mm"))
        .collect();
    if !mm_files.is_empty() {
        println!("--- Metamath ({} files) ---\n", mm_files.len());
        for path in &mm_files {
            convert_metamath(&path.to_string_lossy());
        }
    }

    let shard_output_dir = raw_dir.join("mathverse_shards");

    let ot_dir = raw_dir.join("opentheory");
    if ot_dir.exists() {
        convert_opentheory_dir(&ot_dir, &shard_output_dir);
    }

    let isa_dir = raw_dir.join("isabelle");
    if isa_dir.exists() {
        convert_isabelle_dir(&isa_dir, &shard_output_dir);
    }

    let hl_dir = raw_dir.join("hol-light");
    if hl_dir.exists() {
        println!("--- HOL Light ---");
        println!("  Directory: {}", hl_dir.display());
        let ml_count = count_files_recursive(&hl_dir, "ml");
        println!("  OCaml source files: {ml_count}");
        println!("  (HOL Light requires OCaml evaluation — import via OpenTheory articles)\n");
    }

    let mizar_dir = raw_dir.join("mizar-contents");
    if mizar_dir.exists() {
        println!("--- Mizar MML ---");
        println!("  Directory: {}", mizar_dir.display());
        let abs_count = count_files_recursive(&mizar_dir, "abs");
        let miz_count = count_files_recursive(&mizar_dir, "miz");
        println!("  Abstract files (.abs): {abs_count}");
        println!("  Source files (.miz): {miz_count}");
        println!("  (Mizar XML export requires the Mizar verifier — abstracts available for reference)\n");
    }

    // Structured importers (Isabelle AFP .thy, Dafny, ACL2, Lean 3, Coq .v).
    convert_all_structured_importers(raw_dir, &shard_output_dir);
}

/// Run the five structured source-file importers against their expected directories.
fn convert_all_structured_importers(raw_dir: &Path, shard_output_dir: &Path) {
    use clean_mathverse::structured_import;

    let importers: &[(
        &str,
        &str,
        fn(&Path, &Path) -> structured_import::ConvertDirStats,
    )] = &[
        (
            "Isabelle AFP (.thy)",
            "isabelle-afp",
            structured_import::convert_isabelle_thy_dir,
        ),
        (
            "Dafny (.dfy)",
            "dafny",
            structured_import::convert_dafny_dir,
        ),
        ("ACL2 (.lisp)", "acl2", structured_import::convert_acl2_dir),
        (
            "Lean 3 (.lean)",
            "lean3",
            structured_import::convert_lean3_dir,
        ),
        ("Coq (.v)", "coq", structured_import::convert_coq_v_dir),
        ("Agda (.agda)", "agda", structured_import::convert_agda_dir),
        (
            "Twelf (.elf)",
            "twelf",
            structured_import::convert_twelf_dir,
        ),
        ("F* (.fst)", "fstar", structured_import::convert_fstar_dir),
        ("PVS (.pvs)", "pvs", structured_import::convert_pvs_dir),
        (
            "Mizar source (.miz)",
            "mizar-source",
            structured_import::convert_mizar_source_dir,
        ),
        (
            "Matita (.ma)",
            "matita",
            structured_import::convert_matita_dir,
        ),
        (
            "Idris2 (.idr)",
            "idris",
            structured_import::convert_idris_dir,
        ),
        (
            "Coq SerAPI (.sexp)",
            "coq-sexp",
            structured_import::convert_coq_sexp_dir,
        ),
    ];

    for &(label, dir_name, convert_fn) in importers {
        let dir = raw_dir.join(dir_name);
        if !dir.exists() {
            continue;
        }
        println!("--- {label} ---");
        println!("  Directory: {}\n", dir.display());

        let start = Instant::now();
        let stats = convert_fn(&dir, shard_output_dir);
        let elapsed = start.elapsed();

        println!(
            "  Files: {}, Declarations: {}, Errors: {}",
            stats.files_processed, stats.total_declarations, stats.errors
        );
        println!("  Time: {:.2}s\n", elapsed.as_secs_f64());
    }
}

/// Write the aggregate mathverse_summary.json and print final stats.
fn write_mathverse_summary(
    data_dir: &Path,
    total_declarations: usize,
    total_kernel_verified: usize,
    system_summaries: &[serde_json::Value],
) {
    let summary_json = serde_json::json!({
        "version": env!("CARGO_PKG_VERSION"),
        "total_declarations": total_declarations,
        "total_kernel_verified": total_kernel_verified,
        "kernel_verified_pct": if total_declarations > 0 {
            total_kernel_verified as f64 / total_declarations as f64 * 100.0
        } else {
            0.0
        },
        "systems": system_summaries,
    });
    let summary_path = data_dir.join("mathverse_summary.json");
    match fs::write(
        &summary_path,
        serde_json::to_string_pretty(&summary_json).unwrap_or_default(),
    ) {
        Ok(()) => println!("Summary written to: {}", summary_path.display()),
        Err(e) => eprintln!("Warning: could not write mathverse_summary.json: {e}"),
    }

    println!("\n=== Conversion Complete ===");
    println!("  Total declarations: {total_declarations}");
    println!("  Total KernelVerified: {total_kernel_verified}");
    if total_declarations > 0 {
        println!(
            "  Verified rate: {:.2}%",
            total_kernel_verified as f64 / total_declarations as f64 * 100.0
        );
    }
}

// -- Lean 4 CLI output helpers ------------------------------------------------

fn print_lean4_summary(summary: &clean_olean::verify_batch::BatchSummary, dir_name: &str) {
    println!("  {dir_name} Results:");
    println!(
        "    Files:      {}/{}",
        summary.load_success, summary.total_files
    );
    println!("    Constants:  {}", summary.total_constants);
    println!(
        "    TC pass: {}, TC fail: {}, Skipped: {}",
        summary.tc_pass, summary.tc_fail, summary.total_skipped
    );
    println!(
        "    Pass rate:  {:.2}%, Time: {:.2}s",
        summary.pass_rate_pct, summary.total_elapsed_secs
    );
    for (cat, count) in &summary.error_categories {
        println!("      Error: {cat}: {count}");
    }
}

fn write_lean4_json(
    root: &Path,
    dir_name: &str,
    summary: &clean_olean::verify_batch::BatchSummary,
) {
    let json_path = root.with_extension("mathverse.json");
    let json_output = serde_json::json!({
        "source": dir_name, "system": "lean4",
        "total_files": summary.total_files, "processed_files": summary.processed_files,
        "load_success": summary.load_success, "load_failure": summary.load_failure,
        "total_constants": summary.total_constants,
        "tc_pass": summary.tc_pass, "tc_fail": summary.tc_fail,
        "total_skipped": summary.total_skipped, "pass_rate_pct": summary.pass_rate_pct,
        "kernel_verified": summary.tc_pass, "trust_level": "KernelVerified",
        "total_elapsed_secs": summary.total_elapsed_secs,
    });
    match fs::write(
        &json_path,
        serde_json::to_string_pretty(&json_output).unwrap_or_default(),
    ) {
        Ok(()) => println!("  Output: {}", json_path.display()),
        Err(e) => eprintln!("  Warning: could not write {}: {e}", json_path.display()),
    }
    println!();
}

/// Counters accumulated while processing OpenTheory articles.
struct OtConvertStats {
    ok: u64,
    thm: u64,
    sup: u64,
    asmp: u64,
    err: u64,
    total_shard_decls: usize,
}

fn convert_opentheory_dir(dir: &Path, shard_output_dir: &Path) {
    use clean_kernel::open_theory::OtContext;
    use clean_kernel::Name;
    use clean_mathverse::hol::opentheory_bridge::OtMathverseBridge;
    use clean_mathverse::shard::ShardWriter;
    use clean_mathverse::types::SourceSystem;

    println!("--- OpenTheory ---\n  Directory: {}\n", dir.display());

    let mut art_files = Vec::new();
    collect_files_recursive(dir, "art", &mut art_files);
    art_files.sort();
    if art_files.is_empty() {
        println!("  No .art files found\n");
        return;
    }
    println!("  Found {} article files", art_files.len());

    let bridge = OtMathverseBridge::new(Name::from_string("OpenTheory"), SourceSystem::HolLight);
    let ctx = OtContext::default();
    let mut shard_writer = ShardWriter::new();
    let start = Instant::now();
    let stats = process_ot_articles(&art_files, &bridge, ctx, &mut shard_writer);

    write_ot_shard_if_nonempty(&shard_writer, shard_output_dir, stats.total_shard_decls);

    let elapsed = start.elapsed();
    println!(
        "  Converted: {}/{} articles, Theorems: {}, Support: {}",
        stats.ok,
        art_files.len(),
        stats.thm,
        stats.sup
    );
    println!(
        "  Assumptions: {}, Errors: {}, Time: {:.2}s",
        stats.asmp,
        stats.err,
        elapsed.as_secs_f64()
    );
    if stats.ok > 0 {
        println!(
            "  Throughput: {:.0} articles/sec",
            stats.ok as f64 / elapsed.as_secs_f64()
        );
    }
    println!();
}

fn process_ot_articles(
    art_files: &[PathBuf],
    bridge: &clean_mathverse::hol::opentheory_bridge::OtMathverseBridge,
    mut ctx: clean_kernel::open_theory::OtContext,
    shard_writer: &mut clean_mathverse::shard::ShardWriter,
) -> OtConvertStats {
    use clean_kernel::open_theory::parse_article_with_context;
    use clean_mathverse::hol::opentheory_shard::write_ot_constants_to_shard;

    let mut stats = OtConvertStats {
        ok: 0,
        thm: 0,
        sup: 0,
        asmp: 0,
        err: 0,
        total_shard_decls: 0,
    };
    // Optional per-article budgets (env-driven). Without these the importer
    // can spin silently on a pathological article forever; with them every
    // article gets a fresh timer and we can see which one hangs.
    let max_articles: usize = std::env::var("OT_MAX_ARTICLES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);
    let per_article_secs: u64 = std::env::var("OT_PER_ARTICLE_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    for (idx, path) in art_files.iter().enumerate() {
        if idx >= max_articles {
            println!("  [{}/{}] STOP: hit OT_MAX_ARTICLES", idx, art_files.len());
            break;
        }
        let name = path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_default();
        let phase_start = Instant::now();
        print!("  [{}/{}] {:<32} ", idx + 1, art_files.len(), name);
        let _ = std::io::Write::flush(&mut std::io::stdout());
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => {
                println!("read-error");
                stats.err += 1;
                continue;
            }
        };
        let parse_start = Instant::now();
        let article = match parse_article_with_context(&text, ctx.clone()) {
            Ok(a) => a,
            Err(_) => {
                println!("parse-error ({:.2}s)", parse_start.elapsed().as_secs_f64());
                stats.err += 1;
                continue;
            }
        };
        let parse_elapsed = parse_start.elapsed().as_secs_f64();
        ctx.extend(article.proved_theorems_as_context());
        let import_start = Instant::now();
        match bridge.import_article(&article) {
            Ok((constants, s)) => {
                let metadata = write_ot_constants_to_shard(&constants, &s, shard_writer);
                stats.total_shard_decls += metadata.declaration_count;
                stats.thm += s.theorem_count as u64;
                stats.sup += s.support_count as u64;
                stats.asmp += s.assumption_count as u64;
                stats.ok += 1;
                println!(
                    "ok parse={:.2}s import={:.2}s decls={} thm={}",
                    parse_elapsed,
                    import_start.elapsed().as_secs_f64(),
                    metadata.declaration_count,
                    s.theorem_count
                );
            }
            Err(e) => {
                println!(
                    "import-error parse={:.2}s import={:.2}s: {:?}",
                    parse_elapsed,
                    import_start.elapsed().as_secs_f64(),
                    e
                );
                stats.err += 1;
            }
        }
        // Soft per-article wall-clock check — we can't preempt the article
        // itself (would need threading), but record overall budget and warn.
        if per_article_secs > 0 && phase_start.elapsed().as_secs() > per_article_secs {
            println!(
                "  WARN: article exceeded {}s budget — continuing",
                per_article_secs
            );
        }
    }
    stats
}

fn write_ot_shard_if_nonempty(
    shard_writer: &clean_mathverse::shard::ShardWriter,
    shard_output_dir: &Path,
    total_shard_decls: usize,
) {
    if total_shard_decls > 0 {
        let _ = fs::create_dir_all(shard_output_dir);
        let shard_path = shard_output_dir.join("opentheory.mathverse");
        match shard_writer.write_to_file(&shard_path) {
            Ok(()) => {
                println!(
                    "  Shard written: {} ({} declarations)",
                    shard_path.display(),
                    total_shard_decls
                );
            }
            Err(e) => eprintln!("  Warning: could not write shard: {e}"),
        }
    }
}

fn convert_isabelle_dir(dir: &Path, shard_output_dir: &Path) {
    use clean_mathverse::hol::isabelle::importer::{IsabelleImportConfig, IsabelleImporter};
    use clean_mathverse::hol::isabelle_shard::write_isa_result_to_shard;
    use clean_mathverse::shard::ShardWriter;

    println!("--- Isabelle ---\n  Directory: {}\n", dir.display());

    let mut yxml_files = Vec::new();
    collect_files_recursive(dir, "yxml", &mut yxml_files);
    yxml_files.sort();
    if yxml_files.is_empty() {
        println!("  No .yxml files found\n");
        return;
    }
    println!("  Found {} theory export files", yxml_files.len());

    let config = IsabelleImportConfig::default();
    let importer = IsabelleImporter::new(config);
    let start = Instant::now();
    let mut shard_writer = ShardWriter::new();
    let mut total_shard_decls: usize = 0;
    let mut total_theories: usize = 0;
    let mut total_errors: usize = 0;

    for path in &yxml_files {
        match importer.import_file(path) {
            Ok(result) => {
                let metadata = write_isa_result_to_shard(&result, &mut shard_writer);
                total_shard_decls += metadata.declaration_count;
                total_theories += metadata.theories_processed;
                total_errors += metadata.translation_errors;
            }
            Err(e) => {
                total_errors += 1;
                eprintln!(
                    "  Warning: failed to import {}: {e}",
                    path.file_name().unwrap_or_default().to_string_lossy()
                );
            }
        }
    }

    // Write the shard file if we have any declarations.
    if total_shard_decls > 0 {
        let _ = fs::create_dir_all(shard_output_dir);
        let shard_path = shard_output_dir.join("isabelle.mathverse");
        match shard_writer.write_to_file(&shard_path) {
            Ok(()) => {
                println!(
                    "  Shard written: {} ({} declarations)",
                    shard_path.display(),
                    total_shard_decls
                );
            }
            Err(e) => {
                eprintln!("  Warning: could not write shard: {e}");
            }
        }
    }

    let elapsed = start.elapsed();
    println!(
        "  Theories: {total_theories}, Declarations: {total_shard_decls}, Errors: {total_errors}"
    );
    println!("  Time: {:.2}s", elapsed.as_secs_f64());
    println!();
}

/// Build the Isabelle/HOL ↔ Lean 4/Mathlib cross-system equivalence layer.
///
/// Reads declaration names from the Isabelle shard, matches them against
/// Mathlib (either declaration names from an on-disk Mathlib shard directory,
/// or — when those are unavailable — the real Mathlib names referenced by the
/// curated alias table), and writes a persistent
/// `isabelle_mathlib_equivalences.json` report.
fn bridge_isabelle_mathlib(isa_shard: &Path, mathlib_dir: Option<&Path>, out_dir: &Path) {
    use clean_mathverse::hol::isabelle_mathlib_bridge::{write_report, IsabelleMathlibBridge};
    use clean_mathverse::shard::ShardReader;

    println!("--- Isabelle ↔ Mathlib bridge ---");
    println!("  Isabelle shard: {}", isa_shard.display());

    let reader = match ShardReader::from_file(isa_shard) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("  Could not read Isabelle shard: {e}");
            return;
        }
    };
    let isa_names: Vec<String> = reader
        .constants
        .iter()
        .filter_map(|c| reader.strings.get(c.name_idx as usize).cloned())
        .collect();
    println!("  Isabelle decls: {}", isa_names.len());

    let mut bridge = IsabelleMathlibBridge::with_builtin_aliases();
    bridge.index_isabelle_names(isa_names);

    // Mathlib name source: on-disk shards if non-empty, else the curated table's
    // real Mathlib names.
    let mut ml_names: Vec<String> = Vec::new();
    if let Some(dir) = mathlib_dir {
        let mut shards = Vec::new();
        collect_files_recursive(dir, "mathverse", &mut shards);
        for s in &shards {
            if let Ok(r) = ShardReader::from_file(s) {
                ml_names.extend(
                    r.constants
                        .iter()
                        .filter_map(|c| r.strings.get(c.name_idx as usize).cloned()),
                );
            }
        }
        println!(
            "  Mathlib decls from {} shard(s): {}",
            shards.len(),
            ml_names.len()
        );
    }
    let ml_source = if ml_names.is_empty() {
        ml_names = bridge.curated_mathlib_names();
        "curated-table (real Mathlib names; on-disk Mathlib shards empty/absent)"
    } else {
        "on-disk Mathlib shards"
    };
    bridge.index_mathlib_names(ml_names);
    println!("  Mathlib name source: {ml_source}");

    let report = bridge.report(0.0);
    println!(
        "  Links: {} total ({} curated-alias, {} normalized-name)",
        report.links.len(),
        report.curated_link_count,
        report.normalized_link_count
    );

    let out_path = out_dir.join("isabelle_mathlib_equivalences.json");
    match std::fs::File::create(&out_path).map(std::io::BufWriter::new) {
        Ok(mut w) => match write_report(&mut w, &report) {
            Ok(()) => println!("  Report written: {}", out_path.display()),
            Err(e) => eprintln!("  Could not write report: {e}"),
        },
        Err(e) => eprintln!("  Could not create report file: {e}"),
    }
    println!();
}

fn collect_files_recursive(dir: &Path, ext: &str, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_files_recursive(&path, ext, out);
            } else if path.extension().is_some_and(|e| e == ext) {
                out.push(path);
            }
        }
    }
}

fn count_files_recursive(dir: &Path, ext: &str) -> usize {
    let mut count = 0;
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                count += count_files_recursive(&path, ext);
            } else if path.extension().is_some_and(|e| e == ext) {
                count += 1;
            }
        }
    }
    count
}

fn show_stats(data_dir: &str) {
    let raw_dir = Path::new(data_dir).join("raw");
    println!("=== Mathverse Library Data Stats ===\n");
    if !raw_dir.exists() {
        println!("Raw data directory not found: {}", raw_dir.display());
        return;
    }
    println!("Raw data files:");
    list_dir_recursive(&raw_dir, 0);
}

fn list_dir_recursive(dir: &Path, depth: usize) {
    let indent = "  ".repeat(depth);
    let Ok(rd) = fs::read_dir(dir) else { return };
    let mut items: Vec<_> = rd.filter_map(|e| e.ok()).collect();
    items.sort_by_key(|e| e.file_name());
    for entry in items {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().to_string();
        if name.starts_with('.') {
            continue;
        }
        if path.is_dir() {
            println!("{indent}  {name}/ ({} files)", count_all_files(&path));
            if depth < 1 {
                list_dir_recursive(&path, depth + 1);
            }
        } else {
            let size = fs::metadata(&path).map(|m| m.len()).unwrap_or(0);
            println!("{indent}  {name} ({:.1} MB)", size as f64 / 1_048_576.0);
        }
    }
}

fn count_all_files(dir: &Path) -> usize {
    let Ok(rd) = fs::read_dir(dir) else { return 0 };
    rd.filter_map(|e| e.ok())
        .map(|e| {
            if e.path().is_dir() {
                count_all_files(&e.path())
            } else {
                1
            }
        })
        .sum()
}

fn cmd_verify_shards(shard_dir: &str) {
    use clean_mathverse::shard_verify::{verify_shard_dir_default, write_results_json};
    let shard_dir = Path::new(shard_dir);
    println!("=== Mathverse Shard Kernel Verification ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mut mathverse_files = Vec::new();
    collect_files_recursive(shard_dir, "mathverse", &mut mathverse_files);
    mathverse_files.sort();

    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }

    println!("  Found {} shard files\n", mathverse_files.len());

    let start = Instant::now();
    let report = verify_shard_dir_default(&mathverse_files);

    print_shard_report(&report, start.elapsed());

    let output_path = shard_dir.join("verify_results.json");
    match write_results_json(&report, &output_path) {
        Ok(()) => println!("\n  Results written to: {}", output_path.display()),
        Err(e) => eprintln!("  Warning: {e}"),
    }
}

fn print_shard_report(
    report: &clean_mathverse::shard_verify::VerifyReport,
    elapsed: std::time::Duration,
) {
    use clean_mathverse::shard_verify::source_system_name;

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

    let stats = &report.stats;
    println!("\n=== Verification Summary ===");
    println!(
        "  Shards: {} processed, {} skipped",
        stats.shards_processed, stats.shards_skipped
    );
    println!(
        "  Constants: {} total, {} verified, {} translated",
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
        println!("  Rates: {v:.1}% verified, {t:.1}% translated");
    }

    println!("\n=== Per-System Breakdown ===");
    println!(
        "  {:<10} {:>8} {:>8} {:>10} {:>6}",
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

fn cmd_refresh(args: &[String]) {
    let (mode, manifest_path) = parse_refresh_args(args);
    let manifest_file = resolve_manifest_path(manifest_path);

    let mut manifest = match source_refresh::load_manifest(&manifest_file) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error loading manifest: {e}");
            std::process::exit(1);
        }
    };
    eprintln!(
        "Loaded {} sources from {}",
        manifest.sources.len(),
        manifest_file.display()
    );

    match mode {
        RefreshMode::Check => {
            eprint!(
                "{}",
                source_refresh::check_staleness(&manifest).format_summary()
            );
        }
        RefreshMode::Update | RefreshMode::Rebuild => {
            run_refresh_update(&mut manifest, &manifest_file, mode);
        }
    }
}

fn parse_refresh_args(args: &[String]) -> (RefreshMode, Option<PathBuf>) {
    let mut mode = RefreshMode::Check;
    let mut manifest_path: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--check" => mode = RefreshMode::Check,
            "--update" => mode = RefreshMode::Update,
            "--rebuild" => mode = RefreshMode::Rebuild,
            "--manifest" => {
                i += 1;
                if i < args.len() {
                    manifest_path = Some(PathBuf::from(&args[i]));
                } else {
                    eprintln!("Error: --manifest requires a path");
                    std::process::exit(1);
                }
            }
            o if o.starts_with("--manifest=") => {
                manifest_path = Some(PathBuf::from(o.strip_prefix("--manifest=").unwrap_or("")));
            }
            o => {
                eprintln!("Unknown refresh option: {o}");
                std::process::exit(1);
            }
        }
        i += 1;
    }
    (mode, manifest_path)
}

fn resolve_manifest_path(explicit: Option<PathBuf>) -> PathBuf {
    if let Some(p) = explicit {
        return p;
    }
    let candidates = [
        PathBuf::from("data/mathverse_sources.toml"),
        PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../data/mathverse_sources.toml"
        )),
    ];
    for c in &candidates {
        if c.exists() {
            return c.clone();
        }
    }
    PathBuf::from("data/mathverse_sources.toml")
}

fn run_refresh_update(
    manifest: &mut source_refresh::SourceManifest,
    manifest_file: &Path,
    mode: RefreshMode,
) {
    let pre = source_refresh::check_staleness(manifest);
    eprint!("{}", pre.format_summary());
    if pre.stale_count == 0 {
        eprintln!("All sources are up-to-date. Nothing to fetch.");
        return;
    }
    eprintln!(
        "Fetching updates for {} stale sources...\n",
        pre.stale_count
    );
    let results = source_refresh::fetch_updates(manifest);
    print_fetch_results(&results);

    if let Err(e) = source_refresh::save_manifest(manifest, manifest_file) {
        eprintln!("Warning: could not save updated manifest: {e}");
    } else {
        eprintln!("Manifest updated: {}", manifest_file.display());
    }
    if matches!(mode, RefreshMode::Rebuild) {
        eprintln!("\nRun `mathverse_convert all /tmp/mathverse-data` to rebuild changed sources.");
    }
}

fn print_fetch_results(results: &[source_refresh::FetchResult]) {
    let (mut ok, mut fail) = (0usize, 0usize);
    for r in results {
        if r.success {
            ok += 1;
            let tag = if r.old_sha.is_empty() {
                "NEW CLONE".to_string()
            } else if r.old_sha == r.new_sha {
                "unchanged".to_string()
            } else {
                format!(
                    "{}..{}",
                    &r.old_sha[..7.min(r.old_sha.len())],
                    &r.new_sha[..7.min(r.new_sha.len())]
                )
            };
            eprintln!("  OK  {}: {tag}", r.name);
        } else {
            fail += 1;
            eprintln!(
                "  FAIL {}: {}",
                r.name,
                r.error.as_deref().unwrap_or("unknown")
            );
        }
    }
    eprintln!("\nFetch complete: {ok} succeeded, {fail} failed");
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RefreshMode {
    Check,
    Update,
    Rebuild,
}

fn verify_shard_cmd(path: &str) {
    use clean_mathverse::lean4::shard_verify::verify_shard;
    use clean_mathverse::shard::ShardReader;

    let path = Path::new(path);
    println!("=== Verifying Shard: {} ===", path.display());

    let start = Instant::now();
    let reader = match ShardReader::from_file(path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error reading shard: {e}");
            return;
        }
    };

    println!(
        "  Shard: {} constants, {} exprs, {} levels, {} strings",
        reader.constants.len(),
        reader.exprs.len(),
        reader.levels.len(),
        reader.strings.len()
    );

    let result = match verify_shard(&reader) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Verification error: {e}");
            return;
        }
    };

    let elapsed = start.elapsed();
    println!(
        "  Total: {}, Verified: {}, Axiom: {}, Failed: {}, Time: {:.2}s",
        result.total,
        result.kernel_verified,
        result.axiom_accepted,
        result.failed,
        elapsed.as_secs_f64()
    );
    if result.total > 0 {
        let rate =
            (result.kernel_verified + result.axiom_accepted) as f64 / result.total as f64 * 100.0;
        println!("  Success rate: {rate:.1}%");
    }
    if !result.failures.is_empty() {
        let show = std::cmp::min(10, result.failures.len());
        println!("\n  First {show} failures:");
        for (name, err) in &result.failures[..show] {
            println!("    {name}: {err}");
        }
        if result.failures.len() > show {
            println!("    ... and {} more", result.failures.len() - show);
        }
    }
}
