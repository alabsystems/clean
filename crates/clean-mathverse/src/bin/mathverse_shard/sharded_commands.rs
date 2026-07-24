// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sharded/streaming kernel-verification driver + worker (Lane A scale path).
//!
//! Two subcommand modes, both under `verify-kernel`:
//!
//!   verify-kernel --module <Mathlib.X.Y> --olean-root <dir>... [--emit <sidecar.json>]
//!     WORKER: fresh prelude env, load ONLY that module + its transitive dep
//!     closure, kernel-verify the module's OWN constants, write a per-shard
//!     `KernelVerifiedManifest` sidecar, exit (OS reclaims memory).
//!
//!   verify-kernel --corpus-sharded --olean-root <dir>... --out <dir>
//!                 [--jobs N] [--module-list <file>]
//!     DRIVER: enumerate the module list, spawn the WORKER per module (re-exec
//!     self), bounded to N concurrent children, then MERGE all sidecars into one
//!     consolidated `kernel-verified.json` (set-union of names, summed buckets).
//!
//! The driver/worker split BYPASSES the whole-corpus `as_merged_reader` double
//! arena copy entirely: each worker holds only one module's closure resident.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use clean_mathverse::verify::classify::classification_rule;
use clean_mathverse::verify::kernel_verified_manifest::KernelVerifiedManifest;
use clean_mathverse::verify::sharded::{
    enumerate_modules, verify_module, ClassCounts, ModuleVerifyResult,
};

/// Default cap on retained per-constant failure detail strings (counts stay exact).
const MAX_FAILURE_DETAIL: usize = 50;

/// Parsed options shared by the worker and driver modes.
struct ShardedOpts {
    module: Option<String>,
    corpus_sharded: bool,
    olean_roots: Vec<PathBuf>,
    out_dir: Option<PathBuf>,
    emit: Option<PathBuf>,
    jobs: usize,
    module_list: Option<PathBuf>,
    /// Print the MATH-vs-GENERATED classification audit (rule + per-class
    /// verify rates + per-bucket name samples + MATH-failure detail). The
    /// decisive Lane-A yield number is the MATH-only verify rate.
    classify: bool,
}

/// Returns `Some(exit_code)` if `args` selected a sharded mode (worker or
/// driver); `None` if neither `--module` nor `--corpus-sharded` was present, so
/// the caller falls back to the legacy `verify-kernel` paths.
pub(crate) fn try_cmd_sharded(args: &[String]) -> Option<i32> {
    if !args
        .iter()
        .any(|a| a == "--module" || a == "--corpus-sharded")
    {
        return None;
    }
    let opts = match parse_sharded_args(args) {
        Ok(o) => o,
        Err(msg) => {
            eprintln!("{msg}");
            return Some(2);
        }
    };
    Some(run_sharded(opts))
}

fn parse_sharded_args(args: &[String]) -> Result<ShardedOpts, String> {
    let mut module = None;
    let mut corpus_sharded = false;
    let mut olean_roots = Vec::new();
    let mut out_dir = None;
    let mut emit = None;
    // RAM-aware default worker count — single source of truth shared with the
    // PARAGON `--parallel` verifier (`clean_mathverse::cli::ram_budget`). An
    // explicit `--jobs N` below overrides it verbatim.
    let mut jobs = clean_mathverse::cli::ram_budget::ram_aware_default_jobs();
    let mut module_list = None;
    let mut classify = false;

    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        match arg.as_str() {
            "--corpus-sharded" => corpus_sharded = true,
            "--classify" => classify = true,
            "--module" => module = Some(take_value(args, &mut i, "--module")?),
            "--olean-root" => {
                olean_roots.push(PathBuf::from(take_value(args, &mut i, "--olean-root")?))
            }
            "--out" => out_dir = Some(PathBuf::from(take_value(args, &mut i, "--out")?)),
            "--emit" => emit = Some(PathBuf::from(take_value(args, &mut i, "--emit")?)),
            "--jobs" => {
                jobs = take_value(args, &mut i, "--jobs")?
                    .parse()
                    .map_err(|_| "Error: --jobs must be a positive integer".to_string())?;
            }
            "--module-list" => {
                module_list = Some(PathBuf::from(take_value(args, &mut i, "--module-list")?));
            }
            other => return Err(format!("Unknown sharded option: {other}")),
        }
        i += 1;
    }

    if jobs == 0 {
        return Err("Error: --jobs must be >= 1".to_string());
    }
    if olean_roots.is_empty() {
        return Err(
            "Error: --olean-root <dir> is required (repeatable; e.g. the Mathlib lake \
             build/lib/lean dir, sibling package lib dirs, and the toolchain lib/lean)"
                .to_string(),
        );
    }
    Ok(ShardedOpts {
        module,
        corpus_sharded,
        olean_roots,
        out_dir,
        emit,
        jobs,
        module_list,
        classify,
    })
}

fn take_value(args: &[String], i: &mut usize, flag: &str) -> Result<String, String> {
    *i += 1;
    args.get(*i)
        .cloned()
        .ok_or_else(|| format!("Error: {flag} requires a value"))
}

fn run_sharded(opts: ShardedOpts) -> i32 {
    if opts.corpus_sharded {
        run_driver(&opts)
    } else if let Some(module) = &opts.module {
        run_worker(module, &opts)
    } else {
        eprintln!("Error: --module <name> or --corpus-sharded is required");
        2
    }
}

// -- Worker -------------------------------------------------------------------

fn run_worker(module: &str, opts: &ShardedOpts) -> i32 {
    eprintln!("[worker] verifying {module}");
    let result = match verify_module(module, &opts.olean_roots, MAX_FAILURE_DETAIL) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("[worker] {module}: {e}");
            return 1;
        }
    };
    print_worker_result(&result);
    if opts.classify {
        print_classification(&result);
    }

    if let Some(path) = &opts.emit {
        let manifest = result.to_manifest();
        if let Err(e) = manifest.write_to_file(path) {
            eprintln!(
                "[worker] {module}: failed to write sidecar {}: {e}",
                path.display()
            );
            return 1;
        }
        eprintln!(
            "[worker] {module}: wrote {} verified names to {}",
            manifest.kernel_verified_names.len(),
            path.display()
        );
    }
    0
}

fn print_worker_result(r: &ModuleVerifyResult) {
    println!(
        "  {module}: {own} own constants ({closure} in closure), \
         {kv} verified, {ax} axiom-accepted, {fail} failed, {nf} not-found, \
         {rate:.2}% verified, {secs:.2}s",
        module = r.module,
        own = r.counts.total,
        closure = r.closure_constants,
        kv = r.counts.kernel_verified,
        ax = r.counts.axiom_accepted,
        fail = r.counts.failed,
        nf = r.counts.not_found,
        rate = r.verified_rate(),
        secs = r.elapsed_secs,
    );
    for (name, reason) in &r.failures {
        eprintln!("    FAIL {name}: {reason}");
    }
}

/// Print the MATH-vs-GENERATED audit for one module: the classification rule,
/// per-class verify rates (the decisive Lane-A yield is the MATH rate), a name
/// sample per bucket, and the MATH-failure detail.
fn print_classification(r: &ModuleVerifyResult) {
    println!(
        "  --- classification (MATH vs GENERATED) for {} ---",
        r.module
    );
    println!("  rule: {}", classification_rule());
    print_class_line("MATH     ", &r.math);
    print_class_line("GENERATED", &r.generated);

    println!("  MATH sample ({} shown):", r.math_sample.len());
    for n in &r.math_sample {
        println!("    [math] {n}");
    }
    println!("  GENERATED sample ({} shown):", r.generated_sample.len());
    for n in &r.generated_sample {
        println!("    [gen ] {n}");
    }

    if r.math_failures.is_empty() {
        println!("  MATH failures: none");
    } else {
        println!("  MATH failures ({}):", r.math_failures.len());
        for (name, reason) in &r.math_failures {
            eprintln!("    MATH-FAIL {name}: {reason}");
        }
    }
}

fn print_class_line(label: &str, c: &ClassCounts) {
    let rate = c
        .verified_rate()
        .map_or_else(|| "n/a".to_string(), |r| format!("{r:.2}%"));
    println!(
        "  {label}: resolved={resolved} verified={kv} axiom={ax} failed={fail} \
         not_found={nf} rate={rate}",
        resolved = c.resolved,
        kv = c.kernel_verified,
        ax = c.axiom_accepted,
        fail = c.failed,
        nf = c.not_found,
    );
}

// -- Driver -------------------------------------------------------------------

fn run_driver(opts: &ShardedOpts) -> i32 {
    let out_dir = match &opts.out_dir {
        Some(d) => d.clone(),
        None => {
            eprintln!("Error: --corpus-sharded requires --out <dir>");
            return 2;
        }
    };
    if let Err(e) = std::fs::create_dir_all(&out_dir) {
        eprintln!("Error: cannot create out dir {}: {e}", out_dir.display());
        return 1;
    }

    let modules = match collect_modules(opts) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{e}");
            return 1;
        }
    };
    if modules.is_empty() {
        eprintln!("Error: no modules to verify (empty enumeration / module list)");
        return 1;
    }

    println!("=== Mathverse Sharded Corpus Kernel Verification (driver) ===");
    println!("  Modules:    {}", modules.len());
    println!("  Jobs:       {}", opts.jobs);
    println!("  Out dir:    {}", out_dir.display());
    for r in &opts.olean_roots {
        println!("  olean-root: {}", r.display());
    }
    println!();

    let exe = match std::env::current_exe() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error: cannot locate own executable for worker re-exec: {e}");
            return 1;
        }
    };

    let start = Instant::now();

    // RESUMABILITY: skip any module whose sidecar already exists and parses in
    // --out, so an interrupted or re-run resumes instead of re-verifying ~all
    // 12k modules. The kept (resumable) sidecars still feed the final merge.
    let (to_run, resumable) = partition_resumable(&modules, &out_dir);
    if !resumable.is_empty() {
        println!("  resumed: {} skipped (sidecar present)", resumable.len());
    }

    let mut sidecar_paths = run_workers_bounded(&exe, &to_run, opts, &out_dir);

    // RETRY: one bounded pass over modules that produced NO sidecar or a sidecar
    // that no longer parses (the campaign's no-sidecar WARNINGs). Re-spawn only
    // those, then log whatever is still missing after the retry.
    let missing = missing_modules(&modules, &out_dir);
    if !missing.is_empty() {
        println!(
            "  retry: {} module(s) had no usable sidecar; one bounded retry pass",
            missing.len()
        );
        let retried = run_workers_bounded(&exe, &missing, opts, &out_dir);
        sidecar_paths.extend(retried);
        let still_missing = missing_modules(&modules, &out_dir);
        if still_missing.is_empty() {
            println!("  retry: all recovered");
        } else {
            eprintln!(
                "  retry: {} module(s) STILL missing a sidecar after retry:",
                still_missing.len()
            );
            for m in &still_missing {
                eprintln!("    STILL-MISSING {m}");
            }
        }
    }

    // Resumed sidecars were not re-run this pass; include them in the merge.
    sidecar_paths.extend(resumable);
    sidecar_paths.sort();
    sidecar_paths.dedup();

    let elapsed = start.elapsed();

    merge_and_report(
        &out_dir,
        &sidecar_paths,
        modules.len(),
        elapsed.as_secs_f64(),
    )
}

/// Path of the per-module sidecar inside `out_dir`.
fn sidecar_path_for(out_dir: &Path, module: &str) -> PathBuf {
    out_dir.join(format!("{}.json", sanitize(module)))
}

/// A sidecar is RESUMABLE when it exists on disk AND parses as a
/// [`KernelVerifiedManifest`]. A present-but-corrupt sidecar (interrupted
/// mid-write) is treated as absent so it gets re-verified.
fn sidecar_is_resumable(path: &Path) -> bool {
    path.exists() && KernelVerifiedManifest::from_file(path).is_ok()
}

/// Split `modules` into `(to_run, resumable)` against existing sidecars in
/// `out_dir`. `resumable` holds the sidecar paths to fold into the final merge
/// without re-verifying; `to_run` holds module names that still need a worker.
fn partition_resumable(modules: &[String], out_dir: &Path) -> (Vec<String>, Vec<PathBuf>) {
    let mut to_run = Vec::new();
    let mut resumable = Vec::new();
    for module in modules {
        let sidecar = sidecar_path_for(out_dir, module);
        if sidecar_is_resumable(&sidecar) {
            resumable.push(sidecar);
        } else {
            to_run.push(module.clone());
        }
    }
    (to_run, resumable)
}

/// Module names whose sidecar is absent or no longer parses in `out_dir`.
fn missing_modules(modules: &[String], out_dir: &Path) -> Vec<String> {
    modules
        .iter()
        .filter(|m| !sidecar_is_resumable(&sidecar_path_for(out_dir, m)))
        .cloned()
        .collect()
}

fn collect_modules(opts: &ShardedOpts) -> Result<Vec<String>, String> {
    if let Some(list) = &opts.module_list {
        let text = std::fs::read_to_string(list)
            .map_err(|e| format!("Error: cannot read --module-list {}: {e}", list.display()))?;
        Ok(text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(str::to_string)
            .collect())
    } else {
        // Enumerate from the FIRST olean root (the module corpus root, e.g. the
        // Mathlib lake build dir). Dependency roots (toolchain Init/Std) are
        // search paths, not enumeration roots.
        let root = &opts.olean_roots[0];
        Ok(enumerate_modules(root))
    }
}

/// Spawn one worker per module, bounded to `opts.jobs` concurrent children, via
/// a simple poll loop (no extra dependency). Returns the sidecar paths that were
/// successfully produced.
fn run_workers_bounded(
    exe: &Path,
    modules: &[String],
    opts: &ShardedOpts,
    out_dir: &Path,
) -> Vec<PathBuf> {
    use std::process::Child;

    struct Running {
        child: Child,
        module: String,
        sidecar: PathBuf,
    }

    let mut produced = Vec::new();
    let mut running: Vec<Running> = Vec::new();
    let mut next = 0usize;
    let mut done = 0usize;
    let total = modules.len();

    loop {
        // Fill up to the concurrency bound.
        while running.len() < opts.jobs && next < modules.len() {
            let module = modules[next].clone();
            next += 1;
            let sidecar = sidecar_path_for(out_dir, &module);
            match spawn_worker(exe, &module, opts, &sidecar) {
                Ok(child) => running.push(Running {
                    child,
                    module,
                    sidecar,
                }),
                Err(e) => eprintln!("[driver] spawn failed for {module}: {e}"),
            }
        }

        if running.is_empty() {
            break;
        }

        // Reap any finished children; sleep briefly if none finished this pass.
        let mut reaped_any = false;
        let mut still: Vec<Running> = Vec::with_capacity(running.len());
        for mut r in running.drain(..) {
            match r.child.try_wait() {
                Ok(Some(status)) => {
                    reaped_any = true;
                    done += 1;
                    if status.success() && r.sidecar.exists() {
                        produced.push(r.sidecar);
                    } else {
                        eprintln!(
                            "[driver] {} did not produce a sidecar (exit: {})",
                            r.module, status
                        );
                    }
                    eprintln!("[driver] {}/{} done ({})", done, total, r.module);
                }
                Ok(None) => still.push(r),
                Err(e) => {
                    eprintln!("[driver] wait error for {}: {e}", r.module);
                    done += 1;
                }
            }
        }
        running = still;
        if !reaped_any {
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
    }

    produced
}

fn spawn_worker(
    exe: &Path,
    module: &str,
    opts: &ShardedOpts,
    sidecar: &Path,
) -> std::io::Result<std::process::Child> {
    let mut cmd = Command::new(exe);
    cmd.arg("verify-kernel")
        .arg("--module")
        .arg(module)
        .arg("--emit")
        .arg(sidecar);
    for root in &opts.olean_roots {
        cmd.arg("--olean-root").arg(root);
    }
    // Workers re-check deep proof terms; preserve a large stack like the parent.
    if std::env::var_os("RUST_MIN_STACK").is_none() {
        cmd.env("RUST_MIN_STACK", "67108864");
    }
    cmd.spawn()
}

/// Sanitize a dot-separated module name into a single-file-safe stem.
fn sanitize(module: &str) -> String {
    module
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '.' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn merge_and_report(
    out_dir: &Path,
    sidecar_paths: &[PathBuf],
    module_count: usize,
    elapsed_secs: f64,
) -> i32 {
    let mut sidecars = Vec::with_capacity(sidecar_paths.len());
    let mut read_failures = 0usize;
    for p in sidecar_paths {
        match KernelVerifiedManifest::from_file(p) {
            Ok(m) => sidecars.push(m),
            Err(e) => {
                read_failures += 1;
                eprintln!("[driver] failed to read sidecar {}: {e}", p.display());
            }
        }
    }

    let merged = KernelVerifiedManifest::merge(&out_dir.display().to_string(), &sidecars);
    let consolidated = out_dir.join("kernel-verified.json");
    if let Err(e) = merged.write_to_file(&consolidated) {
        eprintln!("[driver] failed to write consolidated manifest: {e}");
        return 1;
    }

    println!("\n=== Sharded Corpus Verification Summary ===");
    println!("  Modules requested:    {module_count}");
    println!("  Sidecars merged:      {}", sidecars.len());
    println!("  Total OWN constants:  {}", merged.total_constants);
    println!("  Kernel verified:      {}", merged.kernel_verified);
    println!("  Axiom-accepted:       {}", merged.axiom_accepted);
    println!("  Failed:               {}", merged.failed);
    if merged.total_constants > 0 {
        let denom = merged.kernel_verified + merged.axiom_accepted + merged.failed;
        if denom > 0 {
            println!(
                "  Verified rate:        {:.2}%",
                merged.kernel_verified as f64 / denom as f64 * 100.0
            );
        }
    }
    println!("  Wall-clock:           {elapsed_secs:.2}s");
    println!("  Consolidated:         {}", consolidated.display());

    if read_failures > 0 || sidecars.len() < module_count {
        // Missing sidecars (worker OOM/crash/not-found) are a partial-run signal.
        eprintln!(
            "\n  WARNING: {} module(s) produced no usable sidecar",
            module_count - sidecars.len()
        );
        return 1;
    }
    0
}

#[cfg(test)]
mod tests {
    use super::{
        missing_modules, partition_resumable, sanitize, sidecar_is_resumable, sidecar_path_for,
    };
    use clean_mathverse::verify::kernel_verified_manifest::KernelVerifiedManifest;

    /// Write a well-formed sidecar for `module` into `out_dir`.
    fn write_good_sidecar(out_dir: &std::path::Path, module: &str) {
        let m = KernelVerifiedManifest::from_worker_parts(
            module,
            1,
            0,
            0,
            0.0,
            vec![format!("{module}.thm")],
        );
        m.write_to_file(&sidecar_path_for(out_dir, module))
            .expect("write sidecar");
    }

    #[test]
    fn test_sidecar_is_resumable_only_when_present_and_parses() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path();

        // Absent -> not resumable.
        let missing = sidecar_path_for(out, "Mathlib.Absent");
        assert!(!sidecar_is_resumable(&missing));

        // Present + parses -> resumable.
        write_good_sidecar(out, "Mathlib.Good");
        assert!(sidecar_is_resumable(&sidecar_path_for(out, "Mathlib.Good")));

        // Present but corrupt (truncated mid-write) -> NOT resumable.
        let corrupt = sidecar_path_for(out, "Mathlib.Corrupt");
        std::fs::write(&corrupt, b"{ not valid json").expect("write corrupt");
        assert!(!sidecar_is_resumable(&corrupt));
    }

    #[test]
    fn test_partition_resumable_skips_existing_runs_rest() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path();
        let modules = vec![
            "Mathlib.A".to_string(),
            "Mathlib.B".to_string(),
            "Mathlib.C".to_string(),
        ];
        // Only B already has a good sidecar.
        write_good_sidecar(out, "Mathlib.B");

        let (to_run, resumable) = partition_resumable(&modules, out);

        // B is skipped (resumable), A and C still need a worker.
        assert_eq!(
            to_run,
            vec!["Mathlib.A".to_string(), "Mathlib.C".to_string()]
        );
        assert_eq!(resumable.len(), 1);
        assert_eq!(resumable[0], sidecar_path_for(out, "Mathlib.B"));
    }

    #[test]
    fn test_missing_modules_finds_absent_and_corrupt() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path();
        let modules = vec![
            "Mathlib.A".to_string(),
            "Mathlib.B".to_string(),
            "Mathlib.C".to_string(),
        ];
        write_good_sidecar(out, "Mathlib.A");
        // B corrupt, C absent -> both reported missing for the retry pass.
        std::fs::write(sidecar_path_for(out, "Mathlib.B"), b"oops").expect("write");

        let missing = missing_modules(&modules, out);
        assert_eq!(
            missing,
            vec!["Mathlib.B".to_string(), "Mathlib.C".to_string()]
        );
    }

    #[test]
    fn test_sidecar_path_sanitizes_module_name() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path();
        let p = sidecar_path_for(out, "Mathlib.Order.Basic");
        assert_eq!(
            p.file_name().and_then(|s| s.to_str()),
            Some("Mathlib.Order.Basic.json")
        );
        // The sanitizer keeps alphanumerics and dots, replaces the rest.
        assert_eq!(sanitize("A/B C"), "A_B_C");
    }
}
