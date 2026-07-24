// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_shard stamp --shard-dir <dir> --manifest <kernel-verified.json>`.
//!
//! Applies an EXISTING merged kernel-verified manifest to pre-built shards on
//! disk, with NO re-verification. This is the missing glue between the sharded
//! DRIVER (`verify-kernel --corpus-sharded`, which emits a merged
//! `kernel-verified.json` with the higher full-dependency-closure verdict) and
//! a persisted, `stats`-visible stored `KernelVerified` count.
//!
//! Contrast with `clean mathverse stamp-verified`, which RE-converts and
//! RE-verifies internally (a lower-closure, lower-yield path). This subcommand
//! never re-verifies: it only stamps the constants the kernel already accepted.
//!
//! SOUNDNESS: only `manifest.kernel_verified_names` are stamped — exactly the
//! set whose value passed Clean's kernel during the driver's run. Axioms,
//! axiom-fallbacks, and reconstruction failures are excluded upstream and are
//! therefore never raised here. This is the identical guarantee to the existing
//! `stamp-verified` / [`stamp_shard_dir_kernel_verified`] path; there is no
//! heuristic promotion.
//!
//! [`stamp_shard_dir_kernel_verified`]: clean_mathverse::library::stamp_shard_dir_kernel_verified

use std::path::{Path, PathBuf};

use clean_mathverse::library::{count_stored_kernel_verified, stamp_shard_dir_kernel_verified};
use clean_mathverse::verify::kernel_verified_manifest::KernelVerifiedManifest;

/// Parsed options for `mathverse_shard stamp`.
struct StampOpts {
    shard_dir: PathBuf,
    manifest: PathBuf,
    json: bool,
}

/// Entry point for the `stamp` subcommand. Exits the process on usage or
/// runtime errors (mirrors the other `mathverse_shard` subcommands).
pub(crate) fn cmd_stamp(args: &[String]) {
    let opts = match parse_stamp_args(args) {
        Ok(opts) => opts,
        Err(msg) => {
            eprintln!("{msg}");
            print_stamp_usage();
            std::process::exit(2);
        }
    };

    if let Err(code) = run_stamp(&opts) {
        std::process::exit(code);
    }
}

fn parse_stamp_args(args: &[String]) -> Result<StampOpts, String> {
    let mut shard_dir: Option<PathBuf> = None;
    let mut manifest: Option<PathBuf> = None;
    let mut json = false;

    for arg in args {
        if let Some(val) = arg.strip_prefix("--shard-dir=") {
            shard_dir = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--manifest=") {
            manifest = Some(PathBuf::from(val));
        } else if arg == "--json" {
            json = true;
        } else if arg.starts_with("--") {
            return Err(format!("Unknown option: {arg}"));
        } else {
            return Err(format!("Unexpected argument: {arg}"));
        }
    }

    let shard_dir = shard_dir.ok_or_else(|| "Missing required --shard-dir=<dir>".to_string())?;
    let manifest =
        manifest.ok_or_else(|| "Missing required --manifest=<kernel-verified.json>".to_string())?;
    Ok(StampOpts {
        shard_dir,
        manifest,
        json,
    })
}

/// Read the manifest, stamp the shard dir in place, and report the resulting
/// stored count. Returns `Err(exit_code)` on any error.
fn run_stamp(opts: &StampOpts) -> Result<(), i32> {
    if !opts.shard_dir.is_dir() {
        eprintln!("Error: shard dir not found: {}", opts.shard_dir.display());
        return Err(1);
    }
    if !opts.manifest.is_file() {
        eprintln!("Error: manifest not found: {}", opts.manifest.display());
        return Err(1);
    }

    let manifest = KernelVerifiedManifest::from_file(&opts.manifest).map_err(|e| {
        eprintln!("Error reading manifest {}: {e}", opts.manifest.display());
        1
    })?;

    // Count BEFORE so the metric move is auditable.
    let (before, _) = count_stored_kernel_verified(&opts.shard_dir).map_err(|e| {
        eprintln!("Error scanning shard dir: {e}");
        1
    })?;

    // Apply ONLY the kernel's verdict set — no re-verify, no heuristic.
    let stamp = stamp_shard_dir_kernel_verified(&opts.shard_dir, &manifest).map_err(|e| {
        eprintln!("Error stamping shards: {e}");
        1
    })?;

    // Re-read from disk to report the persisted count a `stats` reader sees.
    let (after, unreadable) = count_stored_kernel_verified(&opts.shard_dir).map_err(|e| {
        eprintln!("Error re-scanning shard dir: {e}");
        1
    })?;

    if opts.json {
        print_json(opts, &manifest, before, after, &stamp, &unreadable);
    } else {
        print_human(opts, &manifest, before, after, &stamp, &unreadable);
    }
    Ok(())
}

fn print_human(
    opts: &StampOpts,
    manifest: &KernelVerifiedManifest,
    before: usize,
    after: usize,
    stamp: &clean_mathverse::library::ShardStampResult,
    unreadable: &[String],
) {
    println!("=== Stamp KernelVerified from manifest ===");
    println!("  Shard dir:           {}", opts.shard_dir.display());
    println!("  Manifest:            {}", opts.manifest.display());
    println!("  Manifest tool:       {}", manifest.tool);
    println!(
        "  Manifest names:      {} (kernel verdict set)",
        manifest.kernel_verified_names.len()
    );
    println!("  Stored before:       {before}");
    println!("  Shards rewritten:    {}", stamp.shards_rewritten);
    println!("  Headers stamped:     {}", stamp.constants_stamped);
    println!("  Stored after:        {after}");
    for path in unreadable {
        println!("  WARNING unreadable shard: {path}");
    }
}

fn print_json(
    opts: &StampOpts,
    manifest: &KernelVerifiedManifest,
    before: usize,
    after: usize,
    stamp: &clean_mathverse::library::ShardStampResult,
    unreadable: &[String],
) {
    let unreadable_json: Vec<String> = unreadable
        .iter()
        .map(|p| serde_json::to_string(p).unwrap_or_else(|_| "\"\"".to_string()))
        .collect();
    println!("{{");
    println!("  \"shard_dir\": {},", json_str(&opts.shard_dir));
    println!("  \"manifest\": {},", json_str(&opts.manifest));
    println!(
        "  \"manifest_names\": {},",
        manifest.kernel_verified_names.len()
    );
    println!("  \"stored_before\": {before},");
    println!("  \"shards_rewritten\": {},", stamp.shards_rewritten);
    println!("  \"headers_stamped\": {},", stamp.constants_stamped);
    println!("  \"stored_after\": {after},");
    println!("  \"unreadable\": [{}]", unreadable_json.join(", "));
    println!("}}");
}

fn json_str(path: &Path) -> String {
    serde_json::to_string(&path.display().to_string()).unwrap_or_else(|_| "\"\"".to_string())
}

fn print_stamp_usage() {
    eprintln!(
        "Usage: mathverse_shard stamp --shard-dir=<dir> --manifest=<kernel-verified.json> [--json]"
    );
    eprintln!("  Apply an EXISTING merged kernel-verified manifest to pre-built shards on disk");
    eprintln!("  (NO re-verify). Stamps only manifest.kernel_verified_names, then reports the");
    eprintln!("  stored KernelVerified count a `clean mathverse stats` reader sees.");
}
