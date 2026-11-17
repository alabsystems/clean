// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_shard stamp --shard-dir=<dir> --manifest=<kernel-verified.json>` (the
//! parser takes the `=` form only).
//!
//! The verb's one job was to stamp `KernelVerified` into shard headers from an
//! existing manifest, with no re-verification. Under P6 (reader R1 of
//! `designs/2026-11-16-p6-acceptance-identity.md`) it refuses every manifest
//! this build can read: a schema-1 or identity-less file is refused by its own
//! validation, and a valid one is development tier, which confers no header
//! label (P2 clause 1). The reference producer that could feed it lands in
//! slice 1b, with its receipts. Nothing on disk is touched, and the verb exits
//! non-zero.

use std::path::PathBuf;

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

    if let Err(msg) = run_stamp(&opts) {
        eprintln!("Error: {msg}");
        std::process::exit(1);
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

/// Read the manifest and refuse it: no manifest this build can read grants a
/// header label. Returns the refusal; the shard directory is never written.
fn run_stamp(opts: &StampOpts) -> Result<(), String> {
    if !opts.shard_dir.is_dir() {
        return Err(format!("shard dir not found: {}", opts.shard_dir.display()));
    }
    if !opts.manifest.is_file() {
        return Err(format!("manifest not found: {}", opts.manifest.display()));
    }
    let refusal = KernelVerifiedManifest::refuse_grant(&opts.manifest, "a shard header stamp");
    if opts.json {
        println!(
            "{}",
            serde_json::json!({
                "shard_dir": opts.shard_dir.display().to_string(),
                "manifest": opts.manifest.display().to_string(),
                "refused": refusal.to_string(),
                "headers_stamped": 0,
            })
        );
    }
    Err(refusal.to_string())
}

fn print_stamp_usage() {
    eprintln!(
        "Usage: mathverse_shard stamp --shard-dir=<dir> --manifest=<kernel-verified.json> [--json]"
    );
    eprintln!("  Refuses every manifest this build can read (P6): a development-tier");
    eprintln!("  manifest confers no header label, and no reference producer exists yet.");
    eprintln!("  Nothing on disk is written.");
}

#[cfg(test)]
#[path = "stamp_command_tests.rs"]
mod tests;
