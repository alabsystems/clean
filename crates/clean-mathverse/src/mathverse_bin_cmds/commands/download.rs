// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse download` — fetch a Mathverse corpus and verify it.
//!
//! Two sources:
//! - default: a tagged GitHub Release (`gh`), via [`download_release`];
//! - `--from <server-url>`: a running `mathverse_serve` instance, via
//!   [`download_from_server`] (pulls `/manifest` + each `/download/{shard}`).
//!
//! Either way the landed corpus is blake3-verified against its manifest before
//! the command reports success (`--no-verify` opts out of the gh-path check;
//! the server path is verified by construction).

use std::path::{Path, PathBuf};

use crate::corpus_download::{download_from_server, ServerDownloadConfig};
use crate::release::{
    download_release, verify_release, ReleaseConfig, VerifyResult, DEFAULT_CLEAN_RELEASE_REPO,
};

use super::default_library_dir;

pub fn cmd_download(args: &[String]) {
    let mut version: Option<String> = None;
    let mut from: Option<String> = None;
    let mut out: Option<PathBuf> = None;
    let mut force = false;
    let mut verify = true;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--version" => {
                i += 1;
                version = args.get(i).cloned();
            }
            "--from" => {
                i += 1;
                from = args.get(i).cloned();
            }
            "--out" | "--output" => {
                i += 1;
                out = args.get(i).map(PathBuf::from);
            }
            "--force" => force = true,
            "--no-verify" => verify = false,
            "--help" | "-h" => {
                print_download_usage();
                return;
            }
            other => {
                eprintln!("Unknown download option: {other}");
                print_download_usage();
                std::process::exit(1);
            }
        }
        i += 1;
    }

    let output_dir = out.unwrap_or_else(default_library_dir);

    if let Some(server) = from {
        download_via_server(&server, &output_dir);
    } else {
        download_via_release(version, &output_dir, force, verify);
    }
}

/// `--from <server-url>`: pull + verify from a running `mathverse_serve`.
fn download_via_server(server: &str, output_dir: &Path) {
    println!("Downloading Mathverse corpus from server {server} ...");
    let cfg = ServerDownloadConfig {
        server_url: server.to_string(),
        out_dir: output_dir.to_path_buf(),
    };
    match download_from_server(&cfg) {
        Ok(result) => {
            println!("Corpus downloaded to {}", output_dir.display());
            print_verify_summary(&result);
            println!(
                "Verified {} shard(s) against the server manifest.",
                result.passed
            );
        }
        Err(e) => {
            eprintln!("Server download failed: {e}");
            std::process::exit(1);
        }
    }
}

/// Default source: a tagged GitHub Release, then verify the landed corpus.
fn download_via_release(version: Option<String>, output_dir: &Path, force: bool, verify: bool) {
    if output_dir.is_dir() && !force {
        println!("Library already present at {}", output_dir.display());
        println!("Use --force to re-download.");
        return;
    }

    let config = ReleaseConfig {
        repo: DEFAULT_CLEAN_RELEASE_REPO.to_string(),
        version,
        output_dir: output_dir.to_path_buf(),
    };

    println!("Downloading Mathverse library release ...");
    let path = match download_release(&config) {
        Ok(path) => path,
        Err(e) => {
            eprintln!("Download failed: {e}");
            std::process::exit(1);
        }
    };
    println!("Library downloaded to {}", path.display());

    if !verify {
        return;
    }
    match verify_release(&path) {
        Ok(result) if result.is_ok() => {
            println!(
                "Verified {} shard(s) (blake3) against the release manifest.",
                result.passed
            );
        }
        Ok(result) => {
            print_verify_summary(&result);
            eprintln!("Post-download verification FAILED.");
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("Could not verify downloaded library: {e}");
            std::process::exit(1);
        }
    }
}

fn print_verify_summary(result: &VerifyResult) {
    println!("  Checked: {}", result.checked);
    println!("  Passed:  {}", result.passed);
    if !result.missing.is_empty() {
        println!("  Missing: {}", result.missing.len());
    }
    if !result.failures.is_empty() {
        println!("  Failed:  {}", result.failures.len());
        for f in &result.failures {
            println!("    - {} (blake3 mismatch)", f.path);
        }
    }
}

fn print_download_usage() {
    eprintln!("mathverse download — fetch and verify a Mathverse corpus");
    eprintln!();
    eprintln!("Options:");
    eprintln!(
        "  --from <URL>     Pull from a running mathverse_serve (e.g. http://127.0.0.1:8080)"
    );
    eprintln!("  --version <V>    GitHub release version to fetch (default: latest)");
    eprintln!("  --out <DIR>      Output directory (default: discovery path)");
    eprintln!("  --force          Re-download even if the output dir already exists");
    eprintln!("  --no-verify      Skip the post-download blake3 verification (gh path)");
}
