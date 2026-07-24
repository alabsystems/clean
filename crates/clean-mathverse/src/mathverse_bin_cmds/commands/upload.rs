// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse upload` — publish a local corpus to a distribution destination.
//!
//! `clean mathverse upload <corpus-dir> --to <dest> --version <V>` where `dest`
//! is `release:<tag>`, `gcs:<bucket/path>`, or `server:<url>`. Delegates to
//! [`crate::corpus_upload::upload_corpus`], which packages with a fresh blake3
//! manifest (`release:`) or rsyncs the content-addressed corpus (`gcs:`).

use std::path::PathBuf;

use crate::corpus_upload::{upload_corpus, UploadConfig, UploadDest};
use crate::release::DEFAULT_CLEAN_RELEASE_REPO;

pub fn cmd_upload(args: &[String]) {
    let mut corpus_dir: Option<PathBuf> = None;
    let mut to: Option<String> = None;
    let mut version: Option<String> = None;
    let mut repo = DEFAULT_CLEAN_RELEASE_REPO.to_string();
    let mut staging: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--to" => {
                i += 1;
                to = args.get(i).cloned();
            }
            "--version" => {
                i += 1;
                version = args.get(i).cloned();
            }
            "--repo" => {
                i += 1;
                if let Some(r) = args.get(i) {
                    repo = r.clone();
                }
            }
            "--staging" | "--output" => {
                i += 1;
                staging = args.get(i).map(PathBuf::from);
            }
            "--help" | "-h" => {
                print_upload_usage();
                return;
            }
            other if other.starts_with('-') => {
                eprintln!("Unknown upload option: {other}");
                print_upload_usage();
                std::process::exit(1);
            }
            positional => {
                if corpus_dir.is_none() {
                    corpus_dir = Some(PathBuf::from(positional));
                } else {
                    eprintln!("Unexpected extra argument: {positional}");
                    std::process::exit(1);
                }
            }
        }
        i += 1;
    }

    let corpus_dir = corpus_dir.unwrap_or_else(|| {
        eprintln!("Error: a corpus directory positional argument is required.");
        print_upload_usage();
        std::process::exit(1);
    });
    let to = to.unwrap_or_else(|| {
        eprintln!("Error: --to <release:tag|gcs:uri|server:url> is required.");
        print_upload_usage();
        std::process::exit(1);
    });
    let dest = UploadDest::parse(&to).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });
    let version = version.unwrap_or_else(|| {
        eprintln!("Error: --version <V> is required (embedded in the archive name + manifest).");
        std::process::exit(1);
    });

    let mut cfg = UploadConfig::new(corpus_dir, dest, version);
    cfg.repo = repo;
    if let Some(s) = staging {
        cfg.staging_dir = s;
    }

    println!("Uploading corpus {} -> {to} ...", cfg.corpus_dir.display());
    match upload_corpus(&cfg) {
        Ok(outcome) => {
            if let Some(archive) = &outcome.archive {
                println!("  Packaged archive: {}", archive.display());
            }
            println!("Uploaded to {}", outcome.destination);
        }
        Err(e) => {
            eprintln!("Upload failed: {e}");
            std::process::exit(1);
        }
    }
}

fn print_upload_usage() {
    eprintln!("mathverse upload — publish a local corpus to a distribution destination");
    eprintln!();
    eprintln!("Usage: clean mathverse upload <corpus-dir> --to <dest> --version <V>");
    eprintln!();
    eprintln!("Destinations (--to):");
    eprintln!("  release:<tag>        Package + publish as a GitHub Release asset (gh)");
    eprintln!("  gcs:<bucket/path>    rsync shards + manifest to a GCS bucket (gcloud/gsutil)");
    eprintln!("  server:<url>         Indirect: prints how to publish via release/bucket");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --version <V>        Release version (required)");
    eprintln!(
        "  --repo <owner/name>  GitHub repo for release: (default: {DEFAULT_CLEAN_RELEASE_REPO})"
    );
    eprintln!(
        "  --staging <DIR>      Staging dir for the packaged archive (release:, default dist)"
    );
}
