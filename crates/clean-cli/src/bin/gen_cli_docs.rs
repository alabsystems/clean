// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `gen_cli_docs` — regenerate `docs/cli/` from the `FeatureDescriptor` registry.
//!
//! Part of Epic #3436 Phase 5 (#3482). Pairs with the drift test
//! `crates/clean-cli/tests/docs_drift.rs` which runs the same rendering
//! function in-process and fails if the on-disk tree has diverged.
//!
//! Usage:
//!
//! ```text
//! gen_cli_docs [--output <DIR>]
//! ```
//!
//! Defaults `--output` to `docs/cli/` in the current working directory, which
//! matches the repo-root checkout that `scripts/gen_cli_docs.sh` invokes.
//!
//! The binary owns three responsibilities:
//!
//! 1. Call `clean_cli::__test_support::render_all_docs(all_features())` to
//!    build the in-memory `filename -> contents` map.
//! 2. Ensure the target directory exists.
//! 3. Write each file, removing any pre-existing file in the target directory
//!    that is *not* in the generated set so stale paths from renamed
//!    descriptors do not linger in the repo.
//!
//! The on-disk write is the only side effect; rendering itself is pure.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Parser;
use tracing::info;

use clean_cli::__test_support::{all_features, render_all_docs};

/// CLI arguments for the generator.
#[derive(Debug, Parser)]
#[command(
    name = "gen_cli_docs",
    about = "Regenerate the docs/cli/ Markdown tree from the FeatureDescriptor registry.",
    long_about = None,
)]
struct Args {
    /// Output directory. Defaults to `docs/cli/` relative to the current
    /// working directory, which is the repository root when invoked via
    /// `scripts/gen_cli_docs.sh`.
    #[arg(long, default_value = "docs/cli")]
    output: PathBuf,
}

fn main() -> Result<()> {
    // The default subscriber format writes `INFO` records to stderr, which is
    // the channel the shell wrapper already captures and echoes back to the
    // user. We install a minimal subscriber here so `tracing::info!` lines
    // are visible without requiring callers to configure one.
    tracing_subscriber::fmt()
        .with_target(false)
        .without_time()
        .with_writer(std::io::stderr)
        .init();

    let args = Args::parse();
    let descriptors = all_features();
    let files = render_all_docs(&descriptors);

    write_tree(&args.output, &files)?;

    info!(
        "gen_cli_docs: wrote {count} file{plural} to {dir}",
        count = files.len(),
        plural = if files.len() == 1 { "" } else { "s" },
        dir = args.output.display()
    );
    Ok(())
}

/// Persist the generated file map to `dir`, creating the directory if it
/// does not exist and deleting stale Markdown files that are no longer
/// present in the map.
///
/// Only `*.md` files in the top level of `dir` are considered for deletion;
/// sub-directories and non-Markdown files are left untouched so the
/// generator can coexist with hand-authored narrative docs under the same
/// tree should that ever be wanted.
fn write_tree(dir: &Path, files: &std::collections::BTreeMap<String, String>) -> Result<()> {
    fs::create_dir_all(dir)
        .with_context(|| format!("creating output directory {}", dir.display()))?;

    // Compute the set of expected filenames so we know which existing files
    // are stale and should be removed.
    let expected: BTreeSet<&str> = files.keys().map(String::as_str).collect();

    // Remove stale top-level *.md files.
    for entry in
        fs::read_dir(dir).with_context(|| format!("reading output directory {}", dir.display()))?
    {
        let entry = entry.with_context(|| format!("reading entry in {}", dir.display()))?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let file_name = match path.file_name().and_then(|n| n.to_str()) {
            Some(name) => name,
            None => continue,
        };
        if !file_name.ends_with(".md") {
            continue;
        }
        if !expected.contains(file_name) {
            fs::remove_file(&path)
                .with_context(|| format!("removing stale file {}", path.display()))?;
        }
    }

    // Write every file atomically-ish: write to a temp path alongside then
    // rename. We deliberately avoid `tempfile::NamedTempFile` here because
    // the binary crate does not depend on it (keeps the dep surface minimal);
    // direct write is sufficient for generator idempotency.
    for (name, contents) in files {
        let target = dir.join(name);
        fs::write(&target, contents).with_context(|| format!("writing {}", target.display()))?;
    }

    Ok(())
}
