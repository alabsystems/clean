// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake verify-fresh` — Cake content-hash freshness over built `.olean` artifacts.
//!
//! Reports, per module, whether its `.olean` is content-fresh vs its `.lean` source (the
//! import-list signature: stale iff the source declares an import the `.olean` lacks).
//! Fail-closed: a non-zero exit on any stale module. This is the build-authority freshness
//! check graduation should pass before it trusts an imported environment.

use std::path::PathBuf;

pub(super) fn lake_verify_fresh(
    source_root: PathBuf,
    module: Vec<String>,
    olean_search_path: Vec<PathBuf>,
    json: bool,
) -> anyhow::Result<()> {
    if module.is_empty() {
        anyhow::bail!("verify-fresh: at least one --module is required");
    }
    let search_paths = if olean_search_path.is_empty() {
        vec![source_root.join(".lake/build/lib/lean")]
    } else {
        olean_search_path
    };
    let toolchain = std::fs::read_to_string(source_root.join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string());

    let sig =
        clean_cake::signature_from_search_paths(&module, &source_root, &search_paths, toolchain);

    if json {
        println!("{}", serde_json::to_string_pretty(&sig)?);
    } else {
        println!(
            "Cake freshness — {} module(s), env_digest {}",
            sig.modules.len(),
            sig.env_digest
        );
        for m in &sig.modules {
            println!("  {:<70} {}", m.module, m.freshness.label());
        }
        match sig.staleness_summary() {
            None => println!("OK: all {} module(s) fresh.", sig.modules.len()),
            Some(summary) => eprintln!("STALE: {summary}"),
        }
    }

    if !sig.fresh {
        anyhow::bail!(
            "verify-fresh: {} stale module(s) — rebuild so the .olean artifacts reflect current source",
            sig.stale_modules.len()
        );
    }
    Ok(())
}
