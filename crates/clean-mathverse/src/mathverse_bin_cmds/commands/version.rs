// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse version` — display mathverse library version and summary statistics.

use std::collections::HashMap;

use crate::release::ReleaseManifest;

use crate::mathverse_bin_cmds::fmt::confidence_display;
use crate::mathverse_bin_cmds::{discover_library_path, load_library};

/// The current mathverse library release version.
const MATHVERSE_RELEASE_VERSION: &str = "1.1.0";

/// Number of source systems in the SourceSystem enum.
const SOURCE_SYSTEM_COUNT: u32 = 68;

pub fn cmd_version(args: &[String]) {
    let json = args.iter().any(|a| a == "--json");

    println!("Mathverse Library v{MATHVERSE_RELEASE_VERSION}");

    // Try to load the library for live stats; fall back to known values.
    if let Some(lib_path) = discover_library_path() {
        // Read manifest for shard count.
        let manifest_path = lib_path.join("mathverse-manifest.json");
        let shard_count = ReleaseManifest::from_file(&manifest_path)
            .map(|m| m.total_shards)
            .unwrap_or(107);

        let lib = load_library();
        let count = lib.constant_count();

        let mut by_trust: HashMap<u8, usize> = HashMap::new();
        for idx in 0..count as u32 {
            if let Some(h) = lib.get_constant(idx) {
                *by_trust.entry(h.import_confidence).or_default() += 1;
            }
        }

        if json {
            print_version_json(shard_count, count, &by_trust);
        } else {
            print_version_table(shard_count, count, &by_trust);
        }
    } else {
        println!("Shards: 107  Systems: {SOURCE_SYSTEM_COUNT}  Declarations: 3,254,463");
        println!();
        println!("Library not loaded (run `mathverse download` to fetch).");
    }
}

fn print_version_table(shards: usize, declarations: usize, by_trust: &HashMap<u8, usize>) {
    println!("Shards: {shards}  Systems: {SOURCE_SYSTEM_COUNT}  Declarations: {declarations}");
    if !by_trust.is_empty() {
        let mut trust_sorted: Vec<_> = by_trust.iter().collect();
        trust_sorted.sort_by_key(|&(k, _)| *k);
        let parts: Vec<String> = trust_sorted
            .iter()
            .map(|(&id, &n)| format!("{}={}", confidence_display(id), n))
            .collect();
        println!("Trust: {}", parts.join(", "));
    }
}

fn print_version_json(shards: usize, declarations: usize, by_trust: &HashMap<u8, usize>) {
    let trust_map: serde_json::Map<String, serde_json::Value> = by_trust
        .iter()
        .map(|(&id, &n)| (confidence_display(id).to_string(), serde_json::json!(n)))
        .collect();
    let obj = serde_json::json!({
        "version": MATHVERSE_RELEASE_VERSION,
        "shards": shards,
        "source_systems": SOURCE_SYSTEM_COUNT,
        "declarations": declarations,
        "trust_levels": trust_map,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&obj).expect("invariant: json serialization")
    );
}
