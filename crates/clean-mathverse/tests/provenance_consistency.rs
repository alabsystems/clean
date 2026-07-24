// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #3623: `data/MATHVERSE_PROVENANCE.json`,
//! `data/MATHVERSE_PROVENANCE.md`, `data/MATHVERSE_LIBRARIES.md`, and
//! `crates/clean-mathverse/data/mathverse_summary.json` publish four canonical counts
//! that must agree:
//!
//! | Count                     | Source                                                |
//! |--------------------------|-------------------------------------------------------|
//! | `importer_source_systems` (68) | `SourceSystem` enum in `crates/clean-mathverse/src/types.rs` |
//! | `provenance_records` (131) | length of `.sources` in MATHVERSE_PROVENANCE.json         |
//! | `census_target_repos` (238)| MATHVERSE_LIBRARIES.md headline                           |
//! | `shards_produced` (107)    | release `mathverse-v0.9.0` asset inventory                |
//!
//! Before this audit, these numbers disagreed across artifacts
//! (`total_systems: 238` alongside a sources list of 131, and
//! `mathverse_summary.json` carrying a third unrelated `systems: 158`). This test
//! locks the invariants into place so future refreshes fail loudly if the
//! numbers drift out of sync.

use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};

/// Locate the repo root by walking up from the test binary until the
/// `data/MATHVERSE_PROVENANCE.json` artifact is found.
fn repo_root() -> PathBuf {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    while !dir.join("data/MATHVERSE_PROVENANCE.json").exists() {
        if !dir.pop() {
            panic!(
                "could not locate repo root from {}",
                env!("CARGO_MANIFEST_DIR")
            );
        }
    }
    dir
}

fn read_json(path: &Path) -> Value {
    let raw = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

#[test]
fn mathverse_provenance_has_canonical_vocabulary() {
    let root = repo_root();
    let prov = read_json(&root.join("data/MATHVERSE_PROVENANCE.json"));

    // Canonical fields exist after #3623.
    for field in [
        "schema_version",
        "census_target_repos",
        "importer_source_systems",
        "provenance_records",
        "shards_produced",
        "total_declarations_census",
        "total_declarations_in_records",
        "vocabulary",
    ] {
        assert!(
            prov.get(field).is_some(),
            "MATHVERSE_PROVENANCE.json missing canonical field {field} (see #3623)"
        );
    }

    // `provenance_records` MUST equal `.sources` length.
    let records_field = prov["provenance_records"]
        .as_u64()
        .expect("provenance_records should be a number");
    let sources_len = prov["sources"]
        .as_array()
        .expect("sources should be an array")
        .len() as u64;
    assert_eq!(
        records_field, sources_len,
        "provenance_records ({records_field}) must match .sources length ({sources_len}) (#3623)"
    );

    // Back-compat aliases must still agree with the canonical fields.
    assert_eq!(
        prov["total_systems"].as_u64(),
        prov["census_target_repos"].as_u64(),
        "total_systems (alias) must match census_target_repos (#3623)"
    );
    assert_eq!(
        prov["total_declarations"].as_u64(),
        prov["total_declarations_census"].as_u64(),
        "total_declarations (alias) must match total_declarations_census (#3623)"
    );

    // total_declarations_in_records must equal the sum over populated .sources[].declarations.
    let computed: u64 = prov["sources"]
        .as_array()
        .expect("sources should be an array")
        .iter()
        .filter_map(|s| s.get("declarations").and_then(|d| d.as_u64()))
        .sum();
    let claimed = prov["total_declarations_in_records"]
        .as_u64()
        .expect("total_declarations_in_records should be a number");
    assert_eq!(
        computed, claimed,
        "total_declarations_in_records ({claimed}) must equal Σ sources[].declarations ({computed}) (#3623)"
    );
}

#[test]
fn importer_source_systems_matches_source_system_enum() {
    // SourceSystem variant count is the canonical importer count.
    // Keep in sync with `crates/clean-mathverse/src/types.rs`.
    let root = repo_root();
    let prov = read_json(&root.join("data/MATHVERSE_PROVENANCE.json"));

    let claimed = prov["importer_source_systems"]
        .as_u64()
        .expect("importer_source_systems should be a number");

    // Count variants by parsing the enum source directly. This keeps the test
    // resilient if new systems are added — the JSON must be updated in lockstep.
    let types_src = fs::read_to_string(root.join("crates/clean-mathverse/src/types.rs"))
        .expect("failed to read types.rs");
    let enum_body = types_src
        .split("pub enum SourceSystem {")
        .nth(1)
        .expect("SourceSystem enum not found")
        .split_once('}')
        .expect("SourceSystem enum is not closed")
        .0;
    let variants: usize = enum_body
        .lines()
        .filter(|line| {
            let t = line.trim();
            // Match `Name = 0,` style variants; skip comments and blanks.
            !t.is_empty()
                && !t.starts_with("//")
                && t.chars()
                    .next()
                    .map(|c| c.is_ascii_uppercase())
                    .unwrap_or(false)
        })
        .count();

    assert_eq!(
        claimed as usize, variants,
        "importer_source_systems ({claimed}) must match SourceSystem variant count ({variants}) (#3623)"
    );
}

#[test]
fn mathverse_summary_documents_systems_definition() {
    // The v0.9.0 checked-in summary JSON had a `systems: 158` field with no
    // definition. After #3623 it MUST carry a `systems_definition` note that
    // disambiguates the number from `importer_source_systems: 68`.
    let root = repo_root();
    let summary = read_json(&root.join("crates/clean-mathverse/data/mathverse_summary.json"));

    assert!(
        summary.get("systems_definition").is_some(),
        "crates/clean-mathverse/data/mathverse_summary.json must document `systems_definition` after #3623"
    );

    let def = summary["systems_definition"]
        .as_str()
        .expect("systems_definition should be a string");
    assert!(
        def.contains("#3623"),
        "systems_definition should cite issue #3623 for traceability"
    );
}

#[test]
fn mathverse_libraries_md_references_canonical_vocabulary() {
    let root = repo_root();
    let md = fs::read_to_string(root.join("data/MATHVERSE_LIBRARIES.md"))
        .expect("failed to read MATHVERSE_LIBRARIES.md");
    for token in [
        "importer_source_systems",
        "provenance_records",
        "census_target_repos",
        "shards_produced",
        "#3623",
    ] {
        assert!(
            md.contains(token),
            "MATHVERSE_LIBRARIES.md must reference {token} after #3623"
        );
    }
}

#[test]
fn mathverse_provenance_md_references_canonical_vocabulary() {
    let root = repo_root();
    let md = fs::read_to_string(root.join("data/MATHVERSE_PROVENANCE.md"))
        .expect("failed to read MATHVERSE_PROVENANCE.md");
    for token in [
        "importer_source_systems",
        "provenance_records",
        "census_target_repos",
        "shards_produced",
        "#3623",
    ] {
        assert!(
            md.contains(token),
            "MATHVERSE_PROVENANCE.md must reference {token} after #3623"
        );
    }
}
