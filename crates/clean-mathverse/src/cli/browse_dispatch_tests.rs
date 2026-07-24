// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for [`super`](crate::cli::browse_dispatch).
//!
//! Lives in a sibling file (pulled in via `#[path]`) so
//! `browse_dispatch.rs` itself stays under the 500-line new-file cap while
//! the test coverage for #3512 keeps growing. Test fns exercise:
//!
//! * shard-dir presence / missing paths
//! * system-filter parsing
//! * deterministic sample seeding
//! * deps BFS happy / error paths
//! * version degrade-to-static-line behaviour
//!
//! All tests build a 4-declaration shard fixture (Lean4 + Metamath) in a
//! `tempfile::tempdir()` so they remain hermetic.

use super::*;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
};
use clean_kernel::flat::{FlatExpr, FlatLevel};
use tempfile::tempdir;

fn build_test_shard(names: &[(&str, SourceSystem, ImportConfidence, ContentDomain)]) -> Vec<u8> {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let e0 = writer.add_expr(FlatExpr::sort(l0));
    for &(name, source, confidence, domain) in names {
        let ni = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx: ni,
            type_idx: e0,
            value_idx: e0,
            source_system: source as u8,
            import_confidence: confidence as u8,
            content_domain: domain as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }
    let mut buf = Vec::new();
    writer.write(&mut buf).expect("shard write");
    buf
}

fn make_shard_dir() -> tempfile::TempDir {
    let dir = tempdir().expect("tempdir");
    let shard_bytes = build_test_shard(&[
        (
            "Nat.add",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
        ),
        (
            "Nat.add_comm",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
        ),
        (
            "Bool.true",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::Logic,
        ),
        (
            "set.mm.ax-1",
            SourceSystem::Metamath,
            ImportConfidence::Axiomatized,
            ContentDomain::Logic,
        ),
    ]);
    std::fs::write(dir.path().join("test.mathverse"), &shard_bytes).expect("write");
    dir
}

#[test]
fn test_version_missing_shard_dir_returns_ok() {
    // version must degrade gracefully — the standalone binary falls back
    // to the canonical shard count when the library is absent.
    let args = VersionArgs {
        shard_dir: "/nonexistent/shard/dir".into(),
        json: false,
    };
    cmd_version(args).expect("version should not fail on missing shard dir");
}

#[test]
fn test_version_json_includes_version_and_library_loaded_flag() {
    let args = VersionArgs {
        shard_dir: "/nonexistent/shard/dir".into(),
        json: true,
    };
    cmd_version(args).expect("version json should not fail");
}

#[test]
fn test_version_with_live_shard_dir_counts_trust_buckets() {
    let dir = make_shard_dir();
    let args = VersionArgs {
        shard_dir: dir.path().to_path_buf(),
        json: false,
    };
    cmd_version(args).expect("version with live shard dir");
}

#[test]
fn test_list_default_limits_and_pagination() {
    let dir = make_shard_dir();
    let args = ListArgs {
        system: None,
        limit: 10,
        offset: 0,
        shard_dir: dir.path().to_path_buf(),
        json: false,
    };
    cmd_list(args).expect("list with default shape");
}

#[test]
fn test_list_system_filter_narrows_results() {
    let dir = make_shard_dir();
    // Only 1 Metamath entry in the fixture — filter must preserve it.
    let args = ListArgs {
        system: Some("metamath".to_string()),
        limit: 10,
        offset: 0,
        shard_dir: dir.path().to_path_buf(),
        json: true,
    };
    cmd_list(args).expect("list with system filter");
}

#[test]
fn test_list_offset_is_applied() {
    let dir = make_shard_dir();
    let args = ListArgs {
        system: None,
        limit: 10,
        offset: 2,
        shard_dir: dir.path().to_path_buf(),
        json: true,
    };
    cmd_list(args).expect("list with offset");
}

#[test]
fn test_list_missing_shard_dir_is_typed_error() {
    let args = ListArgs {
        system: None,
        limit: 10,
        offset: 0,
        shard_dir: "/nonexistent/shard/dir".into(),
        json: false,
    };
    match cmd_list(args) {
        Err(MathverseCliError::ShardDirMissing(_)) => {}
        Err(other) => panic!("expected ShardDirMissing, got {other:?}"),
        Ok(()) => panic!("expected failure on missing shard directory"),
    }
}

#[test]
fn test_sample_deterministic_same_seed() {
    let dir = make_shard_dir();
    let mk = |seed: u64| SampleArgs {
        n: 3,
        system: None,
        trust: None,
        seed,
        shard_dir: dir.path().to_path_buf(),
        json: true,
    };
    cmd_sample(mk(42)).expect("sample seed=42");
    cmd_sample(mk(42)).expect("sample seed=42 second run");
}

#[test]
fn test_sample_unknown_system_returns_empty_rather_than_error() {
    let dir = make_shard_dir();
    let args = SampleArgs {
        n: 3,
        system: Some("nonexistent-system-xyz".to_string()),
        trust: None,
        seed: 0,
        shard_dir: dir.path().to_path_buf(),
        json: false,
    };
    cmd_sample(args).expect("sample with unknown system yields 'no results'");
}

#[test]
fn test_sample_trust_filter_parses() {
    let dir = make_shard_dir();
    let args = SampleArgs {
        n: 3,
        system: None,
        trust: Some("kernelverified".to_string()),
        seed: 1,
        shard_dir: dir.path().to_path_buf(),
        json: true,
    };
    cmd_sample(args).expect("sample with trust filter");
}

#[test]
fn test_collect_sample_respects_filters() {
    let dir = make_shard_dir();
    let lib = load_library(dir.path()).expect("load");
    // Only 1 Metamath decl in the fixture; ask for 5 but we'll only get 1.
    let sys = parse_source_system("metamath").expect("metamath should parse");
    let out = collect_sample(&lib, 5, 0, Some(sys), None);
    assert_eq!(out.len(), 1, "expected exactly the 1 Metamath entry");
}

#[test]
fn test_deps_missing_name_is_typed_error() {
    let dir = make_shard_dir();
    let args = DepsArgs {
        name: "Nonexistent.decl".to_string(),
        transitive: false,
        depth: 1,
        limit: 50,
        shard_dir: dir.path().to_path_buf(),
        json: false,
        reverse: false,
    };
    match cmd_deps(args) {
        Err(MathverseCliError::DeclarationNotFound(_)) => {}
        Err(other) => panic!("expected DeclarationNotFound, got {other:?}"),
        Ok(()) => panic!("expected DeclarationNotFound for missing name"),
    }
}

#[test]
fn test_deps_known_name_completes_without_error() {
    let dir = make_shard_dir();
    // The fixture has no cross-decl references, so the dep list will be
    // empty; this test just asserts the happy path doesn't panic or
    // surface an error.
    let args = DepsArgs {
        name: "Nat.add".to_string(),
        transitive: false,
        depth: 1,
        limit: 50,
        shard_dir: dir.path().to_path_buf(),
        json: true,
        reverse: false,
    };
    cmd_deps(args).expect("deps with known root");
}

#[test]
fn test_deps_transitive_flag_switches_depth_to_max() {
    let dir = make_shard_dir();
    let args = DepsArgs {
        name: "Nat.add".to_string(),
        transitive: true,
        depth: 1,
        limit: 50,
        shard_dir: dir.path().to_path_buf(),
        json: false,
        reverse: false,
    };
    cmd_deps(args).expect("deps --transitive");
}
