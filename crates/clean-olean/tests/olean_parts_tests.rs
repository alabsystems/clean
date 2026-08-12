// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for .olean part discovery and parsing semantics.

use clean_olean::{discover_olean_parts, parse_module_parts, OLeanLevel};
use std::fs;
use std::path::{Path, PathBuf};
use tempfile::tempdir;

fn fixtures_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.13.0")
}

fn read_fixture(relative_path: &str) -> Vec<u8> {
    let path = fixtures_path().join(relative_path);
    fs::read(&path).unwrap_or_else(|e| panic!("Failed to read fixture {}: {}", path.display(), e))
}

#[test]
fn test_discover_olean_parts_requires_base() {
    let bytes = read_fixture("custom/Minimal.olean");
    let dir = tempdir().expect("Failed to create temp dir");
    let base_path = dir.path().join("Test.olean");
    let server_path = base_path.with_extension("olean.server");
    let private_path = base_path.with_extension("olean.private");

    fs::write(&server_path, &bytes).expect("Failed to write server part");
    fs::write(&private_path, &bytes).expect("Failed to write private part");

    let parts = discover_olean_parts(&base_path);
    assert!(parts.is_empty(), "Expected no parts when base is missing");
}

#[test]
fn test_discover_olean_parts_prefix_order() {
    let bytes = read_fixture("custom/Minimal.olean");
    let dir = tempdir().expect("Failed to create temp dir");
    let base_path = dir.path().join("Test.olean");
    let server_path = base_path.with_extension("olean.server");
    let private_path = base_path.with_extension("olean.private");

    // Start with base + private (no server)
    fs::write(&base_path, &bytes).expect("Failed to write base part");
    fs::write(&private_path, &bytes).expect("Failed to write private part");

    let parts = discover_olean_parts(&base_path);
    assert_eq!(parts.len(), 1, "Expected only exported part without server");
    assert_eq!(parts[0].0, OLeanLevel::Exported);
    assert_eq!(parts[0].1, base_path);

    // Remove private to test server-only case
    fs::remove_file(&private_path).expect("Failed to remove private part");
    fs::write(&server_path, &bytes).expect("Failed to write server part");
    let parts = discover_olean_parts(&base_path);
    assert_eq!(parts.len(), 2, "Expected exported + server parts");
    assert_eq!(parts[0].0, OLeanLevel::Exported);
    assert_eq!(parts[1].0, OLeanLevel::Server);

    // Now add private back with server present
    fs::write(&private_path, &bytes).expect("Failed to write private part");
    let parts = discover_olean_parts(&base_path);
    assert_eq!(parts.len(), 3, "Expected exported + server + private parts");
    assert_eq!(parts[0].0, OLeanLevel::Exported);
    assert_eq!(parts[1].0, OLeanLevel::Server);
    assert_eq!(parts[2].0, OLeanLevel::Private);
}

#[test]
fn test_parse_module_parts_ignores_private_without_server() {
    let bytes = read_fixture("custom/Minimal.olean");
    let dir = tempdir().expect("Failed to create temp dir");
    let base_path = dir.path().join("Test.olean");
    let private_path = base_path.with_extension("olean.private");

    fs::write(&base_path, &bytes).expect("Failed to write base part");
    fs::write(&private_path, &bytes).expect("Failed to write private part");

    let parts = parse_module_parts(&base_path).expect("Failed to parse module parts");
    assert_eq!(parts.len(), 1, "Expected only exported part without server");
    assert_eq!(parts[0].level, OLeanLevel::Exported);
}

#[test]
fn test_parse_module_parts_errors_on_invalid_server() {
    let bytes = read_fixture("custom/Minimal.olean");
    let dir = tempdir().expect("Failed to create temp dir");
    let base_path = dir.path().join("Test.olean");
    let server_path = base_path.with_extension("olean.server");

    fs::write(&base_path, &bytes).expect("Failed to write base part");
    fs::write(&server_path, b"bad").expect("Failed to write server part");

    assert!(
        parse_module_parts(&base_path).is_err(),
        "Expected error when server part is invalid"
    );
}

#[test]
fn test_parse_module_parts_errors_on_invalid_private() {
    let bytes = read_fixture("custom/Minimal.olean");
    let dir = tempdir().expect("Failed to create temp dir");
    let base_path = dir.path().join("Test.olean");
    let server_path = base_path.with_extension("olean.server");
    let private_path = base_path.with_extension("olean.private");

    fs::write(&base_path, &bytes).expect("Failed to write base part");
    fs::write(&server_path, &bytes).expect("Failed to write server part");
    fs::write(&private_path, b"bad").expect("Failed to write private part");

    assert!(
        parse_module_parts(&base_path).is_err(),
        "Expected error when private part is invalid"
    );
}

#[test]
fn test_parse_module_parts_with_server_only() {
    let bytes = read_fixture("custom/Minimal.olean");
    let dir = tempdir().expect("Failed to create temp dir");
    let base_path = dir.path().join("Test.olean");
    let server_path = base_path.with_extension("olean.server");

    fs::write(&base_path, &bytes).expect("Failed to write base part");
    fs::write(&server_path, &bytes).expect("Failed to write server part");

    let parts = parse_module_parts(&base_path).expect("Failed to parse module parts");
    assert_eq!(parts.len(), 2, "Expected exported + server parts");
    assert_eq!(parts[0].level, OLeanLevel::Exported);
    assert_eq!(parts[1].level, OLeanLevel::Server);
}

#[test]
fn test_parse_module_parts_rejects_overlapping_private_fixture() {
    let bytes = read_fixture("custom/Minimal.olean");
    let dir = tempdir().expect("Failed to create temp dir");
    let base_path = dir.path().join("Test.olean");
    let server_path = base_path.with_extension("olean.server");
    let private_path = base_path.with_extension("olean.private");

    fs::write(&base_path, &bytes).expect("Failed to write base part");
    fs::write(&server_path, &bytes).expect("Failed to write server part");
    fs::write(&private_path, &bytes).expect("Failed to write private part");

    let err = parse_module_parts(&base_path).expect_err(
        "copied .olean bytes are not a valid private incremental region and must fail closed",
    );
    assert!(
        err.to_string().contains("incremental region overlap"),
        "unexpected error: {err}"
    );
}

/// Path to the committed Lean 4.30 module-system triple's base `.olean`.
fn module_system_fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.30.0/module-system/Sigma.olean")
}

#[test]
fn test_parse_module_parts_module_system_recovers_private_proof_values() {
    // Regression: a real Lean `v4.30.0-rc2` module-system triple. The
    // `.olean.server` and `.olean.private` companions are higher-address
    // incremental regions that cross-reference the base address space, so both
    // must be resolved against the base. Before the fix the standalone `.server`
    // parse failed with `InvalidPointer`, aborting the whole parse.
    let base = module_system_fixture();
    let parts = parse_module_parts(&base).expect("parse all module-system parts");

    let levels: Vec<OLeanLevel> = parts.iter().map(|p| p.level).collect();
    assert_eq!(
        levels,
        vec![
            OLeanLevel::Exported,
            OLeanLevel::Server,
            OLeanLevel::Private
        ],
        "all three module-system levels must parse"
    );

    // The public base exposes only value-less, erased stubs.
    let exported = parts
        .iter()
        .find(|p| p.level == OLeanLevel::Exported)
        .expect("exported part");
    assert!(
        exported.module.constants.iter().all(|c| c.value.is_none()),
        "module-system base .olean stubs must be value-less"
    );

    // The private companion carries the real proof values.
    let private = parts
        .iter()
        .find(|p| p.level == OLeanLevel::Private)
        .expect("private part");
    assert!(
        !private.module.constants.is_empty()
            && private.module.constants.iter().any(|c| c.value.is_some()),
        "private companion must recover proof-carrying values"
    );
}
