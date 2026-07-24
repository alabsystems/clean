// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.26 fixture coverage for issue #190.

use clean_kernel::{name::Name, Environment};
use clean_olean::{load_parsed_module, parse_header, parse_module, ConstantKind};
use std::fs;
use std::path::{Path, PathBuf};

fn fixtures_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.26.0")
}

fn read_fixture(relative_path: &str) -> Vec<u8> {
    let path = fixtures_path().join(relative_path);
    fs::read(&path).unwrap_or_else(|e| panic!("Failed to read fixture {}: {}", path.display(), e))
}

#[test]
fn test_parse_string_compat_header_v4_26() {
    let bytes = read_fixture("custom/StringCompat.olean");
    let header = parse_header(&bytes).expect("Failed to parse StringCompat.olean header");

    // Lean 4.26 already uses the v2 .olean header with an embedded Lean version field.
    assert_eq!(header.version, 2);
    assert!(header.base_addr > 0);
}

#[test]
fn test_parse_string_compat_module_v4_26() {
    let bytes = read_fixture("custom/StringCompat.olean");
    let module = parse_module(&bytes).expect("Failed to parse StringCompat.olean");

    let const_names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
    assert!(const_names.contains(&"greeting"));
    assert!(const_names.contains(&"identity"));
    assert!(const_names.contains(&"greeting_eq"));

    let greeting = module
        .constants
        .iter()
        .find(|c| c.name == "greeting")
        .expect("greeting constant not found");
    assert!(matches!(greeting.kind, ConstantKind::Definition));
}

#[test]
fn test_load_string_compat_module_v4_26() {
    let bytes = read_fixture("custom/StringCompat.olean");
    let module = parse_module(&bytes).expect("parse");

    let mut env = Environment::default();
    let summary = load_parsed_module(&mut env, &module, Some("StringCompat".to_string()))
        .expect("load_parsed_module failed");

    assert!(summary.added_constants >= 3);
    assert_eq!(summary.module_name.as_deref(), Some("StringCompat"));
    assert!(
        summary.imports.iter().any(|i| i.contains("Init")),
        "expected Init import, got {:?}",
        summary.imports
    );
    assert!(env.get_const(&Name::from_string("greeting")).is_some());
    assert!(env.get_const(&Name::from_string("greeting_eq")).is_some());
}
