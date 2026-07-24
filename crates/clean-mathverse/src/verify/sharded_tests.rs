// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the sharded-verify pure helpers (no `.olean` needed).

use super::*;

#[test]
fn test_module_rel_path_basic() {
    assert_eq!(
        module_rel_path("Mathlib.Order.Basic"),
        Some(PathBuf::from("Mathlib/Order/Basic.olean"))
    );
    assert_eq!(module_rel_path("Init"), Some(PathBuf::from("Init.olean")));
}

#[test]
fn test_module_rel_path_rejects_empty() {
    assert_eq!(module_rel_path(""), None);
    assert_eq!(module_rel_path("..."), None);
    assert_eq!(module_rel_path("A..B"), None);
}

#[test]
fn test_module_rel_path_trims_outer_dots() {
    // Leading/trailing dots are stripped, interior empties rejected.
    assert_eq!(
        module_rel_path(".Init.Core."),
        Some(PathBuf::from("Init/Core.olean"))
    );
}

#[test]
fn test_resolve_and_enumerate_roundtrip() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path();
    // Lay out a tiny synthetic olean tree.
    std::fs::create_dir_all(root.join("Mathlib/Order")).expect("mkdir");
    std::fs::create_dir_all(root.join("Mathlib/Algebra/Group")).expect("mkdir");
    std::fs::write(root.join("Mathlib/Order/Basic.olean"), b"x").expect("write");
    std::fs::write(root.join("Mathlib/Algebra/Group/Defs.olean"), b"x").expect("write");
    // A non-olean sibling artifact must be ignored.
    std::fs::write(root.join("Mathlib/Order/Basic.olean.private"), b"x").expect("write");
    std::fs::write(root.join("Mathlib/Order/Basic.ilean"), b"x").expect("write");

    let modules = enumerate_modules(root);
    assert_eq!(
        modules,
        vec![
            "Mathlib.Algebra.Group.Defs".to_string(),
            "Mathlib.Order.Basic".to_string()
        ]
    );

    // Each enumerated module resolves back to its file under the root.
    let paths = vec![root.to_path_buf()];
    for m in &modules {
        let resolved = resolve_module_olean(m, &paths).expect("resolve");
        assert!(
            resolved.exists(),
            "resolved path should exist: {resolved:?}"
        );
    }

    // A module absent from the tree does not resolve.
    assert_eq!(resolve_module_olean("Mathlib.Nope.Missing", &paths), None);
}

#[test]
fn test_verified_rate_excludes_not_found() {
    let result = ModuleVerifyResult {
        module: "M".to_string(),
        counts: ModuleVerifyCounts {
            total: 10,
            kernel_verified: 7,
            axiom_accepted: 2,
            failed: 1,
            not_found: 5, // must NOT enter the denominator
        },
        math: ClassCounts::default(),
        generated: ClassCounts::default(),
        closure_constants: 100,
        kernel_verified_names: vec!["a".into(); 7],
        failures: vec![],
        math_failures: vec![],
        math_sample: vec![],
        generated_sample: vec![],
        elapsed_secs: 0.0,
    };
    // 7 / (7 + 2 + 1) = 70%
    assert!((result.verified_rate() - 70.0).abs() < 1e-9);
}

#[test]
fn test_class_counts_verified_rate() {
    // 8 / (8 + 1 + 1) = 80%
    let c = ClassCounts {
        resolved: 10,
        kernel_verified: 8,
        axiom_accepted: 1,
        failed: 1,
        not_found: 3,
    };
    assert!((c.verified_rate().expect("rate") - 80.0).abs() < 1e-9);

    // No resolved constants of this class -> no rate.
    let empty = ClassCounts::default();
    assert_eq!(empty.verified_rate(), None);
}

#[test]
fn test_to_manifest_count_matches_names() {
    let result = ModuleVerifyResult {
        module: "Mathlib.Order.Basic".to_string(),
        counts: ModuleVerifyCounts {
            total: 4,
            kernel_verified: 2,
            axiom_accepted: 1,
            failed: 1,
            not_found: 0,
        },
        math: ClassCounts::default(),
        generated: ClassCounts::default(),
        closure_constants: 50,
        kernel_verified_names: vec!["x".into(), "y".into()],
        failures: vec![("bad".into(), "boom".into())],
        math_failures: vec![],
        math_sample: vec![],
        generated_sample: vec![],
        elapsed_secs: 0.5,
    };
    let m = result.to_manifest();
    assert_eq!(m.shard_dir, "Mathlib.Order.Basic");
    assert_eq!(m.kernel_verified, 2);
    assert_eq!(m.kernel_verified_names.len(), m.kernel_verified);
    assert_eq!(m.axiom_accepted, 1);
    assert_eq!(m.failed, 1);
    assert_eq!(m.total_constants, 4);
}
