// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused assertions for the float chains' unsealed three-build evidence.

use super::fixture;

/// Require the reproduction stanza that the add/sub/mul lineage records carry.
///
/// This is deliberately separate from the sealed-driver A0/A6 helper: the
/// records prove three byte-identical clean builds, but all three use one
/// unsealed local-stage1 producer and carry no negative control. Reusing the
/// sealed helper would overstate that provenance; omitting this helper was the
/// opposite bug and let active docs falsely deny that reproduction existed.
fn assert_three_clean_build_reproduction(ev: &serde_json::Value) {
    assert!(
        ev["build"]["provenance_strength"]
            .as_str()
            .is_some_and(|s| s.contains("THREE clean non-incremental builds")
                && s.contains("unsealed local stage1")),
        "the evidence must state its actual provenance: three clean builds of one unsealed driver"
    );
    let reproduction = &ev["reproduction"];
    assert_eq!(
        reproduction["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true),
        "the evidence carries a three-build reproduction stanza; denying that stanza was a stale \
         documentation claim"
    );
    let hashes = ["sha256_run1", "sha256_run2", "sha256_run3"].map(|key| {
        reproduction[key]
            .as_str()
            .unwrap_or_else(|| panic!("reproduction.{key} must be recorded"))
    });
    assert!(
        !hashes[0].is_empty() && hashes.iter().all(|hash| *hash == hashes[0]),
        "all three clean-build coverage digests must be present and identical: {hashes:?}"
    );
    assert!(
        reproduction["protocol"]
            .as_str()
            .is_some_and(|s| s.contains("three clean non-incremental builds")),
        "the reproduction protocol must name the three clean non-incremental builds"
    );
}

/// Add, subtract, and multiply share one reproduction protocol. Pin every
/// record so a truthful assertion on one cannot mask stale claims on its peers.
#[test]
fn float_add_sub_mul_pin_their_three_clean_build_reproduction() {
    for name in [
        "float_add.lineage.json",
        "float_sub.lineage.json",
        "float_mul.lineage.json",
    ] {
        let evidence: serde_json::Value = serde_json::from_str(&fixture(name))
            .unwrap_or_else(|error| panic!("{name} must be valid JSON: {error}"));
        assert_three_clean_build_reproduction(&evidence);
    }
}
