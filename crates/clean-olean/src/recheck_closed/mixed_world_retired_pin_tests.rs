// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Actual retired rows through the unchanged production binding decision.
//! Capture extraction/provenance belongs to the SHA-bound fixture producer;
//! this test does not mint pins, import a new world, or replace a kernel replay.

use super::super::extension_binding::{
    check_binding, encode_hex, BindingVerdict, ExtensionBindings,
};
use super::super::extension_binding_pins::PINNED_WORLDS;
use clean_kernel::Name;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

const FIXTURE: &str = include_str!(
    "../../../../reports/2026-11-14-extension-binding-not-review/retired_mixed_pins.json"
);
const PROVENANCE: &str = include_str!("../../../../reports/2026-11-14-extension-binding-not-review/retired_mixed_pins.provenance.json");
const PRODUCER: &str = include_str!(
    "../../../../reports/2026-11-14-extension-binding-not-review/mint_retired_mixed_pins.py"
);
const WORLD: &str = "clean-import+lean-v4.30.0-rc2-core";
const OLD_CAPTURE: &str = "b13b432c61feaf3e8d2b62b8630947c07925a9f0eda59ca39d0720011cfcd1ea";
const CURRENT_CAPTURE: &str = "84cf3329f44981eb1ffb41e23e645912c4deab8d26da1cd2257ea19a8ed34e89";
const KEYS: [&str; 11] = [
    "Char.ofNat",
    "Nat.div",
    "Nat.gcd",
    "Nat.land",
    "Nat.lor",
    "Nat.mod",
    "Nat.shiftRight",
    "Nat.xor",
    "String",
    "String.ofList",
    "autoParam",
];

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Row {
    name: String,
    old_digest: String,
    current_digest: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    schema: String,
    world: String,
    lean_toolchain: String,
    old_capture_sha256: String,
    current_capture_sha256: String,
    rows: Vec<Row>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Provenance {
    schema: String,
    fixture_sha256: String,
    producer_sha256: String,
    old_capture_sha256: String,
    current_capture_sha256: String,
    changed_keys: Vec<String>,
    old_table_rows: BTreeMap<String, String>,
    current_root_rows: BTreeMap<String, String>,
    old_row_source: String,
    proof_credit: bool,
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn digest(hex: &str) -> [u8; 32] {
    assert!(
        hex.len() == 64
            && hex
                .bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)),
        "exact lowercase SHA256 digest"
    );
    let mut bytes = [0; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte =
            u8::from_str_radix(&hex[2 * index..2 * index + 2], 16).expect("validated digest byte");
    }
    bytes
}

fn refuses(bindings: &ExtensionBindings, row: &Row, actual: &[u8; 32], label: &str) {
    match check_binding(bindings, &Name::from_string(&row.name), actual) {
        BindingVerdict::Bound => panic!("{label} {} unexpectedly bound", row.name),
        BindingVerdict::Mismatch { expected, found } => {
            assert_eq!(
                found,
                encode_hex(actual),
                "production refusal records actual input"
            );
            let expected = expected.expect("current production row must be present");
            assert!(
                expected.contains(&format!("{WORLD}: {}", row.current_digest)),
                "production refusal must name the actual current mixed row: {expected}"
            );
        }
    }
}

#[test]
fn retired_mixed_world_pins_are_refused_by_production_binding_gate() {
    let fixture: Fixture =
        serde_json::from_str(FIXTURE).expect("strict actual retired-pin fixture");
    let provenance: Provenance =
        serde_json::from_str(PROVENANCE).expect("strict extraction provenance");
    assert_eq!(fixture.schema, "mixed-world-retired-pins/v1");
    assert_eq!(fixture.world, WORLD);
    assert_eq!(fixture.lean_toolchain, "leanprover/lean4:v4.30.0-rc2");
    assert_eq!(fixture.old_capture_sha256, OLD_CAPTURE);
    assert_eq!(fixture.current_capture_sha256, CURRENT_CAPTURE);
    assert_eq!(provenance.schema, "mixed-world-retired-pin-provenance/v1");
    assert_eq!(provenance.fixture_sha256, sha256(FIXTURE.as_bytes()));
    assert_eq!(provenance.producer_sha256, sha256(PRODUCER.as_bytes()));
    assert_eq!(provenance.old_capture_sha256, OLD_CAPTURE);
    assert_eq!(provenance.current_capture_sha256, CURRENT_CAPTURE);
    assert_eq!(
        provenance.old_row_source,
        "expected_worlds[world], independently matched to minted and roots/units"
    );
    assert!(!provenance.proof_credit);
    let keys: BTreeSet<_> = KEYS.into_iter().map(str::to_owned).collect();
    assert_eq!(fixture.rows.len(), 11);
    assert_eq!(
        fixture
            .rows
            .iter()
            .map(|row| row.name.clone())
            .collect::<BTreeSet<_>>(),
        keys
    );
    assert_eq!(provenance.changed_keys.len(), 11);
    assert_eq!(
        provenance.changed_keys.into_iter().collect::<BTreeSet<_>>(),
        keys
    );
    assert_eq!(
        provenance
            .old_table_rows
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>(),
        keys
    );
    assert_eq!(
        provenance
            .current_root_rows
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>(),
        keys
    );
    let worlds: Vec<_> = PINNED_WORLDS
        .iter()
        .filter(|world| world.label == WORLD)
        .collect();
    assert_eq!(worlds.len(), 1);
    let current: BTreeMap<_, _> = worlds[0].rows.iter().copied().collect();
    assert_eq!(
        current.len(),
        worlds[0].rows.len(),
        "unique production world keys"
    );
    let bindings = ExtensionBindings::pinned();
    assert!(bindings.is_pinned(), "exercise actual production pin union");
    for row in &fixture.rows {
        assert_eq!(
            current.get(row.name.as_str()),
            Some(&row.current_digest.as_str())
        );
        assert_eq!(provenance.old_table_rows[&row.name], row.old_digest);
        assert_eq!(provenance.current_root_rows[&row.name], row.current_digest);
        let old = digest(&row.old_digest);
        let accepted = digest(&row.current_digest);
        assert_ne!(old, accepted, "a retired row must actually have changed");
        assert!(
            matches!(
                check_binding(&bindings, &Name::from_string(&row.name), &accepted),
                BindingVerdict::Bound
            ),
            "actual current {} row must bind",
            row.name
        );
        refuses(&bindings, row, &old, "actual retired");
        let mut wrong_bit = accepted;
        wrong_bit[0] ^= 1;
        refuses(&bindings, row, &wrong_bit, "one-bit current mutation");
    }
    eprintln!(
        "retired-mixed-pins production current-bound=11 actual-old-mismatch=11 one-bit-mismatch=11"
    );
}
