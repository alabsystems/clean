// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for Lean 4 **module-system** olean import.
//!
//! In the module system a module's public `.olean` stores every public theorem
//! (and any definition whose body lives in the private region) as a value-less,
//! axiom-shaped stub; the proof/body lives in the `.olean.private` companion,
//! whose objects cross-reference the base region. The batch importer must merge
//! those companions (via [`parse_target_module_with_proofs`]) so the shard
//! stores real, kernel-checkable VALUES rather than registering theorems as
//! value-less axioms.
//!
//! Fixture: `tests/fixtures/olean/v4.30.0/module-system/Sigma.{olean,olean.server,
//! olean.private}` — a two-theorem slice of `Mathlib/Data/Finite/Sigma` built by
//! Lean `v4.30.0-rc2` with the module system enabled. Base-only parsing surfaces
//! two value-less `Axiom` stubs; merging the private companion recovers two
//! proof-carrying `Theorem`s.

use std::path::PathBuf;

use clean_olean::module::ConstantKind;
use clean_olean::parse_module_file;

use super::{Lean4BatchConfig, Lean4BatchImporter};
use crate::lean4::olean::olean_bridge::parse_target_module_with_proofs;
use crate::shard::{ShardReader, ShardWriter};
use crate::types::NO_VALUE;

/// Path to the committed module-system fixture's base `.olean`.
fn sigma_fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|root| root.join("tests/fixtures/olean/v4.30.0/module-system/Sigma.olean"))
        .expect("workspace root")
}

#[test]
fn test_module_system_base_only_exposes_value_less_stubs() {
    // The public `.olean`, parsed alone, carries only erased stubs: no value.
    let module = parse_module_file(sigma_fixture()).expect("parse base .olean");
    assert_eq!(module.constants.len(), 2, "fixture exports two constants");
    assert!(
        module.constants.iter().all(|c| c.value.is_none()),
        "module-system base .olean must expose value-less stubs (proofs erased)"
    );
}

#[test]
fn test_module_system_merge_recovers_theorem_proof_values() {
    // Merging the `.olean.private` companion promotes the stubs to their true,
    // proof-carrying `Theorem` records.
    let module = parse_target_module_with_proofs(&sigma_fixture()).expect("merge companions");
    assert_eq!(
        module.constants.len(),
        2,
        "merge preserves the two constants"
    );
    assert!(
        module
            .constants
            .iter()
            .all(|c| c.kind == ConstantKind::Theorem && c.value.is_some()),
        "merging .olean.private must recover theorem proof values, got {:?}",
        module
            .constants
            .iter()
            .map(|c| (c.name.clone(), format!("{:?}", c.kind), c.value.is_some()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_import_file_stores_private_proof_values_in_shard() {
    // End-to-end: the batch importer must route through the proof-merging parse
    // so the erased theorem proofs land in the shard as real values. Guards
    // against a silent revert to the public-only `parse_module_file`.
    let importer = Lean4BatchImporter::new(Lean4BatchConfig::new(PathBuf::from(".")));
    let mut writer = ShardWriter::new();
    importer
        .import_file(&sigma_fixture(), &mut writer)
        .expect("import_file over module-system olean");

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("serialize shard");
    let reader = ShardReader::from_bytes(&buf).expect("read shard back");

    assert_eq!(reader.header.constant_count, 2, "two constants imported");
    let with_value = reader
        .constants
        .iter()
        .filter(|c| c.value_idx != NO_VALUE)
        .count();
    assert_eq!(
        with_value, 2,
        "both theorems must carry a kernel-checkable value after the .olean.private merge"
    );
}
