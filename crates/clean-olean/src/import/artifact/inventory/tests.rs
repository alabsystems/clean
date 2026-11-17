//! These are fabricated structural/byte adversaries, not producer admission.

use super::*;
use crate::payload::CleanPayload;
use clean_kernel::{ConstantInfo, Expr, Level};

fn empty_bytes() -> Vec<u8> {
    let base = 0x1000u64;
    let mut bytes = vec![0; 200];
    bytes[..5].copy_from_slice(b"olean");
    bytes[5] = 1;
    bytes[6..46].copy_from_slice(b"0000000000000000000000000000000000000000");
    bytes[48..56].copy_from_slice(&base.to_le_bytes());
    bytes[56..64].copy_from_slice(&(base + 88).to_le_bytes());
    bytes[71] = crate::region::tags::ARRAY;
    bytes[94] = 5;
    for field in 0..5 {
        let offset = 96 + field * 8;
        bytes[offset..offset + 8].copy_from_slice(&(base + 64).to_le_bytes());
    }
    bytes
}
fn parse(bytes: Vec<u8>) -> LoadModule {
    crate::import::load_parse::parse_load_module(bytes).unwrap()
}
fn empty() -> LoadModule {
    parse(empty_bytes())
}
fn constant(name: Name) -> ConstantInfo {
    ConstantInfo::new(name, vec![], Expr::sort(Level::zero()), None, false)
}
fn raw_fixture() -> LoadModule {
    parse(
        std::fs::read(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/olean/v4.30.0/closure_cache/Init.olean"),
        )
        .unwrap(),
    )
}

#[test]
fn fabricated_inventory_valid_empty_differs_from_compatibility_malformed_arrays() {
    assert!(build(&empty(), ArtifactInventoryLimits::default())
        .unwrap()
        .declarations()
        .is_empty());
    for field in [1, 2] {
        for bad_pointer in [1u64, 0x1000 + 88] {
            // scalar or wrong object tag
            let mut bytes = empty_bytes();
            let offset = 96 + field * 8;
            bytes[offset..offset + 8].copy_from_slice(&bad_pointer.to_le_bytes());
            let module = parse(bytes);
            assert!(
                module.constants.is_empty(),
                "legacy load still projects an empty array"
            );
            assert!(matches!(
                build(&module, ArtifactInventoryLimits::default()),
                Err(ArtifactInventoryError::MalformedArrays)
            ));
        }
    }
}

#[test]
fn fabricated_inventory_structural_names_payload_only_and_both_origin_are_distinct() {
    let mut module = empty();
    let names = [
        Name::anon().str("a.b"),
        Name::anon().str("a").str("b"),
        Name::anon().str("1"),
        Name::anon().num(1),
    ];
    module.clean_payload = Some(CleanPayload {
        constants: names.iter().cloned().map(constant).collect(),
        ..Default::default()
    });
    let inventory = build(&module, ArtifactInventoryLimits::default()).unwrap();
    assert_eq!(inventory.declarations().len(), 4);
    assert!(inventory
        .declarations()
        .iter()
        .all(|d| d.origin() == ArtifactDeclarationOrigin::CleanPayload));
    for name in names {
        assert!(inventory.declarations().iter().any(|d| d.name() == &name));
    }
    let mut raw = raw_fixture();
    let first = raw.constants.first().unwrap().kernel_name.clone();
    raw.clean_payload = Some(CleanPayload {
        constants: vec![constant(first.clone())],
        ..Default::default()
    });
    let inventory = build(&raw, ArtifactInventoryLimits::default()).unwrap();
    assert_eq!(
        inventory
            .declarations()
            .iter()
            .find(|d| d.name() == &first)
            .unwrap()
            .origin(),
        ArtifactDeclarationOrigin::Both
    );
    assert_eq!(inventory.occurrences(), raw.constants.len() + 1);
}

#[test]
fn fabricated_inventory_duplicate_payload_raw_and_header_mismatch_never_return_prefixes() {
    let mut module = empty();
    let name = Name::from_string("duplicate");
    module.clean_payload = Some(CleanPayload {
        constants: vec![constant(name.clone()), constant(name)],
        ..Default::default()
    });
    assert!(matches!(
        build(&module, ArtifactInventoryLimits::default()),
        Err(ArtifactInventoryError::DuplicateDeclaration)
    ));
    let mut raw = raw_fixture();
    assert!(raw.constants.len() > 1);
    raw.constants[1].kernel_name = raw.constants[0].kernel_name.clone();
    assert!(matches!(
        build(&raw, ArtifactInventoryLimits::default()),
        Err(ArtifactInventoryError::DuplicateDeclaration)
    ));
    let mut raw = raw_fixture();
    raw.const_names.pop();
    assert!(matches!(
        build(&raw, ArtifactInventoryLimits::default()),
        Err(ArtifactInventoryError::NameRecordMismatch)
    ));
    let mut raw = raw_fixture();
    raw.const_names[0] = Name::from_string("notInRawRecords");
    assert!(matches!(
        build(&raw, ArtifactInventoryLimits::default()),
        Err(ArtifactInventoryError::NameRecordMismatch)
    ));
}

#[test]
fn fabricated_inventory_bounds_expanded_names_before_clone_collection_and_comparison() {
    assert!(ArtifactInventoryLimits::new(0, 1).is_err());
    assert!(ArtifactInventoryLimits::new(1, 0).is_err());
    let raw = raw_fixture();
    assert!(matches!(
        build(&raw, ArtifactInventoryLimits::new(1, 1_000_000).unwrap()),
        Err(ArtifactInventoryError::DeclarationLimit)
    ));
    assert!(matches!(
        build(&raw, ArtifactInventoryLimits::new(100_000, 1).unwrap()),
        Err(ArtifactInventoryError::StructuralLimit)
    ));
    let mut module = empty();
    let mut name = Name::anon();
    for _ in 0..100 {
        name = name.str("deep");
    }
    module.clean_payload = Some(CleanPayload {
        constants: vec![constant(name)],
        ..Default::default()
    });
    assert!(matches!(
        build(&module, ArtifactInventoryLimits::new(10, 100).unwrap()),
        Err(ArtifactInventoryError::StructuralLimit)
    ));
    let inventory = build(&module, ArtifactInventoryLimits::default()).unwrap();
    assert!(matches!(
        inventory.check_limits(ArtifactInventoryLimits::new(10, 100).unwrap()),
        Err(ArtifactInventoryError::StructuralLimit)
    ));
    assert!(inventory
        .check_limits(ArtifactInventoryLimits::default())
        .is_ok());
}
