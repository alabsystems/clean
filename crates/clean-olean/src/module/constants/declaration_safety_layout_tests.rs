// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact authority-layout pins for AxiomVal, OpaqueVal, and RecursorVal.
use super::super::{ConstantKind, DefinitionSafety};
use crate::region::{CompactedRegion, ObjectHeader};

fn header(other: u8, cs_sz: u16) -> ObjectHeader {
    ObjectHeader {
        rc: 1,
        cs_sz,
        other,
        tag: 0,
    }
}

fn tagged_bool(value: u64) -> u64 {
    (value << 1) | 1
}

#[test]
fn axiom_real_and_legacy_bool_layouts_decode_exactly() {
    for (raw, expected) in [(0u8, DefinitionSafety::Safe), (1, DefinitionSafety::Unsafe)] {
        let mut real = vec![0u8; 24];
        real[16] = raw;
        assert_eq!(
            CompactedRegion::new(&real, 0)
                .read_definition_safety(&ConstantKind::Axiom, 0, &header(1, 24))
                .expect("real AxiomVal safety"),
            Some(expected)
        );

        let mut legacy = vec![0u8; 24];
        legacy[16..24].copy_from_slice(&tagged_bool(u64::from(raw)).to_le_bytes());
        assert_eq!(
            CompactedRegion::new(&legacy, 0)
                .read_definition_safety(&ConstantKind::Axiom, 0, &header(2, 0))
                .expect("legacy AxiomVal safety"),
            Some(expected)
        );
    }
}

#[test]
fn opaque_real_and_legacy_bool_layouts_decode_exactly() {
    for (raw, expected) in [(0u8, DefinitionSafety::Safe), (1, DefinitionSafety::Unsafe)] {
        let mut real = vec![0u8; 40];
        real[32] = raw;
        assert_eq!(
            CompactedRegion::new(&real, 0)
                .read_definition_safety(&ConstantKind::Opaque, 0, &header(3, 40))
                .expect("real OpaqueVal safety"),
            Some(expected)
        );

        let mut legacy = vec![0u8; 40];
        legacy[24..32].copy_from_slice(&tagged_bool(u64::from(raw)).to_le_bytes());
        assert_eq!(
            CompactedRegion::new(&legacy, 0)
                .read_definition_safety(&ConstantKind::Opaque, 0, &header(4, 0))
                .expect("legacy OpaqueVal safety"),
            Some(expected)
        );
    }
}

#[test]
fn axiom_and_opaque_malformed_authority_fail_closed() {
    let mut invalid_real = vec![0u8; 40];
    invalid_real[16] = 2;
    invalid_real[32] = 2;
    let region = CompactedRegion::new(&invalid_real, 0);
    assert!(region
        .read_definition_safety(&ConstantKind::Axiom, 0, &header(1, 24))
        .is_err());
    assert!(region
        .read_definition_safety(&ConstantKind::Opaque, 0, &header(3, 40))
        .is_err());

    let mut invalid_legacy = vec![0u8; 40];
    invalid_legacy[16..24].copy_from_slice(&tagged_bool(2).to_le_bytes());
    invalid_legacy[24..32].copy_from_slice(&tagged_bool(2).to_le_bytes());
    let region = CompactedRegion::new(&invalid_legacy, 0);
    assert!(region
        .read_definition_safety(&ConstantKind::Axiom, 0, &header(2, 0))
        .is_err());
    assert!(region
        .read_definition_safety(&ConstantKind::Opaque, 0, &header(4, 0))
        .is_err());

    assert!(region
        .read_definition_safety(&ConstantKind::Axiom, 0, &header(1, 16))
        .is_err());
    assert!(region
        .read_definition_safety(&ConstantKind::Opaque, 0, &header(4, 40))
        .is_err());
}

fn write_object_header(bytes: &mut [u8], other: u8, cs_sz: u16) {
    bytes[4..6].copy_from_slice(&cs_sz.to_le_bytes());
    bytes[6] = other;
}

#[test]
fn recursor_real_and_legacy_flags_decode_at_their_exact_offsets() {
    let mut real = vec![0u8; 72];
    write_object_header(&mut real, 7, 72);
    real[64] = 1;
    real[65] = 1;
    assert_eq!(
        CompactedRegion::new(&real, 0)
            .read_recursor_bool_flags(0)
            .expect("real RecursorVal flags"),
        (true, true)
    );

    let mut legacy = vec![0u8; 80];
    write_object_header(&mut legacy, 9, 0);
    legacy[64..72].copy_from_slice(&tagged_bool(1).to_le_bytes());
    legacy[72..80].copy_from_slice(&tagged_bool(1).to_le_bytes());
    assert_eq!(
        CompactedRegion::new(&legacy, 0)
            .read_recursor_bool_flags(0)
            .expect("legacy RecursorVal flags"),
        (true, true)
    );
}

#[test]
fn recursor_wrong_offset_splice_and_invalid_bool_fail_closed() {
    let mut real = vec![0u8; 80];
    write_object_header(&mut real, 7, 72);
    // The historical bug read +72. A true byte spliced there must not
    // influence the real `isUnsafe` byte at +65.
    real[72] = 1;
    assert_eq!(
        CompactedRegion::new(&real, 0)
            .read_recursor_bool_flags(0)
            .expect("real RecursorVal flags"),
        (false, false)
    );
    real[65] = 2;
    assert!(CompactedRegion::new(&real, 0)
        .read_recursor_bool_flags(0)
        .is_err());

    write_object_header(&mut real, 8, 72);
    assert!(CompactedRegion::new(&real, 0)
        .read_recursor_bool_flags(0)
        .is_err());
}
