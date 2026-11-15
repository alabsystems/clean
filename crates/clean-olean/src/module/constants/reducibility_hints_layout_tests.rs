// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact dual-layout pins for `ReducibilityHints`.
//!
//! Genuine Lean uses tagged scalars for the two nullary constructors and
//! a 16-byte object with an unboxed `UInt32` for `regular`. Older Clean
//! exports used heap objects with `cs_sz = 0` and a tagged height word.
//! No other shape may silently mint reduction metadata.
use super::super::{ConstantKind, ReducibilityHintsData};
use crate::region::{CompactedRegion, ObjectHeader};

const HINTS_OFFSET: usize = 40;

fn definition_header() -> ObjectHeader {
    ObjectHeader {
        rc: 0,
        cs_sz: 40,
        other: 3,
        tag: 0,
    }
}

fn scalar_hints(tagged_constructor: u64) -> Vec<u8> {
    let mut bytes = vec![0u8; 32];
    bytes[24..32].copy_from_slice(&tagged_constructor.to_le_bytes());
    bytes
}

fn object_hints(tag: u8, other: u8, cs_sz: u16, payload: Option<u64>) -> Vec<u8> {
    let len = if payload.is_some() {
        HINTS_OFFSET + 16
    } else {
        HINTS_OFFSET + 8
    };
    let mut bytes = vec![0u8; len];
    bytes[24..32].copy_from_slice(&(HINTS_OFFSET as u64).to_le_bytes());
    bytes[HINTS_OFFSET + 4..HINTS_OFFSET + 6].copy_from_slice(&cs_sz.to_le_bytes());
    bytes[HINTS_OFFSET + 6] = other;
    bytes[HINTS_OFFSET + 7] = tag;
    if let Some(payload) = payload {
        bytes[HINTS_OFFSET + 8..HINTS_OFFSET + 16].copy_from_slice(&payload.to_le_bytes());
    }
    bytes
}

fn decode(bytes: &[u8]) -> crate::error::OleanResult<Option<ReducibilityHintsData>> {
    CompactedRegion::new(bytes, 0).read_reducibility_hints(
        &ConstantKind::Definition,
        0,
        &definition_header(),
    )
}

#[test]
fn genuine_nullary_scalar_constructors_decode_exactly() {
    assert_eq!(
        decode(&scalar_hints(1)).expect("opaque scalar must decode"),
        Some(ReducibilityHintsData::Opaque)
    );
    assert_eq!(
        decode(&scalar_hints(3)).expect("abbrev scalar must decode"),
        Some(ReducibilityHintsData::Abbrev)
    );
}

#[test]
fn genuine_regular_unboxed_uint32_decodes_without_scalar_shift() {
    let bytes = object_hints(2, 0, 16, Some(17));
    assert_eq!(
        decode(&bytes).expect("real regular object must decode"),
        Some(ReducibilityHintsData::Regular(17))
    );

    // Bytes above the UInt32 are ABI padding, not part of the height.
    let bytes = object_hints(2, 0, 16, Some(0xa5a5_a5a5_0000_0011));
    assert_eq!(
        decode(&bytes).expect("padding must not change the UInt32"),
        Some(ReducibilityHintsData::Regular(17))
    );
}

#[test]
fn exact_legacy_clean_shapes_remain_readable() {
    assert_eq!(
        decode(&object_hints(0, 0, 0, None)).expect("legacy opaque"),
        Some(ReducibilityHintsData::Opaque)
    );
    assert_eq!(
        decode(&object_hints(1, 0, 0, None)).expect("legacy abbrev"),
        Some(ReducibilityHintsData::Abbrev)
    );
    assert_eq!(
        decode(&object_hints(2, 0, 0, Some((17 << 1) | 1))).expect("legacy regular"),
        Some(ReducibilityHintsData::Regular(17))
    );
}

#[test]
fn malformed_or_unknown_hints_fail_closed() {
    let mut missing_field = definition_header();
    missing_field.other = 2;
    assert!(
        CompactedRegion::new(&scalar_hints(1), 0)
            .read_reducibility_hints(&ConstantKind::Definition, 0, &missing_field)
            .is_err(),
        "a definition without reducibility metadata must fail closed"
    );
    assert!(decode(&scalar_hints(5)).is_err(), "tag-2 needs its UInt32");
    assert!(decode(&scalar_hints(0)).is_err(), "null is not a hint");
    assert!(
        decode(&object_hints(7, 0, 8, None)).is_err(),
        "unknown heap constructor must not fabricate Regular(0)"
    );
    assert!(
        decode(&object_hints(2, 1, 16, Some(17))).is_err(),
        "regular has no pointer fields"
    );
    assert!(
        decode(&object_hints(2, 0, 8, Some(17))).is_err(),
        "unknown compact size must fail"
    );
    assert!(
        decode(&object_hints(2, 0, 0, Some(34))).is_err(),
        "legacy height must be a tagged scalar"
    );
    assert!(
        decode(&object_hints(0, 0, 8, None)).is_err(),
        "only the exact legacy heap-nullary shape is accepted"
    );
}

#[test]
fn truncated_regular_payload_fails_closed() {
    let bytes = object_hints(2, 0, 16, None);
    assert!(decode(&bytes).is_err());
}
