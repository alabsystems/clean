// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dual-layout `read_definition_safety` pins (census 2026-07-06 Class 3).
//!
//! Real Lean 4 `DefnVal`s (v4.30.0-rc2 `Declaration.lean:120-131`) carry
//! `all : List Name` as the fourth BOXED field (+32) and `safety` as an
//! UNBOXED u8 at +40, with Lean's on-disk tag order `| «unsafe» | safe |
//! «partial»` (`Declaration.lean:116-118`): 0=unsafe, 1=safe, 2=partial.
//! Clean's own exporter writes a legacy layout instead: a BOXED safety
//! scalar at +32 in Clean's tag order (safe=0). Both exact layouts decode;
//! every unknown shape or tag is rejected rather than gaining safe
//! definitional authority.
use super::super::{ConstantKind, DefinitionSafety};
use crate::region::{CompactedRegion, ObjectHeader};

/// Build a synthetic 48-byte real-Lean `DefnVal` object at offset 0:
/// header (ignored — passed separately), 4 boxed fields, then the
/// trailing scalar area whose first byte is `safety`.
fn real_lean_defn_val(safety_byte: u8) -> Vec<u8> {
    let mut b = vec![0u8; 48];
    // +8 toConstantVal, +16 value, +24 hints, +32 all — plausible even,
    // non-null pointers (never dereferenced by the safety reader).
    for (i, off) in [8usize, 16, 24, 32].iter().enumerate() {
        let fake_ptr = 0x1000u64 + (i as u64) * 0x100;
        b[*off..*off + 8].copy_from_slice(&fake_ptr.to_le_bytes());
    }
    b[40] = safety_byte;
    b
}

fn real_lean_header() -> ObjectHeader {
    // Exact header shape probed on every v4.30 DefnVal (212/212).
    ObjectHeader {
        rc: 1,
        cs_sz: 48,
        other: 4,
        tag: 0,
    }
}

fn decode(
    bytes: &[u8],
    header: &ObjectHeader,
) -> crate::error::OleanResult<Option<DefinitionSafety>> {
    let region = CompactedRegion::new(bytes, 0);
    region.read_definition_safety(&ConstantKind::Definition, 0, header)
}

#[test]
fn test_real_lean_layout_tag_order_unsafe_safe_partial() {
    // Lean's on-disk order (Declaration.lean:116-118): 0=unsafe, 1=safe,
    // 2=partial. E.g. `ptrEqList` (unsafe def) stores 0; a `._unsafe_rec`
    // twin (partial) stores 2.
    assert_eq!(
        decode(&real_lean_defn_val(0), &real_lean_header()).expect("real unsafe"),
        Some(DefinitionSafety::Unsafe),
        "on-disk 0 must decode as unsafe (Lean declaration order)"
    );
    assert_eq!(
        decode(&real_lean_defn_val(1), &real_lean_header()).expect("real safe"),
        Some(DefinitionSafety::Safe),
        "on-disk 1 must decode as safe"
    );
    assert_eq!(
        decode(&real_lean_defn_val(2), &real_lean_header()).expect("real partial"),
        Some(DefinitionSafety::Partial),
        "on-disk 2 must decode as partial"
    );
    assert!(
        decode(&real_lean_defn_val(3), &real_lean_header()).is_err(),
        "an unknown on-disk tag must fail closed"
    );
}

#[test]
fn test_real_lean_layout_requires_probed_header_shape() {
    // A header that matches neither known layout (e.g. a hypothetical
    // 5-boxed-field future DefnVal) must fail instead of misreading a byte.
    let bytes = real_lean_defn_val(0);
    let five_fields = ObjectHeader {
        rc: 1,
        cs_sz: 56,
        other: 5,
        tag: 0,
    };
    assert!(
        decode(&bytes, &five_fields).is_err(),
        "unknown header shape must fail closed"
    );

    let missing_safety = ObjectHeader {
        rc: 1,
        cs_sz: 32,
        other: 3,
        tag: 0,
    };
    assert!(
        decode(&bytes, &missing_safety).is_err(),
        "a DefinitionVal without safety metadata must fail closed"
    );
}

#[test]
fn test_real_layout_all_nil_is_not_misclassified_as_legacy_safety() {
    // `all : List Name` is a boxed field, but `List.nil` itself is the
    // tagged scalar 1. Header-first discrimination must still read the
    // real safety byte at +40.
    let mut bytes = real_lean_defn_val(2);
    bytes[32..40].copy_from_slice(&1u64.to_le_bytes());
    assert_eq!(
        decode(&bytes, &real_lean_header()).expect("real all=nil layout"),
        Some(DefinitionSafety::Partial)
    );
}

#[test]
fn test_legacy_clean_exporter_layout_boxed_scalar_at_32() {
    // Clean's exporter layout: boxed scalar `(tag << 1) | 1` at +32 in
    // Clean's tag order (safe=0, unsafe=1, partial=2). The full
    // exporter round-trip is pinned separately in `export/tests.rs`;
    // this pins the reader branch in isolation.
    for (tag, expected) in [
        (0u64, DefinitionSafety::Safe),
        (1, DefinitionSafety::Unsafe),
        (2, DefinitionSafety::Partial),
    ] {
        let mut b = vec![0u8; 48];
        let boxed = (tag << 1) | 1;
        b[32..40].copy_from_slice(&boxed.to_le_bytes());
        assert_eq!(
            decode(
                &b,
                &ObjectHeader {
                    rc: 1,
                    cs_sz: 0,
                    other: 4,
                    tag: 0,
                },
            )
            .expect("legacy safety"),
            Some(expected),
            "legacy boxed scalar tag {tag} must decode in historical order"
        );
    }
}

#[test]
fn test_legacy_unknown_or_non_scalar_safety_fails_closed() {
    let header = ObjectHeader {
        rc: 1,
        cs_sz: 0,
        other: 4,
        tag: 0,
    };
    let mut unknown = vec![0u8; 48];
    unknown[32..40].copy_from_slice(&((7u64 << 1) | 1).to_le_bytes());
    assert!(decode(&unknown, &header).is_err());

    let mut pointer = vec![0u8; 48];
    pointer[32..40].copy_from_slice(&0x1000u64.to_le_bytes());
    assert!(decode(&pointer, &header).is_err());
}
