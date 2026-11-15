// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Regression: `read_name_at` memoizes each `Name` object by file offset, so
/// a `Name` shared as the PARENT of several children is decoded exactly once.
/// This is the fix for the `Init` pre-load hot path, where every `Expr::const`
/// re-resolved the same deep names from raw bytes. The test asserts both
/// correctness (identical dotted strings) and that the shared parent lands in
/// the cache after the first child is read.
#[test]
fn test_read_name_at_memoizes_shared_parent() {
    // base_addr = 0 ⇒ pointer value == file offset. Objects are 8-byte
    // aligned so every offset is even and non-zero (a valid `is_ptr`).
    fn push_string(buf: &mut Vec<u8>, s: &str) -> u64 {
        while !buf.len().is_multiple_of(8) {
            buf.push(0);
        }
        let off = buf.len() as u64;
        // header: rc(4)=0, cs_sz(2)=0, other(1)=0, tag(1)=STRING
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.push(0);
        buf.push(tags::STRING);
        let m_size = (s.len() + 1) as u64; // includes null terminator
        buf.extend_from_slice(&m_size.to_le_bytes()); // m_size
        buf.extend_from_slice(&m_size.to_le_bytes()); // m_capacity
        buf.extend_from_slice(&(s.len() as u64).to_le_bytes()); // m_length
        buf.extend_from_slice(s.as_bytes());
        buf.push(0); // null terminator
        off
    }
    fn push_name_str(buf: &mut Vec<u8>, parent_ptr: u64, string_ptr: u64) -> u64 {
        while !buf.len().is_multiple_of(8) {
            buf.push(0);
        }
        let off = buf.len() as u64;
        // header: rc=0, cs_sz=0, other=2 (2 fields), tag=1 (Name.str)
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.push(2);
        buf.push(1);
        buf.extend_from_slice(&parent_ptr.to_le_bytes());
        buf.extend_from_slice(&string_ptr.to_le_bytes());
        off
    }

    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(&[0u8; 8]); // reserve offset 0 as the null slot

    let s_nat = push_string(&mut buf, "Nat");
    let s_succ = push_string(&mut buf, "succ");
    let s_add = push_string(&mut buf, "add");
    const ANON: u64 = 1; // scalar-boxed Name.anonymous
    let n_nat = push_name_str(&mut buf, ANON, s_nat);
    let n_succ = push_name_str(&mut buf, n_nat, s_succ);
    let n_add = push_name_str(&mut buf, n_nat, s_add);

    let region = CompactedRegion::new(&buf, 0);
    assert!(region.name_cache.borrow().is_empty(), "cache starts empty");

    // Reading a child decodes and caches BOTH the child and its parent.
    assert_eq!(region.read_name_at(n_succ as usize).unwrap(), "Nat.succ");
    assert!(
        region.name_cache.borrow().contains_key(&(n_nat as usize)),
        "shared parent `Nat` cached after first child read"
    );
    assert!(region.name_cache.borrow().contains_key(&(n_succ as usize)));

    // A sibling reuses the cached parent yet yields its own distinct name.
    assert_eq!(region.read_name_at(n_add as usize).unwrap(), "Nat.add");
    assert_eq!(region.read_name_at(n_nat as usize).unwrap(), "Nat");

    // Idempotent: a repeat read hits the cache and is byte-identical.
    assert_eq!(region.read_name_at(n_succ as usize).unwrap(), "Nat.succ");
    assert_eq!(region.read_name_at(n_add as usize).unwrap(), "Nat.add");
}

#[test]
fn test_object_header_parse() {
    // Construct a constructor object header
    // rc=0, cs_sz=0x20, other=2 (2 fields), tag=0 (first constructor)
    let bytes = [
        0, 0, 0, 0, // rc = 0
        0x20, 0, // cs_sz = 0x20
        2, // other = 2
        0, // tag = 0
    ];

    let header = ObjectHeader::parse(&bytes).unwrap();
    assert_eq!(header.rc, 0);
    assert_eq!(header.cs_sz, 0x20);
    assert_eq!(header.other, 2);
    assert_eq!(header.tag, 0);
    assert!(header.is_constructor());
    assert_eq!(header.num_fields(), 2);
}

#[test]
fn test_object_header_string() {
    // String object header
    let bytes = [
        0,
        0,
        0,
        0, // rc = 0
        0,
        0,            // cs_sz = 0
        5,            // other = 5 (length?)
        tags::STRING, // tag = STRING
    ];

    let header = ObjectHeader::parse(&bytes).unwrap();
    assert_eq!(header.tag, tags::STRING);
    assert!(!header.is_constructor());
    assert!(header.is_scalar());
}

/// Verify ObjectHeader::parse returns OutOfBounds error when slice is too short
#[test]
fn test_object_header_parse_short_slice() {
    let bytes = [0u8; OBJECT_HEADER_SIZE - 1];
    let err = ObjectHeader::parse(&bytes).unwrap_err();
    assert!(matches!(
        err,
        OleanError::OutOfBounds {
            offset: 0,
            size
        } if size == bytes.len()
    ));
}

/// Verify num_fields() returns 0 for non-constructor objects regardless of `other` field
#[test]
fn test_object_header_num_fields_non_constructor() {
    // Non-constructor with other=9 should still return num_fields=0
    let bytes = [
        0,
        0,
        0,
        0, // rc = 0
        0,
        0,            // cs_sz = 0
        9,            // other = 9 (ignored for non-constructors)
        tags::STRING, // tag = STRING (non-constructor tag)
    ];

    let header = ObjectHeader::parse(&bytes).unwrap();
    assert!(!header.is_constructor());
    assert_eq!(header.num_fields(), 0);
}

/// Verify is_scalar and is_ptr correctly categorize pointer values by LSB
#[test]
fn test_scalar_detection() {
    // Scalar values have LSB = 1
    assert!(is_scalar(1)); // boxed 0 (Name.anonymous)
    assert!(is_scalar(3)); // boxed 1
    assert!(is_scalar(0xFF)); // odd number

    // Pointers have LSB = 0 (and non-zero)
    assert!(is_ptr(0x0010_0000));
    assert!(is_ptr(2));

    // Zero is neither scalar nor valid pointer
    assert!(!is_scalar(0));
    assert!(!is_ptr(0));
}

/// Verify is_scalar and is_ptr are mutually exclusive for all pointer values
#[test]
fn test_scalar_ptr_exclusivity() {
    // No value can be both scalar AND pointer (mutually exclusive)
    let samples = [0u64, 1, 2, 3, 4, 5, 0x10, 0x11];
    for &ptr in &samples {
        assert!(
            !(is_scalar(ptr) && is_ptr(ptr)),
            "ptr={} should not be both scalar and pointer",
            ptr
        );
    }

    // Verify specific categorizations
    assert!(is_scalar(1)); // odd number = scalar
    assert!(is_ptr(2)); // even non-zero = pointer
}

#[test]
fn test_unbox_scalar() {
    assert_eq!(unbox_scalar(1), 0);
    assert_eq!(unbox_scalar(3), 1);
    assert_eq!(unbox_scalar(5), 2);
    assert_eq!(unbox_scalar(201), 100);
}

#[test]
fn test_compacted_region_string() {
    // Create a mock .olean file structure with a string
    let base_addr = 0x1000u64;

    // We need at least 64 bytes header + object
    let mut data = vec![0u8; 128];

    // String object at offset 64 (first object after header)
    let str_offset = 64;
    // Header
    data[str_offset..str_offset + 4].copy_from_slice(&0i32.to_le_bytes()); // rc
    data[str_offset + 4..str_offset + 6].copy_from_slice(&0u16.to_le_bytes()); // cs_sz
    data[str_offset + 6] = 0; // other
    data[str_offset + 7] = tags::STRING;
    // m_size = 6 (5 chars + null)
    data[str_offset + 8..str_offset + 16].copy_from_slice(&6u64.to_le_bytes());
    // m_capacity = 6
    data[str_offset + 16..str_offset + 24].copy_from_slice(&6u64.to_le_bytes());
    // m_length = 5
    data[str_offset + 24..str_offset + 32].copy_from_slice(&5u64.to_le_bytes());
    // String data "hello\0"
    data[str_offset + 32..str_offset + 38].copy_from_slice(b"hello\0");

    let region = CompactedRegion::new(&data, base_addr);
    let s = region.read_lean_string_at(str_offset).unwrap();
    assert_eq!(s, "hello");
}

/// Verify ptr_to_offset validates pointers against region bounds and scalar tagging
#[test]
fn test_ptr_to_offset() {
    let base_addr = 0x0010_0000_u64;
    let data = vec![0u8; 100];
    let region = CompactedRegion::new(&data, base_addr);

    // Null pointer
    assert_eq!(region.ptr_to_offset(0).unwrap(), 0);

    // Valid pointer
    assert_eq!(region.ptr_to_offset(base_addr + 50).unwrap(), 50);

    // Base address points at offset 0
    assert_eq!(region.ptr_to_offset(base_addr).unwrap(), 0);

    // Tagged pointer inside the region should still be rejected
    assert!(
        matches!(
            region.ptr_to_offset(base_addr + 1),
            Err(OleanError::InvalidPointer { .. })
        ),
        "tagged pointer should produce InvalidPointer"
    );

    // Pointer before base is invalid
    assert!(
        matches!(
            region.ptr_to_offset(base_addr - 1),
            Err(OleanError::InvalidPointer { .. })
        ),
        "pointer before base should produce InvalidPointer"
    );

    // Pointer beyond region is invalid
    assert!(
        matches!(
            region.ptr_to_offset(base_addr + 200),
            Err(OleanError::InvalidPointer { .. })
        ),
        "pointer beyond region should produce InvalidPointer"
    );

    // Scalar values are not valid pointers
    assert!(
        matches!(
            region.ptr_to_offset(1),
            Err(OleanError::InvalidPointer { .. })
        ),
        "scalar 1 (boxed 0) should produce InvalidPointer"
    );
    assert!(
        matches!(
            region.ptr_to_offset(3),
            Err(OleanError::InvalidPointer { .. })
        ),
        "scalar 3 (boxed 1) should produce InvalidPointer"
    );
}

/// Verify ptr_to_offset rejects pointer exactly at end of region (off-by-one boundary)
#[test]
fn test_ptr_to_offset_end_boundary() {
    let base_addr = 0x0100_0000_u64;
    let data = vec![0u8; 64];
    let region = CompactedRegion::new(&data, base_addr);
    // Pointer at exactly base_addr + data.len() is invalid (one past end)
    let ptr = base_addr + data.len() as u64;
    let err = region.ptr_to_offset(ptr).unwrap_err();
    assert!(matches!(
        err,
        OleanError::InvalidPointer { ptr: err_ptr, offset }
            if err_ptr == ptr && offset == data.len()
    ));
}

/// Verify offset_to_ptr and ptr_to_offset are inverses for valid offsets
#[test]
fn test_offset_to_ptr_roundtrip() {
    let base_addr = 0x2000_u64;
    let data = vec![0u8; 32];
    let region = CompactedRegion::new(&data, base_addr);
    // Test roundtrip at start, middle, and end of valid range.
    // Use only even offsets since odd addresses are scalar-tagged in Lean's compacted region.
    // Calculate max_even dynamically in case data size changes.
    let max_even = (data.len() - 1) & !1; // Largest even offset within bounds
    for offset in [0usize, 12usize, max_even] {
        let ptr = region.offset_to_ptr(offset);
        assert_eq!(ptr, base_addr + offset as u64);
        assert_eq!(region.ptr_to_offset(ptr).unwrap(), offset);
    }
}

/// Verify odd pointers are rejected as scalars.
///
/// In Lean's runtime, odd addresses (ptr & 1 == 1) represent unboxed scalars,
/// not heap pointers. The actual value is (ptr >> 1). This test ensures
/// ptr_to_offset correctly rejects these as InvalidPointer.
#[test]
fn test_odd_ptr_rejected_as_scalar() {
    let base_addr = 0x2000_u64;
    let data = vec![0u8; 32];
    let region = CompactedRegion::new(&data, base_addr);
    // Test multiple odd offsets: near start, middle, and near end of range
    for odd_offset in [1usize, 15usize, 31usize] {
        let odd_ptr = base_addr + odd_offset as u64;
        let result = region.ptr_to_offset(odd_ptr);
        assert!(
            result.is_err(),
            "Odd pointer 0x{:x} (offset {}) should be rejected as scalar-tagged",
            odd_ptr,
            odd_offset
        );
    }
}

/// Verify read_lean_string_at returns OutOfBounds when m_size exceeds available data
#[test]
fn test_read_lean_string_at_length_mismatch() {
    let base_addr = 0x1000u64;
    let mut data = vec![0u8; 96]; // Only 96 bytes total
    let str_offset = 64;

    // Build string header at offset 64
    data[str_offset..str_offset + 4].copy_from_slice(&0i32.to_le_bytes()); // rc
    data[str_offset + 4..str_offset + 6].copy_from_slice(&0u16.to_le_bytes()); // cs_sz
    data[str_offset + 6] = 0; // other
    data[str_offset + 7] = tags::STRING; // tag
                                         // m_size = 20 (string data would need 20 bytes at offset 64+32=96, but only 0 bytes available)
    data[str_offset + 8..str_offset + 16].copy_from_slice(&20u64.to_le_bytes());

    let region = CompactedRegion::new(&data, base_addr);
    let err = region.read_lean_string_at(str_offset).unwrap_err();
    let data_start = str_offset + 32; // String data starts at header + 32
    assert!(matches!(
        err,
        OleanError::OutOfBounds { offset, size }
            if offset == data_start && size == data.len()
    ));
}
