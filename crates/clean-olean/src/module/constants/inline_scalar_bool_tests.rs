// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS7 regression: inline scalar `Bool` fields (e.g. `RecursorVal.k`) are
//! stored as raw bytes in the object's scalar area, NOT as boxed tagged
//! scalars. The decoder must read the raw byte, not `value >> 1`.
use crate::region::CompactedRegion;

/// Build a `CompactedRegion` over a little-endian `u64` word so we can
/// exercise the byte-level `Bool` decode in isolation.
fn region_from_word(word: u64) -> Vec<u8> {
    word.to_le_bytes().to_vec()
}

#[test]
fn test_read_bool_at_true_byte_decodes_true() {
    // Lean stores `Bool.true` for an inline scalar field as the raw byte
    // 0x01. Before the WS7 fix, `unbox_scalar(0x01) = 0x01 >> 1 = 0` made
    // this read `false`, disabling `Eq.rec`/`HEq.rec` K-reduction.
    let bytes = region_from_word(0x0000_0000_0000_0001);
    let region = CompactedRegion::new(&bytes, 0);
    assert!(
        region
            .read_inline_bool_exact(0, "Test.bool")
            .expect("read inline scalar bool"),
        "inline scalar byte 0x01 must decode as true"
    );
}

#[test]
fn test_read_bool_at_false_byte_decodes_false() {
    // A non-K recursor (e.g. `Nat.rec`) stores k = 0x00.
    let bytes = region_from_word(0x0000_0000_0000_0000);
    let region = CompactedRegion::new(&bytes, 0);
    assert!(
        !region
            .read_inline_bool_exact(0, "Test.bool")
            .expect("read inline scalar bool"),
        "inline scalar byte 0x00 must decode as false"
    );
}

#[test]
fn test_read_bool_at_ignores_high_bytes() {
    // The scalar area may pack the adjacent `isUnsafe` byte and padding into
    // the high bytes of the word; only the least-significant byte is `k`.
    let bytes = region_from_word(0x0701_0010_0000_0001);
    let region = CompactedRegion::new(&bytes, 0);
    assert!(
        region
            .read_inline_bool_exact(0, "Test.bool")
            .expect("read inline scalar bool"),
        "only the low byte determines the Bool; high bytes are unrelated fields"
    );

    let bytes_false = region_from_word(0x0701_0010_0000_0000);
    let region_false = CompactedRegion::new(&bytes_false, 0);
    assert!(
        !region_false
            .read_inline_bool_exact(0, "Test.bool")
            .expect("read inline scalar bool"),
        "low byte 0x00 must decode false even with non-zero high bytes"
    );
}

#[test]
fn test_read_bool_at_rejects_non_bool_byte() {
    let bytes = region_from_word(2);
    let region = CompactedRegion::new(&bytes, 0);
    assert!(region.read_inline_bool_exact(0, "Test.bool").is_err());
}
