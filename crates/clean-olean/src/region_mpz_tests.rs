// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression battery for the two on-disk `lean::mpz` layouts.
//!
//! Until 2026-09-17 [`CompactedRegion::read_bignat_value`] assumed the GMP
//! `__mpz_struct` layout unconditionally. Released Lean toolchains built
//! WITHOUT GMP — 4.8.0 among them — persist `lean::mpz` as
//! `{bool m_sign; size_t m_size; mpn_digit *m_digits}` with 32-bit digits
//! inline at `+32`. Read as GMP, `m_sign`'s padding bytes become `_mp_size`, so
//! the decoder asked for tens of thousands of 64-bit limbs and fell off the end
//! of the region. In Lean 4.8.0's `Init/Data/UInt/Basic.olean` that is exactly
//! `UInt64.ofNat`'s `18446744073709551615` literal, and the failure surfaced as
//! `object at offset 343384 extends beyond region (size 343384)` — the file's
//! own length.
//!
//! Every fixture here is a hand-assembled region, so the battery does not need
//! a Lean toolchain on the machine.

use super::{tags, CompactedRegion};
use crate::expr::BigNat;

const BASE: u64 = 0x1_0000;

/// A region with one object at offset 64 and nothing else.
struct Fixture {
    data: Vec<u8>,
}

impl Fixture {
    fn new() -> Self {
        Self {
            data: vec![0u8; 64],
        }
    }

    fn header(&mut self, cs_sz: u16, other: u8, tag: u8) -> usize {
        while !self.data.len().is_multiple_of(8) {
            self.data.push(0);
        }
        let offset = self.data.len();
        self.data.extend_from_slice(&0i32.to_le_bytes());
        self.data.extend_from_slice(&cs_sz.to_le_bytes());
        self.data.push(other);
        self.data.push(tag);
        offset
    }

    fn u64(&mut self, v: u64) {
        self.data.extend_from_slice(&v.to_le_bytes());
    }

    fn u32(&mut self, v: u32) {
        self.data.extend_from_slice(&v.to_le_bytes());
    }

    fn region(&self) -> CompactedRegion<'_> {
        CompactedRegion::new(&self.data, BASE)
    }

    fn ptr(offset: usize) -> u64 {
        BASE + offset as u64
    }
}

/// The GMP-free `lean::mpz`: sign byte at `+8` (with 7 bytes of real padding
/// garbage after it, exactly as the compactor leaves them), `m_size` at `+16`,
/// a stale `m_digits` host pointer at `+24`, 32-bit digits at `+32`.
fn lean_native_mpz(digits: &[u32], sign: u8, garbage_padding: bool) -> (Fixture, u64) {
    let mut f = Fixture::new();
    let cs_sz = (32 + 4 * digits.len()) as u16;
    let offset = f.header(cs_sz, 0, tags::MPZ);
    let mut sign_word = u64::from(sign);
    if garbage_padding {
        // Whatever the compactor left in the padding must not reach the value:
        // under the retired GMP reading these very bytes became `_mp_size`.
        sign_word |= 0x0000_7fd8_5d4e_3700 & !0xffu64;
    }
    f.u64(sign_word);
    f.u64(digits.len() as u64);
    f.u64(0x0000_7e18_217f_0c48); // stale host pointer, never patched
    for d in digits {
        f.u32(*d);
    }
    (f, Fixture::ptr(offset))
}

/// The GMP `__mpz_struct`: `_mp_alloc` and `_mp_size` as i32 at `+8`/`+12`,
/// `_mp_d` at `+16` patched to the inline array, 64-bit limbs at `+24`.
fn gmp_mpz(limbs: &[u64], inline_pointer: bool) -> (Fixture, u64) {
    let mut f = Fixture::new();
    let cs_sz = (24 + 8 * limbs.len()) as u16;
    let offset = f.header(cs_sz, 0, tags::MPZ);
    f.data
        .extend_from_slice(&(limbs.len() as i32).to_le_bytes()); // _mp_alloc
    f.data
        .extend_from_slice(&(limbs.len() as i32).to_le_bytes()); // _mp_size
    let mp_d = if inline_pointer {
        Fixture::ptr(offset) + 24
    } else {
        0
    };
    f.u64(mp_d);
    for l in limbs {
        f.u64(*l);
    }
    (f, Fixture::ptr(offset))
}

#[test]
fn lean_native_two_digit_bignum_is_the_uint64_maximum() {
    // The literal that made `UInt64.ofNat` unparseable: 2^64 - 1.
    let (f, ptr) = lean_native_mpz(&[0xffff_ffff, 0xffff_ffff], 0, true);
    assert_eq!(
        f.region().read_bignat_value(ptr).expect("must decode"),
        BigNat::from_u64(u64::MAX)
    );
}

#[test]
fn lean_native_three_digit_bignum_is_two_to_the_sixty_fourth() {
    let (f, ptr) = lean_native_mpz(&[0, 0, 1], 0, true);
    assert_eq!(
        f.region().read_bignat_value(ptr).expect("must decode"),
        BigNat::from_limbs(vec![0, 1])
    );
}

#[test]
fn lean_native_padding_garbage_never_reaches_the_value() {
    // Same digits, different padding: the decoded value must not move.
    let (clean_pad, p1) = lean_native_mpz(&[7, 0, 3], 0, false);
    let (dirty_pad, p2) = lean_native_mpz(&[7, 0, 3], 0, true);
    assert_eq!(
        clean_pad.region().read_bignat_value(p1).expect("decodes"),
        dirty_pad.region().read_bignat_value(p2).expect("decodes")
    );
}

#[test]
fn gmp_layout_still_decodes_with_a_patched_inline_pointer() {
    let (f, ptr) = gmp_mpz(&[0xdead_beef_0000_0001, 5], true);
    assert_eq!(
        f.region().read_bignat_value(ptr).expect("must decode"),
        BigNat::from_limbs(vec![0xdead_beef_0000_0001, 5])
    );
}

#[test]
fn gmp_layout_still_decodes_with_a_null_pointer() {
    // Clean's own writers leave `_mp_d` null.
    let (f, ptr) = gmp_mpz(&[0x0123_4567_89ab_cdef], false);
    assert_eq!(
        f.region().read_bignat_value(ptr).expect("must decode"),
        BigNat::from_u64(0x0123_4567_89ab_cdef)
    );
}

#[test]
fn a_negative_lean_native_bignum_is_refused_not_silently_made_positive() {
    let (f, ptr) = lean_native_mpz(&[1, 2], 1, false);
    let err = f
        .region()
        .read_bignat_value(ptr)
        .expect_err("a signed bignum is not a Nat");
    assert!(
        format!("{err}").contains("unrecognized MPZ object"),
        "unexpected error: {err}"
    );
}

#[test]
fn an_object_matching_neither_layout_is_refused_with_both_interpretations_named() {
    let mut f = Fixture::new();
    // `cs_sz` agrees with no digit count under either layout.
    let offset = f.header(37, 0, tags::MPZ);
    f.u64(0);
    f.u64(9);
    f.u64(0);
    f.u64(0);
    let err = f
        .region()
        .read_bignat_value(Fixture::ptr(offset))
        .expect_err("a malformed MPZ must be refused");
    let text = format!("{err}");
    assert!(text.contains("GMP layout"), "unexpected error: {text}");
    assert!(
        text.contains("Lean-native layout"),
        "unexpected error: {text}"
    );
}

#[test]
fn a_truncated_digit_array_is_refused_rather_than_read_past_the_region() {
    // The shape of the original bug: a size field that claims more digits than
    // the region holds. It must come back as a refusal, never a panic and never
    // a silently short value.
    let mut f = Fixture::new();
    let offset = f.header(0, 0, tags::MPZ);
    f.u64(0); // sign
    f.u64(4096); // m_size far beyond the region
    f.u64(0);
    f.u32(1);
    let err = f
        .region()
        .read_bignat_value(Fixture::ptr(offset))
        .expect_err("a truncated digit array must be refused");
    assert!(format!("{err}").contains("unrecognized MPZ object"));
}

/// The discriminator must be exact: a one-limb GMP object and a two-digit
/// Lean-native object can share a `cs_sz` of 32, and only the `_mp_d` field
/// separates them.
#[test]
fn the_two_layouts_are_never_both_accepted_for_one_object() {
    let (gmp, gp) = gmp_mpz(&[0x8000_0000_0000_0000], true);
    assert_eq!(
        gmp.region().read_bignat_value(gp).expect("decodes as GMP"),
        BigNat::from_u64(0x8000_0000_0000_0000)
    );
    let (native, np) = lean_native_mpz(&[0, 0x8000_0000], 0, false);
    assert_eq!(
        native
            .region()
            .read_bignat_value(np)
            .expect("decodes as Lean-native"),
        BigNat::from_u64(0x8000_0000_0000_0000)
    );
}
