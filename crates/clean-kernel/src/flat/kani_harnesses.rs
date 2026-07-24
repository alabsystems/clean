// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kani proofs for unsafe code verification in flat format.
//!
//! These proofs verify the safety invariants of the unsafe code:
//! - Memory layout assumptions (repr(C), SIZE constants)
//! - Alignment requirements
//! - Pointer casting validity
//! - Roundtrip correctness

use super::*;

/// Verify FlatExpr size is exactly 16 bytes.
///
/// The unsafe code assumes `FlatExpr::SIZE == std::mem::size_of::<FlatExpr>()`.
/// This is critical for correct serialization/deserialization.
#[kani::proof]
fn verify_flatexpr_size() {
    assert_eq!(
        std::mem::size_of::<FlatExpr>(),
        FlatExpr::SIZE,
        "FlatExpr must be exactly 16 bytes"
    );
    assert_eq!(FlatExpr::SIZE, 16, "FlatExpr::SIZE constant must be 16");
}

/// Verify FlatLevel size is exactly 12 bytes.
///
/// The unsafe code assumes `FlatLevel::SIZE == std::mem::size_of::<FlatLevel>()`.
#[kani::proof]
fn verify_flatlevel_size() {
    assert_eq!(
        std::mem::size_of::<FlatLevel>(),
        FlatLevel::SIZE,
        "FlatLevel must be exactly 12 bytes"
    );
    assert_eq!(FlatLevel::SIZE, 12, "FlatLevel::SIZE constant must be 12");
}

/// Verify FlatExpr alignment is 16 bytes.
///
/// The #[repr(C, align(16))] attribute must produce 16-byte alignment.
#[kani::proof]
fn verify_flatexpr_alignment() {
    assert_eq!(
        std::mem::align_of::<FlatExpr>(),
        16,
        "FlatExpr must be 16-byte aligned"
    );
}

/// Verify FlatLevel has valid alignment for its size.
#[kani::proof]
fn verify_flatlevel_alignment() {
    let align = std::mem::align_of::<FlatLevel>();
    // repr(C) guarantees natural alignment - at least 1
    assert!(align >= 1, "FlatLevel must have valid alignment");
    // Size must be a multiple of alignment for array layouts
    assert_eq!(
        FlatLevel::SIZE % align,
        0,
        "FlatLevel size must be multiple of alignment"
    );
}

/// Verify FlatExpr BVar roundtrip: serialize and deserialize.
///
/// Tests that the unsafe pointer cast preserves data integrity.
#[kani::proof]
fn verify_flatexpr_bvar_roundtrip() {
    let idx: u32 = kani::any();
    let original = FlatExpr::bvar(idx);

    // Simulate serialization (what the unsafe code does)
    // SAFETY: FlatExpr is #[repr(C, align(16))] with size == 16, so reinterpreting
    // a valid FlatExpr reference as [u8; 16] via pointer cast is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };

    // Simulate deserialization (what the unsafe code does) using unaligned read.
    // SAFETY: `bytes` was initialized from a valid FlatExpr above; read_unaligned
    // reconstructs a valid FlatExpr from the same byte representation.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    // Verify data integrity
    assert_eq!(
        restored.tag, original.tag,
        "Tag must be preserved through roundtrip"
    );
    assert_eq!(
        restored.flags, original.flags,
        "Flags must be preserved through roundtrip"
    );
    assert_eq!(
        restored.data, original.data,
        "Data must be preserved through roundtrip"
    );
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        idx,
        "BVar index must be preserved"
    );
}

/// Verify FlatExpr App roundtrip.
#[kani::proof]
fn verify_flatexpr_app_roundtrip() {
    let fn_idx: u32 = kani::any();
    let arg_idx: u32 = kani::any();
    let original = FlatExpr::app(fn_idx, arg_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };

    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, original.tag);
    assert_eq!(restored.data[0..4], original.data[0..4], "fn_idx preserved");
    assert_eq!(
        restored.data[4..8],
        original.data[4..8],
        "arg_idx preserved"
    );
}

/// Verify FlatExpr LitNat roundtrip with u64 value.
#[kani::proof]
fn verify_flatexpr_litnat_roundtrip() {
    let value: u64 = kani::any();
    let original = FlatExpr::lit_nat(value);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };

    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(
        restored.read_u64(0).expect("valid FlatExpr u64 payload"),
        value,
        "LitNat value must be preserved through roundtrip"
    );
}

/// Verify FlatLevel roundtrip.
#[kani::proof]
fn verify_flatlevel_roundtrip() {
    let idx: u32 = kani::any();
    let original = FlatLevel::succ(idx);

    // SAFETY: FlatLevel is #[repr(C)] with size 12; pointer cast to [u8; 12] is sound.
    let bytes: [u8; 12] = unsafe {
        let ptr = &original as *const FlatLevel as *const [u8; 12];
        *ptr
    };

    // SAFETY: `bytes` was initialized from a valid FlatLevel; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatLevel) };

    assert_eq!(restored.tag, original.tag, "Tag must be preserved");
    assert_eq!(restored.data, original.data, "Data must be preserved");
}

/// Verify all FlatTag values are distinct and valid.
#[kani::proof]
fn verify_flattag_values() {
    // Verify tags are distinct (implicit from enum)
    assert_ne!(FlatTag::BVar as u8, FlatTag::Sort as u8);
    assert_ne!(FlatTag::Const as u8, FlatTag::App as u8);

    // Verify all tags can round-trip through u8 conversion
    let tag_byte: u8 = kani::any();
    kani::assume(tag_byte <= 10); // Valid range for FlatTag

    if let Ok(tag) = FlatTag::try_from(tag_byte) {
        assert_eq!(tag as u8, tag_byte, "Tag round-trip must preserve value");
    }
}

/// Verify FlatFlags bitwise operations are safe.
#[kani::proof]
fn verify_flatflags_operations() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();

    let flags_a = FlatFlags(a);
    let flags_b = FlatFlags(b);

    // Verify with() combines flags correctly
    let combined = flags_a.with(flags_b);
    assert_eq!(combined.0, a | b, "with() must OR flags");

    // Verify contains() checks correctly
    let has_b = combined.contains(flags_b);
    assert!(has_b, "combined must contain flags_b");

    // Verify contains() returns false for flags NOT set
    // When a bit is set in c but not in combined, contains should be false
    let c: u8 = kani::any();
    let flags_c = FlatFlags(c);
    if (combined.0 & c) != c {
        assert!(
            !combined.contains(flags_c),
            "contains must return false for unset flags"
        );
    }
}

/// Verify no buffer overrun in get_expr bounds check.
///
/// The unsafe deserialization in get_expr checks bounds before casting.
/// This verifies the bounds check logic.
#[kani::proof]
fn verify_get_expr_bounds() {
    let expr_count: u32 = kani::any();
    kani::assume(expr_count > 0 && expr_count < 1000); // Reasonable bounds

    let idx: u32 = kani::any();
    let header_size = FlatHeader::SIZE;
    let data_len = header_size + (expr_count as usize) * FlatExpr::SIZE;

    // Verify checked offset arithmetic from get_expr for in-range indices.
    if idx < expr_count {
        let offset = (idx as usize)
            .checked_mul(FlatExpr::SIZE)
            .and_then(|n| header_size.checked_add(n))
            .expect("bounded inputs must not overflow");
        let end = offset
            .checked_add(FlatExpr::SIZE)
            .expect("bounded inputs must not overflow");
        assert!(end <= data_len, "Valid index must be within data bounds");
    }
}

/// Verify the real production unsafe pipeline end-to-end.
///
/// This exercises `FlatBuilder::write_to` (unsafe `from_raw_parts`) and
/// `FlatDb::get_expr` (unsafe `read_unaligned`) together with actual
/// serialized bytes.
#[kani::proof]
#[kani::unwind(32)]
fn verify_flatexpr_end_to_end_write_to_get_expr() {
    let first_idx: u32 = kani::any();
    let second_idx: u32 = kani::any();
    let read_second: bool = kani::any();

    let mut builder = FlatBuilder::new();
    assert_eq!(builder.add_expr(FlatExpr::bvar(first_idx)), 0);
    assert_eq!(builder.add_expr(FlatExpr::bvar(second_idx)), 1);

    let mut bytes = Vec::new();
    assert!(
        builder.write_to(&mut bytes).is_ok(),
        "write_to(Vec<u8>) should not fail"
    );

    let db = FlatDb::from_bytes(&bytes).expect("serialized bytes must parse");
    let idx = if read_second { 1 } else { 0 };
    let expected = if read_second { second_idx } else { first_idx };
    let restored = db.get_expr(idx).expect("valid index must deserialize");

    assert_eq!(restored.tag, FlatTag::BVar as u8, "tag must roundtrip");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        expected,
        "payload must roundtrip"
    );
}

// ========================================================================
// FlatExpr variant roundtrip harnesses (#934)
// ========================================================================

/// Verify FlatExpr Sort roundtrip: level_idx preserved through serialize/deserialize.
#[kani::proof]
fn verify_flatexpr_sort_roundtrip() {
    let level_idx: u32 = kani::any();
    let original = FlatExpr::sort(level_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::Sort as u8);
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        level_idx,
        "level_idx must be preserved"
    );
}

/// Verify FlatExpr Const roundtrip: name_idx and levels_list_idx preserved.
#[kani::proof]
fn verify_flatexpr_const_roundtrip() {
    let name_idx: u32 = kani::any();
    let levels_list_idx: u32 = kani::any();
    let original = FlatExpr::const_ref(name_idx, levels_list_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::Const as u8);
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        name_idx,
        "name_idx must be preserved"
    );
    assert_eq!(
        restored.read_u32(4).expect("valid FlatExpr u32 payload"),
        levels_list_idx,
        "levels_list_idx must be preserved"
    );
}

/// Verify FlatExpr Lam roundtrip: mixed u8+u32+u32 packing preserved.
///
/// This is a high-risk variant because binder_info (u8) at offset 0 causes
/// ty_idx and body_idx to sit at unaligned offsets (1..5, 5..9).
#[kani::proof]
fn verify_flatexpr_lam_roundtrip() {
    let binder_info: u8 = kani::any();
    kani::assume(binder_info <= 3); // Valid BinderInfo values: 0-3
    let ty_idx: u32 = kani::any();
    let body_idx: u32 = kani::any();
    let original = FlatExpr::lam(binder_info, ty_idx, body_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::Lam as u8);
    assert_eq!(
        restored.data[0], binder_info,
        "binder_info must be preserved"
    );
    // ty_idx at unaligned offset 1..5
    let restored_ty = u32::from_le_bytes(
        restored.data[1..5]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(
        restored_ty, ty_idx,
        "ty_idx must be preserved at unaligned offset"
    );
    // body_idx at unaligned offset 5..9
    let restored_body = u32::from_le_bytes(
        restored.data[5..9]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(
        restored_body, body_idx,
        "body_idx must be preserved at unaligned offset"
    );
}

/// Verify FlatExpr Pi roundtrip: identical layout to Lam but different tag.
#[kani::proof]
fn verify_flatexpr_pi_roundtrip() {
    let binder_info: u8 = kani::any();
    kani::assume(binder_info <= 3);
    let ty_idx: u32 = kani::any();
    let body_idx: u32 = kani::any();
    let original = FlatExpr::pi(binder_info, ty_idx, body_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::Pi as u8);
    assert_eq!(
        restored.data[0], binder_info,
        "binder_info must be preserved"
    );
    let restored_ty = u32::from_le_bytes(
        restored.data[1..5]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(restored_ty, ty_idx, "ty_idx must be preserved");
    let restored_body = u32::from_le_bytes(
        restored.data[5..9]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(restored_body, body_idx, "body_idx must be preserved");
}

/// Verify FlatExpr Let roundtrip: three u32 fields using all 12 data bytes.
#[kani::proof]
fn verify_flatexpr_let_roundtrip() {
    let ty_idx: u32 = kani::any();
    let val_idx: u32 = kani::any();
    let body_idx: u32 = kani::any();
    let original = FlatExpr::let_expr(ty_idx, val_idx, body_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::Let as u8);
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        ty_idx,
        "ty_idx must be preserved"
    );
    assert_eq!(
        restored.read_u32(4).expect("valid FlatExpr u32 payload"),
        val_idx,
        "val_idx must be preserved"
    );
    assert_eq!(
        restored.read_u32(8).expect("valid FlatExpr u32 payload"),
        body_idx,
        "body_idx must be preserved"
    );
}

/// Verify FlatExpr LitStr roundtrip: string_idx preserved.
#[kani::proof]
fn verify_flatexpr_litstr_roundtrip() {
    let string_idx: u32 = kani::any();
    let original = FlatExpr::lit_str(string_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::LitStr as u8);
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        string_idx,
        "string_idx must be preserved"
    );
}

/// Verify FlatExpr Proj roundtrip: mixed u32+u16+u32 packing.
///
/// High-risk variant: field (u16) at offset 4..6 causes expr_idx (u32)
/// to sit at non-u32-aligned offset 6..10.
#[kani::proof]
fn verify_flatexpr_proj_roundtrip() {
    let name_idx: u32 = kani::any();
    let field: u16 = kani::any();
    let expr_idx: u32 = kani::any();
    let original = FlatExpr::proj(name_idx, field, expr_idx);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::Proj as u8);
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        name_idx,
        "name_idx must be preserved"
    );
    assert_eq!(
        restored.read_u16(4).expect("valid FlatExpr u16 payload"),
        field,
        "field must be preserved"
    );
    // expr_idx at non-aligned offset 6..10
    let restored_expr = u32::from_le_bytes(
        restored.data[6..10]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(
        restored_expr, expr_idx,
        "expr_idx must be preserved at offset 6"
    );
}

/// Verify FlatExpr FVar roundtrip: u64 id preserved, HAS_FVAR flag set.
#[kani::proof]
fn verify_flatexpr_fvar_roundtrip() {
    let id: u64 = kani::any();
    let original = FlatExpr::fvar(id);

    // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
    let bytes: [u8; 16] = unsafe {
        let ptr = &original as *const FlatExpr as *const [u8; 16];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatExpr; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatExpr) };

    assert_eq!(restored.tag, FlatTag::FVar as u8);
    assert_eq!(
        restored.read_u64(0).expect("valid FlatExpr u64 payload"),
        id,
        "FVar id must be preserved"
    );
    assert!(
        FlatFlags(restored.flags).contains(FlatFlags::HAS_FVAR),
        "HAS_FVAR flag must be set"
    );
}

// ========================================================================
// FlatLevel variant roundtrip harnesses (#934)
// ========================================================================

/// Verify FlatLevel Max roundtrip: left_idx and right_idx preserved.
#[kani::proof]
fn verify_flatlevel_max_roundtrip() {
    let left_idx: u32 = kani::any();
    let right_idx: u32 = kani::any();
    let original = FlatLevel::max(left_idx, right_idx);

    // SAFETY: FlatLevel is #[repr(C)] with size 12; pointer cast to [u8; 12] is sound.
    let bytes: [u8; 12] = unsafe {
        let ptr = &original as *const FlatLevel as *const [u8; 12];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatLevel; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatLevel) };

    assert_eq!(
        restored.tag,
        FlatLevel::TAG_MAX,
        "Max tag must be preserved"
    );
    let restored_left = u32::from_le_bytes(
        restored.data[0..4]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    let restored_right = u32::from_le_bytes(
        restored.data[4..8]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(restored_left, left_idx, "left_idx must be preserved");
    assert_eq!(restored_right, right_idx, "right_idx must be preserved");
}

/// Verify FlatLevel Param roundtrip: name_idx preserved.
#[kani::proof]
fn verify_flatlevel_param_roundtrip() {
    let name_idx: u32 = kani::any();
    let original = FlatLevel::param(name_idx);

    // SAFETY: FlatLevel is #[repr(C)] with size 12; pointer cast to [u8; 12] is sound.
    let bytes: [u8; 12] = unsafe {
        let ptr = &original as *const FlatLevel as *const [u8; 12];
        *ptr
    };
    // SAFETY: `bytes` was initialized from a valid FlatLevel; read_unaligned is sound.
    let restored = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const FlatLevel) };

    assert_eq!(
        restored.tag,
        FlatLevel::TAG_PARAM,
        "Param tag must be preserved"
    );
    let restored_name = u32::from_le_bytes(
        restored.data[0..4]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(restored_name, name_idx, "name_idx must be preserved");
}

// ========================================================================
// Padding byte verification (#934)
// ========================================================================

/// Verify FlatExpr padding bytes are zero-initialized for all variants.
///
/// The unsafe `slice::from_raw_parts` reads include padding bytes at
/// offset 2..4 in the 16-byte struct. If any constructor fails to
/// zero-initialize `_pad`, serialization reads uninitialized memory (UB).
/// We check via the raw bytes (what the unsafe code actually reads).
#[kani::proof]
fn verify_flatexpr_padding_zeroed() {
    let idx: u32 = kani::any();
    let idx2: u32 = kani::any();
    let idx3: u32 = kani::any();
    let bi: u8 = kani::any();
    kani::assume(bi <= 3);
    let val: u64 = kani::any();
    let field: u16 = kani::any();

    // Helper: extract padding bytes (offset 2..4) from serialized form
    fn pad_bytes(expr: &FlatExpr) -> [u8; 2] {
        // SAFETY: FlatExpr is #[repr(C, align(16))] with size 16; pointer cast to [u8; 16] is sound.
        let bytes: [u8; 16] = unsafe {
            let ptr = expr as *const FlatExpr as *const [u8; 16];
            *ptr
        };
        [bytes[2], bytes[3]]
    }

    assert_eq!(pad_bytes(&FlatExpr::bvar(idx)), [0, 0], "BVar padding");
    assert_eq!(pad_bytes(&FlatExpr::sort(idx)), [0, 0], "Sort padding");
    assert_eq!(
        pad_bytes(&FlatExpr::const_ref(idx, idx2)),
        [0, 0],
        "Const padding"
    );
    assert_eq!(pad_bytes(&FlatExpr::app(idx, idx2)), [0, 0], "App padding");
    assert_eq!(
        pad_bytes(&FlatExpr::lam(bi, idx, idx2)),
        [0, 0],
        "Lam padding"
    );
    assert_eq!(
        pad_bytes(&FlatExpr::pi(bi, idx, idx2)),
        [0, 0],
        "Pi padding"
    );
    assert_eq!(
        pad_bytes(&FlatExpr::let_expr(idx, idx2, idx3)),
        [0, 0],
        "Let padding"
    );
    assert_eq!(pad_bytes(&FlatExpr::lit_nat(val)), [0, 0], "LitNat padding");
    assert_eq!(pad_bytes(&FlatExpr::lit_str(idx)), [0, 0], "LitStr padding");
    assert_eq!(
        pad_bytes(&FlatExpr::proj(idx, field, idx2)),
        [0, 0],
        "Proj padding"
    );
    assert_eq!(pad_bytes(&FlatExpr::fvar(val)), [0, 0], "FVar padding");
}

/// Verify FlatLevel padding bytes are zero-initialized for all variants.
///
/// FlatLevel has 3 padding bytes at offset 1..4. Same UB risk as FlatExpr.
#[kani::proof]
fn verify_flatlevel_padding_zeroed() {
    let idx: u32 = kani::any();
    let idx2: u32 = kani::any();

    fn pad_bytes(level: &FlatLevel) -> [u8; 3] {
        // SAFETY: FlatLevel is #[repr(C)] with size 12; pointer cast to [u8; 12] is sound.
        let bytes: [u8; 12] = unsafe {
            let ptr = level as *const FlatLevel as *const [u8; 12];
            *ptr
        };
        [bytes[1], bytes[2], bytes[3]]
    }

    assert_eq!(pad_bytes(&FlatLevel::zero()), [0, 0, 0], "Zero padding");
    assert_eq!(pad_bytes(&FlatLevel::succ(idx)), [0, 0, 0], "Succ padding");
    assert_eq!(
        pad_bytes(&FlatLevel::max(idx, idx2)),
        [0, 0, 0],
        "Max padding"
    );
    assert_eq!(
        pad_bytes(&FlatLevel::param(idx)),
        [0, 0, 0],
        "Param padding"
    );
}

// ========================================================================
// End-to-end production pipeline harnesses (#934, #1347)
//
// These exercise the real FlatBuilder::write_to → FlatDb::from_bytes →
// FlatDb::get_expr path for every FlatExpr variant, closing the gap
// between simulated roundtrips and actual unsafe code verification.
// ========================================================================

/// End-to-end Sort: build Sort expr, write, parse, read back, verify fields.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_sort() {
    let level_idx: u32 = kani::any();
    // Constrain level_idx to a valid range (we add exactly 1 level at index 0)
    kani::assume(level_idx == 0);

    let mut builder = FlatBuilder::new();
    builder.add_level(FlatLevel::zero());
    let expr_idx = builder.add_expr(FlatExpr::sort(level_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(expr_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::Sort as u8, "tag");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        level_idx,
        "level_idx"
    );
}

/// End-to-end App: build two BVars and an App referencing them.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_app() {
    let fn_bvar: u32 = kani::any();
    let arg_bvar: u32 = kani::any();

    let mut builder = FlatBuilder::new();
    let fn_idx = builder.add_expr(FlatExpr::bvar(fn_bvar));
    let arg_idx = builder.add_expr(FlatExpr::bvar(arg_bvar));
    let app_idx = builder.add_expr(FlatExpr::app(fn_idx, arg_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(app_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::App as u8, "tag");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        fn_idx,
        "fn_idx"
    );
    assert_eq!(
        restored.read_u32(4).expect("valid FlatExpr u32 payload"),
        arg_idx,
        "arg_idx"
    );
}

/// End-to-end Lam: build domain + body BVars, then a Lam over them.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_lam() {
    let bi: u8 = kani::any();
    kani::assume(bi <= 3);

    let mut builder = FlatBuilder::new();
    let ty_idx = builder.add_expr(FlatExpr::bvar(0));
    let body_idx = builder.add_expr(FlatExpr::bvar(1));
    let lam_idx = builder.add_expr(FlatExpr::lam(bi, ty_idx, body_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(lam_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::Lam as u8, "tag");
    assert_eq!(restored.data[0], bi, "binder_info");
    let ty_back = u32::from_le_bytes(
        restored.data[1..5]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    let body_back = u32::from_le_bytes(
        restored.data[5..9]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(ty_back, ty_idx, "ty_idx");
    assert_eq!(body_back, body_idx, "body_idx");
}

/// End-to-end Pi: same structure as Lam but Pi tag.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_pi() {
    let bi: u8 = kani::any();
    kani::assume(bi <= 3);

    let mut builder = FlatBuilder::new();
    let ty_idx = builder.add_expr(FlatExpr::bvar(0));
    let body_idx = builder.add_expr(FlatExpr::bvar(1));
    let pi_idx = builder.add_expr(FlatExpr::pi(bi, ty_idx, body_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(pi_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::Pi as u8, "tag");
    assert_eq!(restored.data[0], bi, "binder_info");
    let ty_back = u32::from_le_bytes(
        restored.data[1..5]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    let body_back = u32::from_le_bytes(
        restored.data[5..9]
            .try_into()
            .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes"),
    );
    assert_eq!(ty_back, ty_idx, "ty_idx");
    assert_eq!(body_back, body_idx, "body_idx");
}

/// End-to-end Let: ty + val + body indices roundtrip.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_let() {
    let mut builder = FlatBuilder::new();
    let ty_idx = builder.add_expr(FlatExpr::bvar(0));
    let val_idx = builder.add_expr(FlatExpr::bvar(1));
    let body_idx = builder.add_expr(FlatExpr::bvar(2));
    let let_idx = builder.add_expr(FlatExpr::let_expr(ty_idx, val_idx, body_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(let_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::Let as u8, "tag");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        ty_idx,
        "ty_idx"
    );
    assert_eq!(
        restored.read_u32(4).expect("valid FlatExpr u32 payload"),
        val_idx,
        "val_idx"
    );
    assert_eq!(
        restored.read_u32(8).expect("valid FlatExpr u32 payload"),
        body_idx,
        "body_idx"
    );
}

/// End-to-end LitNat: u64 value roundtrip through production pipeline.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_litnat() {
    let value: u64 = kani::any();

    let mut builder = FlatBuilder::new();
    let expr_idx = builder.add_expr(FlatExpr::lit_nat(value));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(expr_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::LitNat as u8, "tag");
    assert_eq!(
        restored.read_u64(0).expect("valid FlatExpr u64 payload"),
        value,
        "value"
    );
}

/// End-to-end LitStr: string index roundtrip (exercises string table).
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_litstr() {
    let mut builder = FlatBuilder::new();
    let str_idx = builder.add_string("hello");
    let expr_idx = builder.add_expr(FlatExpr::lit_str(str_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(expr_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::LitStr as u8, "tag");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        str_idx,
        "string_idx"
    );

    // Also verify the string table roundtrip
    let s = db.get_string(str_idx).expect("must get string");
    assert_eq!(s, "hello", "string content");
}

/// End-to-end Const: name + level list roundtrip (exercises name table + level lists).
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_const() {
    let mut builder = FlatBuilder::new();
    let name_idx = builder.add_name("Nat.add");
    let level0 = builder.add_level(FlatLevel::zero());
    let level1 = builder.add_level(FlatLevel::succ(level0));
    let levels_list_idx = builder.add_level_list(&[level0, level1]);
    let expr_idx = builder.add_expr(FlatExpr::const_ref(name_idx, levels_list_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(expr_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::Const as u8, "tag");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        name_idx,
        "name_idx"
    );
    assert_eq!(
        restored.read_u32(4).expect("valid FlatExpr u32 payload"),
        levels_list_idx,
        "levels_list_idx"
    );

    // Verify name table roundtrip
    let n = db.get_name(name_idx).expect("must get name");
    assert_eq!(n, "Nat.add", "name content");

    // Verify level list roundtrip
    let lvls = db
        .get_level_list(levels_list_idx)
        .expect("must get level list");
    assert_eq!(lvls.len(), 2, "level list length");
    assert_eq!(lvls[0], level0, "level list [0]");
    assert_eq!(lvls[1], level1, "level list [1]");
}

/// End-to-end Const with empty level list (u32::MAX sentinel).
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_const_no_levels() {
    let mut builder = FlatBuilder::new();
    let name_idx = builder.add_name("Bool");
    let levels_list_idx = builder.add_level_list(&[]);
    assert_eq!(levels_list_idx, u32::MAX);
    let expr_idx = builder.add_expr(FlatExpr::const_ref(name_idx, levels_list_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(expr_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::Const as u8, "tag");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        name_idx,
        "name_idx"
    );
    assert_eq!(
        restored.read_u32(4).expect("valid FlatExpr u32 payload"),
        u32::MAX,
        "empty level list sentinel"
    );

    let lvls = db.get_level_list(u32::MAX).expect("empty list");
    assert!(lvls.is_empty(), "empty level list");
}

/// End-to-end Proj: name_idx + field + expr_idx roundtrip.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_proj() {
    let field: u16 = kani::any();

    let mut builder = FlatBuilder::new();
    let name_idx = builder.add_name("Prod");
    let inner_idx = builder.add_expr(FlatExpr::bvar(0));
    let proj_idx = builder.add_expr(FlatExpr::proj(name_idx, field, inner_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(proj_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::Proj as u8, "tag");
    assert_eq!(
        restored.read_u32(0).expect("valid FlatExpr u32 payload"),
        name_idx,
        "name_idx"
    );
    assert_eq!(
        restored.read_u16(4).expect("valid FlatExpr u16 payload"),
        field,
        "field"
    );
    assert_eq!(
        u32::from_le_bytes(
            restored.data[6..10]
                .try_into()
                .expect("invariant: fixed-width 4-byte slice into [u8; 4] for u32::from_le_bytes")
        ),
        inner_idx,
        "expr_idx"
    );
}

/// End-to-end FVar: u64 id roundtrip.
#[kani::proof]
#[kani::unwind(32)]
fn verify_e2e_fvar() {
    let id: u64 = kani::any();

    let mut builder = FlatBuilder::new();
    let expr_idx = builder.add_expr(FlatExpr::fvar(id));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");
    let restored = db.get_expr(expr_idx).expect("must get");
    assert_eq!(restored.tag, FlatTag::FVar as u8, "tag");
    assert_eq!(
        restored.read_u64(0).expect("valid FlatExpr u64 payload"),
        id,
        "fvar id"
    );
    assert!(
        restored.flags().contains(FlatFlags::HAS_FVAR),
        "HAS_FVAR flag"
    );
}

/// End-to-end mixed: multiple variant types in one FlatDb.
/// Exercises the production pipeline with a heterogeneous expression array.
#[kani::proof]
#[kani::unwind(64)]
fn verify_e2e_mixed_variants() {
    let bvar_val: u32 = kani::any();
    let nat_val: u64 = kani::any();

    let mut builder = FlatBuilder::new();
    let name_idx = builder.add_name("f");
    let level_idx = builder.add_level(FlatLevel::zero());
    let str_idx = builder.add_string("s");

    let bvar_i = builder.add_expr(FlatExpr::bvar(bvar_val));
    let sort_i = builder.add_expr(FlatExpr::sort(level_idx));
    let nat_i = builder.add_expr(FlatExpr::lit_nat(nat_val));
    let app_i = builder.add_expr(FlatExpr::app(bvar_i, sort_i));
    let litstr_i = builder.add_expr(FlatExpr::lit_str(str_idx));

    let mut bytes = Vec::new();
    builder
        .write_to(&mut bytes)
        .expect("FlatBuilder::write_to must succeed");

    let db = FlatDb::from_bytes(&bytes).expect("must parse");

    let r_bvar = db.get_expr(bvar_i).expect("bvar");
    assert_eq!(r_bvar.tag, FlatTag::BVar as u8);
    assert_eq!(
        r_bvar.read_u32(0).expect("valid FlatExpr u32 payload"),
        bvar_val
    );

    let r_sort = db.get_expr(sort_i).expect("sort");
    assert_eq!(r_sort.tag, FlatTag::Sort as u8);
    assert_eq!(
        r_sort.read_u32(0).expect("valid FlatExpr u32 payload"),
        level_idx
    );

    let r_nat = db.get_expr(nat_i).expect("litnat");
    assert_eq!(r_nat.tag, FlatTag::LitNat as u8);
    assert_eq!(
        r_nat.read_u64(0).expect("valid FlatExpr u64 payload"),
        nat_val
    );

    let r_app = db.get_expr(app_i).expect("app");
    assert_eq!(r_app.tag, FlatTag::App as u8);
    assert_eq!(
        r_app.read_u32(0).expect("valid FlatExpr u32 payload"),
        bvar_i
    );
    assert_eq!(
        r_app.read_u32(4).expect("valid FlatExpr u32 payload"),
        sort_i
    );

    let r_str = db.get_expr(litstr_i).expect("litstr");
    assert_eq!(r_str.tag, FlatTag::LitStr as u8);
    assert_eq!(
        r_str.read_u32(0).expect("valid FlatExpr u32 payload"),
        str_idx
    );
}
