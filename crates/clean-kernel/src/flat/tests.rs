// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests and Miri tests for flat format.

use super::codec::{decode_flatexpr, decode_flatlevel, encode_flatexpr, encode_flatlevel};
use super::*;
use proptest::prelude::*;
use std::mem::{align_of, size_of};

fn next_u8(data: &[u8], pos: &mut usize) -> u8 {
    if data.is_empty() {
        return 0;
    }
    let byte = data[*pos % data.len()];
    *pos = pos.wrapping_add(1);
    byte
}

fn flat_expr_bytes(expr: &FlatExpr) -> [u8; FlatExpr::SIZE] {
    encode_flatexpr(expr)
}

fn flat_level_bytes(level: &FlatLevel) -> [u8; FlatLevel::SIZE] {
    encode_flatlevel(level)
}

fn build_builder_from_bytes(data: &[u8]) -> FlatBuilder {
    let mut builder = FlatBuilder::new();
    builder.add_name("N0");
    builder.add_string("S0");
    builder.add_level(FlatLevel::zero());

    let mut pos = 0usize;
    let steps = (next_u8(data, &mut pos) % 32).saturating_add(1);
    for _ in 0..steps {
        if next_u8(data, &mut pos).is_multiple_of(5) {
            let name_id = next_u8(data, &mut pos);
            builder.add_name(&format!("N{name_id}"));
        }
        if next_u8(data, &mut pos).is_multiple_of(7) {
            let string_id = next_u8(data, &mut pos);
            builder.add_string(&format!("S{string_id}"));
        }
        if next_u8(data, &mut pos).is_multiple_of(11) {
            let choice = next_u8(data, &mut pos) % 4;
            let level_count = builder.levels.len().max(1) as u32;
            let level = match choice {
                0 => FlatLevel::zero(),
                1 => FlatLevel::succ(next_u8(data, &mut pos) as u32 % level_count),
                2 => FlatLevel::max(
                    next_u8(data, &mut pos) as u32 % level_count,
                    next_u8(data, &mut pos) as u32 % level_count,
                ),
                _ => {
                    let name_count = builder.names.len().max(1) as u32;
                    FlatLevel::param(next_u8(data, &mut pos) as u32 % name_count)
                }
            };
            builder.add_level(level);
        }

        let expr_count = builder.exprs.len() as u32;
        let name_count = builder.names.len().max(1) as u32;
        let string_count = builder.strings.len().max(1) as u32;
        let level_count = builder.levels.len().max(1) as u32;
        let choice = next_u8(data, &mut pos) % 11;
        let expr = match choice {
            0 => FlatExpr::bvar(next_u8(data, &mut pos) as u32),
            1 => FlatExpr::sort(next_u8(data, &mut pos) as u32 % level_count),
            2 => {
                let name_idx = next_u8(data, &mut pos) as u32 % name_count;
                let levels_idx = if next_u8(data, &mut pos).is_multiple_of(3) {
                    u32::MAX
                } else {
                    next_u8(data, &mut pos) as u32 % level_count
                };
                FlatExpr::const_ref(name_idx, levels_idx)
            }
            3 => {
                if expr_count == 0 {
                    FlatExpr::lit_nat(next_u8(data, &mut pos) as u64)
                } else {
                    FlatExpr::app(
                        next_u8(data, &mut pos) as u32 % expr_count,
                        next_u8(data, &mut pos) as u32 % expr_count,
                    )
                }
            }
            4 => {
                if expr_count == 0 {
                    FlatExpr::bvar(next_u8(data, &mut pos) as u32)
                } else {
                    FlatExpr::lam(
                        next_u8(data, &mut pos) % 4,
                        next_u8(data, &mut pos) as u32 % expr_count,
                        next_u8(data, &mut pos) as u32 % expr_count,
                    )
                }
            }
            5 => {
                if expr_count == 0 {
                    FlatExpr::bvar(next_u8(data, &mut pos) as u32)
                } else {
                    FlatExpr::pi(
                        next_u8(data, &mut pos) % 4,
                        next_u8(data, &mut pos) as u32 % expr_count,
                        next_u8(data, &mut pos) as u32 % expr_count,
                    )
                }
            }
            6 => {
                if expr_count == 0 {
                    FlatExpr::lit_nat(next_u8(data, &mut pos) as u64)
                } else {
                    FlatExpr::let_expr(
                        next_u8(data, &mut pos) as u32 % expr_count,
                        next_u8(data, &mut pos) as u32 % expr_count,
                        next_u8(data, &mut pos) as u32 % expr_count,
                    )
                }
            }
            7 => FlatExpr::lit_nat(next_u8(data, &mut pos) as u64),
            8 => FlatExpr::lit_str(next_u8(data, &mut pos) as u32 % string_count),
            9 => {
                if expr_count == 0 {
                    FlatExpr::lit_str(next_u8(data, &mut pos) as u32 % string_count)
                } else {
                    FlatExpr::proj(
                        next_u8(data, &mut pos) as u32 % name_count,
                        next_u8(data, &mut pos) as u16,
                        next_u8(data, &mut pos) as u32 % expr_count,
                    )
                }
            }
            _ => FlatExpr::fvar(next_u8(data, &mut pos) as u64),
        };
        builder.add_expr(expr);
    }

    builder
}

#[test]
fn test_flat_expr_size() {
    assert_eq!(size_of::<FlatExpr>(), 16);
    assert_eq!(align_of::<FlatExpr>(), 16);
}

#[test]
fn test_flat_header_size() {
    assert_eq!(size_of::<FlatHeader>(), 64);
}

#[test]
fn test_flat_level_size() {
    assert_eq!(size_of::<FlatLevel>(), FlatLevel::SIZE);
    assert_eq!(FlatLevel::SIZE, 12);
}

#[test]
fn test_codec_flatexpr_roundtrip() {
    let expr = FlatExpr::proj(10, 3, 20);
    let bytes = encode_flatexpr(&expr);
    let decoded = decode_flatexpr(&bytes).unwrap();
    assert_eq!(decoded.tag, expr.tag);
    assert_eq!(decoded.flags, expr.flags);
    assert_eq!(decoded.data, expr.data);
}

#[test]
fn test_codec_flatlevel_roundtrip() {
    let level = FlatLevel::max(1, 2);
    let bytes = encode_flatlevel(&level);
    let decoded = decode_flatlevel(&bytes).unwrap();
    assert_eq!(decoded.tag, level.tag);
    assert_eq!(decoded.data, level.data);
}

#[test]
fn test_codec_rejects_invalid_flatexpr_tag() {
    let mut bytes = [0u8; FlatExpr::SIZE];
    bytes[0] = 99;
    let err = decode_flatexpr(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidTag(99)));
}

#[test]
fn test_codec_rejects_invalid_flatlevel_tag() {
    let mut bytes = [0u8; FlatLevel::SIZE];
    bytes[0] = 99;
    let err = decode_flatlevel(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidHeader(_)));
}

#[test]
fn test_flat_builder_roundtrip() {
    let mut builder = FlatBuilder::new();

    // Add some expressions
    let name_idx = builder.add_name("Nat.add");
    let zero_level_idx = builder.add_level(FlatLevel::zero());

    // Use level list for const (multi-level universe support #1162)
    let level_list_idx = builder.add_level_list(&[zero_level_idx]);
    let const_expr = builder.add_expr(FlatExpr::const_ref(name_idx, level_list_idx));
    let nat_lit = builder.add_expr(FlatExpr::lit_nat(42));
    let _app = builder.add_expr(FlatExpr::app(const_expr, nat_lit));

    // Write to bytes
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    // Read back
    let db = FlatDb::from_bytes(&bytes).unwrap();
    assert_eq!(db.expr_count(), 3);

    // Verify expressions
    let expr0 = db.get_expr(0).unwrap();
    assert_eq!(expr0.tag().unwrap(), FlatTag::Const);

    let expr1 = db.get_expr(1).unwrap();
    assert_eq!(expr1.tag().unwrap(), FlatTag::LitNat);
    assert_eq!(expr1.read_u64(0).expect("valid FlatExpr u64 payload"), 42);

    let expr2 = db.get_expr(2).unwrap();
    assert_eq!(expr2.tag().unwrap(), FlatTag::App);

    let level0 = db.get_level(zero_level_idx).unwrap();
    assert_eq!(level0.tag, FlatLevel::TAG_ZERO);

    // Verify name
    let name = db.get_name(0).unwrap();
    assert_eq!(name, "Nat.add");

    // Verify level list roundtrip
    let levels = db.get_level_list(level_list_idx).unwrap();
    assert_eq!(levels, vec![zero_level_idx]);
}

#[test]
fn test_flat_db_rejects_truncated_expr_table() {
    let mut header = FlatHeader::new(1);
    header.name_table_offset = (FlatHeader::SIZE + FlatExpr::SIZE) as u64;
    header.string_table_offset = header.name_table_offset;
    header.level_table_offset = header.name_table_offset;
    header.level_lists_table_offset = header.name_table_offset;
    let bytes = header.to_bytes().to_vec();
    let err = FlatDb::from_bytes(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::TruncatedData));
}

#[test]
fn test_flat_db_rejects_large_expr_count() {
    let mut header = FlatHeader::new(u32::MAX as u64 + 1);
    header.name_table_offset = FlatHeader::SIZE as u64;
    header.string_table_offset = header.name_table_offset;
    header.level_table_offset = header.name_table_offset;
    header.level_lists_table_offset = header.name_table_offset;
    let bytes = header.to_bytes().to_vec();
    let err = FlatDb::from_bytes(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidHeader(_)));
}

#[test]
fn test_flat_header_rejects_truncated_bytes() {
    let bytes = FlatHeader::new(0).to_bytes();
    let err = FlatHeader::from_bytes(&bytes[..FlatHeader::SIZE - 1]).unwrap_err();
    assert!(matches!(err, FlatError::TruncatedHeader));
}

#[test]
fn test_flat_db_rejects_corrupt_name_offset() {
    let mut builder = FlatBuilder::new();
    builder.add_name("Nat.add");
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let header = FlatHeader::from_bytes(&bytes).unwrap();
    let name_offset = header.name_table_offset as usize;
    bytes[name_offset..name_offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());

    let err = FlatDb::from_bytes(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidHeader(_)));
}

#[test]
fn test_flat_db_rejects_corrupt_string_offset() {
    let mut builder = FlatBuilder::new();
    builder.add_string("hello");
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let header = FlatHeader::from_bytes(&bytes).unwrap();
    let string_offset = header.string_table_offset as usize;
    bytes[string_offset..string_offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());

    let err = FlatDb::from_bytes(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidHeader(_)));
}

#[test]
fn test_flat_db_rejects_name_entry_spilling_into_string_table() {
    let mut builder = FlatBuilder::new();
    builder.add_name("Nat.add");
    builder.add_string("hello");
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let header = FlatHeader::from_bytes(&bytes).unwrap();
    let truncated_name_table_end = header.name_table_offset + 4;
    bytes[24..32].copy_from_slice(&truncated_name_table_end.to_le_bytes());

    let err = FlatDb::from_bytes(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidHeader(_)));
}

#[test]
fn test_flat_db_rejects_string_entry_spilling_into_level_table() {
    let mut builder = FlatBuilder::new();
    builder.add_string("hello");
    builder.add_level(FlatLevel::zero());
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let header = FlatHeader::from_bytes(&bytes).unwrap();
    let truncated_string_table_end = header.string_table_offset + 4;
    bytes[32..40].copy_from_slice(&truncated_string_table_end.to_le_bytes());

    let err = FlatDb::from_bytes(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidHeader(_)));
}

#[test]
fn test_flat_db_get_level_list_handles_truncated_entry() {
    let mut builder = FlatBuilder::new();
    let level_idx = builder.add_level(FlatLevel::zero());
    let list_offset = builder.add_level_list(&[level_idx]);
    assert_ne!(list_offset, u32::MAX);
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let header = FlatHeader::from_bytes(&bytes).unwrap();
    let level_lists_offset = header.level_lists_table_offset as usize;
    let list_byte_offset = level_lists_offset + (list_offset as usize) * 4;
    // Corrupt count: claim 2 elements but only 1 is present in the payload.
    bytes[list_byte_offset..list_byte_offset + 4].copy_from_slice(&2u32.to_le_bytes());

    let db = FlatDb::from_bytes(&bytes).unwrap();
    let err = db.get_level_list(list_offset).unwrap_err();
    assert!(matches!(err, FlatError::IndexOutOfBounds(x) if x == list_offset));
}

#[test]
fn test_flat_db_get_level_handles_truncated_table_entry() {
    let mut builder = FlatBuilder::new();
    builder.add_level(FlatLevel::zero());
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let header = FlatHeader::from_bytes(&bytes).unwrap();
    let truncated_level_lists_offset = header.level_table_offset + 4;
    // Header layout: level_lists_table_offset occupies bytes 40..48.
    bytes[40..48].copy_from_slice(&truncated_level_lists_offset.to_le_bytes());

    let err = FlatDb::from_bytes(&bytes).unwrap_err();
    assert!(matches!(err, FlatError::InvalidHeader(_)));
}

#[test]
fn test_flat_expr_bvar() {
    let expr = FlatExpr::bvar(5);
    assert_eq!(expr.tag().unwrap(), FlatTag::BVar);
    assert_eq!(expr.read_u32(0).expect("valid FlatExpr u32 payload"), 5);
    assert!(expr.flags().contains(FlatFlags::HAS_LOOSE_BVAR));
}

#[test]
fn test_flat_expr_pi() {
    let expr = FlatExpr::pi(1, 100, 200);
    assert_eq!(expr.tag().unwrap(), FlatTag::Pi);
    assert_eq!(expr.data[0], 1); // binder_info
    assert_eq!(expr.read_u32(1).expect("valid FlatExpr u32 payload"), 100); // ty_idx
    assert_eq!(expr.read_u32(5).expect("valid FlatExpr u32 payload"), 200); // body_idx
}

#[test]
fn test_flat_expr_read_helpers_reject_out_of_bounds_offsets() {
    let expr = FlatExpr::lit_nat(42);
    assert!(matches!(expr.read_u32(9), Err(FlatError::TruncatedData)));
    assert!(matches!(expr.read_u64(5), Err(FlatError::TruncatedData)));
    assert!(matches!(expr.read_u16(12), Err(FlatError::TruncatedData)));
}

#[test]
fn test_flat_flags() {
    let flags = FlatFlags::empty()
        .with(FlatFlags::VERIFIED)
        .with(FlatFlags::HAS_FVAR);
    assert!(flags.contains(FlatFlags::VERIFIED));
    assert!(flags.contains(FlatFlags::HAS_FVAR));
    assert!(!flags.contains(FlatFlags::HAS_LOOSE_BVAR));
}

#[test]
fn test_flat_flags_unsupported() {
    let flags = FlatFlags::empty().with(FlatFlags::UNSUPPORTED);
    assert!(flags.contains(FlatFlags::UNSUPPORTED));
    assert!(!flags.contains(FlatFlags::VERIFIED));
}

#[test]
fn test_kernel_expr_conversion() {
    use crate::expr::{BinderInfo, Expr, ExprKind};
    use std::sync::Arc;

    let mut builder = FlatBuilder::new();

    // Create a kernel Expr: λ (x : Nat), x
    let nat_const = Expr::const_str("Nat");
    let bvar0 = Expr::from_kind(ExprKind::BVar(0));
    let lam = Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(nat_const),
        Arc::new(bvar0),
    ));

    // Convert to flat format
    let idx = builder.add_kernel_expr(&lam).unwrap();
    assert_eq!(idx, 2); // 0=Nat, 1=BVar(0), 2=Lam

    // Write and read back
    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let db = FlatDb::from_bytes(&bytes).unwrap();
    assert_eq!(db.expr_count(), 3);

    // Verify the lambda
    let flat_lam = db.get_expr(2).unwrap();
    assert_eq!(flat_lam.tag().unwrap(), FlatTag::Lam);
    assert_eq!(flat_lam.data[0], 0); // binder_info = Default

    // Verify Nat constant
    let nat_name = db.get_name(0).unwrap();
    assert_eq!(nat_name, "Nat");
}

#[test]
fn test_kernel_pi_conversion() {
    use crate::expr::{BinderInfo, Expr, ExprKind};
    use std::sync::Arc;

    let mut builder = FlatBuilder::new();

    // Create: ∀ (x : Type), x
    let type0 = Expr::from_kind(ExprKind::Sort(crate::level::Level::Zero));
    let bvar0 = Expr::from_kind(ExprKind::BVar(0));
    let pi = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Implicit.into(),
        Arc::new(type0),
        Arc::new(bvar0),
    ));

    let idx = builder.add_kernel_expr(&pi).unwrap();

    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let db = FlatDb::from_bytes(&bytes).unwrap();
    let flat_pi = db.get_expr(idx).unwrap();
    assert_eq!(flat_pi.tag().unwrap(), FlatTag::Pi);
    assert_eq!(flat_pi.data[0], 1); // binder_info = Implicit
}

#[test]
fn test_kernel_app_conversion() {
    use crate::expr::{Expr, ExprKind, Literal};
    use crate::BigNat;
    use std::sync::Arc;

    let mut builder = FlatBuilder::new();

    // Create: Nat.add 1 2
    let add = Expr::const_str("Nat.add");
    let one = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(1))));
    let two = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(2))));
    let app1 = Expr::from_kind(ExprKind::App(Arc::new(add), Arc::new(one)));
    let app2 = Expr::from_kind(ExprKind::App(Arc::new(app1), Arc::new(two)));

    let idx = builder.add_kernel_expr(&app2).unwrap();

    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let db = FlatDb::from_bytes(&bytes).unwrap();

    // Verify structure
    let outer_app = db.get_expr(idx).unwrap();
    assert_eq!(outer_app.tag().unwrap(), FlatTag::App);
}

/// Test multi-level universe polymorphism support (#1162).
#[test]
fn test_multi_level_universe_polymorphism() {
    use crate::expr::{Expr, ExprKind};
    use crate::level::Level;
    use crate::name::Name;
    use smallvec::smallvec;

    let mut builder = FlatBuilder::new();

    // Create a constant with multiple universe levels: id.{u, v}
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let id_const = Expr::from_kind(ExprKind::Const(Name::from_string("id"), smallvec![u, v]));

    let idx = builder.add_kernel_expr(&id_const).unwrap();

    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let db = FlatDb::from_bytes(&bytes).unwrap();

    // Get the const expression
    let flat_const = db.get_expr(idx).unwrap();
    assert_eq!(flat_const.tag().unwrap(), FlatTag::Const);

    // Extract level list index from const data
    let levels_list_idx = flat_const.read_u32(4).expect("valid FlatExpr u32 payload");

    // Verify we can read back the level list
    let level_indices = db.get_level_list(levels_list_idx).unwrap();
    assert_eq!(level_indices.len(), 2); // Two universe levels

    // Verify the names are correct
    let name_idx = flat_const.read_u32(0).expect("valid FlatExpr u32 payload");
    assert_eq!(db.get_name(name_idx).unwrap(), "id");
}

/// Test empty level list (no universe polymorphism).
#[test]
fn test_empty_level_list() {
    let mut builder = FlatBuilder::new();

    // Empty level list should return sentinel
    let empty_idx = builder.add_level_list(&[]);
    assert_eq!(empty_idx, u32::MAX);

    // Single level list
    let level_idx = builder.add_level(FlatLevel::zero());
    let single_idx = builder.add_level_list(&[level_idx]);
    assert_ne!(single_idx, u32::MAX);

    let mut bytes = Vec::new();
    builder.write_to(&mut bytes).unwrap();

    let db = FlatDb::from_bytes(&bytes).unwrap();

    // Empty list should return empty vec
    let empty_levels = db.get_level_list(u32::MAX).unwrap();
    assert!(empty_levels.is_empty());

    // Single level should roundtrip
    let single_levels = db.get_level_list(single_idx).unwrap();
    assert_eq!(single_levels, vec![level_idx]);
}

proptest! {
    #[test]
    fn prop_flat_builder_roundtrip(bytes in proptest::collection::vec(any::<u8>(), 1..200)) {
        let builder = build_builder_from_bytes(&bytes);
        let mut flat_bytes = Vec::new();
        builder.write_to(&mut flat_bytes).unwrap();

        let db = FlatDb::from_bytes(&flat_bytes).unwrap();
        assert_eq!(db.expr_count(), builder.exprs.len() as u64);

        for (idx, original) in builder.exprs.iter().enumerate() {
            let roundtrip = db.get_expr(idx as u32).unwrap();
            let orig_bytes = flat_expr_bytes(original);
            let roundtrip_bytes = flat_expr_bytes(&roundtrip);
            assert_eq!(orig_bytes, roundtrip_bytes);
        }

        for (idx, name) in builder.names.iter().enumerate() {
            assert_eq!(db.get_name(idx as u32).unwrap(), name);
        }
        for (idx, string) in builder.strings.iter().enumerate() {
            assert_eq!(db.get_string(idx as u32).unwrap(), string);
        }

        let header = FlatHeader::from_bytes(&flat_bytes).unwrap();
        let level_offset = header.level_table_offset as usize;
        let level_lists_offset = header.level_lists_table_offset as usize;
        // Level table size is from level_table_offset to level_lists_table_offset
        let level_bytes = level_lists_offset.saturating_sub(level_offset);
        assert_eq!(level_bytes % FlatLevel::SIZE, 0);
        let level_count = level_bytes / FlatLevel::SIZE;
        assert_eq!(level_count, builder.levels.len());
        for (idx, level) in builder.levels.iter().enumerate() {
            let start = level_offset + idx * FlatLevel::SIZE;
            let end = start + FlatLevel::SIZE;
            let level_slice = &flat_bytes[start..end];
            assert_eq!(level_slice, flat_level_bytes(level).as_slice());
        }

        // Verify level lists table
        let level_lists_bytes = flat_bytes.len().saturating_sub(level_lists_offset);
        assert_eq!(level_lists_bytes % 4, 0);
        let level_lists_count = level_lists_bytes / 4;
        assert_eq!(level_lists_count, builder.level_lists.len());
    }
}

/// Miri tests for runtime memory safety verification.
///
/// These tests exercise flat codec and DB access paths under Miri to detect:
/// - Uninitialized memory reads
/// - Invalid memory accesses
/// - Alignment violations
/// - Out-of-bounds accesses
///
/// Run with: `cargo +nightly miri test flat::tests::miri_`
///
/// All 7 tests pass under Miri, verifying no UB in flat serialization paths.
mod miri_tests {
    use super::*;

    /// Test FlatExpr serialization via explicit byte codec.
    #[test]
    fn miri_flatexpr_serialize() {
        let exprs = [
            FlatExpr::bvar(0),
            FlatExpr::bvar(u32::MAX),
            FlatExpr::sort(1),
            FlatExpr::const_ref(0, 0),
            FlatExpr::app(0, 1),
            FlatExpr::lam(0, 0, 1),
            FlatExpr::pi(3, 2, 3),
            FlatExpr::let_expr(0, 1, 2),
            FlatExpr::lit_nat(0),
            FlatExpr::lit_nat(u64::MAX),
            FlatExpr::lit_str(0),
            FlatExpr::proj(0, 0, 0),
            FlatExpr::fvar(12345),
        ];

        for expr in &exprs {
            let bytes = flat_expr_bytes(expr);
            assert_eq!(bytes.len(), FlatExpr::SIZE);

            // Verify all bytes are accessible (Miri catches uninitialized reads)
            let _sum: u64 = bytes.iter().map(|&b| b as u64).sum();
        }
    }

    /// Test FlatLevel serialization via explicit byte codec.
    #[test]
    fn miri_flatlevel_serialize() {
        let levels = [
            FlatLevel::zero(),
            FlatLevel::succ(0),
            FlatLevel::succ(u32::MAX),
            FlatLevel::max(0, 1),
            FlatLevel::max(u32::MAX, u32::MAX),
            FlatLevel::max(0, 0),
            FlatLevel::param(0),
            FlatLevel::param(u32::MAX),
        ];

        for level in &levels {
            let bytes = flat_level_bytes(level);
            assert_eq!(bytes.len(), FlatLevel::SIZE);

            // Verify all bytes are accessible
            let _sum: u64 = bytes.iter().map(|&b| b as u64).sum();
        }
    }

    /// Test FlatExpr deserialization via checked decode path.
    #[test]
    fn miri_flatexpr_deserialize() {
        let mut builder = FlatBuilder::new();
        builder.add_name("test");
        builder.add_string("str");
        builder.add_level(FlatLevel::zero());

        // Add various expression types
        builder.add_expr(FlatExpr::bvar(0));
        builder.add_expr(FlatExpr::sort(0));
        builder.add_expr(FlatExpr::const_ref(0, 0));
        builder.add_expr(FlatExpr::app(0, 1));
        builder.add_expr(FlatExpr::lam(0, 0, 1));
        builder.add_expr(FlatExpr::pi(1, 2, 3));
        builder.add_expr(FlatExpr::let_expr(0, 1, 2));
        builder.add_expr(FlatExpr::lit_nat(42));
        builder.add_expr(FlatExpr::lit_str(0));
        builder.add_expr(FlatExpr::proj(0, 5, 0));
        builder.add_expr(FlatExpr::fvar(999));

        let mut bytes = Vec::new();
        builder.write_to(&mut bytes).unwrap();

        let db = FlatDb::from_bytes(&bytes).unwrap();
        for i in 0..db.expr_count() as u32 {
            let expr = db.get_expr(i).unwrap();
            // Access all fields to ensure Miri validates decode/read behavior
            let _ = expr.tag();
            let _ = expr.flags();
            let _ = expr.read_u32(0).expect("valid FlatExpr u32 payload");
            let _ = expr.read_u64(0).expect("valid FlatExpr u64 payload");
        }
    }

    /// Test roundtrip: serialize then deserialize (exercises both paths).
    #[test]
    fn miri_flatexpr_roundtrip() {
        let original = FlatExpr::app(100, 200);

        // Serialize
        let bytes = flat_expr_bytes(&original);

        // Create a database with this expression
        let mut builder = FlatBuilder::new();
        builder.add_expr(original);
        let mut db_bytes = Vec::new();
        builder.write_to(&mut db_bytes).unwrap();

        // Deserialize
        let db = FlatDb::from_bytes(&db_bytes).unwrap();
        let roundtrip = db.get_expr(0).unwrap();

        // Verify identity
        assert_eq!(original.tag, roundtrip.tag);
        assert_eq!(original.flags, roundtrip.flags);
        assert_eq!(bytes, flat_expr_bytes(&roundtrip));
    }

    /// Test FlatLevel roundtrip.
    #[test]
    fn miri_flatlevel_roundtrip() {
        let levels = [
            FlatLevel::zero(),
            FlatLevel::succ(42),
            FlatLevel::max(1, 2),
            FlatLevel::max(3, 4),
            FlatLevel::param(5),
        ];

        let mut builder = FlatBuilder::new();
        for level in &levels {
            builder.add_level(*level);
        }

        let mut db_bytes = Vec::new();
        builder.write_to(&mut db_bytes).unwrap();

        // Verify level table is correctly written and readable
        let header = FlatHeader::from_bytes(&db_bytes).unwrap();
        let level_offset = header.level_table_offset as usize;

        for (i, original) in levels.iter().enumerate() {
            let start = level_offset + i * FlatLevel::SIZE;
            let end = start + FlatLevel::SIZE;
            let level_bytes = &db_bytes[start..end];
            assert_eq!(level_bytes, flat_level_bytes(original));
        }
    }

    /// Test with many expressions to stress alignment.
    #[test]
    fn miri_flatexpr_alignment_stress() {
        let mut builder = FlatBuilder::new();
        builder.add_name("n");
        builder.add_string("s");
        builder.add_level(FlatLevel::zero());

        // Add 100 expressions to stress alignment
        for i in 0..100u32 {
            builder.add_expr(FlatExpr::lit_nat(i as u64));
        }

        let mut bytes = Vec::new();
        builder.write_to(&mut bytes).unwrap();

        let db = FlatDb::from_bytes(&bytes).unwrap();
        assert_eq!(db.expr_count(), 100);

        // Access all expressions to verify alignment
        for i in 0..100u32 {
            let expr = db.get_expr(i).unwrap();
            assert_eq!(expr.tag().unwrap(), FlatTag::LitNat);
            assert_eq!(
                expr.read_u64(0).expect("valid FlatExpr u64 payload"),
                i as u64
            );
        }
    }

    /// Test boundary conditions for index access.
    #[test]
    fn miri_flatexpr_boundary_access() {
        let mut builder = FlatBuilder::new();
        builder.add_name("name");
        builder.add_string("string");
        builder.add_level(FlatLevel::zero());
        builder.add_expr(FlatExpr::bvar(0));

        let mut bytes = Vec::new();
        builder.write_to(&mut bytes).unwrap();

        let db = FlatDb::from_bytes(&bytes).unwrap();

        // Valid access
        let expr = db.get_expr(0).expect("Index 0 should be valid");
        assert_eq!(
            expr.tag().unwrap(),
            FlatTag::BVar,
            "Expected BVar tag for bvar(0)"
        );

        // Invalid access (out of bounds)
        let err1 = db.get_expr(1).unwrap_err();
        assert!(
            matches!(err1, FlatError::IndexOutOfBounds(1)),
            "Index 1 should give IndexOutOfBounds, got: {err1}"
        );
        let err_max = db.get_expr(u32::MAX).unwrap_err();
        assert!(
            matches!(err_max, FlatError::IndexOutOfBounds(u32::MAX)),
            "Index u32::MAX should give IndexOutOfBounds, got: {err_max}"
        );
    }

    /// Verify that the pointer-keyed memo in add_kernel_expr correctly deduplicates
    /// shared sub-expressions. When the same Arc<Expr> appears in multiple positions,
    /// the memo ensures each sub-expression is converted exactly once.
    /// Exercises the *const Expr HashMap key invariant (see convert.rs:26).
    #[test]
    fn test_add_kernel_expr_shared_subexpr_memo_dedup() {
        use crate::expr::{BinderInfo, Expr, ExprKind};
        use std::sync::Arc;

        let mut builder = FlatBuilder::new();

        // Create a shared sub-expression via Arc
        let shared_ty: Arc<Expr> = Arc::new(Expr::const_str("Nat"));

        // Build two lambda expressions that share the SAME type Arc:
        //   λ (x : Nat), x
        //   λ (y : Nat), y
        // Both reference the identical Arc<Expr> for "Nat".
        let bvar0 = Arc::new(Expr::from_kind(ExprKind::BVar(0)));
        let lam1 = Expr::from_kind(ExprKind::Lam(
            BinderInfo::Default.into(),
            Arc::clone(&shared_ty),
            Arc::clone(&bvar0),
        ));
        let lam2 = Expr::from_kind(ExprKind::Lam(
            BinderInfo::Default.into(),
            Arc::clone(&shared_ty),
            Arc::clone(&bvar0),
        ));

        // Build App(lam1, lam2) so both lambdas are in the same expression tree
        let app = Expr::from_kind(ExprKind::App(Arc::new(lam1), Arc::new(lam2)));

        let idx = builder.add_kernel_expr(&app).unwrap();

        let mut bytes = Vec::new();
        builder.write_to(&mut bytes).unwrap();
        let db = FlatDb::from_bytes(&bytes).unwrap();

        // The App should be the last expression added
        let flat_app = db.get_expr(idx).unwrap();
        assert_eq!(flat_app.tag().unwrap(), FlatTag::App);

        // Both lam1 and lam2 share the same Arc<Expr> for Nat and BVar(0), and
        // are themselves structurally identical. The content dedup
        // (`add_expr_dedup` hash-consing) collapses them: Nat, BVar(0), one
        // Lam record, one App record = 4 total. This is the canonicality
        // property `expr_canonical_digest` depends on — the encoding must be
        // invariant under Arc-sharing topology, so structurally identical
        // records collapse regardless of how they were built.
        // (Pointer-memo-only granularity gave 5; no dedup at all gave 7.)
        assert_eq!(
            db.expr_count(),
            4,
            "Structurally identical sub-expressions should be hash-consed"
        );
    }
}
