// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reconstruction from flat format back to kernel Expr/Level.
//!
//! This is the reverse of `convert.rs` (Expr → FlatExpr). Given a `FlatDb`,
//! it reconstructs kernel `Expr` trees from the flat arena representation.
//!
//! # Algorithm
//!
//! Bottom-up iterative pass: for each flat index 0..N, look up already-
//! reconstructed children from a memo table, build the kernel Expr, store it.
//! This avoids recursion and handles arbitrarily deep expression trees.
//!
//! # Information loss
//!
//! The forward conversion (convert.rs) deliberately drops:
//! - Let binder names → reconstructed as `Name::anon()`
//! - Let nonDep flag → reconstructed as `false`
//! - Multiplicity → reconstructed as `Multiplicity::Many` (via BinderInfo→BinderData)
//! - MData wrappers → not recoverable (transparent in forward direction)
//! - Mode extensions (cubical, ZFC, SProp) → flagged UNSUPPORTED, returns error

use crate::expr::{BigNat, BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

use super::db::FlatDb;
use super::error::FlatError;
use super::types::{FlatExpr, FlatFlags, FlatLevel, FlatTag};

/// Reconstruct a single expression from a FlatDb.
///
/// Reconstructs the expression at `idx` and all of its transitive
/// dependencies. For batch reconstruction, use `reconstruct_all_exprs`.
pub fn reconstruct_expr(db: &FlatDb, idx: u32) -> Result<Expr, FlatError> {
    let levels = reconstruct_all_levels(db)?;
    let count = db.expr_count() as u32;

    let limit = idx.checked_add(1).ok_or(FlatError::IndexOutOfBounds(idx))?;
    if limit > count {
        return Err(FlatError::IndexOutOfBounds(idx));
    }

    let mut exprs: Vec<Option<Expr>> = vec![None; limit as usize];

    for i in 0..limit {
        let flat_expr = db.get_expr(i)?;
        let expr = reconstruct_single_expr(db, &flat_expr, &levels, &exprs)?;
        exprs[i as usize] = Some(expr);
    }

    exprs[idx as usize]
        .clone()
        .ok_or(FlatError::IndexOutOfBounds(idx))
}

/// Reconstruct all expressions from a FlatDb.
///
/// Returns a Vec indexed by flat expression index, where each entry is
/// the corresponding kernel Expr.
pub fn reconstruct_all_exprs(db: &FlatDb) -> Result<Vec<Expr>, FlatError> {
    let levels = reconstruct_all_levels(db)?;
    let count = db.expr_count() as u32;
    let mut exprs: Vec<Option<Expr>> = vec![None; count as usize];

    for i in 0..count {
        let flat_expr = db.get_expr(i)?;
        let expr = reconstruct_single_expr(db, &flat_expr, &levels, &exprs)?;
        exprs[i as usize] = Some(expr);
    }

    exprs
        .into_iter()
        .enumerate()
        .map(|(i, opt)| opt.ok_or(FlatError::IndexOutOfBounds(i as u32)))
        .collect()
}

/// Reconstruct a single level from a FlatDb (with pre-built level memo).
///
/// For cases where only one level is needed without building the full table.
pub fn reconstruct_level(db: &FlatDb, idx: u32) -> Result<Level, FlatError> {
    let levels = reconstruct_all_levels(db)?;
    levels
        .into_iter()
        .nth(idx as usize)
        .ok_or(FlatError::IndexOutOfBounds(idx))
}

/// Reconstruct all levels from a FlatDb into kernel Level values.
///
/// Returns a Vec indexed by flat level index.
fn reconstruct_all_levels(db: &FlatDb) -> Result<Vec<Level>, FlatError> {
    let count = db.level_count();
    let mut levels: Vec<Option<Level>> = vec![None; count as usize];

    for i in 0..count {
        let flat_level = db.get_level(i)?;
        let level = reconstruct_single_level(db, &flat_level, &levels)?;
        levels[i as usize] = Some(level);
    }

    levels
        .into_iter()
        .enumerate()
        .map(|(i, opt)| opt.ok_or(FlatError::IndexOutOfBounds(i as u32)))
        .collect()
}

/// Reconstruct a single FlatLevel into a kernel Level.
fn reconstruct_single_level(
    db: &FlatDb,
    flat: &FlatLevel,
    levels: &[Option<Level>],
) -> Result<Level, FlatError> {
    match flat.tag {
        FlatLevel::TAG_ZERO => Ok(Level::zero()),

        FlatLevel::TAG_SUCC => {
            let inner_idx = read_level_u32(flat, 0);
            let inner = get_level(levels, inner_idx)?;
            Ok(Level::succ(inner))
        }

        FlatLevel::TAG_MAX => {
            let left_idx = read_level_u32(flat, 0);
            let right_idx = read_level_u32(flat, 4);
            let left = get_level(levels, left_idx)?;
            let right = get_level(levels, right_idx)?;
            Ok(Level::max(left, right))
        }

        FlatLevel::TAG_IMAX => {
            let left_idx = read_level_u32(flat, 0);
            let right_idx = read_level_u32(flat, 4);
            let left = get_level(levels, left_idx)?;
            let right = get_level(levels, right_idx)?;
            Ok(Level::imax(left, right))
        }

        FlatLevel::TAG_PARAM => {
            let name_idx = read_level_u32(flat, 0);
            let name_str = db.get_name(name_idx)?;
            Ok(Level::param(Name::from_string(name_str)))
        }

        _ => Err(FlatError::InvalidTag(flat.tag)),
    }
}

/// Reconstruct a single FlatExpr into a kernel Expr.
fn reconstruct_single_expr(
    db: &FlatDb,
    flat: &FlatExpr,
    levels: &[Level],
    exprs: &[Option<Expr>],
) -> Result<Expr, FlatError> {
    if flat.flags().contains(FlatFlags::UNSUPPORTED) {
        return Err(FlatError::UnsupportedExpression);
    }

    match flat.tag()? {
        FlatTag::BVar => {
            let idx = flat.read_u32(0)?;
            Ok(Expr::bvar(idx))
        }

        FlatTag::Sort => {
            let level_idx = flat.read_u32(0)?;
            let level = levels
                .get(level_idx as usize)
                .ok_or(FlatError::IndexOutOfBounds(level_idx))?
                .clone();
            Ok(Expr::sort(level))
        }

        FlatTag::Const => {
            let name_idx = flat.read_u32(0)?;
            let levels_list_idx = flat.read_u32(4)?;
            let name_str = db.get_name(name_idx)?;
            let name = Name::from_string(name_str);
            let level_indices = db.get_level_list(levels_list_idx)?;
            let lvls: Vec<Level> = level_indices
                .iter()
                .map(|&li| {
                    levels
                        .get(li as usize)
                        .ok_or(FlatError::IndexOutOfBounds(li))
                        .cloned()
                })
                .collect::<Result<_, _>>()?;
            Ok(Expr::const_(name, lvls))
        }

        FlatTag::App => {
            let fn_idx = flat.read_u32(0)?;
            let arg_idx = flat.read_u32(4)?;
            let func = get_expr(exprs, fn_idx)?;
            let arg = get_expr(exprs, arg_idx)?;
            Ok(Expr::app(func, arg))
        }

        FlatTag::Lam => {
            let binder_info_u8 = flat.data[0];
            let ty_idx = flat.read_u32(1)?;
            let body_idx = flat.read_u32(5)?;
            let bi = u8_to_binder_info(binder_info_u8)?;
            let ty = get_expr(exprs, ty_idx)?;
            let body = get_expr(exprs, body_idx)?;
            Ok(Expr::lam(bi, ty, body))
        }

        FlatTag::Pi => {
            let binder_info_u8 = flat.data[0];
            let ty_idx = flat.read_u32(1)?;
            let body_idx = flat.read_u32(5)?;
            let bi = u8_to_binder_info(binder_info_u8)?;
            let ty = get_expr(exprs, ty_idx)?;
            let body = get_expr(exprs, body_idx)?;
            Ok(Expr::pi(bi, ty, body))
        }

        FlatTag::Let => {
            let ty_idx = flat.read_u32(0)?;
            let val_idx = flat.read_u32(4)?;
            let body_idx = flat.read_u32(8)?;
            let ty = get_expr(exprs, ty_idx)?;
            let val = get_expr(exprs, val_idx)?;
            let body = get_expr(exprs, body_idx)?;
            // Name and nonDep are lost in flat format
            Ok(Expr::let_named(Name::anon(), ty, val, body, false))
        }

        FlatTag::LitNat => {
            if flat.flags().contains(super::types::FlatFlags::NAT_BIG) {
                // BigNat > u64: data[0..4] is a string index to the comma-joined
                // decimal little-endian u64 limbs (see flat::convert).
                let str_idx = flat.read_u32(0)?;
                let s = db.get_string(str_idx)?;
                Ok(Expr::bignat_lit(parse_bignat_limbs(s)?))
            } else {
                let value = flat.read_u64(0)?;
                Ok(Expr::nat_lit(value))
            }
        }

        FlatTag::LitStr => {
            let str_idx = flat.read_u32(0)?;
            let s = db.get_string(str_idx)?;
            Ok(Expr::str_lit(s))
        }

        FlatTag::Proj => {
            let name_idx = flat.read_u32(0)?;
            let field = flat.read_u16(4)?;
            let expr_idx = flat.read_u32(6)?;
            let name_str = db.get_name(name_idx)?;
            let name = Name::from_string(name_str);
            let inner = get_expr(exprs, expr_idx)?;
            Ok(Expr::proj(name, field as u32, inner))
        }

        FlatTag::FVar => {
            let id = flat.read_u64(0)?;
            Ok(Expr::fvar(FVarId(id)))
        }
    }
}

/// Get an already-reconstructed expression from the memo table.
fn get_expr(exprs: &[Option<Expr>], idx: u32) -> Result<Expr, FlatError> {
    exprs
        .get(idx as usize)
        .and_then(|opt| opt.clone())
        .ok_or(FlatError::IndexOutOfBounds(idx))
}

/// Parse the NAT_BIG limb string (`"limb0,limb1,..."`, decimal little-endian
/// u64 limbs) written by `flat::convert` back into a `BigNat`.
pub(crate) fn parse_bignat_limbs(s: &str) -> Result<BigNat, FlatError> {
    let mut limbs = Vec::new();
    for part in s.split(',') {
        let limb = part.parse::<u64>().map_err(|_| {
            FlatError::InvalidHeader(format!("invalid BigNat limb {part:?} in NAT_BIG literal"))
        })?;
        limbs.push(limb);
    }
    Ok(BigNat::from_limbs(limbs))
}

/// Get an already-reconstructed level from the memo table.
fn get_level(levels: &[Option<Level>], idx: u32) -> Result<Level, FlatError> {
    levels
        .get(idx as usize)
        .and_then(|opt| opt.clone())
        .ok_or(FlatError::IndexOutOfBounds(idx))
}

/// Read a u32 from FlatLevel data at the given byte offset.
#[inline]
fn read_level_u32(flat: &FlatLevel, offset: usize) -> u32 {
    u32::from_le_bytes([
        flat.data[offset],
        flat.data[offset + 1],
        flat.data[offset + 2],
        flat.data[offset + 3],
    ])
}

/// Convert u8 back to BinderInfo (reverse of binder_info_to_u8 in convert.rs).
fn u8_to_binder_info(b: u8) -> Result<BinderInfo, FlatError> {
    match b {
        0 => Ok(BinderInfo::Default),
        1 => Ok(BinderInfo::Implicit),
        2 => Ok(BinderInfo::StrictImplicit),
        3 => Ok(BinderInfo::InstImplicit),
        _ => Err(FlatError::InvalidTag(b)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flat::builder::FlatBuilder;

    /// Round-trip test: Expr → FlatBuilder → bytes → FlatDb → reconstruct_expr
    #[test]
    fn test_roundtrip_bvar() {
        let original = Expr::bvar(42);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert_eq!(format!("{:?}", original), format!("{:?}", reconstructed));
    }

    #[test]
    fn test_roundtrip_sort_zero() {
        let original = Expr::sort(Level::zero());
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_sort());
    }

    #[test]
    fn test_roundtrip_sort_succ() {
        let original = Expr::sort(Level::succ(Level::zero()));
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_sort());
    }

    #[test]
    fn test_roundtrip_const() {
        let original = Expr::const_(
            Name::from_string("Nat.add"),
            vec![Level::param(Name::from_string("u"))],
        );
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_const());
    }

    #[test]
    fn test_roundtrip_app() {
        let f = Expr::const_str("Nat.succ");
        let a = Expr::bvar(0);
        let original = Expr::app(f, a);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_app());
    }

    #[test]
    fn test_roundtrip_lam() {
        let ty = Expr::const_str("Nat");
        let body = Expr::bvar(0);
        let original = Expr::lam(BinderInfo::Default, ty, body);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_lam());
    }

    #[test]
    fn test_roundtrip_pi() {
        let ty = Expr::const_str("Nat");
        let body = Expr::const_str("Bool");
        let original = Expr::pi(BinderInfo::Implicit, ty, body);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_pi());
    }

    #[test]
    fn test_roundtrip_let() {
        let ty = Expr::const_str("Nat");
        let val = Expr::nat_lit(42);
        let body = Expr::bvar(0);
        let original = Expr::let_named(Name::anon(), ty, val, body, false);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_let());
    }

    #[test]
    fn test_roundtrip_nat_lit() {
        let original = Expr::nat_lit(12345);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_lit());
    }

    #[test]
    fn test_roundtrip_str_lit() {
        let original = Expr::str_lit("hello world");
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_lit());
    }

    #[test]
    fn test_roundtrip_proj() {
        let inner = Expr::bvar(0);
        let original = Expr::proj(Name::from_string("Prod"), 1, inner);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_proj());
    }

    #[test]
    fn test_roundtrip_complex_expr() {
        // λ (n : Nat), Nat.succ n
        let nat = Expr::const_str("Nat");
        let succ = Expr::const_str("Nat.succ");
        let body = Expr::app(succ, Expr::bvar(0));
        let original = Expr::lam(BinderInfo::Default, nat, body);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_lam());
    }

    #[test]
    fn test_roundtrip_universe_polymorphic() {
        // List.{u} where u is a universe parameter
        let u = Level::param(Name::from_string("u"));
        let original = Expr::const_(Name::from_string("List"), vec![u]);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_const());
    }

    #[test]
    fn test_roundtrip_level_max() {
        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));
        let max_uv = Level::max(u, v);
        let original = Expr::sort(max_uv);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        assert!(reconstructed.is_sort());
    }

    #[test]
    fn test_roundtrip_level_imax() {
        let u = Level::param(Name::from_string("u"));
        let imax = Level::imax(u, Level::zero());
        let original = Expr::sort(imax);
        let (bytes, idx) = build_flat_bytes(&original);
        let db = FlatDb::from_bytes(&bytes).unwrap();
        let reconstructed = reconstruct_expr(&db, idx).unwrap();
        // imax(u, 0) = 0, so this becomes Sort(0)
        assert!(reconstructed.is_sort());
    }

    #[test]
    fn test_reconstruct_all_exprs() {
        let nat = Expr::const_str("Nat");
        let succ = Expr::const_str("Nat.succ");
        let body = Expr::app(succ, Expr::bvar(0));
        let lam = Expr::lam(BinderInfo::Default, nat, body);

        let mut builder = FlatBuilder::new();
        let _ = builder.add_kernel_expr(&lam).unwrap();
        let mut bytes = Vec::new();
        builder.write_to(&mut bytes).unwrap();
        let db = FlatDb::from_bytes(&bytes).unwrap();

        let all = reconstruct_all_exprs(&db).unwrap();
        assert!(!all.is_empty());
        // Last expression should be the lambda
        assert!(all.last().unwrap().is_lam());
    }

    /// Helper: build flat bytes from an Expr and return (bytes, root_idx).
    fn build_flat_bytes(expr: &Expr) -> (Vec<u8>, u32) {
        let mut builder = FlatBuilder::new();
        let idx = builder.add_kernel_expr(expr).unwrap();
        let mut bytes = Vec::new();
        builder.write_to(&mut bytes).unwrap();
        (bytes, idx)
    }
}
