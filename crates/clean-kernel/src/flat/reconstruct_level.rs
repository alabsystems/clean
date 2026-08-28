// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Level reconstruction from the flat format back to kernel `Level`.
//!
//! Split out of `reconstruct.rs`: the universe-level half of the reverse of
//! `convert.rs`. Levels form their own arena in a `FlatDb` and are rebuilt in
//! one bottom-up pass BEFORE any expression is rebuilt, because `Sort` and
//! `Const` nodes index into the finished level table. `reconstruct.rs` owns
//! the expression half and calls `reconstruct_all_levels` first.

use crate::level::Level;
use crate::name::Name;

use super::db::FlatDb;
use super::error::FlatError;
use super::types::FlatLevel;

/// Reconstruct a single level from a FlatDb (with pre-built level memo).
///
/// For cases where only one level is needed without building the full table.
pub fn reconstruct_level(db: &FlatDb<'_>, idx: u32) -> Result<Level, FlatError> {
    let levels = reconstruct_all_levels(db)?;
    levels
        .into_iter()
        .nth(idx as usize)
        .ok_or(FlatError::IndexOutOfBounds(idx))
}

/// Reconstruct all levels from a FlatDb into kernel Level values.
///
/// Returns a Vec indexed by flat level index.
pub(super) fn reconstruct_all_levels(db: &FlatDb<'_>) -> Result<Vec<Level>, FlatError> {
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
    db: &FlatDb<'_>,
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
