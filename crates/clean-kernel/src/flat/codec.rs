// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Explicit wire codec for flat expressions and levels.

use super::error::FlatError;
use super::types::{FlatExpr, FlatLevel, FlatTag};

/// Encode a flat expression into its 16-byte wire representation.
#[inline]
pub(crate) fn encode_flatexpr(expr: &FlatExpr) -> [u8; FlatExpr::SIZE] {
    let mut bytes = [0u8; FlatExpr::SIZE];
    bytes[0] = expr.tag;
    bytes[1] = expr.flags;
    bytes[2] = expr._pad[0];
    bytes[3] = expr._pad[1];
    bytes[4..].copy_from_slice(&expr.data);
    bytes
}

/// Decode a flat expression from 16 wire bytes.
#[inline]
pub(crate) fn decode_flatexpr(bytes: &[u8; FlatExpr::SIZE]) -> Result<FlatExpr, FlatError> {
    let tag = bytes[0];
    FlatTag::try_from(tag)?;

    let mut data = [0u8; 12];
    data.copy_from_slice(&bytes[4..]);

    Ok(FlatExpr {
        tag,
        flags: bytes[1],
        _pad: [bytes[2], bytes[3]],
        data,
    })
}

/// Encode a flat level into its 12-byte wire representation.
#[inline]
pub(crate) fn encode_flatlevel(level: &FlatLevel) -> [u8; FlatLevel::SIZE] {
    let mut bytes = [0u8; FlatLevel::SIZE];
    bytes[0] = level.tag;
    bytes[1] = level._pad[0];
    bytes[2] = level._pad[1];
    bytes[3] = level._pad[2];
    bytes[4..].copy_from_slice(&level.data);
    bytes
}

/// Decode a flat level from 12 wire bytes.
#[inline]
pub(crate) fn decode_flatlevel(bytes: &[u8; FlatLevel::SIZE]) -> Result<FlatLevel, FlatError> {
    let tag = bytes[0];
    if !matches!(
        tag,
        FlatLevel::TAG_ZERO
            | FlatLevel::TAG_SUCC
            | FlatLevel::TAG_MAX
            | FlatLevel::TAG_IMAX
            | FlatLevel::TAG_PARAM
    ) {
        return Err(FlatError::InvalidHeader(format!(
            "invalid level tag in level table: {tag}"
        )));
    }

    let mut data = [0u8; 8];
    data.copy_from_slice(&bytes[4..]);

    Ok(FlatLevel {
        tag,
        _pad: [bytes[1], bytes[2], bytes[3]],
        data,
    })
}
