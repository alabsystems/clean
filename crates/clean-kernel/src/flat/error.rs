// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Flat format error types.

use std::io;

/// Errors from flat format operations.
#[derive(Clone, Debug, thiserror::Error)]
#[non_exhaustive]
pub enum FlatError {
    /// Invalid magic number in header.
    #[error("invalid magic number (expected L5FM)")]
    InvalidMagic,
    /// Unsupported format version.
    #[error("unsupported format version: {0}")]
    UnsupportedVersion(u32),
    /// Header is truncated.
    #[error("truncated header")]
    TruncatedHeader,
    /// Header fields are inconsistent or unsupported.
    #[error("invalid header: {0}")]
    InvalidHeader(String),
    /// Data is shorter than the header declares.
    #[error("truncated data")]
    TruncatedData,
    /// Invalid expression tag.
    #[error("invalid expression tag: {0}")]
    InvalidTag(u8),
    /// Expression index out of bounds.
    #[error("expression index out of bounds: {0}")]
    IndexOutOfBounds(u32),
    /// I/O error.
    #[error("I/O error: {0}")]
    Io(String),
    /// BigNat literal exceeds u64::MAX (flat format only supports u64 literals).
    #[error("BigNat literal exceeds u64::MAX (flat format limitation)")]
    UnsupportedBigNat,
    /// Expression was stored with UNSUPPORTED flag (cubical, ZFC, SProp mode extension).
    #[error("unsupported expression (mode extension not representable in flat format)")]
    UnsupportedExpression,
}

impl From<io::Error> for FlatError {
    fn from(e: io::Error) -> Self {
        FlatError::Io(e.to_string())
    }
}
