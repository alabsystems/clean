// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Flat file header format.

use super::error::FlatError;
use super::types::FlatExpr;

/// Flat file header (64 bytes).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct FlatHeader {
    /// Magic number: "L5FM" (clean Flat Mmap)
    pub magic: [u8; 4],
    /// Format version
    pub version: u32,
    /// Number of expressions
    pub expr_count: u64,
    /// Offset to name table
    pub name_table_offset: u64,
    /// Offset to string table
    pub string_table_offset: u64,
    /// Offset to level table
    pub level_table_offset: u64,
    /// Offset to level lists table (for multi-level universe polymorphism, #1162)
    pub level_lists_table_offset: u64,
    /// Number of names in name table (v3+, #1583)
    pub name_count: u32,
    /// Number of strings in string table (v3+, #1583)
    pub string_count: u32,
    /// Reserved for future use
    _reserved: [u8; 8],
}

impl FlatHeader {
    /// Magic bytes for clean flat format.
    pub const MAGIC: [u8; 4] = *b"L5FM";
    /// Current format version (v3 adds name_count/string_count + offset tables for O(1) lookup, #1583).
    pub const VERSION: u32 = 3;
    /// Header size in bytes.
    pub const SIZE: usize = 64;

    /// Create a new header.
    pub fn new(expr_count: u64) -> Self {
        Self {
            magic: Self::MAGIC,
            version: Self::VERSION,
            expr_count,
            name_table_offset: Self::SIZE as u64 + (expr_count * FlatExpr::SIZE as u64),
            string_table_offset: 0,      // Set later
            level_table_offset: 0,       // Set later
            level_lists_table_offset: 0, // Set later
            name_count: 0,               // Set later
            string_count: 0,             // Set later
            _reserved: [0; 8],
        }
    }

    /// Validate the header.
    ///
    /// # Contract
    ///
    /// REQUIRES: Header bytes are properly formatted
    /// ENSURES: Ok(()) iff magic == MAGIC && version == VERSION
    pub fn validate(&self) -> Result<(), FlatError> {
        if self.magic != Self::MAGIC {
            return Err(FlatError::InvalidMagic);
        }
        if self.version != Self::VERSION {
            return Err(FlatError::UnsupportedVersion(self.version));
        }
        Ok(())
    }

    /// Write header to bytes.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut bytes = [0u8; Self::SIZE];
        bytes[0..4].copy_from_slice(&self.magic);
        bytes[4..8].copy_from_slice(&self.version.to_le_bytes());
        bytes[8..16].copy_from_slice(&self.expr_count.to_le_bytes());
        bytes[16..24].copy_from_slice(&self.name_table_offset.to_le_bytes());
        bytes[24..32].copy_from_slice(&self.string_table_offset.to_le_bytes());
        bytes[32..40].copy_from_slice(&self.level_table_offset.to_le_bytes());
        bytes[40..48].copy_from_slice(&self.level_lists_table_offset.to_le_bytes());
        bytes[48..52].copy_from_slice(&self.name_count.to_le_bytes());
        bytes[52..56].copy_from_slice(&self.string_count.to_le_bytes());
        bytes
    }

    /// Read header from bytes.
    ///
    /// # Contract
    ///
    /// REQUIRES: `bytes.len() >= FlatHeader::SIZE`
    /// ENSURES: Ok(result) where result.magic == MAGIC && result.version == VERSION
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, FlatError> {
        if bytes.len() < Self::SIZE {
            return Err(FlatError::TruncatedHeader);
        }
        let header = Self {
            magic: Self::read_fixed::<4>(bytes, 0)?,
            version: u32::from_le_bytes(Self::read_fixed::<4>(bytes, 4)?),
            expr_count: u64::from_le_bytes(Self::read_fixed::<8>(bytes, 8)?),
            name_table_offset: u64::from_le_bytes(Self::read_fixed::<8>(bytes, 16)?),
            string_table_offset: u64::from_le_bytes(Self::read_fixed::<8>(bytes, 24)?),
            level_table_offset: u64::from_le_bytes(Self::read_fixed::<8>(bytes, 32)?),
            level_lists_table_offset: u64::from_le_bytes(Self::read_fixed::<8>(bytes, 40)?),
            name_count: u32::from_le_bytes(Self::read_fixed::<4>(bytes, 48)?),
            string_count: u32::from_le_bytes(Self::read_fixed::<4>(bytes, 52)?),
            _reserved: [0; 8],
        };
        header.validate()?;
        Ok(header)
    }

    #[inline]
    fn read_fixed<const N: usize>(bytes: &[u8], offset: usize) -> Result<[u8; N], FlatError> {
        let end = offset.checked_add(N).ok_or(FlatError::TruncatedHeader)?;
        let slice = bytes.get(offset..end).ok_or(FlatError::TruncatedHeader)?;
        let mut out = [0u8; N];
        out.copy_from_slice(slice);
        Ok(out)
    }
}
