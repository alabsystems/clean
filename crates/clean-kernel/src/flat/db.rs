// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FlatDb: read-side validation and decode for flat expression databases.

use super::codec::{decode_flatexpr, decode_flatlevel};
use super::error::FlatError;
use super::header::FlatHeader;
use super::types::{FlatExpr, FlatLevel};

/// Read-only view of a flat expression database.
///
/// Designed for zero-copy access to memory-mapped files.
/// Uses raw byte slices to avoid any deserialization overhead.
#[derive(Debug)]
pub struct FlatDb<'a> {
    /// Raw bytes of the entire file.
    data: &'a [u8],
    /// Parsed header.
    header: FlatHeader,
}

impl<'a> FlatDb<'a> {
    /// Create a FlatDb from a byte slice.
    ///
    /// This is designed for use with memory-mapped files:
    /// ```text
    /// let mmap = unsafe { memmap2::Mmap::map(&file)? };
    /// let db = FlatDb::from_bytes(&mmap)?;
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `data.len() >= FlatHeader::SIZE`
    /// REQUIRES: Header passes `FlatHeader::validate()` (correct magic, version)
    /// ENSURES: Ok(result) where result.header.magic == FlatHeader::MAGIC
    pub fn from_bytes(data: &'a [u8]) -> Result<Self, FlatError> {
        let header = FlatHeader::from_bytes(data)?;
        if header.expr_count > u32::MAX as u64 {
            return Err(FlatError::InvalidHeader(format!(
                "expr_count exceeds u32::MAX: {}",
                header.expr_count
            )));
        }
        let expr_bytes = header
            .expr_count
            .checked_mul(FlatExpr::SIZE as u64)
            .ok_or_else(|| FlatError::InvalidHeader("expr_count overflow".to_string()))?;
        let expr_end = FlatHeader::SIZE as u64 + expr_bytes;
        let data_len = data.len() as u64;
        let [name_table_offset, string_table_offset, level_table_offset, level_lists_table_offset] =
            Self::validate_table_layout(&header, expr_end, data_len)?;

        Self::validate_indexed_string_table(
            data,
            name_table_offset,
            string_table_offset,
            header.name_count,
            "name",
        )?;
        Self::validate_indexed_string_table(
            data,
            string_table_offset,
            level_table_offset,
            header.string_count,
            "string",
        )?;

        let level_table_bytes = level_lists_table_offset - level_table_offset;
        if !level_table_bytes.is_multiple_of(FlatLevel::SIZE) {
            return Err(FlatError::InvalidHeader(
                "level table is not aligned to FlatLevel::SIZE".to_string(),
            ));
        }
        Ok(Self { data, header })
    }

    /// Get the number of expressions.
    #[inline]
    pub fn expr_count(&self) -> u64 {
        self.header.expr_count
    }

    /// Get an expression by index.
    ///
    /// Returns a copy of the expression to avoid alignment UB. FlatExpr is
    /// Copy and only 16 bytes, so this is efficient.
    ///
    /// # Contract
    ///
    /// REQUIRES: `idx < self.expr_count()`
    /// ENSURES: Ok(expr) where expr is the expression at the given index
    #[inline]
    pub fn get_expr(&self, idx: u32) -> Result<FlatExpr, FlatError> {
        if idx as u64 >= self.header.expr_count {
            return Err(FlatError::IndexOutOfBounds(idx));
        }
        let offset = (idx as usize)
            .checked_mul(FlatExpr::SIZE)
            .and_then(|n| FlatHeader::SIZE.checked_add(n))
            .ok_or(FlatError::TruncatedData)?;
        let end = offset
            .checked_add(FlatExpr::SIZE)
            .ok_or(FlatError::TruncatedData)?;
        if end > self.data.len() {
            return Err(FlatError::TruncatedData);
        }
        let mut bytes = [0u8; FlatExpr::SIZE];
        bytes.copy_from_slice(&self.data[offset..end]);
        decode_flatexpr(&bytes)
    }

    /// Get the number of names.
    #[inline]
    pub fn name_count(&self) -> u32 {
        self.header.name_count
    }

    /// Get the number of strings.
    #[inline]
    pub fn string_count(&self) -> u32 {
        self.header.string_count
    }

    /// Get a name by index (O(1) via offset table).
    ///
    /// # Contract
    ///
    /// REQUIRES: `idx < self.name_count()`
    /// ENSURES: Ok(name) where name is valid UTF-8
    pub fn get_name(&self, idx: u32) -> Result<&str, FlatError> {
        if idx >= self.header.name_count {
            return Err(FlatError::IndexOutOfBounds(idx));
        }
        let table_offset = self.header.name_table_offset as usize;
        let table_end = self.header.string_table_offset as usize;
        self.read_indexed_string(table_offset, table_end, self.header.name_count, idx)
    }

    /// Get a string literal by index (O(1) via offset table).
    ///
    /// # Contract
    ///
    /// REQUIRES: `idx < self.string_count()`
    /// ENSURES: Ok(s) where s is valid UTF-8
    pub fn get_string(&self, idx: u32) -> Result<&str, FlatError> {
        if idx >= self.header.string_count {
            return Err(FlatError::IndexOutOfBounds(idx));
        }
        let table_offset = self.header.string_table_offset as usize;
        let table_end = self.header.level_table_offset as usize;
        self.read_indexed_string(table_offset, table_end, self.header.string_count, idx)
    }

    /// Read a string from an offset-indexed table in O(1).
    ///
    /// Table layout: [offset_0: u32, ..., offset_N-1: u32][len_0: u32, data_0, len_1: u32, data_1, ...]
    /// Each offset_i is a byte offset from table_offset to the length-prefix of entry i.
    fn read_indexed_string(
        &self,
        table_offset: usize,
        table_end: usize,
        count: u32,
        idx: u32,
    ) -> Result<&str, FlatError> {
        let offsets_bytes = (count as usize)
            .checked_mul(4)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        let entries_start = table_offset
            .checked_add(offsets_bytes)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        if entries_start > table_end {
            return Err(FlatError::IndexOutOfBounds(idx));
        }

        // Read the offset for entry idx from the offset array
        let offset_pos = table_offset
            .checked_add(
                (idx as usize)
                    .checked_mul(4)
                    .ok_or(FlatError::IndexOutOfBounds(idx))?,
            )
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        let entry_rel_offset = self.read_u32_at(offset_pos, idx)? as usize;

        // Jump to the entry's length-prefixed string
        let entry_offset = table_offset
            .checked_add(entry_rel_offset)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        if entry_offset < entries_start {
            return Err(FlatError::IndexOutOfBounds(idx));
        }
        let len_end = entry_offset
            .checked_add(4)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        if len_end > table_end {
            return Err(FlatError::IndexOutOfBounds(idx));
        }
        let len = self.read_u32_at(entry_offset, idx)? as usize;
        let data_start = entry_offset
            .checked_add(4)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        let data_end = data_start
            .checked_add(len)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        if data_end > table_end {
            return Err(FlatError::IndexOutOfBounds(idx));
        }
        let raw = self
            .data
            .get(data_start..data_end)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        std::str::from_utf8(raw)
            .map_err(|_| FlatError::Io("invalid UTF-8 in string table".to_string()))
    }

    /// Get the number of levels in the level table.
    ///
    /// Computed from the table offsets and FlatLevel::SIZE.
    #[inline]
    pub fn level_count(&self) -> u32 {
        let table_bytes = self.header.level_lists_table_offset - self.header.level_table_offset;
        (table_bytes / FlatLevel::SIZE as u64) as u32
    }

    /// Iterate over all expressions.
    pub fn iter_exprs(&self) -> impl Iterator<Item = FlatExpr> + '_ {
        (0..self.header.expr_count as u32).filter_map(|i| self.get_expr(i).ok())
    }

    /// Get a universe level by index from the level table.
    pub fn get_level(&self, idx: u32) -> Result<FlatLevel, FlatError> {
        let table_start = self.header.level_table_offset as usize;
        let table_end = self.header.level_lists_table_offset as usize;
        let offset = (idx as usize)
            .checked_mul(FlatLevel::SIZE)
            .and_then(|n| table_start.checked_add(n))
            .ok_or(FlatError::TruncatedData)?;
        let end = offset
            .checked_add(FlatLevel::SIZE)
            .ok_or(FlatError::TruncatedData)?;
        if end > table_end || end > self.data.len() {
            return Err(FlatError::IndexOutOfBounds(idx));
        }

        let mut bytes = [0u8; FlatLevel::SIZE];
        bytes.copy_from_slice(&self.data[offset..end]);
        decode_flatlevel(&bytes)
    }

    /// Get a level list by offset into the level_lists table.
    ///
    /// Returns the list of level indices stored at the given offset.
    /// The format at the offset is: [count: u32, level_idx_0: u32, ..., level_idx_N: u32]
    /// The offset is a u32 index into the level_lists array (not a byte offset).
    ///
    /// For multi-level universe polymorphism (#1162).
    ///
    /// # Contract
    ///
    /// REQUIRES: `offset` is a valid index in level_lists table, or `u32::MAX` (empty list)
    /// ENSURES: Ok(indices) where indices is the list of level table indices
    pub fn get_level_list(&self, offset: u32) -> Result<Vec<u32>, FlatError> {
        if offset == u32::MAX {
            return Ok(Vec::new());
        }

        let table_start = self.header.level_lists_table_offset as usize;
        // Each entry in level_lists is a u32, so byte offset = table_start + offset * 4
        let byte_offset = table_start
            .checked_add(
                (offset as usize)
                    .checked_mul(4)
                    .ok_or(FlatError::IndexOutOfBounds(offset))?,
            )
            .ok_or(FlatError::IndexOutOfBounds(offset))?;
        let count = self.read_u32_at(byte_offset, offset)? as usize;

        // Read level indices (each is 4 bytes)
        let mut indices = Vec::with_capacity(count);
        for i in 0..count {
            let idx_offset = byte_offset
                .checked_add(4)
                .and_then(|n| n.checked_add(i.checked_mul(4)?))
                .ok_or(FlatError::IndexOutOfBounds(offset))?;
            let level_idx = self.read_u32_at(idx_offset, offset)?;
            indices.push(level_idx);
        }

        Ok(indices)
    }

    #[inline]
    fn read_u32_at(&self, offset: usize, idx: u32) -> Result<u32, FlatError> {
        let end = offset
            .checked_add(4)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        let slice = self
            .data
            .get(offset..end)
            .ok_or(FlatError::IndexOutOfBounds(idx))?;
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(slice);
        Ok(u32::from_le_bytes(bytes))
    }

    fn validate_table_layout(
        header: &FlatHeader,
        expr_end: u64,
        data_len: u64,
    ) -> Result<[usize; 4], FlatError> {
        Self::validate_table_offset(
            "name_table_offset",
            header.name_table_offset,
            expr_end,
            data_len,
            "expr table",
        )?;
        Self::validate_table_offset(
            "string_table_offset",
            header.string_table_offset,
            header.name_table_offset,
            data_len,
            "name table",
        )?;
        Self::validate_table_offset(
            "level_table_offset",
            header.level_table_offset,
            header.string_table_offset,
            data_len,
            "string table",
        )?;
        Self::validate_table_offset(
            "level_lists_table_offset",
            header.level_lists_table_offset,
            header.level_table_offset,
            data_len,
            "level table",
        )?;

        Ok([
            header.name_table_offset as usize,
            header.string_table_offset as usize,
            header.level_table_offset as usize,
            header.level_lists_table_offset as usize,
        ])
    }

    fn validate_table_offset(
        field_name: &str,
        offset: u64,
        min_offset: u64,
        data_len: u64,
        previous_label: &str,
    ) -> Result<(), FlatError> {
        if offset < min_offset {
            return Err(FlatError::InvalidHeader(format!(
                "{field_name} before end of {previous_label}"
            )));
        }
        if offset > data_len {
            return Err(FlatError::TruncatedData);
        }
        Ok(())
    }

    fn validate_indexed_string_table(
        data: &[u8],
        table_offset: usize,
        table_end: usize,
        count: u32,
        table_name: &str,
    ) -> Result<(), FlatError> {
        let offsets_bytes = (count as usize).checked_mul(4).ok_or_else(|| {
            FlatError::InvalidHeader(format!("{table_name} table offset array overflows"))
        })?;
        let entries_start = table_offset.checked_add(offsets_bytes).ok_or_else(|| {
            FlatError::InvalidHeader(format!("{table_name} table start overflows"))
        })?;
        if entries_start > table_end {
            return Err(FlatError::InvalidHeader(format!(
                "{table_name} table truncated before entry payloads"
            )));
        }

        for idx in 0..count {
            let offset_pos = table_offset
                .checked_add((idx as usize).checked_mul(4).ok_or_else(|| {
                    FlatError::InvalidHeader(format!(
                        "{table_name} table index {idx} offset overflows"
                    ))
                })?)
                .ok_or_else(|| {
                    FlatError::InvalidHeader(format!(
                        "{table_name} table index {idx} offset overflows"
                    ))
                })?;
            let entry_rel_offset = Self::read_u32_from(data, offset_pos).ok_or_else(|| {
                FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} offset is truncated"
                ))
            })? as usize;
            if entry_rel_offset < offsets_bytes {
                return Err(FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} points into offset array"
                )));
            }

            let entry_offset = table_offset.checked_add(entry_rel_offset).ok_or_else(|| {
                FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} entry offset overflows"
                ))
            })?;
            let len_end = entry_offset.checked_add(4).ok_or_else(|| {
                FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} length prefix overflows"
                ))
            })?;
            if len_end > table_end {
                return Err(FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} spills past section end"
                )));
            }

            let len = Self::read_u32_from(data, entry_offset).ok_or_else(|| {
                FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} length prefix is truncated"
                ))
            })? as usize;
            let data_start = len_end;
            let data_end = data_start.checked_add(len).ok_or_else(|| {
                FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} payload overflows"
                ))
            })?;
            if data_end > table_end {
                return Err(FlatError::InvalidHeader(format!(
                    "{table_name} table index {idx} payload spills past section end"
                )));
            }
        }

        Ok(())
    }

    fn read_u32_from(data: &[u8], offset: usize) -> Option<u32> {
        let end = offset.checked_add(4)?;
        let slice = data.get(offset..end)?;
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(slice);
        Some(u32::from_le_bytes(bytes))
    }
}
