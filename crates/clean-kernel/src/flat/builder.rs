// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FlatBuilder: table ownership and write path for flat expression files.

#[cfg(kani)]
use std::collections::BTreeMap;
#[cfg(not(kani))]
use std::collections::HashMap;
use std::io::Write as IoWrite;
use std::path::Path;

/// Index map type: HashMap in production, BTreeMap under Kani verification.
/// HashMap's RandomState calls CCRandomGenerateBytes (Apple random) which Kani
/// cannot model (kani#2423). BTreeMap avoids this by using Ord instead of Hash.
#[cfg(not(kani))]
type IndexMap<K, V> = HashMap<K, V>;
#[cfg(kani)]
type IndexMap<K, V> = BTreeMap<K, V>;

use super::codec::{encode_flatexpr, encode_flatlevel};
use super::error::FlatError;
use super::header::FlatHeader;
use super::types::{FlatExpr, FlatLevel};

/// Builder for creating flat expression files.
///
/// Collects expressions and auxiliary tables, then writes to a file.
pub struct FlatBuilder {
    /// Expression array.
    pub(crate) exprs: Vec<FlatExpr>,
    /// Name table (interned names).
    pub(crate) names: Vec<String>,
    /// Name index for deduplication lookup.
    name_index: IndexMap<String, u32>,
    /// String table (literal strings).
    pub(crate) strings: Vec<String>,
    /// String index for deduplication lookup.
    string_index: IndexMap<String, u32>,
    /// Level table (universe level expressions).
    pub(crate) levels: Vec<FlatLevel>,
    /// Level lists table (for multi-level universe polymorphism, #1162).
    /// Format: [count: u32, level_idx_0: u32, ..., level_idx_N: u32, ...]
    pub(crate) level_lists: Vec<u32>,
    /// Level list index for deduplication lookup (maps list of level indices to offset).
    level_list_index: IndexMap<Vec<u32>, u32>,
    /// Expression content-dedup index for [`FlatBuilder::add_expr_dedup`]
    /// (hash-consing: maps a record's full semantic content to its index).
    expr_index: IndexMap<(u8, u8, [u8; 12]), u32>,
    /// Level content-dedup index for [`FlatBuilder::add_level_dedup`].
    level_index: IndexMap<(u8, [u8; 8]), u32>,
}

impl FlatBuilder {
    /// Create a new builder.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.expr_count() == 0`
    pub fn new() -> Self {
        Self {
            exprs: Vec::new(),
            names: Vec::new(),
            name_index: IndexMap::new(),
            strings: Vec::new(),
            string_index: IndexMap::new(),
            levels: Vec::new(),
            level_lists: Vec::new(),
            level_list_index: IndexMap::new(),
            expr_index: IndexMap::new(),
            level_index: IndexMap::new(),
        }
    }

    /// Add an expression, returning its index.
    ///
    /// # Contract
    ///
    /// ENSURES: `result == old(self.expr_count())`
    /// ENSURES: `self.expr_count() == old(self.expr_count()) + 1`
    pub fn add_expr(&mut self, expr: FlatExpr) -> u32 {
        let idx = self.exprs.len() as u32;
        self.exprs.push(expr);
        idx
    }

    /// Add an expression with CONTENT deduplication (hash-consing), returning
    /// the canonical index for its content.
    ///
    /// `(tag, flags, data)` is a record's full semantic content (`_pad` is
    /// always zeroed by every constructor), and child references inside `data`
    /// are themselves canonical indices by induction — so record equality is
    /// structural equality, and the resulting encoding is invariant under
    /// `Arc`-sharing topology. This is what makes
    /// `expr_canonical_digest`-style consumers actually canonical: a maximally
    /// shared DAG and a fresh unshared tree of the same term serialize to the
    /// same bytes. Raw [`FlatBuilder::add_expr`] keeps its append-only
    /// contract (Kani-pinned) for callers that want positional encoding.
    ///
    /// # Contract
    ///
    /// ENSURES: If content was new, `result == old(self.expr_count())`
    /// ENSURES: If content existed, `result < old(self.expr_count())`
    pub(crate) fn add_expr_dedup(&mut self, expr: FlatExpr) -> u32 {
        let key = (expr.tag, expr.flags, expr.data);
        if let Some(&idx) = self.expr_index.get(&key) {
            return idx;
        }
        let idx = self.add_expr(expr);
        self.expr_index.insert(key, idx);
        idx
    }

    /// Add a name, returning its index.
    ///
    /// Deduplicates: if the name already exists, returns the existing index.
    /// Uses O(1) HashMap lookup for performance.
    ///
    /// # Contract
    ///
    /// ENSURES: If name was new, `result == old(self.name_count())`
    /// ENSURES: If name existed, `result < old(self.name_count())`
    pub fn add_name(&mut self, name: &str) -> u32 {
        // O(1) lookup via HashMap
        if let Some(&idx) = self.name_index.get(name) {
            return idx;
        }
        let idx = self.names.len() as u32;
        self.names.push(name.to_string());
        self.name_index.insert(name.to_string(), idx);
        idx
    }

    /// Add a string literal, returning its index.
    ///
    /// Deduplicates: if the string already exists, returns the existing index.
    /// Uses O(1) HashMap lookup for performance.
    ///
    /// # Contract
    ///
    /// ENSURES: If string was new, `result == old(self.string_count())`
    /// ENSURES: If string existed, `result < old(self.string_count())`
    pub fn add_string(&mut self, s: &str) -> u32 {
        // O(1) lookup via HashMap
        if let Some(&idx) = self.string_index.get(s) {
            return idx;
        }
        let idx = self.strings.len() as u32;
        self.strings.push(s.to_string());
        self.string_index.insert(s.to_string(), idx);
        idx
    }

    /// Add a level, returning its index.
    ///
    /// # Contract
    ///
    /// ENSURES: `result == old(self.level_count())`
    /// ENSURES: `self.level_count() == old(self.level_count()) + 1`
    pub fn add_level(&mut self, level: FlatLevel) -> u32 {
        let idx = self.levels.len() as u32;
        self.levels.push(level);
        idx
    }

    /// Add a level with CONTENT deduplication (hash-consing), returning the
    /// canonical index for its content. See [`FlatBuilder::add_expr_dedup`] —
    /// same contract, for the level table.
    ///
    /// # Contract
    ///
    /// ENSURES: If content was new, `result == old(self.level_count())`
    /// ENSURES: If content existed, `result < old(self.level_count())`
    pub(crate) fn add_level_dedup(&mut self, level: FlatLevel) -> u32 {
        let key = (level.tag, level.data);
        if let Some(&idx) = self.level_index.get(&key) {
            return idx;
        }
        let idx = self.add_level(level);
        self.level_index.insert(key, idx);
        idx
    }

    /// Add a list of level indices, returning the offset into level_lists table.
    ///
    /// For multi-level universe polymorphism (#1162). The format in level_lists is:
    /// [count: u32, level_idx_0: u32, ..., level_idx_N: u32]
    ///
    /// Returns u32::MAX for empty lists (sentinel value).
    ///
    /// # Contract
    ///
    /// ENSURES: For non-empty input, result is offset into level_lists table
    /// ENSURES: For empty input, result == u32::MAX
    pub fn add_level_list(&mut self, level_indices: &[u32]) -> u32 {
        if level_indices.is_empty() {
            return u32::MAX;
        }

        // Check if this list already exists (deduplication)
        if let Some(&offset) = self.level_list_index.get(level_indices) {
            return offset;
        }

        // Add new list: [count, idx0, idx1, ...]
        let offset = self.level_lists.len() as u32;
        self.level_lists.push(level_indices.len() as u32);
        self.level_lists.extend_from_slice(level_indices);

        // Cache for deduplication
        self.level_list_index.insert(level_indices.to_vec(), offset);

        offset
    }

    /// Get expression count.
    pub fn expr_count(&self) -> usize {
        self.exprs.len()
    }

    /// Read-only access to the collected expressions.
    pub fn exprs(&self) -> &[FlatExpr] {
        &self.exprs
    }

    /// Read-only access to the collected levels.
    pub fn levels(&self) -> &[FlatLevel] {
        &self.levels
    }

    /// Read-only access to the interned name table.
    pub fn names(&self) -> &[String] {
        &self.names
    }

    /// Read-only access to the string literal table.
    pub fn strings(&self) -> &[String] {
        &self.strings
    }

    /// Write the flat file to a path.
    pub fn write_to_file(&self, path: &Path) -> Result<(), FlatError> {
        let file = std::fs::File::create(path)?;
        let mut writer = std::io::BufWriter::new(file);
        self.write_to(&mut writer)
    }

    /// Write the flat file to a writer.
    pub fn write_to<W: IoWrite>(&self, writer: &mut W) -> Result<(), FlatError> {
        // Calculate offsets
        let expr_array_size = self.exprs.len() * FlatExpr::SIZE;
        let name_table_offset = FlatHeader::SIZE + expr_array_size;

        // Build name table: [offset_0, offset_1, ..., offset_N-1, len_0, data_0, len_1, data_1, ...]
        // Each offset_i is a byte offset from name_table_offset to the length-prefix of entry i.
        let name_count = self.names.len();
        let name_offsets_size = name_count * 4; // u32 per entry
        let mut name_data = Vec::new();
        let mut name_offsets = Vec::with_capacity(name_count);
        for name in &self.names {
            let bytes = name.as_bytes();
            name_offsets.push((name_offsets_size + name_data.len()) as u32);
            name_data.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
            name_data.extend_from_slice(bytes);
        }

        let string_table_offset = name_table_offset + name_offsets_size + name_data.len();

        // Build string table (same layout as name table)
        let string_count = self.strings.len();
        let string_offsets_size = string_count * 4;
        let mut string_data = Vec::new();
        let mut string_offsets = Vec::with_capacity(string_count);
        for s in &self.strings {
            let bytes = s.as_bytes();
            string_offsets.push((string_offsets_size + string_data.len()) as u32);
            string_data.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
            string_data.extend_from_slice(bytes);
        }

        let level_table_offset = string_table_offset + string_offsets_size + string_data.len();
        let level_table_size = self.levels.len() * FlatLevel::SIZE;
        let level_lists_table_offset = level_table_offset + level_table_size;

        // Write header
        let mut header = FlatHeader::new(self.exprs.len() as u64);
        header.name_table_offset = name_table_offset as u64;
        header.string_table_offset = string_table_offset as u64;
        header.level_table_offset = level_table_offset as u64;
        header.level_lists_table_offset = level_lists_table_offset as u64;
        header.name_count = name_count as u32;
        header.string_count = string_count as u32;
        writer.write_all(&header.to_bytes())?;

        // Write expressions
        for expr in &self.exprs {
            writer.write_all(&encode_flatexpr(expr))?;
        }

        // Write name table: offset array then data
        for &off in &name_offsets {
            writer.write_all(&off.to_le_bytes())?;
        }
        writer.write_all(&name_data)?;

        // Write string table: offset array then data
        for &off in &string_offsets {
            writer.write_all(&off.to_le_bytes())?;
        }
        writer.write_all(&string_data)?;

        // Write level table
        for level in &self.levels {
            writer.write_all(&encode_flatlevel(level))?;
        }

        // Write level lists table (u32 array)
        for &val in &self.level_lists {
            writer.write_all(&val.to_le_bytes())?;
        }

        Ok(())
    }
}

impl Default for FlatBuilder {
    fn default() -> Self {
        Self::new()
    }
}
