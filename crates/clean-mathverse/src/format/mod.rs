// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arena-based `.mathverse` shard format for the Mathverse Library.
//!
//! Provides a flat, mmap-friendly representation of imported constants,
//! their types, and metadata. Each shard contains:
//!
//! 1. **Header** — magic, version, constant count
//! 2. **Constant table** — `MathverseConstantHeader` array (32 bytes each)
//! 3. **Name table** — interned string pool
//! 4. **Expr arena** — flattened expression data
//!
//! The arena allocator (`ExprArena`) packs expressions into a contiguous
//! byte buffer for zero-copy access after mmap.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::types::{AxiomProfile, MathverseConstantHeader};

// ─── Shard file format ───────────────────────────────────────────────────

/// Magic bytes for `.mathverse` shard files.
pub const MATHVERSE_MAGIC: [u8; 4] = *b"OMG\x01";

/// Current shard format version.
pub const MATHVERSE_VERSION: u32 = 1;

/// Header for an `.mathverse` shard file.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct ShardHeader {
    /// Magic bytes (`MATHVERSE_MAGIC`).
    pub magic: [u8; 4],
    /// Format version.
    pub version: u32,
    /// Number of constants in this shard.
    pub constant_count: u32,
    /// Byte offset of the name table from file start.
    pub name_table_offset: u32,
    /// Byte offset of the expr arena from file start.
    pub expr_arena_offset: u32,
    /// Total shard size in bytes.
    pub total_size: u32,
    /// Reserved for future use.
    _reserved: [u8; 8],
}

impl ShardHeader {
    pub const SIZE: usize = 32;

    #[must_use]
    pub fn new(constant_count: u32) -> Self {
        Self {
            magic: MATHVERSE_MAGIC,
            version: MATHVERSE_VERSION,
            constant_count,
            name_table_offset: 0,
            expr_arena_offset: 0,
            total_size: 0,
            _reserved: [0; 8],
        }
    }

    /// Validate the magic bytes and version.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.magic == MATHVERSE_MAGIC && self.version == MATHVERSE_VERSION
    }
}

// ─── Name table ──────────────────────────────────────────────────────────

/// Interned string pool for constant names.
///
/// Stores names as length-prefixed UTF-8 strings in a flat buffer.
/// Each name gets a `NameIdx` that can be stored in `MathverseConstantHeader`.
#[derive(Clone, Debug, Default)]
pub struct NameTable {
    /// Flat buffer of length-prefixed strings: [u32 len][utf8 bytes]...
    data: Vec<u8>,
    /// Map from string to its offset in `data`.
    index: HashMap<String, u32>,
    /// Number of interned names.
    count: u32,
}

impl NameTable {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a name, returning its index. Deduplicates.
    pub fn intern(&mut self, name: &str) -> u32 {
        if let Some(&idx) = self.index.get(name) {
            return idx;
        }
        let idx = self.count;
        let offset = self.data.len() as u32;
        let len = name.len() as u32;
        self.data.extend_from_slice(&len.to_le_bytes());
        self.data.extend_from_slice(name.as_bytes());
        self.index.insert(name.to_owned(), idx);
        self.count += 1;
        let _ = offset; // offset stored implicitly by index order
        idx
    }

    /// Look up a name by index (linear scan — for diagnostics, not hot path).
    #[must_use]
    pub fn lookup(&self, idx: u32) -> Option<&str> {
        let mut offset = 0usize;
        let mut current = 0u32;
        while offset + 4 <= self.data.len() {
            let len = u32::from_le_bytes([
                self.data[offset],
                self.data[offset + 1],
                self.data[offset + 2],
                self.data[offset + 3],
            ]) as usize;
            offset += 4;
            if current == idx {
                return std::str::from_utf8(&self.data[offset..offset + len]).ok();
            }
            offset += len;
            current += 1;
        }
        None
    }

    /// Number of interned names.
    #[must_use]
    pub fn len(&self) -> u32 {
        self.count
    }

    /// Whether the table is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Raw data bytes for serialization.
    #[must_use]
    pub fn data(&self) -> &[u8] {
        &self.data
    }
}

// ─── Expression arena ────────────────────────────────────────────────────

/// Tag byte for arena-packed expressions.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExprTag {
    /// Variable reference: [tag][u32 de-bruijn index]
    BVar = 0,
    /// Sort/universe: [tag][u32 level]
    Sort = 1,
    /// Constant reference: [tag][u32 name_idx]
    Const = 2,
    /// Application: [tag][u32 fn_offset][u32 arg_offset]
    App = 3,
    /// Lambda: [tag][u32 binder_name][u32 domain_offset][u32 body_offset]
    Lambda = 4,
    /// Pi/forall: [tag][u32 binder_name][u32 domain_offset][u32 body_offset]
    Pi = 5,
    /// Let binding: [tag][u32 name][u32 type_offset][u32 value_offset][u32 body_offset]
    Let = 6,
    /// Literal: [tag][u8 kind][u64 value]
    Lit = 7,
}

/// Arena allocator for flat expression storage.
///
/// Expressions are packed into a contiguous byte buffer. Each expression
/// is a tag byte followed by fixed-size payloads. References between
/// expressions use byte offsets into this buffer.
#[derive(Clone, Debug, Default)]
pub struct ExprArena {
    data: Vec<u8>,
}

impl ExprArena {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a bound variable expression.
    pub fn alloc_bvar(&mut self, idx: u32) -> u32 {
        let offset = self.data.len() as u32;
        self.data.push(ExprTag::BVar as u8);
        self.data.extend_from_slice(&idx.to_le_bytes());
        offset
    }

    /// Allocate a sort expression.
    pub fn alloc_sort(&mut self, level: u32) -> u32 {
        let offset = self.data.len() as u32;
        self.data.push(ExprTag::Sort as u8);
        self.data.extend_from_slice(&level.to_le_bytes());
        offset
    }

    /// Allocate a constant reference.
    pub fn alloc_const(&mut self, name_idx: u32) -> u32 {
        let offset = self.data.len() as u32;
        self.data.push(ExprTag::Const as u8);
        self.data.extend_from_slice(&name_idx.to_le_bytes());
        offset
    }

    /// Allocate an application node.
    pub fn alloc_app(&mut self, fn_offset: u32, arg_offset: u32) -> u32 {
        let offset = self.data.len() as u32;
        self.data.push(ExprTag::App as u8);
        self.data.extend_from_slice(&fn_offset.to_le_bytes());
        self.data.extend_from_slice(&arg_offset.to_le_bytes());
        offset
    }

    /// Allocate a lambda node.
    pub fn alloc_lambda(&mut self, binder: u32, domain: u32, body: u32) -> u32 {
        let offset = self.data.len() as u32;
        self.data.push(ExprTag::Lambda as u8);
        self.data.extend_from_slice(&binder.to_le_bytes());
        self.data.extend_from_slice(&domain.to_le_bytes());
        self.data.extend_from_slice(&body.to_le_bytes());
        offset
    }

    /// Allocate a Pi/forall node.
    pub fn alloc_pi(&mut self, binder: u32, domain: u32, body: u32) -> u32 {
        let offset = self.data.len() as u32;
        self.data.push(ExprTag::Pi as u8);
        self.data.extend_from_slice(&binder.to_le_bytes());
        self.data.extend_from_slice(&domain.to_le_bytes());
        self.data.extend_from_slice(&body.to_le_bytes());
        offset
    }

    /// Read the tag at a given offset.
    #[must_use]
    pub fn tag_at(&self, offset: u32) -> Option<ExprTag> {
        let byte = *self.data.get(offset as usize)?;
        match byte {
            0 => Some(ExprTag::BVar),
            1 => Some(ExprTag::Sort),
            2 => Some(ExprTag::Const),
            3 => Some(ExprTag::App),
            4 => Some(ExprTag::Lambda),
            5 => Some(ExprTag::Pi),
            6 => Some(ExprTag::Let),
            7 => Some(ExprTag::Lit),
            _ => None,
        }
    }

    /// Total bytes used.
    #[must_use]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Whether the arena is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Raw data bytes for serialization.
    #[must_use]
    pub fn data(&self) -> &[u8] {
        &self.data
    }
}

// ─── Shard builder ───────────────────────────────────────────────────────

/// Builder for constructing `.mathverse` shard files.
#[derive(Clone, Debug)]
pub struct ShardBuilder {
    names: NameTable,
    arena: ExprArena,
    constants: Vec<MathverseConstantHeader>,
}

impl ShardBuilder {
    #[must_use]
    pub fn new() -> Self {
        Self {
            names: NameTable::new(),
            arena: ExprArena::new(),
            constants: Vec::new(),
        }
    }

    /// Add a constant to the shard. Returns its index.
    pub fn add_constant(
        &mut self,
        name: &str,
        type_expr_offset: u32,
        value_expr_offset: u32,
        axiom_profile: u64,
        source_system: u8,
    ) -> u32 {
        let name_idx = self.names.intern(name);
        let idx = self.constants.len() as u32;
        self.constants.push(MathverseConstantHeader {
            name_idx,
            type_idx: type_expr_offset,
            value_idx: value_expr_offset,
            source_system,
            import_confidence: 0,
            content_domain: 0,
            // NOTE: this generic builder API has no kind information; callers
            // that care about decl_kind should construct MathverseConstantHeader
            // directly. Defaults to `Theorem` (discriminant 0) — see #3532.
            decl_kind: 0,
            axiom_profile: AxiomProfile(axiom_profile),
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        idx
    }

    /// Access the name table for interning names.
    pub fn names(&mut self) -> &mut NameTable {
        &mut self.names
    }

    /// Access the expression arena for allocating expressions.
    pub fn arena(&mut self) -> &mut ExprArena {
        &mut self.arena
    }

    /// Number of constants added.
    #[must_use]
    pub fn constant_count(&self) -> usize {
        self.constants.len()
    }

    /// Serialize the shard to bytes.
    #[must_use]
    pub fn build(&self) -> Vec<u8> {
        let header_size = ShardHeader::SIZE;
        let constants_size = self.constants.len() * MathverseConstantHeader::SIZE;
        let name_table_offset = header_size + constants_size;
        let name_data = self.names.data();
        let expr_arena_offset = name_table_offset + name_data.len();
        let expr_data = self.arena.data();
        let total_size = expr_arena_offset + expr_data.len();

        let mut header = ShardHeader::new(self.constants.len() as u32);
        header.name_table_offset = name_table_offset as u32;
        header.expr_arena_offset = expr_arena_offset as u32;
        header.total_size = total_size as u32;

        let mut buf = Vec::with_capacity(total_size);

        // Header
        buf.extend_from_slice(&header.magic);
        buf.extend_from_slice(&header.version.to_le_bytes());
        buf.extend_from_slice(&header.constant_count.to_le_bytes());
        buf.extend_from_slice(&header.name_table_offset.to_le_bytes());
        buf.extend_from_slice(&header.expr_arena_offset.to_le_bytes());
        buf.extend_from_slice(&header.total_size.to_le_bytes());
        buf.extend_from_slice(&[0u8; 8]); // reserved

        // Constant headers (simplified serialization)
        for c in &self.constants {
            buf.extend_from_slice(&c.type_idx.to_le_bytes());
            buf.extend_from_slice(&c.value_idx.to_le_bytes());
            buf.extend_from_slice(&c.name_idx.to_le_bytes());
            buf.extend_from_slice(&c.axiom_profile.0.to_le_bytes());
            buf.extend_from_slice(&(c.source_system as u16).to_le_bytes());
            buf.extend_from_slice(
                &(((c.content_domain as u16) << 8) | c.import_confidence as u16).to_le_bytes(),
            );
            buf.extend_from_slice(&[0u8; 4]); // reserved
        }

        // Name table
        buf.extend_from_slice(name_data);

        // Expression arena
        buf.extend_from_slice(expr_data);

        buf
    }
}

impl Default for ShardBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ─── Shard info (read-only metadata) ─────────────────────────────────────

/// Read-only metadata about a built shard.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShardInfo {
    pub constant_count: u32,
    pub name_count: u32,
    pub expr_arena_bytes: usize,
    pub total_bytes: usize,
}

impl ShardBuilder {
    /// Extract metadata about the shard being built.
    #[must_use]
    pub fn info(&self) -> ShardInfo {
        ShardInfo {
            constant_count: self.constants.len() as u32,
            name_count: self.names.len(),
            expr_arena_bytes: self.arena.len(),
            total_bytes: ShardHeader::SIZE
                + self.constants.len() * MathverseConstantHeader::SIZE
                + self.names.data().len()
                + self.arena.data().len(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shard_header_size() {
        assert_eq!(ShardHeader::SIZE, 32);
    }

    #[test]
    fn test_shard_header_valid() {
        let h = ShardHeader::new(10);
        assert!(h.is_valid());
    }

    #[test]
    fn test_name_table_intern_dedup() {
        let mut nt = NameTable::new();
        let a = nt.intern("Nat.add");
        let b = nt.intern("Nat.succ");
        let c = nt.intern("Nat.add");
        assert_eq!(a, 0);
        assert_eq!(b, 1);
        assert_eq!(c, 0); // deduplicated
        assert_eq!(nt.len(), 2);
    }

    #[test]
    fn test_name_table_lookup() {
        let mut nt = NameTable::new();
        nt.intern("hello");
        nt.intern("world");
        assert_eq!(nt.lookup(0), Some("hello"));
        assert_eq!(nt.lookup(1), Some("world"));
        assert_eq!(nt.lookup(2), None);
    }

    #[test]
    fn test_expr_arena_bvar() {
        let mut arena = ExprArena::new();
        let off = arena.alloc_bvar(42);
        assert_eq!(off, 0);
        assert_eq!(arena.tag_at(0), Some(ExprTag::BVar));
    }

    #[test]
    fn test_expr_arena_app() {
        let mut arena = ExprArena::new();
        let f = arena.alloc_const(0);
        let x = arena.alloc_bvar(0);
        let app = arena.alloc_app(f, x);
        assert_eq!(arena.tag_at(app), Some(ExprTag::App));
    }

    #[test]
    fn test_shard_builder_roundtrip() {
        let mut builder = ShardBuilder::new();
        let type_off = builder.arena().alloc_sort(0);
        let val_off = builder.arena().alloc_sort(0);
        builder.add_constant("Nat.zero", type_off, val_off, 0, 0);
        builder.add_constant("Nat.succ", type_off, val_off, 0, 0);

        let bytes = builder.build();
        assert!(bytes.len() > ShardHeader::SIZE);
        assert_eq!(&bytes[0..4], &MATHVERSE_MAGIC);
        assert_eq!(builder.constant_count(), 2);
    }

    #[test]
    fn test_shard_builder_info() {
        let mut builder = ShardBuilder::new();
        let t = builder.arena().alloc_sort(0);
        builder.add_constant("test", t, 0, 1, 1);
        let info = builder.info();
        assert_eq!(info.constant_count, 1);
        assert_eq!(info.name_count, 1);
        assert!(info.expr_arena_bytes > 0);
        assert!(info.total_bytes > 0);
    }
}
