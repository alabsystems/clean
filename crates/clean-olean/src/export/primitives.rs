// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core primitives, string/name interning, and level serialization.

use super::{OleanExporter, DEFAULT_BASE_ADDR};
use crate::header::HEADER_SIZE;
use crate::level::level_tags;
use crate::region::tags;
use clean_kernel::level::Level;
use clean_kernel::name::Name;

impl OleanExporter {
    /// Create a new exporter with default settings
    ///
    /// # ENSURES
    /// - Returns an exporter with empty output buffer.
    /// - Base address is `DEFAULT_BASE_ADDR`.
    pub fn new() -> Self {
        Self::with_base_addr(DEFAULT_BASE_ADDR)
    }

    /// Create a new exporter with a specific base address
    ///
    /// # REQUIRES
    /// - `base_addr` matches the intended runtime base address for pointers.
    ///
    /// # ENSURES
    /// - Output buffer is initialized with header + root pointer space.
    /// - Returned exporter uses the provided `base_addr`.
    pub fn with_base_addr(base_addr: u64) -> Self {
        let mut exporter = Self {
            data: Vec::new(),
            base_addr,
            strings: std::collections::HashMap::new(),
            names: std::collections::HashMap::new(),
        };

        // Reserve space for header (56 bytes) + root pointer (8 bytes)
        exporter.data.resize(HEADER_SIZE + 8, 0);
        exporter
    }

    /// Get current write offset
    pub(super) fn current_offset(&self) -> usize {
        self.data.len()
    }

    /// Convert an offset to a pointer value
    pub(super) fn offset_to_ptr(&self, offset: usize) -> u64 {
        self.base_addr + offset as u64
    }

    /// Align to 8-byte boundary
    pub(super) fn align8(&mut self) {
        while !self.data.len().is_multiple_of(8) {
            self.data.push(0);
        }
    }

    /// Write an object header
    pub(super) fn write_header(&mut self, tag: u8, other: u8, cs_sz: u16) {
        // rc = 0 for compacted objects
        self.data.extend_from_slice(&0i32.to_le_bytes());
        self.data.extend_from_slice(&cs_sz.to_le_bytes());
        self.data.push(other);
        self.data.push(tag);
    }

    /// Write a u64 value
    pub(super) fn write_u64(&mut self, value: u64) {
        self.data.extend_from_slice(&value.to_le_bytes());
    }

    /// Write a tagged scalar (small nat)
    pub(super) fn scalar_ptr(value: u64) -> u64 {
        (value << 1) | 1
    }

    /// Pack up to three trailing `Bool` (UInt8) scalar fields into a single
    /// little-endian 8-byte word.
    ///
    /// Lean's compacted region stores trailing `Bool` fields of a structure
    /// as consecutive raw `u8`s (0 or 1) packed after the boxed/scalar
    /// fields, rather than as individually boxed scalars. The loader reads
    /// them back as raw bytes (e.g. `InductiveVal`'s `isRec`/`isUnsafe`/
    /// `isReflexive` at byte offsets +0/+1/+2 of this word), so the exporter
    /// must lay them out the same way for a lossless round-trip.
    ///
    /// Byte 0 holds `b0`, byte 1 holds `b1`, byte 2 holds `b2`; the
    /// remaining bytes are zero.
    pub(super) fn pack_bools3(b0: bool, b1: bool, b2: bool) -> u64 {
        u64::from(b0) | (u64::from(b1) << 8) | (u64::from(b2) << 16)
    }

    /// Write a string object and return its offset
    ///
    /// # REQUIRES
    /// - `s` is valid UTF-8 (Rust &str guarantees this).
    ///
    /// # ENSURES
    /// - Returns the offset of the interned string object.
    /// - Reuses the same offset for repeated `s`.
    pub(crate) fn write_string(&mut self, s: &str) -> usize {
        // Check if already interned
        if let Some(&offset) = self.strings.get(s) {
            return offset;
        }

        self.align8();
        let offset = self.current_offset();

        // String header
        self.write_header(tags::STRING, 0, 0);

        // m_size: byte length including null terminator
        let size = s.len() + 1;
        self.write_u64(size as u64);

        // m_capacity: same as size for compacted strings
        self.write_u64(size as u64);

        // m_length: UTF-8 character count
        let char_count = s.chars().count();
        self.write_u64(char_count as u64);

        // String data with null terminator
        self.data.extend_from_slice(s.as_bytes());
        self.data.push(0);

        // Pad to alignment
        self.align8();

        self.strings.insert(s.to_string(), offset);
        offset
    }

    /// Write a Name.anonymous object (tag 0, 0 fields)
    pub(super) fn write_name_anonymous(&mut self) -> usize {
        self.align8();
        let offset = self.current_offset();
        self.write_header(0, 0, 0);
        offset
    }

    /// Write a Name.str object (tag 1, 2 fields: parent, string)
    pub(super) fn write_name_str(&mut self, parent_ptr: u64, string_ptr: u64) -> usize {
        self.align8();
        let offset = self.current_offset();
        self.write_header(1, 2, 0);
        self.write_u64(parent_ptr);
        self.write_u64(string_ptr);
        offset
    }

    /// Write a Name.num object (tag 2, 2 fields: parent, number)
    pub(super) fn write_name_num(&mut self, parent_ptr: u64, num: u64) -> usize {
        self.align8();
        let offset = self.current_offset();
        self.write_header(2, 2, 0);
        self.write_u64(parent_ptr);
        self.write_u64(num);
        offset
    }

    /// Write a hierarchical name (e.g., "Nat.add") and return its offset
    ///
    /// # REQUIRES
    /// - `name` uses '.' as separator for hierarchical components.
    ///
    /// # ENSURES
    /// - Returns the offset of the interned name object.
    /// - Reuses the same offset for repeated `name`.
    pub(crate) fn write_name(&mut self, name: &str) -> usize {
        // Check if already interned
        if let Some(&offset) = self.names.get(name) {
            return offset;
        }

        if name.is_empty() {
            // Name.anonymous
            let offset = self.write_name_anonymous();
            self.names.insert(name.to_string(), offset);
            return offset;
        }

        // Split name into components
        let components: Vec<&str> = name.split('.').collect();

        // Build name from root to leaf
        let mut parent_ptr: u64 = Self::scalar_ptr(0); // Name.anonymous as scalar

        for component in components {
            // Check if component is a number
            if let Ok(num) = component.parse::<u64>() {
                let offset = self.write_name_num(parent_ptr, num);
                parent_ptr = self.offset_to_ptr(offset);
            } else {
                let str_offset = self.write_string(component);
                let str_ptr = self.offset_to_ptr(str_offset);
                let offset = self.write_name_str(parent_ptr, str_ptr);
                parent_ptr = self.offset_to_ptr(offset);
            }
        }

        // The last offset is the full name
        let final_offset = (parent_ptr - self.base_addr) as usize;
        self.names.insert(name.to_string(), final_offset);
        final_offset
    }

    /// Write a Name from kernel Name type
    pub(super) fn write_kernel_name(&mut self, name: &Name) -> usize {
        self.write_name(&name.to_string())
    }

    // =========================================================================
    // Level Serialization
    // =========================================================================

    /// Write a Level object and return its pointer value
    ///
    /// Level is an inductive type:
    /// - zero (tag 0, 0 fields)
    /// - succ (tag 1, 1 field: pred)
    /// - max (tag 2, 2 fields: l, r)
    /// - imax (tag 3, 2 fields: l, r)
    /// - param (tag 4, 1 field: name)
    /// - mvar (tag 5, 1 field: mvarId)
    ///
    /// # ENSURES
    /// - Returns a pointer value (not offset) for use in parent objects.
    /// - Level.zero is encoded as scalar 0 (pointer value 1).
    pub(crate) fn write_level(&mut self, level: &Level) -> u64 {
        match level {
            Level::Zero => {
                // Level.zero is encoded as scalar 0 (pointer value 1)
                Self::scalar_ptr(0)
            }
            Level::Succ(pred) => {
                // Write the predecessor level, then wrap in Succ constructor
                let pred_ptr = self.write_level(pred);
                self.align8();
                let succ_offset = self.current_offset();
                self.write_header(level_tags::SUCC, 1, 0);
                self.write_u64(pred_ptr);
                self.offset_to_ptr(succ_offset)
            }
            Level::Max(lhs, rhs) => {
                let l_ptr = self.write_level(lhs);
                let r_ptr = self.write_level(rhs);
                self.align8();
                let offset = self.current_offset();
                self.write_header(level_tags::MAX, 2, 0);
                self.write_u64(l_ptr);
                self.write_u64(r_ptr);
                self.offset_to_ptr(offset)
            }
            Level::IMax(lhs, rhs) => {
                let l_ptr = self.write_level(lhs);
                let r_ptr = self.write_level(rhs);
                self.align8();
                let offset = self.current_offset();
                self.write_header(level_tags::IMAX, 2, 0);
                self.write_u64(l_ptr);
                self.write_u64(r_ptr);
                self.offset_to_ptr(offset)
            }
            Level::Param(name) => {
                let name_offset = self.write_kernel_name(name);
                let name_ptr = self.offset_to_ptr(name_offset);
                self.align8();
                let offset = self.current_offset();
                self.write_header(level_tags::PARAM, 1, 0);
                self.write_u64(name_ptr);
                self.offset_to_ptr(offset)
            }
        }
    }

    /// Write an array of level parameters and return its pointer
    ///
    /// Lean 4 stores `ConstantVal.levelParams` as `List Name`, not `List Level`.
    /// Each element is a bare Name object, not a `Level.param` wrapper.
    pub(super) fn write_level_params(&mut self, params: &[Name]) -> u64 {
        self.write_name_list(params)
    }
}
