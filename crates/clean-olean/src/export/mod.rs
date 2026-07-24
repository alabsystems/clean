// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! .olean file export
//!
//! This module provides functionality to serialize clean environments to .olean files.
//! The format matches Lean 4's compacted region format for compatibility.

mod api;
mod constant_info;
mod expr;
mod module_data;
mod primitives;
#[cfg(test)]
mod tests;

/// Default base address for exported .olean files
/// This matches the typical base address used by Lean 4
const DEFAULT_BASE_ADDR: u64 = 0x10000;

/// .olean file exporter
///
/// Builds a compacted region containing serialized Lean objects.
pub struct OleanExporter {
    /// Output buffer
    pub(super) data: Vec<u8>,
    /// Base address for pointer calculation
    pub(super) base_addr: u64,
    /// String interning table (string -> offset)
    pub(super) strings: std::collections::HashMap<String, usize>,
    /// Name interning table (name -> offset)
    pub(super) names: std::collections::HashMap<String, usize>,
}
