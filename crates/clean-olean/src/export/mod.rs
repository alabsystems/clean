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
mod lean_v2;
mod lean_v2_decl;
mod lean_v2_extensions;
mod lean_v2_module;
mod module_data;
#[cfg(test)]
mod payload_layout_tests;
mod primitives;
#[cfg(test)]
mod tests;

pub use lean_v2::{LeanV2RegionWriter, LeanV2Value};
pub use lean_v2_module::{
    write_lean_v2_module, LeanV2ModuleDeclaration, LeanV2ModuleOptions, LeanV2ModuleParts,
    LeanV2Visibility,
};

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
    /// Kernel names never use display strings as cache keys.
    pub(super) kernel_names: std::collections::HashMap<clean_kernel::name::Name, usize>,
}
