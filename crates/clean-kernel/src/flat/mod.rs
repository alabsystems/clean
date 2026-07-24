// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Flat expression format for memory-mapped proof databases.
//!
//! This module provides a compact 16-byte expression representation optimized for:
//! - Memory-mapped file access (zero-copy, no deserialization)
//! - Cache-friendly linear traversal
//! - Parallel verification (lock-free read access)
//! - Batch processing of millions of proofs
//!
//! # Format
//!
//! Each `FlatExpr` is exactly 16 bytes, aligned to 16-byte boundaries for optimal
//! cache line utilization:
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │  tag (1)  │ flags (1) │   pad (2)   │      data (12)       │
//! └─────────────────────────────────────────────────────────────┘
//! ```
//!
//! Indices refer to other expressions in the same flat array by offset.

mod builder;
mod codec;
mod convert;
mod db;
mod error;
mod header;
pub mod reconstruct;
mod types;

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod kani_harnesses;

// Re-export public API (preserves existing import paths)
pub use builder::FlatBuilder;
pub use db::FlatDb;
pub use error::FlatError;
pub use header::FlatHeader;
pub use reconstruct::{reconstruct_all_exprs, reconstruct_expr, reconstruct_level};
pub use types::{FlatExpr, FlatFlags, FlatLevel, FlatTag};
