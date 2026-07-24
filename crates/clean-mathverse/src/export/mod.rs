// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Export API for the Mathverse Library.
//!
//! Hosts the graduation/export pipeline surfaces:
//! - **Kernel export** (`kernel_export`): kernel `Declaration` → `.mathverse` shards.
//! - **Native export** (`native_export`): native theorems with tags/conjecture metadata.
//! - **Alpha exporter** (`alpha`): export config/exporter for external formats.
//! - **Convert output** (`convert_output`): converter output writing and summaries.

// Consolidated export-surface modules (relocated from crate root; callers use the
// canonical `crate::export::*` paths — the transitional lib.rs aliases were removed).
pub mod alpha;
pub mod convert_output;
pub mod kernel_export;
pub mod native_export;
