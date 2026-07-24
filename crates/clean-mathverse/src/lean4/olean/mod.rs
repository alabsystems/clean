// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.olean`-oriented Lean 4 import/verification modules.
//!
//! These modules were consolidated from the former top-level `lean4_*`
//! modules. Callers use the canonical `crate::lean4::olean::*` paths directly
//! (the transitional `crate::lean4_*` lib.rs aliases were removed).

pub mod alpha;
pub mod axiom_profile;
pub mod batch;
pub mod decl_kind;
pub mod olean_bridge;
pub mod shard;
pub mod verify;
