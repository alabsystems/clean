// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Centralized pseudo-operation name constants for the RC pipeline.
//!
//! The RC pipeline encodes reference-counting operations as `LetValue::Const`
//! calls with well-known names (e.g., `_inc`, `_dec`, `_reset`). Previously
//! these names were scattered as string literals across 10+ files.
//!
//! This module provides:
//! - `&str` constants for string comparisons (`name.to_string() == pseudo_op::INC`)
//! - `LazyLock<Name>` statics for constructing `Name` values without per-call allocation
//!
//! Part of #2029.

use clean_kernel::Name;
use std::sync::LazyLock;

// ═══════════════════════════════════════════════════════════════════════════
// String constants (for comparisons)
// ═══════════════════════════════════════════════════════════════════════════

/// Increment reference count.
pub const INC: &str = "_inc";
/// Decrement reference count.
pub const DEC: &str = "_dec";
/// Delete (free) an object known to have refcount 1.
pub const DEL: &str = "_del";
/// Reset an object for potential reuse.
pub const RESET: &str = "_reset";
/// Reuse a reset slot for a new constructor.
pub const REUSE: &str = "_reuse";
/// Check if an object's reference count > 1.
pub const IS_SHARED: &str = "_isShared";
/// Generic constructor placeholder (slow-path fallback).
pub const CTOR: &str = "_ctor";
/// Set an object pointer field.
pub const SET: &str = "_set";
/// Set the constructor tag on a reused object.
pub const SET_TAG: &str = "_setTag";
/// Bind a reuse slot on the fast path.
#[cfg(test)]
pub const REUSE_SLOT: &str = "_reuse_slot";
/// Placeholder name for projected-but-unread fields.
pub const UNUSED_FIELD: &str = "_unused_field";
/// Set a USize scalar field.
pub const USET: &str = "_uset";
/// Set a non-USize scalar field.
pub const SSET: &str = "_sset";

// ═══════════════════════════════════════════════════════════════════════════
// Cached Name constants (for construction — avoids per-call allocation)
// ═══════════════════════════════════════════════════════════════════════════

/// Cached `Name` for `_inc`.
pub static NAME_INC: LazyLock<Name> = LazyLock::new(|| Name::from_string(INC));
/// Cached `Name` for `_dec`.
pub static NAME_DEC: LazyLock<Name> = LazyLock::new(|| Name::from_string(DEC));
/// Cached `Name` for `_del`.
pub static NAME_DEL: LazyLock<Name> = LazyLock::new(|| Name::from_string(DEL));
/// Cached `Name` for `_reset`.
pub static NAME_RESET: LazyLock<Name> = LazyLock::new(|| Name::from_string(RESET));
/// Cached `Name` for `_isShared`.
pub static NAME_IS_SHARED: LazyLock<Name> = LazyLock::new(|| Name::from_string(IS_SHARED));
/// Cached `Name` for `_ctor`.
pub static NAME_CTOR: LazyLock<Name> = LazyLock::new(|| Name::from_string(CTOR));
/// Cached `Name` for `_set`.
pub static NAME_SET: LazyLock<Name> = LazyLock::new(|| Name::from_string(SET));
/// Cached `Name` for `_setTag`.
pub static NAME_SET_TAG: LazyLock<Name> = LazyLock::new(|| Name::from_string(SET_TAG));
/// Cached `Name` for `_unused_field`.
pub static NAME_UNUSED_FIELD: LazyLock<Name> = LazyLock::new(|| Name::from_string(UNUSED_FIELD));
