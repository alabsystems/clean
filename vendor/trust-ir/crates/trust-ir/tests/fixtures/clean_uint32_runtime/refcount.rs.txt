// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reference counting: increment, decrement, and uniqueness checks.
//!
//! Thin names over [`crate::rc_core`], which the native facade shares: sticky
//! counts (a count in the band at the top of the u32 is frozen and never
//! freed) and a worklist deletion that frees a graph of any depth in constant
//! stack and never adjusts a frozen child (Part of #1934).

use super::types::LeanObjPtr;
use crate::rc_core;

/// Increment the reference count of a heap object. No-op for scalars and
/// frozen counts.
#[inline]
pub(crate) fn lean_inc(o: LeanObjPtr) {
    rc_core::inc_n(o, 1);
}

/// Increment the reference count by `n`. No-op for scalars and frozen counts;
/// an `n` that would pass the band leaves the count frozen.
#[inline]
pub(crate) fn lean_inc_n(o: LeanObjPtr, n: usize) {
    rc_core::inc_n(o, n);
}

/// Decrement the reference count. If the last reference is dropped, free the
/// object and every child that reference kept alive. No-op for scalars and
/// frozen counts.
pub(crate) fn lean_dec(o: LeanObjPtr) {
    rc_core::dec(o);
}

/// Returns `true` if the object is uniquely owned (ref_count == 0).
/// Scalars are always considered unique; a frozen object never is.
#[inline]
pub(crate) fn lean_is_unique(o: LeanObjPtr) -> bool {
    rc_core::is_exclusive(o)
}
