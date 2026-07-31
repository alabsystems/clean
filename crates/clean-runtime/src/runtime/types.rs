// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Re-export shim: all type definitions now live in `crate::object_model`.
//!
//! This file preserves the existing `super::types::*` import pattern used by
//! all `runtime/` submodules. After the #2827 unification, the canonical
//! definitions live in `crate::object_model` and this module re-exports them.

// Public types (part of the crate's public API surface).
pub use crate::object_model::{CleanExternalClass, CleanObj, LeanObjPtr};

#[inline]
#[cfg(any(test, kani))]
pub(crate) fn closure_layout(num_fixed: u16) -> std::alloc::Layout {
    crate::object_model::closure_layout(num_fixed)
}

// Crate-internal re-exports for runtime submodules.
pub(crate) use crate::object_model::{
    // Allocation
    alloc_obj,
    // Invariant helpers
    expect,
    expect_index_lt,
    expect_obj_kind,
    // Tagged pointer helpers
    is_scalar,
    lean_box,
    // Panic & lifecycle
    lean_panic,
    lean_unbox,
    obj_layout,
    runtime_finalize,
    runtime_init,
    // Types
    ArrayObj,
    ClosureObj,
    ExternalObj,
    ObjHeader,
    ObjKind,
    StringObj,
    TaskObj,
    ThunkObj,
    MAX_SMALL,
};
