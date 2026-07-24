// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-native runtime primitives for compiled clean programs.
//!
//! Pure Rust reimplementation of the C runtime (`clean_runtime.h`/`clean_runtime.c`).
//! Provides the same object model, reference counting, tagged pointers, and memory
//! management primitives needed by the Rust compilation backend. After #2827,
//! `runtime/types.rs` is only a compatibility shim; the canonical object model
//! lives in `crate::object_model`.
//!
//! Part of #1887 and #2827.

// Runtime library functions are called by generated code, not by this crate
// itself. The dead_code lint would flag every pub(crate) function as unused.
mod array;
pub(crate) mod closure;
mod ctor_scalar;
mod public_api;
mod refcount;
mod string_reset;
mod types;

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod kani_harnesses;

// Re-export all public types and functions so downstream code sees the same API.
pub use public_api::*;
pub use types::{CleanExternalClass, CleanObj, LeanObjPtr};

// Re-export internal items for tests and kani harnesses (via super::*).
pub(crate) use array::*;
pub(crate) use closure::{
    alloc_closure, closure_apply, closure_arg, closure_arity, closure_func, closure_num_fixed,
};
pub(crate) use ctor_scalar::*;
pub(crate) use refcount::*;
pub(crate) use string_reset::*;
pub(crate) use types::*;
