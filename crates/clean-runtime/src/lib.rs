// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean Runtime Library
//!
//! Provides C runtime support for compiled clean programs. This crate:
//! 1. Embeds the C header files needed by generated code
//! 2. Provides build integration for compiling generated C code
//! 3. Contains reference counting and memory management primitives
//!
//! # Usage
//!
//! Generated C code includes `clean_runtime.h` which provides:
//! - Object representation (clean_obj)
//! - Reference counting (clean_inc, clean_dec)
//! - Constructor allocation (clean_alloc_ctor)
//! - Field access (clean_ctor_get, clean_ctor_set)
//! - Tagged pointers (clean_box, clean_unbox)
//!
//! # Architecture
//!
//! Based on Lean 4's runtime (lean4/src/runtime/).
//!
//! Part of #963 - Compiler IR infrastructure (Phase 4).

pub mod ffi_bridge;
pub mod ffi_exports;
pub mod io_runtime;
pub mod native;
pub(crate) mod object_model;
pub mod runtime;
pub mod task;

// Re-export public runtime API at crate root so generated code can use
// `use clean_runtime::*;` to access all clean_* functions and the CleanObj type.
// Part of #2005 Phase 2.
pub use runtime::{
    clean_alloc_array, clean_alloc_closure, clean_alloc_ctor, clean_alloc_external,
    clean_alloc_task, clean_alloc_thunk, clean_array_data, clean_array_fget, clean_array_fset,
    clean_array_fswap, clean_array_get, clean_array_get_checked, clean_array_get_size,
    clean_array_pop, clean_array_push, clean_array_set, clean_array_size, clean_array_swap,
    clean_array_uget, clean_array_uset, clean_array_uswap, clean_box, clean_box_float,
    clean_box_uint32, clean_box_uint64, clean_closure_apply, clean_closure_arg,
    clean_closure_arity, clean_closure_func, clean_closure_num_fixed, clean_copy_array,
    clean_ctor_get, clean_ctor_get_float, clean_ctor_get_float32, clean_ctor_get_uint16,
    clean_ctor_get_uint32, clean_ctor_get_uint64, clean_ctor_get_uint8, clean_ctor_get_usize,
    clean_ctor_set, clean_ctor_set_float, clean_ctor_set_float32, clean_ctor_set_tag,
    clean_ctor_set_uint16, clean_ctor_set_uint32, clean_ctor_set_uint64, clean_ctor_set_uint8,
    clean_ctor_set_usize, clean_dec, clean_ensure_exclusive_array, clean_inc, clean_inc_n,
    clean_is_exclusive, clean_is_scalar, clean_is_unique, clean_mk_array, clean_mk_empty_array,
    clean_mk_empty_array_with_capacity, clean_mk_string, clean_mk_string_from_bytes, clean_obj_tag,
    clean_panic, clean_reset, clean_reuse, clean_reuse_slot, clean_runtime_finalize,
    clean_runtime_init, clean_string_data, clean_string_len, clean_unbox, clean_unbox_float,
    clean_unbox_uint32, clean_unbox_uint64, CleanExternalClass, CleanObj, LeanObjPtr,
};

use std::path::PathBuf;

/// Get the path to the runtime include directory.
///
/// Returns the directory containing `clean_runtime.h` and other headers.
pub fn include_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("include")
}

/// Get the C header content as a string.
///
/// Useful for embedding the runtime header directly without file system access.
pub fn runtime_header() -> &'static str {
    include_str!("../include/clean_runtime.h")
}

/// Get the C runtime implementation source as a string.
///
/// Returns the full text of `clean_runtime.c`. Useful for the native
/// build-and-run path (`clean run`), which writes this alongside
/// [`runtime_header`] into a scratch directory and `cc`-compiles it together
/// with generated code into a self-contained executable — no prebuilt
/// `libclean_runtime.a` or `CARGO_MANIFEST_DIR` path is required at run time.
///
/// The first line of the shipped file is `#include "../include/clean_runtime.h"`,
/// a path relative to the crate layout. Callers that materialize this source in
/// a flat directory should drop [`runtime_header`] next to it as
/// `clean_runtime.h` and rewrite that include to `"clean_runtime.h"` (or pass an
/// appropriate `-I`).
pub fn runtime_source() -> &'static str {
    include_str!("clean_runtime.c")
}

/// Get the external-symbol materialization TU as a string.
///
/// The RC / box / field-access primitives in `clean_runtime.h` are declared
/// `static inline` (internal linkage — no exported symbol). The `emit_c`
/// backend inlines them directly; the `trust-cg` backend lowers them to
/// *external calls* and therefore needs a real, link-visible definition of
/// each. This translation unit ([`runtime_extern.c`](../src/runtime_extern.c))
/// exports one authoritative external forwarder per header primitive WITHOUT
/// modifying the header (so `emit_c` still inlines) or [`runtime_source`] (so
/// the runtime still compiles standalone).
///
/// Compile it into its own object and link it alongside the runtime object for
/// any consumer that binds runtime primitives at link time (the trust-cg
/// object path). It is a no-op for `emit_c`, whose emitted program inlines its
/// own copies and never references these external symbols. Like
/// [`runtime_source`] its first line is a crate-relative
/// `#include "../include/clean_runtime.h"`; materialize [`runtime_header`] next
/// to it (or pass an appropriate `-I`).
pub fn runtime_extern_source() -> &'static str {
    include_str!("runtime_extern.c")
}

/// Get the runtime object file path (if compiled).
pub fn runtime_lib() -> Option<PathBuf> {
    let lib_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("libclean_runtime.a");
    if lib_path.exists() {
        Some(lib_path)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_include_dir_exists() {
        let dir = include_dir();
        // Directory may not exist yet if headers haven't been generated
        assert!(dir.ends_with("include"));
    }

    #[test]
    fn test_runtime_header_not_empty() {
        let header = runtime_header();
        assert!(header.contains("clean_obj"));
        assert!(header.contains("clean_inc"));
    }

    #[test]
    fn test_runtime_header_uses_relaxed_is_exclusive_contract() {
        let header = runtime_header();
        let block_start = header
            .find("/* Check if object is exclusively owned")
            .expect("clean_is_exclusive comment should be present in runtime header");
        let block_end = header[block_start..]
            .find("/* ============================================================================")
            .map(|offset| block_start + offset)
            .expect("clean_is_exclusive block should end before the allocation section");
        let is_exclusive_block = &header[block_start..block_end];

        assert!(
            is_exclusive_block.contains("memory_order_relaxed"),
            "clean_is_exclusive should use memory_order_relaxed in the shipped header"
        );
        assert!(
            is_exclusive_block
                .contains("Relaxed suffices: is_unique is a hint for reuse optimization."),
            "clean_is_exclusive should document why Relaxed ordering is sufficient"
        );
        assert!(
            is_exclusive_block.contains("Matches Lean 4 lean_is_exclusive (lean.h:550)."),
            "clean_is_exclusive should cite the Lean 4 naming/ordering contract"
        );
    }
}
