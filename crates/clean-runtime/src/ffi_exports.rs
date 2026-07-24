// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C-ABI export layer for the clean runtime.
//!
//! This module defines the `#[no_mangle] extern "C"` wrapper functions that
//! provide the C-callable interface to the Rust runtime. Compiled Lean 5 programs
//! (emitted as C code) link against these symbols.
//!
//! # Architecture
//!
//! ```text
//! Generated C code  ──calls──►  clean_runtime.h (declarations)
//!                                      │
//!                                      ▼
//!                               ffi_exports.rs (definitions)
//!                                      │
//!                                      ▼
//!                               runtime/*.rs (implementation)
//! ```
//!
//! # Lean 4 Reference
//!
//! Lean 4 defines its C runtime in `lean4/src/runtime/object.cpp`. The C
//! declarations in `lean.h` mirror the runtime implementations. Our approach
//! is the same: `clean_runtime.h` mirrors these `extern "C"` exports.
//!
//! # Safety
//!
//! All functions in this module are `unsafe extern "C"` because they operate
//! on raw pointers from C code. The caller (generated C code) is responsible
//! for passing valid, properly ref-counted `clean_obj*` pointers.

// Runtime types will be used when actual extern "C" wrappers are added.
// For now this module provides the ABI catalog and C declaration generator.

/// ABI metadata for an exported runtime function.
///
/// Used by the compiler's FFI verifier to validate extern declarations
/// against the actual runtime ABI surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExportedFn {
    /// The C symbol name (e.g., `"clean_alloc_ctor"`).
    pub name: &'static str,
    /// Number of fixed (non-variadic) parameters.
    pub fixed_arity: usize,
    /// Whether the function accepts additional variadic arguments.
    pub variadic: bool,
    /// Brief description of what the function does.
    pub description: &'static str,
}

/// Complete catalog of all C-ABI exported runtime functions.
///
/// This is the single source of truth for the runtime ABI surface.
/// The compiler's `ffi_verify.rs` and `ffi_bridge.rs` should consult
/// this list (or a parallel const table derived from it) to validate
/// extern declarations.
pub const EXPORTED_FUNCTIONS: &[ExportedFn] = &[
    // ── Memory management ─────────────────────────────────────────────
    ExportedFn {
        name: "clean_inc",
        fixed_arity: 1,
        variadic: false,
        description: "Increment reference count",
    },
    ExportedFn {
        name: "clean_inc_n",
        fixed_arity: 2,
        variadic: false,
        description: "Increment reference count by n",
    },
    ExportedFn {
        name: "clean_dec",
        fixed_arity: 1,
        variadic: false,
        description: "Decrement reference count (free if zero)",
    },
    ExportedFn {
        name: "clean_is_exclusive",
        fixed_arity: 1,
        variadic: false,
        description: "Check if object is uniquely owned",
    },
    ExportedFn {
        name: "clean_is_scalar",
        fixed_arity: 1,
        variadic: false,
        description: "Check if object is a tagged scalar (not heap-allocated)",
    },
    // ── Constructor allocation ──────────────────────────────────────────
    ExportedFn {
        name: "clean_alloc_ctor",
        fixed_arity: 3,
        variadic: true,
        description: "Allocate constructor object (tag, num_objs, scalar_sz, ...fields)",
    },
    ExportedFn {
        name: "clean_box",
        fixed_arity: 1,
        variadic: false,
        description: "Box a scalar value into a tagged pointer",
    },
    ExportedFn {
        name: "clean_unbox",
        fixed_arity: 1,
        variadic: false,
        description: "Unbox a tagged pointer to a scalar value",
    },
    ExportedFn {
        name: "clean_box_uint32",
        fixed_arity: 1,
        variadic: false,
        description: "Box a uint32 value",
    },
    ExportedFn {
        name: "clean_box_uint64",
        fixed_arity: 1,
        variadic: false,
        description: "Box a uint64 value",
    },
    ExportedFn {
        name: "clean_box_float",
        fixed_arity: 1,
        variadic: false,
        description: "Box a float64 value",
    },
    ExportedFn {
        name: "clean_unbox_uint32",
        fixed_arity: 1,
        variadic: false,
        description: "Unbox a uint32 value",
    },
    ExportedFn {
        name: "clean_unbox_uint64",
        fixed_arity: 1,
        variadic: false,
        description: "Unbox a uint64 value",
    },
    ExportedFn {
        name: "clean_unbox_float",
        fixed_arity: 1,
        variadic: false,
        description: "Unbox a float64 value",
    },
    // ── Field access ──────────────────────────────────────────────────
    ExportedFn {
        name: "clean_ctor_get",
        fixed_arity: 2,
        variadic: false,
        description: "Get object field at index",
    },
    ExportedFn {
        name: "clean_ctor_set",
        fixed_arity: 3,
        variadic: false,
        description: "Set object field at index",
    },
    ExportedFn {
        name: "clean_obj_tag",
        fixed_arity: 1,
        variadic: false,
        description: "Get constructor tag",
    },
    // ── Scalar field access ───────────────────────────────────────────
    ExportedFn {
        name: "clean_ctor_get_uint8",
        fixed_arity: 2,
        variadic: false,
        description: "Get uint8 scalar field",
    },
    ExportedFn {
        name: "clean_ctor_get_uint16",
        fixed_arity: 2,
        variadic: false,
        description: "Get uint16 scalar field",
    },
    ExportedFn {
        name: "clean_ctor_get_uint32",
        fixed_arity: 2,
        variadic: false,
        description: "Get uint32 scalar field",
    },
    ExportedFn {
        name: "clean_ctor_get_uint64",
        fixed_arity: 2,
        variadic: false,
        description: "Get uint64 scalar field",
    },
    ExportedFn {
        name: "clean_ctor_get_usize",
        fixed_arity: 2,
        variadic: false,
        description: "Get usize scalar field",
    },
    ExportedFn {
        name: "clean_ctor_get_float",
        fixed_arity: 2,
        variadic: false,
        description: "Get float64 scalar field",
    },
    ExportedFn {
        name: "clean_ctor_get_float32",
        fixed_arity: 2,
        variadic: false,
        description: "Get float32 scalar field",
    },
    // ── Closure operations ────────────────────────────────────────────
    ExportedFn {
        name: "clean_alloc_closure",
        fixed_arity: 3,
        variadic: true,
        description: "Allocate closure (fn, arity, num_fixed, ...args)",
    },
    // ── String operations ────────────────────────────────────────────
    ExportedFn {
        name: "clean_mk_string",
        fixed_arity: 1,
        variadic: false,
        description: "Create string from C string literal",
    },
    // ── Array operations ─────────────────────────────────────────────
    ExportedFn {
        name: "clean_mk_empty_array",
        fixed_arity: 0,
        variadic: false,
        description: "Create empty array",
    },
    ExportedFn {
        name: "clean_array_push",
        fixed_arity: 2,
        variadic: false,
        description: "Push element onto array",
    },
    ExportedFn {
        name: "clean_array_get_size",
        fixed_arity: 1,
        variadic: false,
        description: "Get array size",
    },
    // ── Reset/Reuse ──────────────────────────────────────────────────
    ExportedFn {
        name: "clean_reset",
        fixed_arity: 1,
        variadic: false,
        description: "Reset object for reuse",
    },
    ExportedFn {
        name: "clean_reuse",
        fixed_arity: 4,
        variadic: true,
        description: "Reuse reset slot (slot, tag, num_objs, scalar_sz, ...args)",
    },
    // ── Runtime lifecycle ────────────────────────────────────────────
    ExportedFn {
        name: "clean_runtime_init",
        fixed_arity: 0,
        variadic: false,
        description: "Initialize runtime (call once at startup)",
    },
    ExportedFn {
        name: "clean_runtime_finalize",
        fixed_arity: 0,
        variadic: false,
        description: "Finalize runtime (call once at shutdown)",
    },
    // ── Panic ────────────────────────────────────────────────────────
    ExportedFn {
        name: "clean_panic",
        fixed_arity: 1,
        variadic: false,
        description: "Panic with message",
    },
];

/// Generate C header declarations for all exported runtime functions.
///
/// Returns a string containing `extern` C function declarations suitable
/// for inclusion in a C header file. This is the programmatic equivalent
/// of `clean_runtime.h` — useful for code generators that want to emit
/// inline extern declarations without depending on the header file.
#[must_use]
pub fn generate_c_declarations() -> String {
    let mut out = String::with_capacity(4096);
    out.push_str("/* Auto-generated clean runtime C declarations */\n");
    out.push_str("/* Do not edit — regenerate from ffi_exports.rs */\n\n");
    out.push_str("#ifndef CLEAN_FFI_DECLS_H\n");
    out.push_str("#define CLEAN_FFI_DECLS_H\n\n");
    out.push_str("#include <stdint.h>\n");
    out.push_str("#include <stdbool.h>\n");
    out.push_str("#include <stddef.h>\n\n");
    out.push_str("typedef struct clean_obj clean_obj;\n\n");

    for func in EXPORTED_FUNCTIONS {
        out.push_str(&format!("/* {} */\n", func.description));
        // We emit a simplified declaration; the full signatures are in
        // clean_runtime.h. This is for FFI stub validation only.
        if func.variadic {
            out.push_str(&format!(
                "clean_obj* {}(/* {} fixed args + variadic */);\n\n",
                func.name, func.fixed_arity
            ));
        } else if func.fixed_arity == 0 {
            out.push_str(&format!("void {}(void);\n\n", func.name));
        } else {
            out.push_str(&format!("/* arity: {} */\n", func.fixed_arity));
            out.push_str(&format!("clean_obj* {}();\n\n", func.name));
        }
    }

    out.push_str("#endif /* CLEAN_FFI_DECLS_H */\n");
    out
}

/// Look up an exported function by name.
///
/// Used by the FFI verifier to validate that an `@[extern]` declaration
/// references a known runtime symbol.
#[must_use]
pub fn lookup_exported_fn(name: &str) -> Option<&'static ExportedFn> {
    EXPORTED_FUNCTIONS.iter().find(|f| f.name == name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exported_functions_catalog_nonempty() {
        assert!(
            !EXPORTED_FUNCTIONS.is_empty(),
            "should have exported functions"
        );
    }

    #[test]
    fn test_exported_functions_names_unique() {
        let mut names: Vec<&str> = EXPORTED_FUNCTIONS.iter().map(|f| f.name).collect();
        let len_before = names.len();
        names.sort();
        names.dedup();
        assert_eq!(
            names.len(),
            len_before,
            "all exported function names should be unique"
        );
    }

    #[test]
    fn test_lookup_exported_fn_found() {
        let f = lookup_exported_fn("clean_inc").expect("clean_inc should exist");
        assert_eq!(f.fixed_arity, 1);
        assert!(!f.variadic);
    }

    #[test]
    fn test_lookup_exported_fn_not_found() {
        assert!(lookup_exported_fn("nonexistent_symbol").is_none());
    }

    #[test]
    fn test_lookup_alloc_ctor_variadic() {
        let f = lookup_exported_fn("clean_alloc_ctor").expect("clean_alloc_ctor should exist");
        assert_eq!(f.fixed_arity, 3);
        assert!(f.variadic);
    }

    #[test]
    fn test_generate_c_declarations_includes_guard() {
        let decls = generate_c_declarations();
        assert!(decls.contains("CLEAN_FFI_DECLS_H"));
        assert!(decls.contains("clean_inc"));
        assert!(decls.contains("clean_dec"));
        assert!(decls.contains("clean_alloc_ctor"));
    }

    #[test]
    fn test_generate_c_declarations_describes_functions() {
        let decls = generate_c_declarations();
        assert!(
            decls.contains("Increment reference count"),
            "should include descriptions"
        );
    }

    #[test]
    fn test_all_runtime_lifecycle_functions_present() {
        assert!(lookup_exported_fn("clean_runtime_init").is_some());
        assert!(lookup_exported_fn("clean_runtime_finalize").is_some());
    }

    #[test]
    fn test_all_core_memory_functions_present() {
        for name in &[
            "clean_inc",
            "clean_dec",
            "clean_inc_n",
            "clean_is_exclusive",
            "clean_is_scalar",
            "clean_box",
            "clean_unbox",
        ] {
            assert!(
                lookup_exported_fn(name).is_some(),
                "core memory function {} should be exported",
                name
            );
        }
    }

    #[test]
    fn test_all_scalar_accessor_functions_present() {
        for name in &[
            "clean_ctor_get_uint8",
            "clean_ctor_get_uint16",
            "clean_ctor_get_uint32",
            "clean_ctor_get_uint64",
            "clean_ctor_get_usize",
            "clean_ctor_get_float",
            "clean_ctor_get_float32",
        ] {
            assert!(
                lookup_exported_fn(name).is_some(),
                "scalar accessor {} should be exported",
                name
            );
        }
    }
}
