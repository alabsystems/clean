// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-native runtime primitives for clean (C-interop oriented facade).
//!
//! After #2827, all low-level type definitions live in `crate::object_model`.
//! This module re-exports them under the original `native` API names so
//! compiler-facing callers (e.g. `pipeline_rust_e2e.rs`) are unaffected.
//!
//! Part of #1887 and #2827.

mod alloc;
mod boxing;
mod closure_apply;
mod rc;
mod scalar;

#[cfg(kani)]
mod kani_pointer_layout_tests;
#[cfg(kani)]
mod kani_rc_apply_reuse_tests;

pub use alloc::{alloc_closure, alloc_ctor, reset, reuse};
pub use boxing::{
    box_float, box_float32, box_uint32, box_uint64, mk_string, mk_string_from_str, panic_msg,
    runtime_finalize, runtime_init, string_data, string_len, unbox_float, unbox_float32,
    unbox_uint32, unbox_uint64,
};
pub use closure_apply::{apply_1, apply_2, apply_3, apply_4, apply_n};
pub use rc::{dec, inc, inc_n, is_unique};
pub use scalar::{
    ctor_get_float, ctor_get_float32, ctor_get_uint16, ctor_get_uint32, ctor_get_uint64,
    ctor_get_uint8, ctor_get_usize, ctor_set_float, ctor_set_float32, ctor_set_uint16,
    ctor_set_uint32, ctor_set_uint64, ctor_set_uint8, ctor_set_usize,
};

// Public re-exports from shared core (part of the `native` public API).
pub use crate::object_model::{
    box_val, ctor_get, ctor_set, is_scalar, obj_tag, unbox_val, ObjHeader, ObjKind, MAX_SMALL,
};

// Crate-internal re-exports from shared core.
pub(crate) use crate::object_model::{ctor_scalar_ptr, expect, expect_obj_kind};

// Test-only helpers used by the `native` module unit tests.
#[cfg(test)]
pub(crate) use crate::object_model::obj_fields_ptr;

// Kani-only re-exports (used by kani_pointer_layout_tests.rs).
#[cfg(kani)]
pub(crate) use crate::object_model::{
    closure_args_ptr, closure_layout, ctor_layout, string_layout, OBJ_ALIGN,
};

/// Generic clean heap object (native API name for `CleanObj`).
pub type LeanObj = crate::object_model::CleanObj;

/// Closure object (native API name for `ClosureObj`). Used by kani harnesses.
#[cfg(any(test, kani))]
pub(crate) type LeanClosure = crate::object_model::ClosureObj;

/// String object (native API name for `StringObj`).
pub(crate) type LeanString = crate::object_model::StringObj;

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::alloc::alloc_ctor_uninit;
    use super::*;
    use std::mem::{align_of, size_of};

    #[test]
    fn test_header_size_is_8_bytes() {
        assert_eq!(size_of::<ObjHeader>(), 8);
    }

    #[test]
    fn test_lean_obj_size_is_8_bytes() {
        assert_eq!(size_of::<LeanObj>(), 8);
    }

    #[test]
    fn test_closure_args_offset_abi_compatible() {
        assert_eq!(
            size_of::<LeanClosure>(),
            24,
            "LeanClosure must be 24 bytes (8 header + 8 fun + 2 arity + 2 num_fixed + 4 padding)"
        );
        assert_eq!(
            size_of::<LeanClosure>() % align_of::<*mut LeanObj>(),
            0,
            "closure args offset must be pointer-aligned for FAM ABI compatibility"
        );
    }

    #[test]
    fn test_tagged_pointer_roundtrip() {
        for n in [0, 1, 42, 255, MAX_SMALL] {
            let tagged = box_val(n);
            assert!(is_scalar(tagged));
            assert_eq!(unbox_val(tagged), n);
        }
    }

    #[test]
    fn test_heap_pointer_is_not_scalar() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = alloc_ctor_uninit(0, 0, 0);
            assert!(!is_scalar(o));
            dec(o);
        }
    }

    #[test]
    fn test_alloc_ctor_empty() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = alloc_ctor(0, &[]);
            assert_eq!(obj_tag(o), 0);
            assert!(!is_scalar(o));
            assert!(is_unique(o));
            dec(o);
        }
    }

    #[test]
    fn test_alloc_ctor_with_fields() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let a = box_val(10);
            let b = box_val(20);
            let o = alloc_ctor(5, &[a, b]);
            assert_eq!(obj_tag(o), 5);
            assert_eq!(ctor_get(o, 0), a);
            assert_eq!(ctor_get(o, 1), b);
            dec(o);
        }
    }

    #[test]
    fn test_ctor_set_replaces_field() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let a = box_val(1);
            let b = box_val(2);
            let o = alloc_ctor(0, &[a]);
            assert_eq!(ctor_get(o, 0), a);
            ctor_set(o, 0, b);
            assert_eq!(ctor_get(o, 0), b);
            dec(o);
        }
    }

    #[test]
    fn test_ctor_scalar_data_uint64() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let o = alloc_ctor_uninit(0, 0, 8);
            let scalar = ctor_scalar_ptr(o);
            (scalar as *mut u64).write(0xDEAD_BEEF_CAFE_BABE);
            assert_eq!((scalar as *const u64).read(), 0xDEAD_BEEF_CAFE_BABE);
            assert_eq!((*o).header.scalar_sz, 8);
            dec(o);
        }
    }

    #[test]
    fn test_ctor_with_fields_and_scalars() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let field = box_val(99);
            let o = alloc_ctor_uninit(1, 1, 4);
            let field_ptr = obj_fields_ptr(o);
            field_ptr.write(field);
            let scalar = ctor_scalar_ptr(o);
            (scalar as *mut u32).write(12345);
            assert_eq!(ctor_get(o, 0), field);
            assert_eq!((scalar as *const u32).read(), 12345);
            assert_eq!((*o).header.num_objs, 1);
            assert_eq!((*o).header.scalar_sz, 4);
            dec(o);
        }
    }

    #[test]
    fn test_obj_tag_scalar() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let s = box_val(42);
            assert_eq!(obj_tag(s), 42);
        }
    }

    #[test]
    fn test_alloc_ctor_with_tag() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = alloc_ctor(42, &[]);
            assert_eq!(obj_tag(o), 42);
            dec(o);
        }
    }

    #[test]
    fn test_ctor_set_does_not_dec_old_heap_child() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let old_child = alloc_ctor(0, &[]);
            inc(old_child);
            let parent = alloc_ctor(1, &[old_child]);

            let new_child = box_val(99);
            ctor_set(parent, 0, new_child);

            assert_eq!(obj_tag(old_child), 0);
            assert!(!is_unique(old_child));

            dec(old_child);
            assert!(is_unique(old_child));
            dec(old_child);

            dec(parent);
        }
    }

    #[test]
    fn test_ctor_max_fields_u8() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let fields: Vec<*mut LeanObj> =
                (0..255).map(|i| box_val(i % (MAX_SMALL + 1))).collect();
            let o = alloc_ctor(0, &fields);
            assert_eq!((*o).header.num_objs, 255);
            assert_eq!(ctor_get(o, 0), box_val(0));
            assert_eq!(ctor_get(o, 254), box_val(254 % (MAX_SMALL + 1)));
            dec(o);
        }
    }

    #[test]
    fn test_ctor_mixed_many_fields_and_scalar() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let f0 = box_val(1);
            let f1 = box_val(2);
            let f2 = alloc_ctor(0, &[]);
            let o = alloc_ctor_uninit(5, 3, 8);
            let fptr = obj_fields_ptr(o);
            fptr.add(0).write(f0);
            fptr.add(1).write(f1);
            fptr.add(2).write(f2);
            let scalar = ctor_scalar_ptr(o);
            (scalar as *mut u64).write(0xCAFE_BABE);

            assert_eq!(ctor_get(o, 0), f0);
            assert_eq!(ctor_get(o, 1), f1);
            assert_eq!(ctor_get(o, 2), f2);
            assert_eq!((scalar as *const u64).read(), 0xCAFE_BABE);
            assert_eq!((*o).header.num_objs, 3);
            assert_eq!((*o).header.scalar_sz, 8);
            dec(o);
        }
    }
}
