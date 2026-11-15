// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reference counting and deallocation for clean objects.
//!
//! Ref count semantics: 0 = uniquely owned (1 reference), N = (N+1)
//! references below the sticky band; a count at or above
//! `rc_core::RC_STICKY_DROP` is frozen and its object is never freed. Thin
//! `unsafe` names over [`crate::rc_core`], which `runtime::refcount` shares.

use crate::object_model::CleanObj;
use crate::rc_core;

// Type aliases for native naming convention.
type LeanObj = CleanObj;

/// Increment reference count. No-op for scalars and frozen counts.
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
#[inline]
pub unsafe fn inc(o: *mut LeanObj) {
    rc_core::inc_n(o, 1);
}

/// Increment reference count by `n`. No-op for scalars and frozen counts; an
/// `n` that would pass the band leaves the count frozen.
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
#[inline]
pub unsafe fn inc_n(o: *mut LeanObj, n: usize) {
    rc_core::inc_n(o, n);
}

/// Check if the object is uniquely owned (ref_count == 0 means 1 reference).
/// A frozen object is never unique.
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
#[inline]
#[must_use]
pub unsafe fn is_unique(o: *const LeanObj) -> bool {
    rc_core::is_exclusive(o.cast_mut())
}

/// Decrement reference count. Free the object, and every child the last
/// reference kept alive, when the last reference is released. No-op for
/// frozen counts.
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
/// After calling dec, `o` must not be used unless the caller holds
/// another reference.
pub unsafe fn dec(o: *mut LeanObj) {
    rc_core::dec(o);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::alloc::alloc_ctor_uninit;
    use crate::native::{alloc_ctor, box_val, obj_tag};
    use crate::object_model::is_scalar;
    use std::mem::size_of;
    use std::sync::atomic::Ordering;

    #[test]
    fn test_new_object_is_unique() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = alloc_ctor_uninit(0, 0, 0);
            assert!(is_unique(o));
            dec(o);
        }
    }

    #[test]
    fn test_inc_makes_non_unique() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = alloc_ctor_uninit(0, 0, 0);
            inc(o);
            assert!(!is_unique(o));
            dec(o); // back to uniquely owned
            assert!(is_unique(o));
            dec(o); // free
        }
    }

    #[test]
    fn test_inc_n_adds_n_refs() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = alloc_ctor_uninit(0, 0, 0);
            inc_n(o, 3);
            assert!(!is_unique(o));
            dec(o);
            dec(o);
            dec(o);
            assert!(is_unique(o));
            dec(o); // free
        }
    }

    #[test]
    fn test_inc_dec_on_scalar_is_noop() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let s = box_val(42);
            inc(s);
            dec(s);
            assert!(is_scalar(s));
            assert_eq!(super::super::unbox_val(s), 42);
        }
    }

    #[test]
    fn test_dec_frees_children() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let child1 = alloc_ctor(0, &[]);
            let child2 = alloc_ctor(1, &[]);
            let parent = alloc_ctor(2, &[child1, child2]);
            dec(parent);
        }
    }

    #[test]
    fn test_dec_shared_child_not_freed() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let child = alloc_ctor(0, &[]);
            inc(child); // child has 2 references
            let parent = alloc_ctor(1, &[child]);
            dec(parent); // decrements child, but child still has 1 ref
            assert_eq!(obj_tag(child), 0);
            dec(child); // now free child
        }
    }

    #[test]
    fn test_dealloc_ctor_with_scalar_sz_8() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let o = crate::native::box_uint64(42);
            assert_eq!((*o).header.scalar_sz, 8);
            dec(o);
        }
    }

    /// Verify that dealloc computes the correct layout for a Ctor with scalar
    /// payload (scalar_sz=4, num_objs=0). Regression for #1904.
    #[test]
    fn test_dealloc_ctor_with_scalar_sz_4() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            // Construct a heap Ctor directly — box_uint32 returns a tagged
            // scalar for all u32 values on 64-bit (MAX_SMALL = usize::MAX >> 1).
            let o = alloc_ctor_uninit(0, 0, size_of::<u32>() as u8);
            assert!(
                !is_scalar(o),
                "regression test requires a heap-allocated ctor"
            );
            assert_eq!((*o).header.scalar_sz, 4);
            let scalar = crate::native::ctor_scalar_ptr(o);
            (scalar as *mut u32).write(0x1000);
            dec(o);
        }
    }

    /// Verify that dec on a closure recursively decrements captured heap args.
    /// Issue #1908: only Ctor recursive dec was tested.
    #[test]
    fn test_closure_dec_frees_captured_heap_args() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let arg1 = alloc_ctor(0, &[]);
            let arg2 = alloc_ctor(1, &[]);
            // Both args are uniquely owned (ref_count = 0)
            assert!(is_unique(arg1));
            assert!(is_unique(arg2));

            let fun = std::ptr::null_mut::<()>();
            let closure = crate::native::alloc_closure(fun, 3, &[arg1, arg2]);
            // Dropping the closure should recursively dec both captured args
            dec(closure);
            // If dealloc_obj didn't handle Closure child fields, Miri would
            // report use-after-free or leak.
        }
    }

    /// Verify that dec handles deeply nested object trees without stack overflow.
    /// Tests recursive deallocation through 3 levels of Ctor nesting.
    #[test]
    fn test_dec_nested_tree() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let leaf1 = alloc_ctor(0, &[]);
            let leaf2 = alloc_ctor(0, &[]);
            let mid = alloc_ctor(1, &[leaf1, leaf2]);
            let root = alloc_ctor(2, &[mid]);
            // Dropping root should recursively free mid, leaf1, leaf2
            dec(root);
        }
    }

    /// Verify that dec on a closure with mixed scalar/heap captured args
    /// correctly skips scalars and frees heap objects.
    #[test]
    fn test_closure_dec_mixed_scalar_heap_args() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let scalar_arg = box_val(42); // tagged pointer, not heap
            let heap_arg = alloc_ctor(0, &[]);
            assert!(is_scalar(scalar_arg));
            assert!(!is_scalar(heap_arg));

            let fun = std::ptr::null_mut::<()>();
            let closure = crate::native::alloc_closure(fun, 3, &[scalar_arg, heap_arg]);
            dec(closure);
            // inc/dec on scalar is a no-op, so this should work cleanly
        }
    }

    /// Verify that dec on a string object deallocates correctly.
    #[test]
    fn test_dec_string_object() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let s = crate::native::mk_string(b"adversarial test string");
            assert!(!is_scalar(s));
            dec(s);
            // Miri will catch mismatched Layout on dealloc
        }
    }

    // -- Native dec path for extended types (Part of #2250 self-audit) --
    // These tests exercise dealloc_obj through native::dec, not lean_dec.

    /// Verify that native dec handles ThunkObj with correct layout (24 bytes,
    /// not obj_layout(0,0) = 8 bytes). Also tests child dec for closure.
    #[test]
    fn test_native_dec_thunk_correct_layout() {
        use crate::runtime::{alloc_thunk, lean_box};
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            // Scalar closure — no child to dec, just tests layout correctness.
            let thunk = alloc_thunk(lean_box(0));
            dec(thunk as *mut LeanObj);
        }
    }

    /// Verify that native dec handles TaskObj with correct layout.
    #[test]
    fn test_native_dec_task_correct_layout() {
        use crate::runtime::alloc_task;
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let task = alloc_task(std::ptr::null_mut());
            dec(task as *mut LeanObj);
        }
    }

    /// Verify that native dec handles ExternalObj with correct layout
    /// and calls finalize.
    #[test]
    fn test_native_dec_external_calls_finalize() {
        use crate::runtime::{alloc_external, CleanExternalClass};
        use std::sync::atomic::AtomicBool;
        static FINALIZED: AtomicBool = AtomicBool::new(false);

        unsafe fn test_fin(_data: *mut ()) {
            FINALIZED.store(true, Ordering::SeqCst);
        }

        static CLASS: CleanExternalClass = CleanExternalClass {
            finalize: Some(test_fin),
            foreach: None,
        };

        FINALIZED.store(false, Ordering::SeqCst);
        // SAFETY: Pointers are valid heap objects allocated by the runtime.
        unsafe {
            let ext = alloc_external(&CLASS, std::ptr::null_mut());
            dec(ext as *mut LeanObj);
        }
        assert!(
            FINALIZED.load(Ordering::SeqCst),
            "native dec must call finalize for External objects"
        );
    }

    /// Verify that native dec handles ArrayObj with correct capacity-based layout
    /// and decs all live elements.
    #[test]
    fn test_native_dec_array_decs_elements() {
        use crate::runtime::{alloc_array, alloc_ctor_uninit, array_push};
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let arr = alloc_array(2);
            let c1 = alloc_ctor_uninit(0, 0, 0);
            // array_push takes ownership of the caller's reference (rc=0 →
            // array is sole owner). No clean_inc needed.
            let arr = array_push(arr, c1);
            // Drop via native dec — should use correct layout and dec elements.
            dec(arr as *mut LeanObj);
        }
    }

    /// Verify that shared refcounts in the upper half of the u32 space do not
    /// trigger the underflow guard. Part of #2111.
    #[test]
    fn test_dec_allows_high_bit_shared_refcount() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let o = alloc_ctor_uninit(0, 0, 0);
            (*o).header.ref_count.store(0x8000_0000, Ordering::Relaxed);
            dec(o);
            assert_eq!(
                (*o).header.ref_count.load(Ordering::Relaxed),
                0x7FFF_FFFF,
                "dec must accept still-representable shared refcounts"
            );

            // Restore unique ownership so the test can free the object cleanly.
            (*o).header.ref_count.store(0, Ordering::Relaxed);
            dec(o);
        }
    }

    /// Verify that the debug_assert in dec() detects the wrapped underflow
    /// sentinel (`u32::MAX`). Part of #2111.
    #[test]
    #[should_panic(expected = "ref_count wrapped to u32::MAX")]
    fn test_dec_underflow_detected() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let o = alloc_ctor_uninit(0, 0, 0);
            (*o).header.ref_count.store(u32::MAX, Ordering::Relaxed);
            dec(o);
        }
    }
}
