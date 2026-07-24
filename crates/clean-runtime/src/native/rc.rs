// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![allow(unsafe_op_in_unsafe_fn)]

//! Reference counting and deallocation for clean objects.
//!
//! Ref count semantics: 0 = uniquely owned (1 reference), N = (N+1) references.

use std::alloc::{self, Layout};
use std::mem::{align_of, size_of};
use std::sync::atomic::Ordering;

use crate::object_model::{
    alloc_closure_obj, is_scalar, lean_box, obj_child_count, obj_child_ptrs, object_layout,
    ArrayObj, CleanObj, ExternalObj, LeanObjPtr, ObjKind, TaskObj, ThunkObj,
};

// Type aliases for native naming convention.
type LeanObj = CleanObj;

/// Closure target for External foreach: dec a Lean child and return Unit.
/// # Safety
/// `child` must be a valid LeanObjPtr (heap object or tagged scalar).
unsafe fn dec_child_fn(child: LeanObjPtr) -> LeanObjPtr {
    dec(child as *mut LeanObj);
    lean_box(0)
}

/// clean up an External object's children and resources before dealloc.
/// # Safety
/// `o` must be a valid External object pointer (kind == External).
unsafe fn external_cleanup(o: LeanObjPtr) {
    // SAFETY: Caller guarantees `o` is a valid External object. The cast to
    // ExternalObj is valid because kind == External. Dereferencing class to
    // read foreach/finalize function pointers is valid because the class
    // pointer outlives the object (caller contract on alloc_external).
    // The temporary dec_closure is freed directly after foreach returns
    // (b_lean_obj_arg convention — foreach borrows, refcount stays 0).
    let ext = o as *const ExternalObj;
    if let Some(foreach) = (*(*ext).class).foreach {
        let dec_closure = alloc_closure_obj(dec_child_fn as *const (), 1, &[]);
        foreach((*ext).data, dec_closure);
        alloc::dealloc(dec_closure as *mut u8, object_layout(dec_closure));
    }
    if let Some(finalize) = (*(*ext).class).finalize {
        finalize((*ext).data);
    }
}

/// Increment reference count.
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
#[inline]
pub unsafe fn inc(o: *mut LeanObj) {
    if !is_scalar(o) {
        // SAFETY: is_scalar check ensures `o` is a valid heap pointer.
        // Relaxed ordering suffices — inc only needs atomicity, not ordering.
        (*o).header.ref_count.fetch_add(1, Ordering::Relaxed);
    }
}

/// Increment reference count by `n`.
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
#[inline]
pub unsafe fn inc_n(o: *mut LeanObj, n: u32) {
    if !is_scalar(o) {
        // SAFETY: is_scalar check ensures `o` is a valid heap pointer.
        (*o).header.ref_count.fetch_add(n, Ordering::Relaxed);
    }
}

/// Check if the object is uniquely owned (ref_count == 0 means 1 reference).
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
#[inline]
#[must_use]
pub unsafe fn is_unique(o: *const LeanObj) -> bool {
    if is_scalar(o) {
        return true;
    }
    // SAFETY: is_scalar check ensures `o` is a valid heap pointer.
    // Relaxed suffices: is_unique is a hint for reuse optimization.
    // False positive (shared when exclusive) → unnecessary alloc (safe).
    // False negative cannot happen — the caller holds a reference.
    // Matches Lean 4 lean_is_exclusive (lean.h:550).
    (*o).header.ref_count.load(Ordering::Relaxed) == 0
}

/// Decrement reference count. Free the object (and recursively dec fields)
/// when the last reference is released.
///
/// # Safety
/// `o` must be a valid clean object pointer or tagged scalar.
/// After calling dec, `o` must not be used unless the caller holds
/// another reference.
pub unsafe fn dec(o: *mut LeanObj) {
    if is_scalar(o) {
        return;
    }
    // SAFETY: is_scalar check ensures `o` is a valid heap pointer.
    // Release ordering ensures all prior writes are visible before the
    // ref_count drop. The Acquire fence below synchronizes with this
    // Release when the last reference is dropped (old == 0).
    let old = (*o).header.ref_count.fetch_sub(1, Ordering::Release);
    // `u32::MAX` is the only wrapped sentinel that can result from prior
    // refcount underflow (0 -> MAX) without rejecting still-representable
    // shared counts in the upper half of the `u32` range.
    debug_assert_ne!(
        old,
        u32::MAX,
        "dec: ref_count wrapped to u32::MAX before decrement — likely prior underflow"
    );
    if old == 0 {
        // Was uniquely owned — synchronize with the Release store above
        // to ensure all writes by other threads that previously held
        // references are visible before we read the object's fields
        // during recursive deallocation.
        std::sync::atomic::fence(Ordering::Acquire);
        dealloc_obj(o);
    }
}

/// Deallocate a clean object, recursively decrementing child references.
///
/// Reads `scalar_sz` from the header to compute the correct deallocation
/// `Layout`, addressing the UB where scalar payload size was ignored (#1904).
///
/// # Safety
/// `o` must be a valid, uniquely owned clean heap object.
unsafe fn dealloc_obj(o: *mut LeanObj) {
    let kind = ObjKind::from_u8((*o).header.kind);

    if matches!(kind, ObjKind::Ctor | ObjKind::Closure | ObjKind::Str) {
        let num_children = obj_child_count(o);
        let children = obj_child_ptrs(o);
        for i in 0..num_children {
            dec(*children.add(i));
        }
        alloc::dealloc(o as *mut u8, object_layout(o));
    } else if kind == ObjKind::Thunk {
        // SAFETY: kind == Thunk guarantees `o` was allocated as ThunkObj.
        // Dec children before dealloc. Part of #2250.
        let thunk = o as *const ThunkObj;
        if !(*thunk).closure.is_null() {
            dec((*thunk).closure as *mut LeanObj);
        }
        if !(*thunk).value.is_null() {
            dec((*thunk).value as *mut LeanObj);
        }
        let layout = Layout::new::<ThunkObj>();
        alloc::dealloc(o as *mut u8, layout);
    } else if kind == ObjKind::Task {
        // SAFETY: kind == Task guarantees `o` was allocated as TaskObj.
        let task = o as *const TaskObj;
        if !(*task).value.is_null() {
            dec((*task).value as *mut LeanObj);
        }
        let layout = Layout::new::<TaskObj>();
        alloc::dealloc(o as *mut u8, layout);
    } else if kind == ObjKind::External {
        // SAFETY: kind == External guarantees `o` was allocated as ExternalObj.
        // Calls foreach (dec Lean children) + finalize (free FFI resources)
        // via shared helper. Part of #2250 self-audit.
        external_cleanup(o as LeanObjPtr);
        let layout = Layout::new::<ExternalObj>();
        alloc::dealloc(o as *mut u8, layout);
    } else if kind == ObjKind::Array {
        // SAFETY: kind == Array guarantees `o` was allocated as ArrayObj +
        // flexible trailing buffer. Reconstruct the layout from capacity.
        let arr = o as *const ArrayObj;
        let cap = (*arr).capacity;
        let size = size_of::<ArrayObj>() + cap * size_of::<*mut LeanObj>();
        let layout = Layout::from_size_align(size, align_of::<ArrayObj>())
            .expect("invalid array dealloc layout");
        // Dec all live elements before dealloc.
        let data = (o as *const u8).add(size_of::<ArrayObj>()) as *const *mut LeanObj;
        let sz = (*arr).size;
        for i in 0..sz {
            dec(*data.add(i));
        }
        alloc::dealloc(o as *mut u8, layout);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::alloc::alloc_ctor_uninit;
    use crate::native::{alloc_ctor, box_val, obj_tag};

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
