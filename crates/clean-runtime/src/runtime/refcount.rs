// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reference counting: increment, decrement, and uniqueness checks.

use std::alloc;
use std::mem::size_of;
use std::sync::atomic::Ordering;

use super::types::*;
use crate::object_model::{alloc_closure_obj, obj_child_count, obj_child_ptrs, object_layout};

// ---------------------------------------------------------------------------
// Reference counting
// ---------------------------------------------------------------------------

/// Increment the reference count of a heap object. No-op for scalars.
#[inline]
pub(crate) fn lean_inc(o: LeanObjPtr) {
    if !is_scalar(o) {
        // SAFETY: non-scalar means valid heap pointer.
        unsafe {
            (*o).header.ref_count.fetch_add(1, Ordering::Relaxed);
        }
    }
}

/// Increment the reference count by `n`. No-op for scalars.
#[inline]
pub(crate) fn lean_inc_n(o: LeanObjPtr, n: u32) {
    if !is_scalar(o) {
        // SAFETY: non-scalar means valid heap pointer (tagged pointers filtered above).
        unsafe {
            (*o).header.ref_count.fetch_add(n, Ordering::Relaxed);
        }
    }
}

/// Decrement the reference count. If the last reference is dropped, dec all
/// children and deallocate.
///
/// Uses iterative tail-child optimization: for objects with N children,
/// children 0..N-2 are dec'd recursively but the last child (N-1) is handled
/// by looping back, converting O(depth) stack usage to O(1) for linked-list
/// shaped graphs (where the tail pointer is the last field). This prevents
/// stack overflow on deep object graphs (Part of #1934).
///
/// Closure target for External foreach: dec a Lean child and return Unit.
/// Arity 1, invoked via closure_apply when foreach calls the visitor.
/// Matches Lean 4's mark_persistent_fn/mark_mt_fn pattern (object.cpp:542).
/// Part of #2244.
fn dec_child_fn(child: LeanObjPtr) -> LeanObjPtr {
    lean_dec(child);
    lean_box(0) // Lean Unit = boxed 0
}

/// clean up an External object's children and resources before dealloc.
///
/// Calls `foreach` (dec internal Lean children via visitor closure) then
/// `finalize` (release non-Lean FFI resources). Must be called before
/// `alloc::dealloc`. Used by both `lean_dec` (runtime) and `dealloc_obj`
/// (native) to avoid duplicating the foreach+finalize pattern.
///
/// # Safety
///
/// `o` must be a valid External object pointer (kind == External).
pub(crate) unsafe fn external_cleanup(o: LeanObjPtr) {
    // SAFETY: caller guarantees `o` is a valid External object (kind == External).
    // Casting to ExternalObj is valid because the kind check is a precondition.
    // The class pointer is valid for the lifetime of the object. foreach and
    // finalize function pointers (if Some) are safe to call with the external data.
    unsafe {
        let ext = o as *const ExternalObj;
        if let Some(foreach) = (*(*ext).class).foreach {
            let dec_closure = alloc_closure_obj(dec_child_fn as *const (), 1, &[]);
            foreach((*ext).data, dec_closure);
            // Free the temporary closure directly — foreach borrows it
            // (b_lean_obj_arg convention) so refcount is still 0.
            alloc::dealloc(dec_closure as *mut u8, object_layout(dec_closure));
        }
        if let Some(f) = (*(*ext).class).finalize {
            f((*ext).data);
        }
    }
}

/// No-op for scalars.
pub(crate) fn lean_dec(mut o: LeanObjPtr) {
    loop {
        if is_scalar(o) {
            return;
        }
        // SAFETY: non-scalar means valid heap pointer.
        unsafe {
            let old = (*o).header.ref_count.fetch_sub(1, Ordering::Release);
            // `u32::MAX` is the only wrapped sentinel that can result from
            // prior refcount underflow (0 -> MAX) without rejecting still-
            // representable shared counts in the upper half of the u32 range.
            debug_assert_ne!(
                old,
                u32::MAX,
                "dec: ref_count wrapped to u32::MAX before decrement — likely prior underflow"
            );
            if old != 0 {
                // Still referenced — nothing to free.
                return;
            }
            // We held the last reference. Synchronize (acquire) to ensure all
            // writes to the object are visible before we read/free it.
            std::sync::atomic::fence(Ordering::Acquire);

            let kind = ObjKind::from_u8((*o).header.kind);
            let num = obj_child_count(o);
            let layout = object_layout(o);

            if num == 0 {
                // Extended types: dec internal children before dealloc.
                // These types store children in struct fields (not via
                // header.num_objs), so we handle them explicitly here.
                // Part of #2250, #2244, #2241.
                match kind {
                    ObjKind::External => {
                        external_cleanup(o);
                    }
                    ObjKind::Thunk => {
                        let thunk = o as *const ThunkObj;
                        // Dec closure (if unforced) and value (if forced).
                        // Matches Lean 4 lean_thunk_object dealloc.
                        if !(*thunk).closure.is_null() {
                            lean_dec((*thunk).closure);
                        }
                        if !(*thunk).value.is_null() {
                            lean_dec((*thunk).value);
                        }
                    }
                    ObjKind::Task => {
                        let task = o as *const TaskObj;
                        // Dec value when task is complete.
                        if !(*task).value.is_null() {
                            lean_dec((*task).value);
                        }
                    }
                    ObjKind::Array => {
                        // Dec all live elements in the array.
                        // Inline array_data to avoid circular dependency with array module.
                        let arr = o as *const ArrayObj;
                        let sz = (*arr).size;
                        let data = (o as *mut u8).add(size_of::<ArrayObj>()) as *mut LeanObjPtr;
                        for i in 0..sz {
                            lean_dec(*data.add(i));
                        }
                    }
                    _ => {} // Ctor/Closure/Str with 0 children — nothing to dec
                }
                alloc::dealloc(o as *mut u8, layout);
                return;
            }

            // Dec all children except the last, then tail-loop on the last.
            match kind {
                ObjKind::Closure | ObjKind::Ctor | ObjKind::Str => {
                    let children = obj_child_ptrs(o);
                    for i in 0..num - 1 {
                        lean_dec(*children.add(i));
                    }
                    let last = *children.add(num - 1);
                    alloc::dealloc(o as *mut u8, layout);
                    o = last;
                }
                ObjKind::Array | ObjKind::Thunk | ObjKind::Task | ObjKind::External => {
                    // Extended types always have header.num_objs == 0, so
                    // num > 0 is unreachable. Handled in the num == 0 branch
                    // above. Part of #2250.
                    lean_panic("lean_dec: extended type with num_objs > 0");
                }
            }
        }
    }
}

/// Returns `true` if the object is uniquely owned (ref_count == 0).
/// Scalars are always considered unique.
#[inline]
pub(crate) fn lean_is_unique(o: LeanObjPtr) -> bool {
    if is_scalar(o) {
        return true;
    }
    // SAFETY: non-scalar means valid heap pointer.
    // Relaxed suffices: is_unique is a hint for reuse optimization.
    // False positive (shared when exclusive) → unnecessary alloc (safe).
    // False negative cannot happen — the caller holds a reference.
    // Matches Lean 4 lean_is_exclusive (lean.h:550).
    unsafe { (*o).header.ref_count.load(Ordering::Relaxed) == 0 }
}
