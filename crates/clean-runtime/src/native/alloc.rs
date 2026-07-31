// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Object allocation, reset, and reuse for clean runtime.

use std::alloc;
use std::sync::atomic::AtomicU32;

use super::expect;
use super::rc::dec;
use super::rc::is_unique;
#[cfg(test)]
use crate::object_model::closure_args_ptr;
use crate::object_model::{
    alloc_closure_obj, ctor_layout, obj_child_count, obj_child_ptrs, obj_fields_ptr, object_layout,
    CleanObj, ObjKind,
};

// Type aliases for native naming convention.
type LeanObj = CleanObj;
#[cfg(test)]
type LeanClosure = crate::object_model::ClosureObj;

/// Allocate a constructor without initializing fields.
///
/// Returns a uniquely owned object (ref_count = 0).
/// Stores `scalar_sz` in the header for correct deallocation.
///
/// # Safety
/// Caller must initialize all `num_objs` pointer fields and any scalar data
/// before sharing the object.
#[must_use]
pub(crate) unsafe fn alloc_ctor_uninit(tag: u8, num_objs: u8, scalar_sz: u8) -> *mut LeanObj {
    // SAFETY: The caller upholds this function’s documented Lean-object validity and ownership contract; checked layouts bound every allocation and pointer access below.
    unsafe {
        let layout = ctor_layout(num_objs, scalar_sz);
        let ptr = alloc::alloc(layout) as *mut LeanObj;
        if ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }
        // SAFETY: ptr is non-null, layout covers ObjHeader + fields + scalar.
        (*ptr).header.ref_count = AtomicU32::new(0);
        (*ptr).header.tag = tag;
        (*ptr).header.kind = ObjKind::Ctor as u8;
        (*ptr).header.num_objs = num_objs;
        (*ptr).header.scalar_sz = scalar_sz;
        ptr
    }
}

/// Allocate a constructor with the given object fields (no scalar payload).
///
/// # Safety
/// All elements of `fields` must be valid clean object pointers or tagged scalars.
#[must_use]
pub unsafe fn alloc_ctor(tag: u8, fields: &[*mut LeanObj]) -> *mut LeanObj {
    // SAFETY: The caller upholds this function’s documented Lean-object validity and ownership contract; checked layouts bound every allocation and pointer access below.
    unsafe {
        expect(
            fields.len() <= u8::MAX as usize,
            "alloc_ctor: fields.len() exceeds u8::MAX",
        );
        let num_objs = fields.len() as u8;
        let o = alloc_ctor_uninit(tag, num_objs, 0);
        // SAFETY: allocation has num_objs pointer slots; i < num_objs.
        let field_ptr = obj_fields_ptr(o);
        for (i, &f) in fields.iter().enumerate() {
            field_ptr.add(i).write(f);
        }
        o
    }
}

/// Allocate a closure.
///
/// # Safety
/// `fun` must be a valid function pointer. All `args` must be valid clean objects.
#[must_use]
pub unsafe fn alloc_closure(fun: *mut (), arity: u16, args: &[*mut LeanObj]) -> *mut LeanObj {
    alloc_closure_obj(fun as *const (), arity, args)
}

/// Reset an object for potential reuse. Ctor: dec children, return slot.
/// Closure: dec args via `num_fixed`, free, return null (#1944).
///
/// # Safety
/// `o` must be a valid clean heap object (Ctor or Closure).
#[must_use]
pub unsafe fn reset(o: *mut LeanObj) -> *mut LeanObj {
    // SAFETY: The caller upholds this function’s documented Lean-object validity and ownership contract; checked layouts bound every allocation and pointer access below.
    unsafe {
        if !is_unique(o) {
            dec(o);
            return std::ptr::null_mut();
        }

        let kind = ObjKind::from_u8((*o).header.kind);
        match kind {
            ObjKind::Ctor => {
                let num_children = obj_child_count(o);
                let children = obj_child_ptrs(o);
                for i in 0..num_children {
                    dec(*children.add(i));
                }
                o
            }
            ObjKind::Closure | ObjKind::Str => {
                let num_children = obj_child_count(o);
                let children = obj_child_ptrs(o);
                for i in 0..num_children {
                    dec(*children.add(i));
                }
                alloc::dealloc(o as *mut u8, object_layout(o));
                std::ptr::null_mut()
            }
            ObjKind::Array | ObjKind::Thunk | ObjKind::Task | ObjKind::External => {
                dec(o);
                std::ptr::null_mut()
            }
        }
    }
}

/// Reuse a reset slot or allocate a new constructor. Same-inductive-type
/// invariants are enforced in release builds. `scalar_sz` for fallback alloc
/// (#1928).
///
/// # Safety
/// `reset_slot` must be null or a valid reset Ctor from the same inductive type.
#[must_use]
pub unsafe fn reuse(
    reset_slot: *mut LeanObj,
    tag: u8,
    fields: &[*mut LeanObj],
    scalar_sz: u8,
) -> *mut LeanObj {
    // SAFETY: The caller upholds this function’s documented Lean-object validity and ownership contract; checked layouts bound every allocation and pointer access below.
    unsafe {
        expect(
            fields.len() <= u8::MAX as usize,
            "reuse: fields.len() exceeds u8::MAX",
        );
        let o = if !reset_slot.is_null() {
            // SAFETY: reset_slot is a valid, uniquely-owned Ctor from reset().
            // Closure-to-Ctor reuse is UB (layout mismatch).
            expect(
                (*reset_slot).header.kind == ObjKind::Ctor as u8,
                "reuse: reset_slot must be a constructor",
            );
            // Same-inductive-type invariant: num_objs and scalar_sz must match.
            expect(
                (*reset_slot).header.num_objs as usize == fields.len(),
                "reuse: field count must match slot capacity",
            );
            expect(
                (*reset_slot).header.scalar_sz == scalar_sz,
                "reuse: scalar size must match slot layout",
            );
            // SAFETY: uniquely owned after reset(). Writing header is safe.
            (*reset_slot).header.tag = tag;
            (*reset_slot)
                .header
                .ref_count
                .store(0, std::sync::atomic::Ordering::Relaxed);
            reset_slot
        } else {
            alloc_ctor_uninit(tag, fields.len() as u8, scalar_sz)
        };
        // SAFETY: `o` is a valid Ctor allocation (either reused slot or fresh
        // alloc) with at least fields.len() pointer slots.
        let field_ptr = obj_fields_ptr(o);
        for (i, &f) in fields.iter().enumerate() {
            // SAFETY: i < fields.len() == num_objs, within the allocation.
            field_ptr.add(i).write(f);
        }
        o
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::{box_val, ctor_get, dec, is_scalar, is_unique, obj_tag};

    #[test]
    fn test_alloc_closure_empty() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let fun = std::ptr::null_mut::<()>();
            let o = alloc_closure(fun, 2, &[]);
            assert!(!is_scalar(o));
            assert_eq!((*o).header.kind, ObjKind::Closure as u8);
            dec(o);
        }
    }

    #[test]
    fn test_alloc_closure_with_args() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let fun = std::ptr::null_mut::<()>();
            let arg1 = box_val(10);
            let arg2 = box_val(20);
            let o = alloc_closure(fun, 3, &[arg1, arg2]);
            let c = o as *const LeanClosure;
            assert_eq!((*c).arity, 3);
            assert_eq!((*c).num_fixed, 2);
            let args = closure_args_ptr(c);
            assert_eq!(*args.add(0), arg1);
            assert_eq!(*args.add(1), arg2);
            dec(o);
        }
    }

    #[test]
    fn test_reset_unique_returns_object() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let a = box_val(1);
            let o = alloc_ctor(0, &[a]);
            let slot = reset(o);
            assert!(!slot.is_null());
            assert_eq!(slot, o);
            // Must free the reset slot since fields were dec'd but memory remains
            alloc::dealloc(
                slot as *mut u8,
                ctor_layout((*slot).header.num_objs, (*slot).header.scalar_sz),
            );
        }
    }

    #[test]
    fn test_reset_shared_returns_null() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = alloc_ctor(0, &[]);
            crate::native::inc(o); // now shared
            let slot = reset(o);
            assert!(slot.is_null());
            dec(o);
        }
    }

    #[test]
    fn test_reuse_with_slot() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let a = box_val(1);
            let o = alloc_ctor(0, &[a]);
            let slot = reset(o);
            assert!(!slot.is_null());

            let b = box_val(2);
            let reused = reuse(slot, 3, &[b], 0);
            assert_eq!(reused, slot);
            assert_eq!(obj_tag(reused), 3);
            assert_eq!(ctor_get(reused, 0), b);
            dec(reused);
        }
    }

    #[test]
    fn test_reuse_without_slot_allocates() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let a = box_val(1);
            let o = reuse(std::ptr::null_mut(), 5, &[a], 0);
            assert_eq!(obj_tag(o), 5);
            assert_eq!(ctor_get(o, 0), a);
            dec(o);
        }
    }

    #[test]
    fn test_reuse_resets_refcount() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let a = box_val(1);
            let o = alloc_ctor(0, &[a]);
            // Object starts uniquely owned
            assert!(is_unique(o));
            let slot = reset(o);
            assert!(!slot.is_null());

            let b = box_val(2);
            let reused = reuse(slot, 3, &[b], 0);
            // Reused object must be uniquely owned (ref_count reset to 0)
            assert!(is_unique(reused));
            dec(reused);
        }
    }

    #[test]
    fn test_alloc_ctor_uninit_stores_scalar_sz() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            // Use num_objs=0 to test header storage without needing field init
            let o = alloc_ctor_uninit(7, 0, 16);
            assert_eq!((*o).header.tag, 7);
            assert_eq!((*o).header.num_objs, 0);
            assert_eq!((*o).header.scalar_sz, 16);
            assert_eq!((*o).header.kind, ObjKind::Ctor as u8);
            assert!(is_unique(o));
            dec(o);
        }
    }

    /// Issue #1908: reset with heap children must actually decrement them.
    /// Previous test only used scalar fields (dec is a no-op on scalars).
    #[test]
    fn test_reset_decrements_heap_children() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let child = alloc_ctor(0, &[]);
            crate::native::inc(child); // ref_count = 1 (2 references)
            let parent = alloc_ctor(1, &[child]);
            // parent owns one ref to child, we hold another via inc

            let slot = reset(parent);
            assert!(!slot.is_null());
            // After reset, child should have been dec'd back to unique
            assert!(is_unique(child));
            dec(child); // free our reference

            // Free the reset slot
            alloc::dealloc(
                slot as *mut u8,
                ctor_layout((*slot).header.num_objs, (*slot).header.scalar_sz),
            );
        }
    }

    /// Issue #1908: reuse must work correctly with heap children.
    /// Lean 4 compiler guarantees same-ctor reuse (same num_objs).
    #[test]
    fn test_reuse_same_field_count_heap_children() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let old_child = alloc_ctor(0, &[]);
            let parent = alloc_ctor(1, &[old_child]);

            let slot = reset(parent);
            assert!(!slot.is_null());
            // old_child was dec'd by reset (freed since uniquely owned)

            let new_child = alloc_ctor(2, &[]);
            let reused = reuse(slot, 3, &[new_child], 0);
            assert_eq!(reused, slot);
            assert_eq!(obj_tag(reused), 3);
            assert_eq!(ctor_get(reused, 0), new_child);
            dec(reused); // frees reused + new_child
        }
    }

    /// Issue #1908: closure allocation with many captured args.
    #[test]
    fn test_alloc_closure_many_args() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let fun = std::ptr::null_mut::<()>();
            let args: Vec<*mut LeanObj> = (0..10).map(box_val).collect();
            let o = alloc_closure(fun, 12, &args);
            let c = o as *const LeanClosure;
            assert_eq!((*c).arity, 12);
            assert_eq!((*c).num_fixed, 10);
            let arg_ptr = closure_args_ptr(c);
            for i in 0..10 {
                assert_eq!(*arg_ptr.add(i), box_val(i));
            }
            dec(o);
        }
    }

    /// INV-5: closure header.num_objs == 0 (matches Lean 4).
    ///
    /// alloc_closure sets header.num_objs = 0. The authoritative captured arg
    /// count is LeanClosure.num_fixed (u16). This eliminates the u8 truncation
    /// bug (#1937) — reset() and dec() dispatch on kind to read num_fixed.
    #[test]
    fn test_closure_header_num_objs_is_zero() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let fun = std::ptr::null_mut::<()>();
            // 10 scalar args
            let args: Vec<*mut LeanObj> = (0..10).map(box_val).collect();
            let o = alloc_closure(fun, 12, &args);
            let c = o as *const LeanClosure;

            // INV-5: header.num_objs must be 0 for closures
            assert_eq!((*o).header.num_objs, 0);
            // INV-6: header.scalar_sz must be 0 for closures
            assert_eq!((*o).header.scalar_sz, 0);
            // Authoritative count is in the closure struct
            assert_eq!((*c).num_fixed, 10);
            dec(o);
        }
    }

    /// Reuse fallback (null slot) allocates with the provided scalar_sz.
    ///
    /// Before #1928, the fallback hardcoded scalar_sz=0, which caused
    /// dealloc layout mismatch UB for scalar-bearing constructors.
    #[test]
    fn test_reuse_null_slot_preserves_scalar_sz() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            // Pure-object ctor: scalar_sz=0
            let f0 = box_val(42);
            let f1 = box_val(99);
            let o = reuse(std::ptr::null_mut(), 7, &[f0, f1], 0);
            assert_eq!(obj_tag(o), 7);
            assert_eq!((*o).header.num_objs, 2);
            assert_eq!((*o).header.scalar_sz, 0);
            assert_eq!(ctor_get(o, 0), f0);
            assert_eq!(ctor_get(o, 1), f1);
            dec(o);

            // Scalar-bearing ctor: scalar_sz=8 (e.g., boxed UInt64)
            let o2 = reuse(std::ptr::null_mut(), 0, &[], 8);
            assert_eq!((*o2).header.num_objs, 0);
            assert_eq!(
                (*o2).header.scalar_sz,
                8,
                "reuse fallback must use provided scalar_sz, not hardcode 0"
            );
            // Write and read back scalar data to verify allocation is large enough
            let scalar = crate::native::ctor_scalar_ptr(o2);
            (scalar as *mut u64).write(0xDEAD_BEEF_CAFE_BABE);
            assert_eq!((scalar as *const u64).read(), 0xDEAD_BEEF_CAFE_BABE);
            dec(o2);
        }
    }

    /// Issue #1928: reuse with non-null slot preserves original scalar_sz.
    /// Verifies the slot path doesn't corrupt scalar data.
    #[test]
    fn test_reuse_slot_preserves_scalar_data() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            // Allocate a ctor with scalar data (num_objs=0, scalar_sz=8)
            let o = alloc_ctor_uninit(0, 0, 8);
            let scalar = crate::native::ctor_scalar_ptr(o);
            (scalar as *mut u64).write(0xCAFE);

            // Reset returns the slot (uniquely owned)
            let slot = reset(o);
            assert!(!slot.is_null());
            assert_eq!((*slot).header.scalar_sz, 8);

            // Reuse the slot with same layout (0 fields, 8 bytes scalar)
            let reused = reuse(slot, 5, &[], 8);
            assert_eq!(reused, slot);
            assert_eq!((*reused).header.tag, 5);
            assert_eq!((*reused).header.scalar_sz, 8);
            // Write new scalar data
            let scalar2 = crate::native::ctor_scalar_ptr(reused);
            (scalar2 as *mut u64).write(0xBEEF);
            assert_eq!((scalar2 as *const u64).read(), 0xBEEF);
            dec(reused);
        }
    }

    /// Issue #1944: reset() on a closure dispatches to closure layout,
    /// decrements captured args, frees the closure, and returns null.
    /// Closures cannot be reused as Ctor slots (layout mismatch).
    #[test]
    fn test_reset_closure_returns_null() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let fun = std::ptr::null_mut::<()>();
            let arg = box_val(42);
            let closure = alloc_closure(fun, 2, &[arg]);
            // reset() on a closure: dec captured args, free, return null
            let slot = reset(closure);
            assert!(slot.is_null(), "reset() on closure must return null");
        }
    }

    /// Issue #1944: reset() on a closure with heap children correctly
    /// decrements their ref counts before freeing.
    #[test]
    fn test_reset_closure_decrements_heap_children() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let child = alloc_ctor(0, &[]);
            crate::native::inc(child); // ref_count = 1 (2 references)
            let fun = std::ptr::null_mut::<()>();
            let closure = alloc_closure(fun, 2, &[child]);
            // We hold one ref to child via inc, closure holds another

            let slot = reset(closure);
            assert!(slot.is_null());
            // After reset, child should have been dec'd back to unique
            assert!(is_unique(child));
            dec(child); // free our reference
        }
    }
}
