// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![allow(unsafe_op_in_unsafe_fn)]

//! Array operations (COW semantics) and extended type allocation
//! (thunk, task, external).

use std::alloc;
use std::mem::size_of;
use std::sync::atomic::AtomicU32;

use super::ctor_scalar::alloc_ctor_uninit;
use super::refcount::{lean_dec, lean_inc, lean_inc_n, lean_is_unique};
use super::types::*;
use crate::object_model::{alloc_string_bytes, array_layout, object_layout};

// ---------------------------------------------------------------------------
// Array allocation and access
// ---------------------------------------------------------------------------

/// Allocate an array with the given initial capacity.
///
/// The returned array has `size = 0` (empty) and `capacity = cap`.
pub(crate) fn alloc_array(cap: usize) -> LeanObjPtr {
    let layout = array_layout(cap);
    // SAFETY: `layout` was computed by array_layout which produces a valid,
    // non-zero-sized layout. alloc::alloc returns a valid pointer or null.
    let raw = unsafe { alloc::alloc(layout) };
    if raw.is_null() {
        lean_panic("out of memory");
    }
    let arr = raw as *mut ArrayObj;
    // SAFETY: `arr` is non-null (checked above) and points to a freshly
    // allocated region of array_layout(cap) bytes. Header is written via
    // `&raw mut` to avoid referencing uninitialized memory. The size and
    // capacity fields are within the ArrayObj struct.
    unsafe {
        std::ptr::write(
            &raw mut (*arr).header,
            ObjHeader {
                ref_count: AtomicU32::new(0),
                tag: 0,
                kind: ObjKind::Array as u8,
                num_objs: 0, // Array uses .size, not header.num_objs
                scalar_sz: 0,
            },
        );
        (*arr).size = 0;
        (*arr).capacity = cap;
    }
    arr as LeanObjPtr
}

/// Get the data pointer for an array (pointer to first element slot).
///
/// # Safety
///
/// `o` must be an Array object.
#[inline]
pub(crate) unsafe fn array_data(o: LeanObjPtr) -> *mut LeanObjPtr {
    (o as *mut u8).add(size_of::<ArrayObj>()) as *mut LeanObjPtr
}

/// Get the array size (number of elements).
///
/// # Safety
///
/// `o` must be an Array object.
#[inline]
pub(crate) unsafe fn array_size(o: LeanObjPtr) -> usize {
    (*(o as *mut ArrayObj)).size
}

/// Push an element onto the array with COW and automatic reallocation.
///
/// Returns the (possibly new) array pointer. The caller must use the
/// returned pointer, not the original — COW or reallocation may have
/// produced a new allocation.
///
/// Matches Lean 4 `lean_array_push` (object.cpp:2640-2656). Part of #2020.
///
/// # Safety
///
/// `o` must be a valid Array object pointer. `v` is a valid obj pointer.
pub(crate) unsafe fn array_push(o: LeanObjPtr, v: LeanObjPtr) -> LeanObjPtr {
    let arr = o as *const ArrayObj;
    let sz = (*arr).size;
    let cap = (*arr).capacity;
    let r = if lean_is_unique(o) && cap > sz {
        // Fast path: exclusive and has room.
        o
    } else if lean_is_unique(o) {
        // Exclusive but full — expand capacity.
        copy_array(o, true)
    } else {
        // Shared — must copy. Expand if also full.
        copy_array(o, sz >= cap)
    };
    let r_arr = r as *mut ArrayObj;
    let data = array_data(r);
    std::ptr::write(data.add((*r_arr).size), v);
    (*r_arr).size += 1;
    r
}

/// Get the element at index `idx` (borrowed — no inc).
///
/// # Safety
///
/// `o` must be an Array object and `idx < size`.
#[inline]
pub(crate) unsafe fn array_get(o: LeanObjPtr, idx: usize) -> LeanObjPtr {
    *array_data(o).add(idx)
}

// ---------------------------------------------------------------------------
// Array COW (copy-on-write) and mutation primitives
// Matches Lean 4's lean_ensure_exclusive_array / lean_copy_expand_array.
// Part of #2020.
// ---------------------------------------------------------------------------

/// Copy an array, optionally doubling its capacity.
///
/// - Allocates a new array
/// - Copies all elements with `lean_inc` on each
/// - `lean_dec`s the original (ownership transferred from caller)
/// - Returns the new array
///
/// # Safety
///
/// `a` must be a valid Array object pointer.
pub(crate) unsafe fn copy_array(a: LeanObjPtr, expand: bool) -> LeanObjPtr {
    let src = a as *const ArrayObj;
    let old_cap = (*src).capacity;
    let new_cap = if expand {
        if old_cap == 0 {
            8
        } else {
            old_cap * 2
        }
    } else {
        old_cap
    };
    let sz = (*src).size;
    let new_arr = alloc_array(new_cap);
    let src_data = array_data(a);
    let dst_data = array_data(new_arr);
    for i in 0..sz {
        let elem = *src_data.add(i);
        lean_inc(elem);
        std::ptr::write(dst_data.add(i), elem);
    }
    (*(new_arr as *mut ArrayObj)).size = sz;
    lean_dec(a);
    new_arr
}

/// If the array is uniquely owned, return it as-is. Otherwise, copy it.
///
/// # Safety
///
/// `a` must be a valid Array object pointer.
#[inline]
pub(crate) unsafe fn ensure_exclusive_array(a: LeanObjPtr) -> LeanObjPtr {
    if lean_is_unique(a) {
        a
    } else {
        copy_array(a, false)
    }
}

/// Set element at unboxed index `i` with COW semantics. Returns the
/// (possibly new) array pointer. Caller must use the returned pointer.
///
/// # Safety
///
/// `a` must be a valid Array, `i < size`, `v` is a valid obj pointer.
pub(crate) unsafe fn array_uset(a: LeanObjPtr, i: usize, v: LeanObjPtr) -> LeanObjPtr {
    let r = ensure_exclusive_array(a);
    let it = array_data(r).add(i);
    lean_dec(*it);
    *it = v;
    r
}

/// Set element at boxed index with COW. Returns the (possibly new) array.
///
/// # Safety
///
/// `a` must be a valid Array, unboxed `i < size`, `v` is valid.
pub(crate) unsafe fn array_fset(a: LeanObjPtr, i: LeanObjPtr, v: LeanObjPtr) -> LeanObjPtr {
    array_uset(a, lean_unbox(i), v)
}

/// Bounds-checked set with COW. Returns the (possibly new) array.
/// If index is out of bounds, panics and dec's `v`.
///
/// # Safety
///
/// `a` must be a valid Array, `i` and `v` are valid obj pointers.
pub(crate) unsafe fn array_set(a: LeanObjPtr, i: LeanObjPtr, v: LeanObjPtr) -> LeanObjPtr {
    if is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < array_size(a) {
            return array_uset(a, idx, v);
        }
    }
    // Out of bounds — dec the value we were given, return array unchanged.
    // Note: Lean 4 lean_array_set calls lean_dec(v) then panics on OOB.
    // We dec v but return unchanged (non-panicking) for robustness.
    lean_dec(v);
    a
}

/// Get element at unboxed index with inc (non-borrowed).
/// Matches Lean 4 `lean_array_uget`.
///
/// # Safety
///
/// `a` must be a valid Array, `i < size`.
#[inline]
pub(crate) unsafe fn array_uget(a: LeanObjPtr, i: usize) -> LeanObjPtr {
    let r = *array_data(a).add(i);
    lean_inc(r);
    r
}

/// Get element at boxed index with inc.
///
/// # Safety
///
/// `a` must be a valid Array, unboxed `i < size`.
#[inline]
pub(crate) unsafe fn array_fget(a: LeanObjPtr, i: LeanObjPtr) -> LeanObjPtr {
    array_uget(a, lean_unbox(i))
}

/// Bounds-checked get with default. Returns `clean_inc(default)` on OOB.
///
/// # Safety
///
/// `def`, `a` must be valid obj pointers, `i` is a valid obj pointer.
pub(crate) unsafe fn array_get_checked(
    def: LeanObjPtr,
    a: LeanObjPtr,
    i: LeanObjPtr,
) -> LeanObjPtr {
    if is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < array_size(a) {
            return array_uget(a, idx);
        }
    }
    lean_inc(def);
    def
}

/// Pop the last element from the array with COW. Returns the
/// (possibly new) array. The popped element is dec'd.
/// If the array is empty, returns it unchanged (matches Lean 4).
///
/// # Safety
///
/// `a` must be a valid Array.
pub(crate) unsafe fn array_pop(a: LeanObjPtr) -> LeanObjPtr {
    let r = ensure_exclusive_array(a);
    let arr = r as *mut ArrayObj;
    let sz = (*arr).size;
    if sz == 0 {
        return r;
    }
    let new_size = sz - 1;
    (*arr).size = new_size;
    lean_dec(*array_data(r).add(new_size));
    r
}

/// Swap elements at unboxed indices with COW.
///
/// # Safety
///
/// `a` must be a valid Array, `i < size`, `j < size`.
pub(crate) unsafe fn array_uswap(a: LeanObjPtr, i: usize, j: usize) -> LeanObjPtr {
    let r = ensure_exclusive_array(a);
    let data = array_data(r);
    let tmp = *data.add(i);
    *data.add(i) = *data.add(j);
    *data.add(j) = tmp;
    r
}

/// Swap elements at boxed indices with COW.
///
/// # Safety
///
/// `a` must be a valid Array, unboxed `i < size`, unboxed `j < size`.
pub(crate) unsafe fn array_fswap(a: LeanObjPtr, i: LeanObjPtr, j: LeanObjPtr) -> LeanObjPtr {
    array_uswap(a, lean_unbox(i), lean_unbox(j))
}

/// Bounds-checked swap with COW.
///
/// # Safety
///
/// `a` must be a valid Array, `i` and `j` are valid obj pointers.
pub(crate) unsafe fn array_swap(a: LeanObjPtr, i: LeanObjPtr, j: LeanObjPtr) -> LeanObjPtr {
    if is_scalar(i) && is_scalar(j) {
        let ui = lean_unbox(i);
        let uj = lean_unbox(j);
        let sz = array_size(a);
        if ui < sz && uj < sz {
            return array_uswap(a, ui, uj);
        }
    }
    a
}

/// Get the boxed array size.
#[inline]
pub(crate) unsafe fn array_get_size(a: LeanObjPtr) -> LeanObjPtr {
    lean_box(array_size(a))
}

/// Create an array of `n` copies of `v`. Consumes `v` (takes ownership).
/// Matches Lean 4 `lean_mk_array` (object.cpp:2587).
///
/// # Safety
///
/// `v` must be a valid obj pointer (or scalar).
pub(crate) unsafe fn mk_array(n: usize, v: LeanObjPtr) -> LeanObjPtr {
    let a = alloc_array(n);
    let data = array_data(a);
    for i in 0..n {
        std::ptr::write(data.add(i), v);
    }
    // The caller's reference is consumed. For n=0, dec it (unused).
    // For n=1, the caller's ref is used directly (no inc/dec needed).
    // For n>1, we need (n-1) additional refs beyond the caller's one.
    // Matches Lean 4: lean_inc_n(v, sz-1) when sz>1, lean_dec(v) when sz==0.
    if n == 0 {
        lean_dec(v);
    } else if n > 1 {
        lean_inc_n(v, (n - 1) as u32);
    }
    (*(a as *mut ArrayObj)).size = n;
    a
}

/// Create an empty array with capacity 0.
#[inline]
pub(crate) fn mk_empty_array() -> LeanObjPtr {
    alloc_array(0)
}

/// Create an empty array with the given capacity (boxed input).
///
/// # Safety
///
/// `cap` must be a valid boxed scalar.
#[inline]
pub(crate) unsafe fn mk_empty_array_with_capacity(cap: LeanObjPtr) -> LeanObjPtr {
    alloc_array(lean_unbox(cap))
}

// ---------------------------------------------------------------------------
// Extended type allocation: thunk, task, external
// ---------------------------------------------------------------------------

/// Allocate a thunk with the given closure.
///
/// # Safety
///
/// `closure` must be a valid CleanObj pointer.
pub(crate) unsafe fn alloc_thunk(closure: LeanObjPtr) -> LeanObjPtr {
    let layout = alloc::Layout::new::<ThunkObj>();
    // SAFETY: Layout::new::<ThunkObj>() is a valid, non-zero-sized layout.
    let raw = alloc::alloc(layout);
    if raw.is_null() {
        lean_panic("out of memory");
    }
    // SAFETY: `raw` is non-null (checked above) and points to a freshly
    // allocated ThunkObj-sized region. Header is written via `&raw mut` to
    // avoid referencing uninitialized memory. The value and closure fields
    // are within the ThunkObj struct bounds.
    let thunk = raw as *mut ThunkObj;
    std::ptr::write(
        &raw mut (*thunk).header,
        ObjHeader {
            ref_count: AtomicU32::new(0),
            tag: 0,
            kind: ObjKind::Thunk as u8,
            num_objs: 0,
            scalar_sz: 0,
        },
    );
    (*thunk).value = std::ptr::null_mut();
    (*thunk).closure = closure;
    thunk as LeanObjPtr
}

/// Allocate a task object.
///
/// # Safety
///
/// `imp` must be null or a valid pointer to task implementation data.
pub(crate) unsafe fn alloc_task(imp: *mut ()) -> LeanObjPtr {
    let layout = alloc::Layout::new::<TaskObj>();
    // SAFETY: Layout::new::<TaskObj>() is a valid, non-zero-sized layout.
    let raw = alloc::alloc(layout);
    if raw.is_null() {
        lean_panic("out of memory");
    }
    // SAFETY: `raw` is non-null (checked above) and points to a freshly
    // allocated TaskObj-sized region. Header is written via `&raw mut`.
    // The value and imp fields are within the TaskObj struct bounds.
    let task = raw as *mut TaskObj;
    std::ptr::write(
        &raw mut (*task).header,
        ObjHeader {
            ref_count: AtomicU32::new(0),
            tag: 0,
            kind: ObjKind::Task as u8,
            num_objs: 0,
            scalar_sz: 0,
        },
    );
    (*task).value = std::ptr::null_mut();
    (*task).imp = imp;
    task as LeanObjPtr
}

/// Allocate an external (FFI) object.
///
/// # Safety
///
/// `class` must point to a valid `CleanExternalClass` that outlives the object.
pub(crate) unsafe fn alloc_external(class: *const CleanExternalClass, data: *mut ()) -> LeanObjPtr {
    let layout = alloc::Layout::new::<ExternalObj>();
    // SAFETY: Layout::new::<ExternalObj>() is a valid, non-zero-sized layout.
    let raw = alloc::alloc(layout);
    if raw.is_null() {
        lean_panic("out of memory");
    }
    // SAFETY: `raw` is non-null (checked above) and points to a freshly
    // allocated ExternalObj-sized region. Header is written via `&raw mut`.
    // The class and data fields are within the ExternalObj struct bounds.
    // Caller guarantees `class` points to a valid CleanExternalClass.
    let ext = raw as *mut ExternalObj;
    std::ptr::write(
        &raw mut (*ext).header,
        ObjHeader {
            ref_count: AtomicU32::new(0),
            tag: 0,
            kind: ObjKind::External as u8,
            num_objs: 0,
            scalar_sz: 0,
        },
    );
    (*ext).class = class;
    (*ext).data = data;
    ext as LeanObjPtr
}

/// Create a string object from a byte slice.
pub(crate) fn mk_string_from_bytes(s: &[u8]) -> LeanObjPtr {
    alloc_string_bytes(s)
}

/// Reuse a reset slot or allocate fresh (scalar-aware, no field init).
///
/// Unlike [`lean_reuse`] which initializes pointer fields, this variant
/// does NOT set fields — the caller emits individual `clean_ctor_set` /
/// scalar setter calls. This is the correct entry point for constructors
/// with scalar fields, where `lean_reuse` would hardcode `scalar_sz = 0`.
///
/// # Safety
///
/// `reset_slot` must be null or a valid reset object.
pub(crate) unsafe fn reuse_slot(
    reset_slot: LeanObjPtr,
    tag: u8,
    num_objs: u8,
    scalar_size: u8,
) -> LeanObjPtr {
    // SAFETY for all pointer dereferences below: caller guarantees
    // `reset_slot` is null or a valid heap object from lean_reset.
    // When non-null, reading header fields and deallocating with the
    // correct layout are valid operations on the live allocation.
    if !reset_slot.is_null() {
        if (*reset_slot).header.kind != ObjKind::Ctor as u8 {
            // Non-Ctor slot: layout mismatch, deallocate and allocate fresh.
            alloc::dealloc(reset_slot as *mut u8, object_layout(reset_slot));
            return alloc_ctor_uninit(tag, num_objs, scalar_size);
        }
        // Validate that the new fields fit within the original Ctor allocation.
        // If the new layout is larger, fall back to fresh allocation to prevent
        // heap buffer overflow. Matches Lean 4 lean_reuse contract. Part of #2241.
        let old_layout = obj_layout(
            (*reset_slot).header.num_objs,
            (*reset_slot).header.scalar_sz,
        );
        let new_layout = obj_layout(num_objs, scalar_size);
        if new_layout.size() > old_layout.size() {
            alloc::dealloc(reset_slot as *mut u8, old_layout);
            return alloc_ctor_uninit(tag, num_objs, scalar_size);
        }
        (*reset_slot).header.tag = tag;
        (*reset_slot).header.ref_count = AtomicU32::new(0);
        (*reset_slot).header.num_objs = num_objs;
        (*reset_slot).header.scalar_sz = scalar_size;
        reset_slot
    } else {
        alloc_ctor_uninit(tag, num_objs, scalar_size)
    }
}

// ---------------------------------------------------------------------------
// Thunk accessors
// ---------------------------------------------------------------------------

/// Get the forced value from a thunk, or null if not yet forced.
///
/// # Safety
///
/// `o` must be a valid Thunk object.
#[inline]
pub(crate) unsafe fn thunk_get_value(o: LeanObjPtr) -> LeanObjPtr {
    (*(o as *const ThunkObj)).value
}

/// Get the closure stored in a thunk, or null if already forced.
///
/// # Safety
///
/// `o` must be a valid Thunk object.
#[inline]
pub(crate) unsafe fn thunk_get_closure(o: LeanObjPtr) -> LeanObjPtr {
    (*(o as *const ThunkObj)).closure
}

/// Store the forced value in a thunk and clear its closure.
///
/// After forcing, the closure is dec'd and set to null. The value
/// pointer is stored without inc — the caller transfers ownership.
/// Matches Lean 4 `lean_thunk_set_value` semantics.
///
/// # Safety
///
/// `o` must be a uniquely owned Thunk object. `value` must be a valid
/// obj pointer (ownership transferred to the thunk).
pub(crate) unsafe fn thunk_set_value(o: LeanObjPtr, value: LeanObjPtr) {
    let thunk = o as *mut ThunkObj;
    // Dec the old closure if present — it is no longer needed.
    if !(*thunk).closure.is_null() {
        lean_dec((*thunk).closure);
        (*thunk).closure = std::ptr::null_mut();
    }
    (*thunk).value = value;
}

// ---------------------------------------------------------------------------
// Task accessors
// ---------------------------------------------------------------------------

/// Get the resolved value from a task, or null if not yet complete.
///
/// # Safety
///
/// `o` must be a valid Task object.
#[inline]
pub(crate) unsafe fn task_get_value(o: LeanObjPtr) -> LeanObjPtr {
    (*(o as *const TaskObj)).value
}

/// Get the implementation pointer from a task.
///
/// # Safety
///
/// `o` must be a valid Task object.
#[inline]
pub(crate) unsafe fn task_get_imp(o: LeanObjPtr) -> *mut () {
    (*(o as *const TaskObj)).imp
}

/// Store the resolved value in a task.
///
/// The value pointer is stored without inc — the caller transfers ownership.
///
/// # Safety
///
/// `o` must be a uniquely owned Task object. `value` must be a valid
/// obj pointer (ownership transferred to the task).
pub(crate) unsafe fn task_set_value(o: LeanObjPtr, value: LeanObjPtr) {
    (*(o as *mut TaskObj)).value = value;
}

// ---------------------------------------------------------------------------
// External accessors
// ---------------------------------------------------------------------------

/// Get the data pointer from an external object.
///
/// # Safety
///
/// `o` must be a valid External object.
#[inline]
pub(crate) unsafe fn external_get_data(o: LeanObjPtr) -> *mut () {
    (*(o as *const ExternalObj)).data
}

/// Get the class descriptor from an external object.
///
/// # Safety
///
/// `o` must be a valid External object.
#[inline]
pub(crate) unsafe fn external_get_class(o: LeanObjPtr) -> *const CleanExternalClass {
    (*(o as *const ExternalObj)).class
}
