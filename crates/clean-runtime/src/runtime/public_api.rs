// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![allow(unsafe_op_in_unsafe_fn)]

//! Public API — `clean_` prefixed functions for generated code.
//!
//! These functions provide the public interface matching the names emitted by
//! the Rust and C code generators. Internal helpers remain `pub(crate)`.
//! Part of #2005 Phase 2.

use super::array::*;
use super::closure::*;
use super::ctor_scalar::*;
use super::refcount::*;
use super::string_reset::*;
use super::types::*;

// -- Tagged pointer operations --

/// Box a small integer into a tagged pointer. No heap allocation.
#[inline]
pub fn clean_box(n: usize) -> LeanObjPtr {
    lean_box(n)
}

/// Unbox a tagged pointer to retrieve the stored small integer.
#[inline]
pub fn clean_unbox(o: LeanObjPtr) -> usize {
    lean_unbox(o)
}

/// Returns `true` if the pointer is a tagged scalar (not a heap object).
#[inline]
pub fn clean_is_scalar(o: LeanObjPtr) -> bool {
    is_scalar(o)
}

// -- Typed boxing/unboxing --

/// Box a `u32` value (tagged pointer for small values, heap for large).
#[inline]
pub fn clean_box_uint32(n: u32) -> LeanObjPtr {
    box_uint32(n)
}

/// Box a `u64` value. Always heap-allocates.
#[inline]
pub fn clean_box_uint64(n: u64) -> LeanObjPtr {
    box_uint64(n)
}

/// Box an `f64` value. Always heap-allocates.
#[inline]
pub fn clean_box_float(f: f64) -> LeanObjPtr {
    box_float(f)
}

/// Unbox a `u32` from tagged pointer or heap allocation.
#[inline]
pub fn clean_unbox_uint32(o: LeanObjPtr) -> u32 {
    unbox_uint32(o)
}

/// Unbox a heap-allocated `u64`.
#[inline]
pub fn clean_unbox_uint64(o: LeanObjPtr) -> u64 {
    unbox_uint64(o)
}

/// Unbox a heap-allocated `f64`.
#[inline]
pub fn clean_unbox_float(o: LeanObjPtr) -> f64 {
    unbox_float(o)
}

// -- Reference counting --

/// Increment the reference count. No-op for scalars.
#[inline]
pub fn clean_inc(o: LeanObjPtr) {
    lean_inc(o)
}

/// Increment the reference count by `n`. No-op for scalars.
#[inline]
pub fn clean_inc_n(o: LeanObjPtr, n: u32) {
    lean_inc_n(o, n)
}

/// Decrement the reference count. Frees on last reference. No-op for scalars.
#[inline]
pub fn clean_dec(o: LeanObjPtr) {
    lean_dec(o)
}

// -- Object field access --

/// Read the `idx`-th object-pointer field from a constructor.
#[inline]
pub fn clean_ctor_get(o: LeanObjPtr, idx: usize) -> LeanObjPtr {
    ctor_get(o, idx)
}

/// Write the `idx`-th object-pointer field. Requires unique ownership.
#[inline]
pub fn clean_ctor_set(o: LeanObjPtr, idx: usize, v: LeanObjPtr) {
    ctor_set(o, idx, v)
}

/// Get the constructor tag of an object.
#[inline]
pub fn clean_obj_tag(o: LeanObjPtr) -> u8 {
    obj_tag(o)
}

// -- Typed scalar getters --

/// Read a `u8` from the scalar region at byte offset.
#[inline]
pub fn clean_ctor_get_uint8(o: LeanObjPtr, offset: usize) -> u8 {
    ctor_get_uint8(o, offset)
}

/// Read a `u16` from the scalar region at byte offset.
#[inline]
pub fn clean_ctor_get_uint16(o: LeanObjPtr, offset: usize) -> u16 {
    ctor_get_uint16(o, offset)
}

/// Read a `u32` from the scalar region at byte offset.
#[inline]
pub fn clean_ctor_get_uint32(o: LeanObjPtr, offset: usize) -> u32 {
    ctor_get_uint32(o, offset)
}

/// Read a `u64` from the scalar region at byte offset.
#[inline]
pub fn clean_ctor_get_uint64(o: LeanObjPtr, offset: usize) -> u64 {
    ctor_get_uint64(o, offset)
}

/// Read a `usize` from slot index `i`.
#[inline]
pub fn clean_ctor_get_usize(o: LeanObjPtr, i: usize) -> usize {
    ctor_get_usize(o, i)
}

/// Read an `f64` from the scalar region at byte offset.
#[inline]
pub fn clean_ctor_get_float(o: LeanObjPtr, offset: usize) -> f64 {
    ctor_get_float(o, offset)
}

/// Read an `f32` from the scalar region at byte offset.
#[inline]
pub fn clean_ctor_get_float32(o: LeanObjPtr, offset: usize) -> f32 {
    ctor_get_float32(o, offset)
}

// -- Typed scalar setters --

/// Write a `u8` to the scalar region at byte offset.
#[inline]
pub fn clean_ctor_set_uint8(o: LeanObjPtr, offset: usize, v: u8) {
    ctor_set_uint8(o, offset, v)
}

/// Write a `u16` to the scalar region at byte offset.
#[inline]
pub fn clean_ctor_set_uint16(o: LeanObjPtr, offset: usize, v: u16) {
    ctor_set_uint16(o, offset, v)
}

/// Write a `u32` to the scalar region at byte offset.
#[inline]
pub fn clean_ctor_set_uint32(o: LeanObjPtr, offset: usize, v: u32) {
    ctor_set_uint32(o, offset, v)
}

/// Write a `u64` to the scalar region at byte offset.
#[inline]
pub fn clean_ctor_set_uint64(o: LeanObjPtr, offset: usize, v: u64) {
    ctor_set_uint64(o, offset, v)
}

/// Write a `usize` to slot index `i`.
#[inline]
pub fn clean_ctor_set_usize(o: LeanObjPtr, i: usize, v: usize) {
    ctor_set_usize(o, i, v)
}

/// Write an `f64` to the scalar region at byte offset.
#[inline]
pub fn clean_ctor_set_float(o: LeanObjPtr, offset: usize, v: f64) {
    ctor_set_float(o, offset, v)
}

/// Write an `f32` to the scalar region at byte offset.
#[inline]
pub fn clean_ctor_set_float32(o: LeanObjPtr, offset: usize, v: f32) {
    ctor_set_float32(o, offset, v)
}

// -- Tag mutation --

/// Set the constructor tag. Requires unique ownership.
#[inline]
pub fn clean_ctor_set_tag(o: LeanObjPtr, new_tag: u8) {
    ctor_set_tag(o, new_tag)
}

// -- Ownership check --

/// Returns `true` if the object is uniquely owned (ref_count == 0).
///
/// Named `clean_is_exclusive` to match Lean 4 convention and the emitter output.
/// The internal helper is `lean_is_unique` (legacy naming).
#[inline]
pub fn clean_is_exclusive(o: LeanObjPtr) -> bool {
    lean_is_unique(o)
}

// -- Constructor allocation --

/// Allocate a constructor with the given tag, scalar size, and fields.
///
/// This is the Rust runtime equivalent of the C `clean_alloc_ctor`. The `_num_objs`
/// parameter is accepted for API compatibility with the C version but is derived
/// from `fields.len()` — the release-enforced checks verify consistency.
pub fn clean_alloc_ctor(
    tag: u8,
    _num_objs: u8,
    scalar_sz: u8,
    fields: &[LeanObjPtr],
) -> LeanObjPtr {
    expect(
        _num_objs as usize == fields.len(),
        "clean_alloc_ctor: num_objs must match fields.len()",
    );
    expect(
        fields.len() <= u8::MAX as usize,
        "clean_alloc_ctor: fields.len() exceeds u8::MAX",
    );
    let o = alloc_ctor_uninit(tag, fields.len() as u8, scalar_sz);
    // SAFETY: `o` was just allocated by alloc_ctor_uninit with space for
    // `fields.len()` pointer fields. fields_ptr returns a valid pointer to
    // that region, and each write is within bounds.
    unsafe {
        let dst = CleanObj::fields_ptr(o);
        for (i, &f) in fields.iter().enumerate() {
            std::ptr::write(dst.add(i), f);
        }
    }
    o
}

// -- Closures --

/// Allocate a closure for generated Rust code.
pub fn clean_alloc_closure(func: *const (), arity: u16, args: &[LeanObjPtr]) -> LeanObjPtr {
    alloc_closure(func, arity, args)
}

/// Dynamic closure application for generated Rust code.
pub fn clean_closure_apply(closure: LeanObjPtr, args: &[LeanObjPtr]) -> LeanObjPtr {
    closure_apply(closure, args)
}

/// Get the function pointer from a closure.
pub fn clean_closure_func(o: LeanObjPtr) -> *const () {
    closure_func(o)
}

/// Get the total arity of a closure.
pub fn clean_closure_arity(o: LeanObjPtr) -> u16 {
    closure_arity(o)
}

/// Get the number of captured arguments in a closure.
pub fn clean_closure_num_fixed(o: LeanObjPtr) -> u16 {
    closure_num_fixed(o)
}

/// Get the idx-th captured argument from a closure.
pub fn clean_closure_arg(o: LeanObjPtr, idx: usize) -> LeanObjPtr {
    closure_arg(o, idx)
}

// -- Strings --

/// Create a string object from a Rust `&str`.
pub fn clean_mk_string(s: &str) -> LeanObjPtr {
    mk_string(s)
}

/// Abort with an error message.
#[cold]
pub fn clean_panic(msg: &str) -> ! {
    lean_panic(msg)
}

// -- Reset / Reuse --

/// Reset an object for potential memory reuse.
pub fn clean_reset(o: LeanObjPtr) -> LeanObjPtr {
    lean_reset(o)
}

/// Reuse a reset slot or allocate a fresh constructor.
pub fn clean_reuse(
    reset_slot: LeanObjPtr,
    tag: u8,
    scalar_sz: u8,
    fields: &[LeanObjPtr],
) -> LeanObjPtr {
    lean_reuse(reset_slot, tag, scalar_sz, fields)
}

// -- Lifecycle --

/// Initialize the runtime. Call once at program start.
pub fn clean_runtime_init() {
    runtime_init()
}

/// Finalize the runtime. Call before exit.
pub fn clean_runtime_finalize() {
    runtime_finalize()
}

// ---------------------------------------------------------------------------
// Extended operations (zone/rust-backend merge)
// ---------------------------------------------------------------------------

/// Allocate an array with the given initial capacity.
pub fn clean_alloc_array(cap: usize) -> LeanObjPtr {
    alloc_array(cap)
}

/// Get the data pointer for an array.
///
/// # Safety
///
/// `o` must be an Array object.
#[inline]
pub unsafe fn clean_array_data(o: LeanObjPtr) -> *mut LeanObjPtr {
    array_data(o)
}

/// Get the array size (number of elements).
///
/// # Safety
///
/// `o` must be an Array object.
#[inline]
pub unsafe fn clean_array_size(o: LeanObjPtr) -> usize {
    array_size(o)
}

/// Push an element onto the array with COW and auto-reallocation.
///
/// Returns the (possibly new) array pointer. Matches Lean 4 `lean_array_push`.
///
/// # Safety
///
/// `o` must be a valid Array. `v` must be a valid obj pointer.
pub unsafe fn clean_array_push(o: LeanObjPtr, v: LeanObjPtr) -> LeanObjPtr {
    array_push(o, v)
}

/// Get element at unboxed index (borrowed — no inc). Matches Lean 4
/// `lean_array_uget_borrowed`.
///
/// # Safety
///
/// `o` must be an Array object and `idx < size`.
#[inline]
pub unsafe fn clean_array_get(o: LeanObjPtr, idx: usize) -> LeanObjPtr {
    array_get(o, idx)
}

/// Get element at unboxed index with inc. Matches Lean 4 `lean_array_uget`.
///
/// # Safety
///
/// `o` must be an Array object and `idx < size`.
#[inline]
pub unsafe fn clean_array_uget(o: LeanObjPtr, idx: usize) -> LeanObjPtr {
    array_uget(o, idx)
}

/// Get element at boxed index with inc.
///
/// # Safety
///
/// `o` must be an Array, unboxed `idx < size`.
#[inline]
pub unsafe fn clean_array_fget(o: LeanObjPtr, idx: LeanObjPtr) -> LeanObjPtr {
    array_fget(o, idx)
}

/// Bounds-checked get with default value. Returns `clean_inc(def)` on OOB.
///
/// # Safety
///
/// `def`, `o`, `idx` must be valid obj pointers.
pub unsafe fn clean_array_get_checked(
    def: LeanObjPtr,
    o: LeanObjPtr,
    idx: LeanObjPtr,
) -> LeanObjPtr {
    array_get_checked(def, o, idx)
}

/// Set element at unboxed index with COW.
///
/// # Safety
///
/// `o` must be a valid Array, `idx < size`, `v` is valid.
pub unsafe fn clean_array_uset(o: LeanObjPtr, idx: usize, v: LeanObjPtr) -> LeanObjPtr {
    array_uset(o, idx, v)
}

/// Set element at boxed index with COW.
///
/// # Safety
///
/// `o` must be a valid Array, unboxed `idx < size`, `v` is valid.
pub unsafe fn clean_array_fset(o: LeanObjPtr, idx: LeanObjPtr, v: LeanObjPtr) -> LeanObjPtr {
    array_fset(o, idx, v)
}

/// Bounds-checked set with COW.
///
/// # Safety
///
/// `o` must be a valid Array, `idx` and `v` are valid.
pub unsafe fn clean_array_set(o: LeanObjPtr, idx: LeanObjPtr, v: LeanObjPtr) -> LeanObjPtr {
    array_set(o, idx, v)
}

/// Pop the last element with COW.
///
/// # Safety
///
/// `o` must be a valid Array with `size > 0`.
pub unsafe fn clean_array_pop(o: LeanObjPtr) -> LeanObjPtr {
    array_pop(o)
}

/// Swap elements at unboxed indices with COW.
///
/// # Safety
///
/// `o` must be a valid Array, `i < size`, `j < size`.
pub unsafe fn clean_array_uswap(o: LeanObjPtr, i: usize, j: usize) -> LeanObjPtr {
    array_uswap(o, i, j)
}

/// Swap elements at boxed indices with COW.
///
/// # Safety
///
/// `o` must be a valid Array, unboxed `i < size`, unboxed `j < size`.
pub unsafe fn clean_array_fswap(o: LeanObjPtr, i: LeanObjPtr, j: LeanObjPtr) -> LeanObjPtr {
    array_fswap(o, i, j)
}

/// Bounds-checked swap with COW.
///
/// # Safety
///
/// `o` must be a valid Array, `i` and `j` are valid.
pub unsafe fn clean_array_swap(o: LeanObjPtr, i: LeanObjPtr, j: LeanObjPtr) -> LeanObjPtr {
    array_swap(o, i, j)
}

/// Get boxed array size.
///
/// # Safety
///
/// `o` must be a valid Array.
#[inline]
pub unsafe fn clean_array_get_size(o: LeanObjPtr) -> LeanObjPtr {
    array_get_size(o)
}

/// If exclusive, return as-is. Otherwise, copy.
///
/// # Safety
///
/// `o` must be a valid Array.
#[inline]
pub unsafe fn clean_ensure_exclusive_array(o: LeanObjPtr) -> LeanObjPtr {
    ensure_exclusive_array(o)
}

/// Copy array, optionally doubling capacity.
///
/// # Safety
///
/// `o` must be a valid Array.
pub unsafe fn clean_copy_array(o: LeanObjPtr, expand: bool) -> LeanObjPtr {
    copy_array(o, expand)
}

/// Create an array of `n` copies of `v`.
///
/// # Safety
///
/// `v` must be a valid obj pointer.
pub unsafe fn clean_mk_array(n: usize, v: LeanObjPtr) -> LeanObjPtr {
    mk_array(n, v)
}

/// Create an empty array.
pub fn clean_mk_empty_array() -> LeanObjPtr {
    mk_empty_array()
}

/// Create an empty array with boxed capacity.
///
/// # Safety
///
/// `cap` must be a valid boxed scalar.
pub unsafe fn clean_mk_empty_array_with_capacity(cap: LeanObjPtr) -> LeanObjPtr {
    mk_empty_array_with_capacity(cap)
}

/// Allocate a thunk with the given closure.
///
/// # Safety
///
/// `closure` must be a valid CleanObj pointer.
pub unsafe fn clean_alloc_thunk(closure: LeanObjPtr) -> LeanObjPtr {
    alloc_thunk(closure)
}

/// Get the forced value from a thunk, or null if not yet forced.
///
/// # Safety
///
/// `o` must be a valid Thunk object.
#[inline]
pub unsafe fn clean_thunk_get_value(o: LeanObjPtr) -> LeanObjPtr {
    thunk_get_value(o)
}

/// Get the closure from a thunk, or null if already forced.
///
/// # Safety
///
/// `o` must be a valid Thunk object.
#[inline]
pub unsafe fn clean_thunk_get_closure(o: LeanObjPtr) -> LeanObjPtr {
    thunk_get_closure(o)
}

/// Store the forced value in a thunk and clear its closure.
///
/// # Safety
///
/// `o` must be a uniquely owned Thunk. `value` ownership is transferred.
pub unsafe fn clean_thunk_set_value(o: LeanObjPtr, value: LeanObjPtr) {
    thunk_set_value(o, value)
}

/// Allocate a task object.
///
/// # Safety
///
/// `imp` must be null or a valid pointer to task implementation data.
pub unsafe fn clean_alloc_task(imp: *mut ()) -> LeanObjPtr {
    alloc_task(imp)
}

/// Get the resolved value from a task, or null if not yet complete.
///
/// # Safety
///
/// `o` must be a valid Task object.
#[inline]
pub unsafe fn clean_task_get_value(o: LeanObjPtr) -> LeanObjPtr {
    task_get_value(o)
}

/// Get the implementation pointer from a task.
///
/// # Safety
///
/// `o` must be a valid Task object.
#[inline]
pub unsafe fn clean_task_get_imp(o: LeanObjPtr) -> *mut () {
    task_get_imp(o)
}

/// Store the resolved value in a task.
///
/// # Safety
///
/// `o` must be a uniquely owned Task. `value` ownership is transferred.
pub unsafe fn clean_task_set_value(o: LeanObjPtr, value: LeanObjPtr) {
    task_set_value(o, value)
}

/// Allocate an external (FFI) object.
///
/// # Safety
///
/// `class` must point to a valid `CleanExternalClass` that outlives the object.
pub unsafe fn clean_alloc_external(class: *const CleanExternalClass, data: *mut ()) -> LeanObjPtr {
    alloc_external(class, data)
}

/// Get the data pointer from an external object.
///
/// # Safety
///
/// `o` must be a valid External object.
#[inline]
pub unsafe fn clean_external_get_data(o: LeanObjPtr) -> *mut () {
    external_get_data(o)
}

/// Get the class descriptor from an external object.
///
/// # Safety
///
/// `o` must be a valid External object.
#[inline]
pub unsafe fn clean_external_get_class(o: LeanObjPtr) -> *const CleanExternalClass {
    external_get_class(o)
}

/// Create a string object from a byte slice.
pub fn clean_mk_string_from_bytes(s: &[u8]) -> LeanObjPtr {
    mk_string_from_bytes(s)
}

/// Get the string data as a byte slice.
///
/// # Safety
///
/// `o` must be a string object.
pub unsafe fn clean_string_data(o: LeanObjPtr) -> &'static [u8] {
    string_data(o)
}

/// Get the string length in bytes.
///
/// # Safety
///
/// `o` must be a string object.
pub unsafe fn clean_string_len(o: LeanObjPtr) -> usize {
    string_len(o)
}

/// Reuse a reset slot or allocate fresh (scalar-aware, no field init).
///
/// # Safety
///
/// `reset_slot` must be null or a valid reset object.
pub unsafe fn clean_reuse_slot(
    reset_slot: LeanObjPtr,
    tag: u8,
    num_objs: u8,
    scalar_size: u8,
) -> LeanObjPtr {
    reuse_slot(reset_slot, tag, num_objs, scalar_size)
}

/// Returns `true` if the object is uniquely owned (ref_count == 0).
/// Alias for `clean_is_exclusive` matching Zone A naming convention.
#[inline]
pub fn clean_is_unique(o: LeanObjPtr) -> bool {
    lean_is_unique(o)
}
