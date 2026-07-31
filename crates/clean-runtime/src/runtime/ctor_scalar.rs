// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructor allocation, field access, typed scalar getters/setters,
//! tag mutation, and heap-allocated boxing.

use super::types::*;
use std::mem::size_of;

// ---------------------------------------------------------------------------
// Constructor allocation and field access
// ---------------------------------------------------------------------------

/// Allocate a constructor object without initializing its fields.
///
/// `scalar_size` is the number of extra bytes for non-pointer payload
/// (e.g., `UInt32` stored inline in a structure).
pub(crate) fn alloc_ctor_uninit(tag: u8, num_objs: u8, scalar_size: u8) -> LeanObjPtr {
    alloc_obj(tag, ObjKind::Ctor, num_objs, scalar_size)
}

/// Allocate a constructor and initialize its object-pointer fields.
#[cfg(any(test, kani))]
pub(crate) fn alloc_ctor(tag: u8, fields: &[LeanObjPtr]) -> LeanObjPtr {
    expect(
        fields.len() <= u8::MAX as usize,
        "alloc_ctor: fields.len() exceeds u8::MAX",
    );
    let o = alloc_ctor_uninit(tag, fields.len() as u8, 0);
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

/// Read the `idx`-th object-pointer field from a constructor.
#[inline]
pub(crate) fn ctor_get(o: LeanObjPtr, idx: usize) -> LeanObjPtr {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(o, ObjKind::Ctor, "ctor_get: pointer is not a constructor");
    }
    // SAFETY: caller guarantees `o` is a valid constructor object. The
    // release-enforced checks above verify the kind and field bounds before
    // pointer arithmetic.
    unsafe {
        expect_index_lt(
            idx,
            (*o).header.num_objs as usize,
            "ctor_get: field index out of bounds",
        );
        *CleanObj::fields_ptr(o).add(idx)
    }
}

/// Write the `idx`-th object-pointer field. Requires unique ownership.
#[inline]
pub(crate) fn ctor_set(o: LeanObjPtr, idx: usize, v: LeanObjPtr) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(o, ObjKind::Ctor, "ctor_set: pointer is not a constructor");
    }
    // SAFETY: caller guarantees unique ownership and `o` is a valid constructor
    // object. The release-enforced checks above verify the kind and field
    // bounds before the write.
    unsafe {
        expect_index_lt(
            idx,
            (*o).header.num_objs as usize,
            "ctor_set: field index out of bounds",
        );
        std::ptr::write(CleanObj::fields_ptr(o).add(idx), v);
    }
}

/// Get the constructor tag of an object. For scalars, returns the unboxed value
/// truncated to `u8` (matching C semantics).
#[inline]
pub(crate) fn obj_tag(o: LeanObjPtr) -> u8 {
    if is_scalar(o) {
        lean_unbox(o) as u8
    } else {
        // SAFETY: non-scalar means valid heap pointer.
        unsafe { (*o).header.tag }
    }
}

// ---------------------------------------------------------------------------
// Typed scalar getters (access scalar region after pointer fields)
// ---------------------------------------------------------------------------
//
// These follow Lean 4's lean.h:650-680 pattern. The scalar region begins at
// `num_objs * sizeof(void*)` from fields[0]. `offset` is a byte offset
// measured from fields[0], so callers must pass offset >= num_objs * ptr_size.
//
// Exception: `ctor_get_usize` takes a slot index `i` (not byte offset) because
// usize fields occupy pointer-sized slots interleaved with object fields.

/// Read a `u8` from the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_get_uint8(o: LeanObjPtr, offset: usize) -> u8 {
    // SAFETY: `o` is a non-scalar heap pointer; header deref for kind check is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_get_uint8: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees `o` is a non-scalar heap ctor and `offset`
    // points within the scalar region. Single byte read is within bounds.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *const u8;
        *base.add(offset)
    }
}

/// Read a `u16` from the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_get_uint16(o: LeanObjPtr, offset: usize) -> u16 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_get_uint16: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees valid offset into scalar region. Read is aligned
    // per Lean object layout (scalar region is packed, unaligned read is safe via
    // read_unaligned).
    unsafe {
        let base = CleanObj::fields_ptr(o) as *const u8;
        std::ptr::read_unaligned(base.add(offset) as *const u16)
    }
}

/// Read a `u32` from the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_get_uint32(o: LeanObjPtr, offset: usize) -> u32 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_get_uint32: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_get_uint16 — unaligned read from scalar region.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *const u8;
        std::ptr::read_unaligned(base.add(offset) as *const u32)
    }
}

/// Read a `u64` from the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_get_uint64(o: LeanObjPtr, offset: usize) -> u64 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_get_uint64: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_get_uint16 — unaligned read from scalar region.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *const u8;
        std::ptr::read_unaligned(base.add(offset) as *const u64)
    }
}

/// Read a `usize` from the field array at slot index `i`.
///
/// Unlike other scalar getters, this takes a slot index (not byte offset)
/// because usize fields are pointer-sized and interleaved with object fields.
/// The index `i` must be >= `num_objs` to point into the scalar region.
#[inline]
pub(crate) fn ctor_get_usize(o: LeanObjPtr, i: usize) -> usize {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_get_usize: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees `i` is a valid slot index into the fields/scalar
    // region. Pointer-sized read at fields_ptr + i is within allocation bounds.
    unsafe { *(CleanObj::fields_ptr(o) as *const usize).add(i) }
}

/// Read an `f64` from the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_get_float(o: LeanObjPtr, offset: usize) -> f64 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_get_float: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_get_uint16 — unaligned read from scalar region.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *const u8;
        std::ptr::read_unaligned(base.add(offset) as *const f64)
    }
}

/// Read an `f32` from the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_get_float32(o: LeanObjPtr, offset: usize) -> f32 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_get_float32: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_get_uint16 — unaligned read from scalar region.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *const u8;
        std::ptr::read_unaligned(base.add(offset) as *const f32)
    }
}

// ---------------------------------------------------------------------------
// Typed scalar setters (write to scalar region after pointer fields)
// ---------------------------------------------------------------------------

/// Write a `u8` to the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_set_uint8(o: LeanObjPtr, offset: usize, v: u8) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_uint8: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees unique ownership, `o` is a non-scalar heap ctor,
    // and `offset` points within the scalar region.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *mut u8;
        *base.add(offset) = v;
    }
}

/// Write a `u16` to the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_set_uint16(o: LeanObjPtr, offset: usize, v: u16) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_uint16: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees unique ownership and valid offset into scalar region.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *mut u8;
        std::ptr::write_unaligned(base.add(offset) as *mut u16, v);
    }
}

/// Write a `u32` to the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_set_uint32(o: LeanObjPtr, offset: usize, v: u32) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_uint32: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_set_uint16.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *mut u8;
        std::ptr::write_unaligned(base.add(offset) as *mut u32, v);
    }
}

/// Write a `u64` to the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_set_uint64(o: LeanObjPtr, offset: usize, v: u64) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_uint64: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_set_uint16.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *mut u8;
        std::ptr::write_unaligned(base.add(offset) as *mut u64, v);
    }
}

/// Write a `usize` to the field array at slot index `i`.
///
/// Same slot-index convention as [`ctor_get_usize`].
#[inline]
pub(crate) fn ctor_set_usize(o: LeanObjPtr, i: usize, v: usize) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_usize: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees unique ownership and valid slot index.
    unsafe {
        *(CleanObj::fields_ptr(o) as *mut usize).add(i) = v;
    }
}

/// Write an `f64` to the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_set_float(o: LeanObjPtr, offset: usize, v: f64) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_float: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_set_uint16.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *mut u8;
        std::ptr::write_unaligned(base.add(offset) as *mut f64, v);
    }
}

/// Write an `f32` to the scalar region at the given byte offset.
#[inline]
pub(crate) fn ctor_set_float32(o: LeanObjPtr, offset: usize, v: f32) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_float32: pointer is not a constructor",
        );
    }
    // SAFETY: same as ctor_set_uint16.
    unsafe {
        let base = CleanObj::fields_ptr(o) as *mut u8;
        std::ptr::write_unaligned(base.add(offset) as *mut f32, v);
    }
}

// ---------------------------------------------------------------------------
// Tag mutation
// ---------------------------------------------------------------------------

/// Set the constructor tag of an object. Requires unique ownership.
///
/// Used by `IRBody::SetTag` for in-place tag update during reuse optimization.
#[inline]
pub(crate) fn ctor_set_tag(o: LeanObjPtr, new_tag: u8) {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "ctor_set_tag: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees unique ownership and `o` is a non-scalar heap object.
    unsafe {
        (*o).header.tag = new_tag;
    }
}

// ---------------------------------------------------------------------------
// Heap-allocated boxing (for values that don't fit in tagged pointers)
// ---------------------------------------------------------------------------

/// Box a `u64` value. Always heap-allocates (value doesn't fit in a tagged pointer).
pub(crate) fn box_uint64(n: u64) -> LeanObjPtr {
    let o = alloc_ctor_uninit(0, 0, size_of::<u64>() as u8);
    // SAFETY: `o` was allocated with scalar_size = size_of::<u64>() bytes.
    // scalar_ptr returns a pointer to that region, write is within bounds.
    unsafe {
        let p = CleanObj::scalar_ptr(o) as *mut u64;
        std::ptr::write(p, n);
    }
    o
}

/// Unbox a heap-allocated `u64`.
pub(crate) fn unbox_uint64(o: LeanObjPtr) -> u64 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "unbox_uint64: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees `o` is a heap-allocated u64 box (non-scalar,
    // allocated with scalar_size = size_of::<u64>()). Read is within bounds.
    unsafe {
        let p = CleanObj::scalar_ptr(o) as *const u64;
        std::ptr::read(p)
    }
}

/// Box a `u32` value. Uses a tagged pointer if the value fits (≤ MAX_SMALL),
/// otherwise heap-allocates.
pub(crate) fn box_uint32(n: u32) -> LeanObjPtr {
    if (n as usize) <= MAX_SMALL {
        lean_box(n as usize)
    } else {
        let o = alloc_ctor_uninit(0, 0, size_of::<u32>() as u8);
        // SAFETY: `o` was allocated with scalar_size = size_of::<u32>().
        unsafe {
            let p = CleanObj::scalar_ptr(o) as *mut u32;
            std::ptr::write(p, n);
        }
        o
    }
}

/// Unbox a `u32`. Handles both tagged pointers and heap-allocated values.
pub(crate) fn unbox_uint32(o: LeanObjPtr) -> u32 {
    if is_scalar(o) {
        lean_unbox(o) as u32
    } else {
        // SAFETY: non-scalar means heap-allocated u32 box with
        // scalar_size = size_of::<u32>(). Read is within bounds.
        unsafe {
            let p = CleanObj::scalar_ptr(o) as *const u32;
            std::ptr::read(p)
        }
    }
}

/// Box an `f64` value. Always heap-allocates.
pub(crate) fn box_float(f: f64) -> LeanObjPtr {
    let o = alloc_ctor_uninit(0, 0, size_of::<f64>() as u8);
    // SAFETY: `o` was allocated with scalar_size = size_of::<f64>().
    unsafe {
        let p = CleanObj::scalar_ptr(o) as *mut f64;
        std::ptr::write(p, f);
    }
    o
}

/// Unbox a heap-allocated `f64`.
pub(crate) fn unbox_float(o: LeanObjPtr) -> f64 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Ctor,
            "unbox_float: pointer is not a constructor",
        );
    }
    // SAFETY: caller guarantees `o` is a heap-allocated f64 box (non-scalar,
    // allocated with scalar_size = size_of::<f64>()). Read is within bounds.
    unsafe {
        let p = CleanObj::scalar_ptr(o) as *const f64;
        std::ptr::read(p)
    }
}
