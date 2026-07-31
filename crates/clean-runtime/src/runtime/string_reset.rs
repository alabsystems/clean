// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! String operations and reset/reuse memory optimization.

use std::alloc;

use super::ctor_scalar::alloc_ctor_uninit;
use super::refcount::{lean_dec, lean_is_unique};
use super::types::*;
use crate::object_model::{alloc_string_bytes, obj_child_count, obj_child_ptrs, object_layout};

// ---------------------------------------------------------------------------
// String operations
// ---------------------------------------------------------------------------

/// Create a string object from a Rust `&str`.
pub(crate) fn mk_string(s: &str) -> LeanObjPtr {
    alloc_string_bytes(s.as_bytes())
}

/// Get the UTF-8 bytes of a string object (without NUL terminator).
///
/// # Safety
///
/// The returned slice borrows from `o`'s heap allocation. The caller must
/// not use the slice after `lean_dec`/`lean_free` on `o`. The `'static`
/// lifetime is a simplification for FFI compatibility — the real lifetime
/// is bounded by `o`'s allocation. Part of #1923.
pub(crate) unsafe fn string_data(o: LeanObjPtr) -> &'static [u8] {
    // SAFETY: caller guarantees `o` is a valid string object pointer.
    unsafe {
        expect_obj_kind(o, ObjKind::Str, "string_data: pointer is not a string");
        let s = o as *mut StringObj;
        let len = (*s).len;
        let data = StringObj::data_ptr(s);
        std::slice::from_raw_parts(data, len)
    }
}

/// Get the byte length of a string object.
pub(crate) fn string_len(o: LeanObjPtr) -> usize {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(o, ObjKind::Str, "string_len: pointer is not a string");
    }
    // SAFETY: `o` is a non-scalar string object (kind = ObjKind::Str).
    unsafe { (*(o as *const StringObj)).len }
}

/// Get the string content as a `&str`.
///
/// # Safety
///
/// Same as [`string_data`] — the returned reference borrows from `o`'s
/// allocation and must not outlive the object. Part of #1923.
///
/// # Panics
/// Panics if the string is not valid UTF-8.
#[cfg(test)]
pub(crate) unsafe fn string_as_str(o: LeanObjPtr) -> &'static str {
    // SAFETY: caller guarantees `o` is alive; string_data safety delegated.
    std::str::from_utf8(unsafe { string_data(o) }).expect("clean string is not valid UTF-8")
}

// ---------------------------------------------------------------------------
// Reset / Reuse (memory optimization)
// ---------------------------------------------------------------------------

/// Reset an object for potential memory reuse.
///
/// If the object is uniquely owned, decrements all child fields and returns
/// the raw pointer for reuse via [`lean_reuse`]. Otherwise, decrements the
/// object and returns `null`.
pub(crate) fn lean_reset(o: LeanObjPtr) -> LeanObjPtr {
    // Scalars are always "unique" but are not heap objects — dereferencing
    // a tagged pointer to read header fields is UB. Return as-is.
    if is_scalar(o) {
        return o;
    }
    if lean_is_unique(o) {
        // Dec all child fields but keep the allocation.
        // Must use the correct field pointer for closures (args follow
        // func/arity/num_fixed, not the header) — same dispatch as lean_dec.
        // SAFETY: `o` is a non-scalar, uniquely owned heap object. Reading
        // header fields and child pointers is valid. lean_dec on each child
        // is safe because children are valid LeanObjPtr values.
        unsafe {
            let kind = ObjKind::from_u8((*o).header.kind);
            let num = obj_child_count(o);
            match kind {
                ObjKind::Closure | ObjKind::Ctor | ObjKind::Str => {
                    let children = obj_child_ptrs(o);
                    for i in 0..num {
                        lean_dec(*children.add(i));
                    }
                }
                ObjKind::Array | ObjKind::Thunk | ObjKind::Task | ObjKind::External => {
                    // These kinds have per-kind internal structure (array buffer,
                    // thunk closure/value, task value, external data) that requires
                    // specialized teardown via lean_dec → lean_dealloc_obj.
                    // Not reusable — dec the whole object and return null.
                    // Matches C runtime clean_reset (clean_runtime.h). Part of #2033.
                    lean_dec(o);
                    return std::ptr::null_mut();
                }
            }
        }
        o // Caller can reuse this allocation
    } else {
        lean_dec(o);
        std::ptr::null_mut() // Must allocate fresh
    }
}

/// Reuse a previously reset object slot, or allocate a fresh constructor.
///
/// If `reset_slot` is non-null, reuses its memory with a new `tag` and fields.
/// Otherwise allocates a new constructor.
///
/// `scalar_sz` is the total byte count for inline scalar storage. Scalars are
/// written separately via SSet instructions; this parameter only affects the
/// fresh-allocation fallback path sizing. Part of #1974.
///
/// # Safety invariant
///
/// When reusing a reset slot, `fields.len()` must equal the original
/// `num_objs` of the slot — the allocation is not resized, and
/// `alloc::dealloc` requires exact layout match. The Lean compiler
/// only generates reuse for same-arity constructors.
pub(crate) fn lean_reuse(
    reset_slot: LeanObjPtr,
    tag: u8,
    scalar_sz: u8,
    fields: &[LeanObjPtr],
) -> LeanObjPtr {
    // SAFETY: non-null reset_slot is a valid heap pointer (came from lean_reset).
    let o = if !reset_slot.is_null() && unsafe { (*reset_slot).header.kind == ObjKind::Ctor as u8 }
    {
        // Reuse existing Ctor allocation: update tag, write new fields.
        // SAFETY: reset_slot is non-null and kind==Ctor. Header writes are
        // within the allocated region.
        //
        unsafe {
            expect(
                fields.len() == (*reset_slot).header.num_objs as usize,
                "lean_reuse: field count must match slot capacity",
            );
            expect(
                scalar_sz == (*reset_slot).header.scalar_sz,
                "lean_reuse: scalar size must match slot layout",
            );
            (*reset_slot).header.tag = tag;
            (*reset_slot).header.num_objs = fields.len() as u8;
            (*reset_slot).header.scalar_sz = scalar_sz;
        }
        reset_slot
    } else {
        expect(
            fields.len() <= u8::MAX as usize,
            "lean_reuse: fields.len() exceeds u8::MAX on fallback allocation",
        );
        if !reset_slot.is_null() {
            // Non-Ctor slot (Closure, String, etc.) — layout mismatch prevents
            // safe in-place reuse. Deallocate using the correct kind-specific layout.
            // SAFETY: reset_slot is non-null heap pointer. Header fields are read
            // to compute the correct layout for deallocation. dealloc is called
            // with the same layout that was used for the original allocation.
            unsafe {
                alloc::dealloc(reset_slot as *mut u8, object_layout(reset_slot));
            }
        }
        // Part of #1974: pass scalar_sz instead of hardcoded 0.
        alloc_ctor_uninit(tag, fields.len() as u8, scalar_sz)
    };
    // SAFETY: `o` is a valid ctor allocation (either reused or fresh) with
    // space for `fields.len()` pointer fields. Writes are within bounds.
    unsafe {
        let dst = CleanObj::fields_ptr(o);
        for (i, &f) in fields.iter().enumerate() {
            std::ptr::write(dst.add(i), f);
        }
    }
    o
}
