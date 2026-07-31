// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed scalar field accessors for clean constructor objects.
//!
//! These functions read/write scalar fields within a constructor's scalar
//! data region. The `offset` parameter is a **byte offset** from the start
//! of the scalar area (not a field index).
//!
//! Memory layout: `[ObjHeader | obj_fields[0..num_objs] | scalar_bytes[0..scalar_sz]]`
//!
//! Matches the C header API (`clean_runtime.h:206-253`).
//!
//! Part of #1975.

use super::{ctor_scalar_ptr, LeanObj};

// -- Getters ------------------------------------------------------------------

/// Read a `u8` from the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a valid Ctor with `scalar_sz >= offset + 1`.
#[inline]
#[must_use]
pub unsafe fn ctor_get_uint8(o: *mut LeanObj, offset: usize) -> u8 {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor and offset within scalar_sz.
        ctor_scalar_ptr(o).add(offset).read()
    }
}

/// Read a `u16` from the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a valid Ctor with `scalar_sz >= offset + 2`.
#[inline]
#[must_use]
pub unsafe fn ctor_get_uint16(o: *mut LeanObj, offset: usize) -> u16 {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *const u16).read_unaligned()
    }
}

/// Read a `u32` from the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a valid Ctor with `scalar_sz >= offset + 4`.
#[inline]
#[must_use]
pub unsafe fn ctor_get_uint32(o: *mut LeanObj, offset: usize) -> u32 {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *const u32).read_unaligned()
    }
}

/// Read a `u64` from the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a valid Ctor with `scalar_sz >= offset + 8`.
#[inline]
#[must_use]
pub unsafe fn ctor_get_uint64(o: *mut LeanObj, offset: usize) -> u64 {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *const u64).read_unaligned()
    }
}

/// Read a `usize` from the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a valid Ctor with `scalar_sz >= offset + size_of::<usize>()`.
#[inline]
#[must_use]
pub unsafe fn ctor_get_usize(o: *mut LeanObj, offset: usize) -> usize {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *const usize).read_unaligned()
    }
}

/// Read an `f64` from the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a valid Ctor with `scalar_sz >= offset + 8`.
#[inline]
#[must_use]
pub unsafe fn ctor_get_float(o: *mut LeanObj, offset: usize) -> f64 {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *const f64).read_unaligned()
    }
}

/// Read an `f32` from the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a valid Ctor with `scalar_sz >= offset + 4`.
#[inline]
#[must_use]
pub unsafe fn ctor_get_float32(o: *mut LeanObj, offset: usize) -> f32 {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *const f32).read_unaligned()
    }
}

// -- Setters ------------------------------------------------------------------

/// Write a `u8` to the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a uniquely owned Ctor with `scalar_sz >= offset + 1`.
#[inline]
pub unsafe fn ctor_set_uint8(o: *mut LeanObj, offset: usize, v: u8) {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor, unique ownership, and offset within scalar_sz.
        ctor_scalar_ptr(o).add(offset).write(v);
    }
}

/// Write a `u16` to the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a uniquely owned Ctor with `scalar_sz >= offset + 2`.
#[inline]
pub unsafe fn ctor_set_uint16(o: *mut LeanObj, offset: usize, v: u16) {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor, unique ownership, and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *mut u16).write_unaligned(v);
    }
}

/// Write a `u32` to the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a uniquely owned Ctor with `scalar_sz >= offset + 4`.
#[inline]
pub unsafe fn ctor_set_uint32(o: *mut LeanObj, offset: usize, v: u32) {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor, unique ownership, and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *mut u32).write_unaligned(v);
    }
}

/// Write a `u64` to the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a uniquely owned Ctor with `scalar_sz >= offset + 8`.
#[inline]
pub unsafe fn ctor_set_uint64(o: *mut LeanObj, offset: usize, v: u64) {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor, unique ownership, and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *mut u64).write_unaligned(v);
    }
}

/// Write a `usize` to the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a uniquely owned Ctor with `scalar_sz >= offset + size_of::<usize>()`.
#[inline]
pub unsafe fn ctor_set_usize(o: *mut LeanObj, offset: usize, v: usize) {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor, unique ownership, and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *mut usize).write_unaligned(v);
    }
}

/// Write an `f64` to the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a uniquely owned Ctor with `scalar_sz >= offset + 8`.
#[inline]
pub unsafe fn ctor_set_float(o: *mut LeanObj, offset: usize, v: f64) {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor, unique ownership, and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *mut f64).write_unaligned(v);
    }
}

/// Write an `f32` to the scalar region at byte `offset`.
///
/// # Safety
/// `o` must be a uniquely owned Ctor with `scalar_sz >= offset + 4`.
#[inline]
pub unsafe fn ctor_set_float32(o: *mut LeanObj, offset: usize, v: f32) {
    // SAFETY: The caller provides a valid constructor allocation; the documented offset and scalar type identify an in-bounds, properly aligned payload slot.
    unsafe {
        // SAFETY: Caller guarantees valid Ctor, unique ownership, and offset within scalar_sz.
        (ctor_scalar_ptr(o).add(offset) as *mut f32).write_unaligned(v);
    }
}

// -- Tests --------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::alloc::alloc_ctor_uninit;

    /// Helper: allocate a ctor with 0 object fields and `scalar_sz` scalar bytes.
    unsafe fn make_scalar_ctor(scalar_sz: u8) -> *mut LeanObj {
        // SAFETY: This helper requests an empty constructor with a valid
        // scalar payload size and transfers ownership of the allocation to
        // its test caller.
        unsafe { alloc_ctor_uninit(0, 0, scalar_sz) }
    }

    #[test]
    fn test_uint8_round_trip() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(1);
            ctor_set_uint8(o, 0, 0xAB);
            assert_eq!(ctor_get_uint8(o, 0), 0xAB);
        }
    }

    #[test]
    fn test_uint16_round_trip() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(2);
            ctor_set_uint16(o, 0, 0x1234);
            assert_eq!(ctor_get_uint16(o, 0), 0x1234);
        }
    }

    #[test]
    fn test_uint32_round_trip() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(4);
            ctor_set_uint32(o, 0, 0xDEADBEEF);
            assert_eq!(ctor_get_uint32(o, 0), 0xDEADBEEF);
        }
    }

    #[test]
    fn test_uint64_round_trip() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(8);
            ctor_set_uint64(o, 0, 0x0123456789ABCDEF);
            assert_eq!(ctor_get_uint64(o, 0), 0x0123456789ABCDEF);
        }
    }

    #[test]
    fn test_usize_round_trip() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(8);
            ctor_set_usize(o, 0, usize::MAX);
            assert_eq!(ctor_get_usize(o, 0), usize::MAX);
        }
    }

    #[test]
    fn test_float_round_trip() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(8);
            ctor_set_float(o, 0, std::f64::consts::PI);
            assert_eq!(ctor_get_float(o, 0), std::f64::consts::PI);
        }
    }

    #[test]
    fn test_float32_round_trip() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(4);
            ctor_set_float32(o, 0, std::f32::consts::E);
            assert_eq!(ctor_get_float32(o, 0), std::f32::consts::E);
        }
    }

    #[test]
    fn test_multiple_scalar_fields_at_offsets() {
        // Simulate a ctor with a u8 at offset 0 and a u64 at offset 1.
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let o = make_scalar_ctor(9); // 1 + 8 = 9 bytes
            ctor_set_uint8(o, 0, 42);
            ctor_set_uint64(o, 1, 0xFFFF_FFFF_FFFF_FFFF);
            assert_eq!(ctor_get_uint8(o, 0), 42);
            assert_eq!(ctor_get_uint64(o, 1), 0xFFFF_FFFF_FFFF_FFFF);
        }
    }
}
