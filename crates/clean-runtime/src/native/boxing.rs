// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boxing, unboxing, string operations, and runtime lifecycle.

use std::mem::size_of;

use super::alloc::alloc_ctor_uninit;
use super::{box_val, ctor_scalar_ptr, is_scalar, unbox_val, LeanObj, LeanString, MAX_SMALL};
use crate::object_model::alloc_string_bytes;

// ============================================================================
// Boxing
// ============================================================================

/// Box a u64 into a heap object (always allocates).
///
/// # Safety
/// The returned object must be managed via inc/dec.
#[must_use]
pub unsafe fn box_uint64(n: u64) -> *mut LeanObj {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        let o = alloc_ctor_uninit(0, 0, size_of::<u64>() as u8);
        // SAFETY: alloc_ctor_uninit returned a valid Ctor with scalar_sz=8.
        // ctor_scalar_ptr returns a pointer to the 8-byte scalar region.
        // Writing a u64 (8 bytes) is within the allocated scalar region.
        let scalar = ctor_scalar_ptr(o);
        (scalar as *mut u64).write(n);
        o
    }
}

/// Unbox a u64 from a tagged scalar or heap object.
///
/// Mirrors [`unbox_uint32`]'s tagged-or-heap dispatch: a small value is the
/// tagged immediate, a larger value the heap box. Was heap-only, which read
/// garbage off a tagged pointer — the parity fix for the C header's
/// `clean_unbox_uint64`, so the `UInt64.ofNat`/`ofNatLT` and `USize.ofNatLT`
/// Nat-carrier decode is faithful across every runtime.
///
/// # Safety
/// `o` must be a boxed u64 (tagged scalar or heap object with scalar_sz=8).
#[must_use]
pub unsafe fn unbox_uint64(o: *const LeanObj) -> u64 {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        if is_scalar(o) {
            unbox_val(o) as u64
        } else {
            // SAFETY: caller guarantees `o` is a boxed u64 (scalar_sz=8).
            // ctor_scalar_ptr returns a pointer to the 8-byte scalar region.
            let scalar = ctor_scalar_ptr(o as *mut LeanObj);
            (scalar as *const u64).read()
        }
    }
}

/// Box a u32. Values <= MAX_SMALL use tagged pointers; larger values allocate.
///
/// # Safety
/// If heap-allocated, the returned object must be managed via inc/dec.
#[must_use]
pub unsafe fn box_uint32(n: u32) -> *mut LeanObj {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        if (n as usize) <= MAX_SMALL {
            box_val(n as usize)
        } else {
            let o = alloc_ctor_uninit(0, 0, size_of::<u32>() as u8);
            // SAFETY: alloc_ctor_uninit returned a valid Ctor with scalar_sz=4.
            // Writing a u32 (4 bytes) fits within the scalar region.
            let scalar = ctor_scalar_ptr(o);
            (scalar as *mut u32).write(n);
            o
        }
    }
}

/// Unbox a u32.
///
/// # Safety
/// `o` must be a boxed u32 (tagged scalar or heap-allocated).
#[must_use]
pub unsafe fn unbox_uint32(o: *const LeanObj) -> u32 {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        if is_scalar(o) {
            unbox_val(o) as u32
        } else {
            // SAFETY: caller guarantees `o` is a boxed u32 (scalar_sz=4).
            let scalar = ctor_scalar_ptr(o as *mut LeanObj);
            (scalar as *const u32).read()
        }
    }
}

/// Box an f32 (always allocates -- no tagged pointer for floats).
///
/// # Safety
/// The returned object must be managed via inc/dec.
#[must_use]
pub unsafe fn box_float32(f: f32) -> *mut LeanObj {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        let o = alloc_ctor_uninit(0, 0, size_of::<f32>() as u8);
        // SAFETY: alloc_ctor_uninit returned a valid Ctor with scalar_sz=4.
        // Writing an f32 (4 bytes) fits within the scalar region.
        let scalar = ctor_scalar_ptr(o);
        (scalar as *mut f32).write(f);
        o
    }
}

/// Unbox an f32.
///
/// # Safety
/// `o` must be a boxed f32 object (kind=Ctor, num_objs=0, scalar_sz=4).
#[must_use]
pub unsafe fn unbox_float32(o: *const LeanObj) -> f32 {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        // SAFETY: caller guarantees `o` is a boxed f32 (scalar_sz=4).
        // ctor_scalar_ptr returns a pointer to the 4-byte scalar region.
        let scalar = ctor_scalar_ptr(o as *mut LeanObj);
        (scalar as *const f32).read()
    }
}

/// Box a f64 (always allocates -- no tagged pointer for floats).
///
/// # Safety
/// The returned object must be managed via inc/dec.
#[must_use]
pub unsafe fn box_float(f: f64) -> *mut LeanObj {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        let o = alloc_ctor_uninit(0, 0, size_of::<f64>() as u8);
        // SAFETY: alloc_ctor_uninit returned a valid Ctor with scalar_sz=8.
        // Writing an f64 (8 bytes) fits within the scalar region.
        let scalar = ctor_scalar_ptr(o);
        (scalar as *mut f64).write(f);
        o
    }
}

/// Unbox a f64.
///
/// # Safety
/// `o` must be a boxed f64 object.
#[must_use]
pub unsafe fn unbox_float(o: *const LeanObj) -> f64 {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        // SAFETY: caller guarantees `o` is a boxed f64 (scalar_sz=8).
        let scalar = ctor_scalar_ptr(o as *mut LeanObj);
        (scalar as *const f64).read()
    }
}

// ============================================================================
// Strings
// ============================================================================

/// Create a string object from a byte slice.
///
/// The string is stored null-terminated internally.
///
/// # Safety
/// The returned object must be managed via inc/dec.
#[must_use]
pub unsafe fn mk_string(s: &[u8]) -> *mut LeanObj {
    alloc_string_bytes(s)
}

/// Create a string object from a Rust `&str`.
///
/// # Safety
/// The returned object must be managed via inc/dec.
#[must_use]
pub unsafe fn mk_string_from_str(s: &str) -> *mut LeanObj {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        // SAFETY: &str guarantees valid UTF-8; as_bytes() is a zero-cost view.
        // Safety of the allocation is delegated to mk_string.
        mk_string(s.as_bytes())
    }
}

/// Get the byte length of a string object.
///
/// # Safety
/// `o` must be a valid String object.
#[must_use]
pub unsafe fn string_len(o: *const LeanObj) -> usize {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        // SAFETY: caller guarantees `o` is a valid String object (kind=String).
        // The cast to LeanString is valid because the allocation was created
        // with string_layout and the header kind field confirms String.
        (*(o as *const LeanString)).len
    }
}

/// Get a pointer to the string's UTF-8 data (null-terminated).
///
/// # Safety
/// `o` must be a valid String object. The returned pointer is valid
/// as long as `o` is alive.
#[must_use]
pub unsafe fn string_data(o: *const LeanObj) -> *const u8 {
    // SAFETY: The caller provides values encoded by the documented Lean scalar/object ABI; the body checks the representation before reading or writing its payload.
    unsafe {
        // SAFETY: caller guarantees `o` is a valid String object. The data
        // region starts immediately after the LeanString struct, within
        // the same allocation.
        (o as *const u8).add(size_of::<LeanString>())
    }
}

// ============================================================================
// Panic
// ============================================================================

/// Abort with an error message.
///
/// Delegates to `crate::object_model::lean_panic` — the canonical panic
/// implementation shared by both `native` and `runtime` facades. Part of #2827.
pub fn panic_msg(msg: &str) -> ! {
    crate::object_model::lean_panic(msg)
}

// ============================================================================
// Init / Finalize
// ============================================================================

/// Initialize the runtime. Delegates to the shared canonical implementation.
pub fn runtime_init() {
    crate::object_model::runtime_init()
}

/// Finalize the runtime. Delegates to the shared canonical implementation.
pub fn runtime_finalize() {
    crate::object_model::runtime_finalize()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::{dec, is_scalar, ObjKind};

    #[test]
    fn test_box_uint64_roundtrip() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = box_uint64(u64::MAX);
            assert!(!is_scalar(o));
            assert_eq!(unbox_uint64(o), u64::MAX);
            dec(o);
        }
    }

    #[test]
    fn test_box_uint64_zero() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = box_uint64(0);
            assert_eq!(unbox_uint64(o), 0);
            dec(o);
        }
    }

    #[test]
    fn test_box_uint32_small_uses_tagged() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = box_uint32(42);
            assert!(is_scalar(o));
            assert_eq!(unbox_uint32(o), 42);
        }
    }

    #[test]
    fn test_box_uint32_large_uses_tag() {
        // 0x1000 is above the old 0xFFF cutoff but still fits within MAX_SMALL.
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = box_uint32(0x1000);
            assert!(is_scalar(o));
            assert_eq!(unbox_uint32(o), 0x1000);
        }
    }

    #[test]
    fn test_box_uint32_boundary() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o1 = box_uint32(0xFFF);
            assert!(is_scalar(o1));
            assert_eq!(unbox_uint32(o1), 0xFFF);

            // 0x1000 crosses the old cutoff, but it still remains tagged under MAX_SMALL.
            let o2 = box_uint32(0x1000);
            assert!(is_scalar(o2));
            assert_eq!(unbox_uint32(o2), 0x1000);
        }
    }

    #[test]
    fn test_box_float32_roundtrip() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let o = box_float32(std::f32::consts::PI);
            assert!(!is_scalar(o));
            assert_eq!(unbox_float32(o), std::f32::consts::PI);
            assert_eq!((*o).header.scalar_sz, 4);
            dec(o);
        }
    }

    #[test]
    fn test_box_float32_special_values() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            // Use to_bits() for -0.0 since assert_eq!(-0.0, 0.0) is true in IEEE 754
            for val in [0.0f32, -0.0, f32::INFINITY, f32::NEG_INFINITY] {
                let o = box_float32(val);
                assert_eq!(unbox_float32(o).to_bits(), val.to_bits());
                dec(o);
            }
            let o = box_float32(f32::NAN);
            let roundtrip = unbox_float32(o);
            assert!(roundtrip.is_nan());
            // Verify bit-exact NaN payload preservation (not just "is NaN")
            assert_eq!(roundtrip.to_bits(), f32::NAN.to_bits());
            dec(o);
        }
    }

    /// Float32 subnormal and edge values — mirrors test_box_float_subnormal_and_edge.
    #[test]
    fn test_box_float32_subnormal_and_edge() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let edge_values: [f32; 6] = [
                f32::MIN_POSITIVE,      // smallest normal
                1.4e-45,                // smallest f32 subnormal
                f32::MAX,               // largest finite
                f32::MIN,               // most negative finite
                f32::EPSILON,           // smallest difference from 1.0
                1.0_f32 + f32::EPSILON, // 1.0 + epsilon
            ];
            for val in edge_values {
                let o = box_float32(val);
                assert_eq!(
                    unbox_float32(o).to_bits(),
                    val.to_bits(),
                    "Float32 roundtrip failed for {val:e} (bits: {:#010x})",
                    val.to_bits()
                );
                dec(o);
            }
        }
    }

    #[test]
    fn test_box_float_roundtrip() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let o = box_float(std::f64::consts::PI);
            assert!(!is_scalar(o));
            assert_eq!(unbox_float(o), std::f64::consts::PI);
            dec(o);
        }
    }

    #[test]
    fn test_box_float_special_values() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            // Use to_bits() for -0.0 since assert_eq!(-0.0, 0.0) is true in IEEE 754
            for val in [0.0, -0.0, f64::INFINITY, f64::NEG_INFINITY] {
                let o = box_float(val);
                assert_eq!(unbox_float(o).to_bits(), val.to_bits());
                dec(o);
            }
            let o = box_float(f64::NAN);
            assert!(unbox_float(o).is_nan());
            dec(o);
        }
    }

    #[test]
    fn test_mk_string_roundtrip() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let s = mk_string(b"hello");
            assert_eq!(string_len(s), 5);
            let data = string_data(s);
            let slice = std::slice::from_raw_parts(data, 5);
            assert_eq!(slice, b"hello");
            assert_eq!(*data.add(5), 0);
            dec(s);
        }
    }

    #[test]
    fn test_mk_string_empty() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let s = mk_string(b"");
            assert_eq!(string_len(s), 0);
            assert_eq!(*string_data(s), 0);
            dec(s);
        }
    }

    #[test]
    fn test_mk_string_from_str() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let s = mk_string_from_str("world");
            assert_eq!(string_len(s), 5);
            let data = std::slice::from_raw_parts(string_data(s), 5);
            assert_eq!(data, b"world");
            dec(s);
        }
    }

    #[test]
    fn test_string_kind() {
        // SAFETY: All objects were allocated by test helpers above and are valid
        // for the duration of this test. Header dereferences are within bounds.
        unsafe {
            let s = mk_string(b"test");
            assert_eq!((*s).header.kind, ObjKind::Str as u8);
            dec(s);
        }
    }

    #[test]
    fn test_runtime_init_finalize() {
        runtime_init();
        runtime_finalize();
    }

    /// Issue #1908: string deallocation with non-trivial content.
    /// Verifies no layout mismatch for strings of various lengths.
    #[test]
    fn test_mk_string_various_lengths() {
        // SAFETY: Pointers were returned by allocation functions above.
        // Pointer arithmetic stays within the allocated region.
        unsafe {
            for len in [1, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 1024] {
                let data = vec![b'x'; len];
                let s = mk_string(&data);
                assert_eq!(string_len(s), len);
                let ptr = string_data(s);
                // Verify null terminator
                assert_eq!(*ptr.add(len), 0);
                // Verify first byte
                assert_eq!(*ptr, b'x');
                dec(s);
            }
        }
    }

    /// Issue #1908: box_uint64 with edge values near overflow boundaries.
    #[test]
    fn test_box_uint64_edge_values() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            for val in [
                1u64,
                u32::MAX as u64,
                u32::MAX as u64 + 1,
                u64::MAX - 1,
                u64::MAX,
            ] {
                let o = box_uint64(val);
                assert_eq!(unbox_uint64(o), val);
                dec(o);
            }
        }
    }

    /// Issue #1908: box_float with subnormal and edge IEEE 754 values.
    #[test]
    fn test_box_float_subnormal_and_edge() {
        // SAFETY: All pointers are valid heap objects allocated in this test
        // and remain live for the duration of the unsafe block.
        unsafe {
            let edge_values = [
                f64::MIN_POSITIVE, // smallest normal
                5e-324,            // smallest subnormal
                f64::MAX,          // largest finite
                f64::MIN,          // most negative finite
                f64::EPSILON,      // smallest difference from 1.0
                1.0_f64.next_up(), // 1.0 + epsilon
            ];
            for val in edge_values {
                let o = box_float(val);
                assert_eq!(unbox_float(o), val);
                dec(o);
            }
        }
    }

    /// Issue #1908: box_uint32 around the historical 0xFFF/0x1000 transition.
    #[test]
    fn test_box_uint32_exhaustive_boundary() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            // This range used to straddle the old cutoff; now it stays on the tagged side.
            for n in 4090..4100u32 {
                let o = box_uint32(n);
                assert_eq!(unbox_uint32(o), n);
                if (n as usize) <= MAX_SMALL {
                    assert!(is_scalar(o));
                } else {
                    assert!(!is_scalar(o));
                    dec(o);
                }
            }
        }
    }
}
