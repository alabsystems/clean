// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![allow(unsafe_op_in_unsafe_fn)]

//! Closure application for clean objects.
//!
//! Implements the core closure dispatch: under-saturation (extend closure),
//! exact saturation (call function), and over-application (call then apply
//! remaining args to result).
//!
//! Matches the C runtime API (`clean_runtime.c:246-418`).
//!
//! Part of #1952.

use super::alloc::alloc_closure;
use super::rc::{dec, inc};
use super::{expect, expect_obj_kind};
use crate::object_model::{closure_args_ptr, CleanObj, ClosureObj};

type LeanObj = CleanObj;
type LeanClosure = ClosureObj;

/// Maximum closure arity (matches C runtime's CLEAN_MAX_CLOSURE_ARGS).
const MAX_CLOSURE_ARGS: usize = 16;

/// Generate type aliases and call_closure dispatch for arities 1..N.
macro_rules! dispatch_call {
    ($fun:expr, $args:expr, $($n:tt),+) => {
        match (*$fun).arity {
            $(
                $n => {
                    dispatch_call!(@call $fun, $args, $n)
                }
            )+
            _ => super::boxing::panic_msg(
                "closure arity exceeds MAX_CLOSURE_ARGS (16)",
            ),
        }
    };
    // Expand a single call with $n positional args from $args slice.
    (@call $fun:expr, $args:expr, 1) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(*mut LeanObj) -> *mut LeanObj>(
            (*$fun).func,
        ))($args[0])
    };
    (@call $fun:expr, $args:expr, 2) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(*mut LeanObj, *mut LeanObj) -> *mut LeanObj>(
            (*$fun).func,
        ))($args[0], $args[1])
    };
    (@call $fun:expr, $args:expr, 3) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))($args[0], $args[1], $args[2])
    };
    (@call $fun:expr, $args:expr, 4) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))($args[0], $args[1], $args[2], $args[3])
    };
    (@call $fun:expr, $args:expr, 5) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))($args[0], $args[1], $args[2], $args[3], $args[4])
    };
    (@call $fun:expr, $args:expr, 6) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))($args[0], $args[1], $args[2], $args[3], $args[4], $args[5])
    };
    (@call $fun:expr, $args:expr, 7) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6],
        )
    };
    (@call $fun:expr, $args:expr, 8) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
        )
    };
    (@call $fun:expr, $args:expr, 9) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8],
        )
    };
    (@call $fun:expr, $args:expr, 10) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8], $args[9],
        )
    };
    (@call $fun:expr, $args:expr, 11) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8], $args[9], $args[10],
        )
    };
    (@call $fun:expr, $args:expr, 12) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8], $args[9], $args[10], $args[11],
        )
    };
    (@call $fun:expr, $args:expr, 13) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8], $args[9], $args[10], $args[11], $args[12],
        )
    };
    (@call $fun:expr, $args:expr, 14) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8], $args[9], $args[10], $args[11], $args[12], $args[13],
        )
    };
    (@call $fun:expr, $args:expr, 15) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8], $args[9], $args[10], $args[11], $args[12], $args[13], $args[14],
        )
    };
    (@call $fun:expr, $args:expr, 16) => {
        (std::mem::transmute::<_, unsafe extern "C" fn(
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
            *mut LeanObj,
        ) -> *mut LeanObj>((*$fun).func))(
            $args[0], $args[1], $args[2], $args[3], $args[4], $args[5], $args[6], $args[7],
            $args[8], $args[9], $args[10], $args[11], $args[12], $args[13], $args[14], $args[15],
        )
    };
}

/// Call a fully saturated closure with positional arguments.
///
/// # Safety
/// `c` must be a valid `LeanClosure`. `all_args` must have exactly
/// `(*c).arity` elements, each a valid clean object.
#[allow(clippy::missing_transmute_annotations)]
unsafe fn call_closure(c: *mut LeanClosure, all_args: &[*mut LeanObj]) -> *mut LeanObj {
    // SAFETY: Caller guarantees valid closure and correct arg count.
    dispatch_call!(c, all_args, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16)
}

/// Create a new closure extending `c` with additional captured arguments.
///
/// Increments refcounts on existing captured args (shared with old closure).
/// Caller transfers ownership of `new_args` (no inc needed).
///
/// # Safety
/// `c` must be a valid `LeanClosure`. `new_args` must all be valid clean objects.
unsafe fn extend_closure(c: *mut LeanClosure, new_args: &[*mut LeanObj]) -> *mut LeanObj {
    // SAFETY: Build combined args: existing captured (inc'd) + new (transferred).
    let old_fixed = (*c).num_fixed as usize;
    let new_fixed = old_fixed + new_args.len();
    expect(
        new_fixed <= MAX_CLOSURE_ARGS,
        "extend_closure: captured args exceed MAX_CLOSURE_ARGS",
    );

    let mut all_fixed = Vec::with_capacity(new_fixed);
    let old_args = closure_args_ptr(c);
    for i in 0..old_fixed {
        let arg = *old_args.add(i);
        inc(arg);
        all_fixed.push(arg);
    }
    all_fixed.extend_from_slice(new_args);

    // SAFETY: alloc_closure handles allocation and field writes.
    alloc_closure((*c).func as *mut (), (*c).arity, &all_fixed)
}

/// Collect fixed + new args into a stack buffer, returns arity.
///
/// # Safety
/// `c` must be a valid `LeanClosure`. `new_args` must be within `args[offset..]`.
unsafe fn collect_args(
    c: *mut LeanClosure,
    args: &[*mut LeanObj],
    offset: usize,
    n_new: usize,
    buf: &mut [*mut LeanObj; MAX_CLOSURE_ARGS],
) {
    let num_fixed = (*c).num_fixed as usize;
    let fixed_args = closure_args_ptr(c);
    // SAFETY: fixed_args points to num_fixed valid pointers within the closure.
    let fixed_slice = std::slice::from_raw_parts(fixed_args, num_fixed);
    buf[..num_fixed].copy_from_slice(fixed_slice);
    buf[num_fixed..num_fixed + n_new].copy_from_slice(&args[offset..offset + n_new]);
}

/// Apply `args` to closure `f`. Handles under-saturation, exact saturation,
/// and over-application.
///
/// Consumes one reference to `f`. Caller retains ownership of args.
///
/// # Safety
/// `f` must be a valid closure object. All `args` must be valid clean objects.
#[must_use]
pub unsafe fn apply_n(mut f: *mut LeanObj, args: &[*mut LeanObj]) -> *mut LeanObj {
    // SAFETY: Loop invariant: `f` is a valid closure, args[offset..] are valid.
    let mut offset = 0;
    while offset < args.len() {
        let c = f as *mut LeanClosure;
        expect_obj_kind(
            f,
            crate::object_model::ObjKind::Closure,
            "apply_n: pointer is not a closure",
        );
        let remaining = (*c).arity as usize - (*c).num_fixed as usize;
        expect(
            remaining > 0,
            "apply_n: remaining closure arity must be > 0",
        );

        let n = args.len() - offset;
        if n < remaining {
            let result = extend_closure(c, &args[offset..]);
            dec(f);
            return result;
        }
        let saturate_n = if n == remaining { n } else { remaining };
        let mut all_args = [std::ptr::null_mut::<LeanObj>(); MAX_CLOSURE_ARGS];
        collect_args(c, args, offset, saturate_n, &mut all_args);
        let result = call_closure(c, &all_args[..(*c).arity as usize]);
        dec(f);
        if n == remaining {
            return result;
        }
        f = result;
        offset += remaining;
    }
    f
}

// -- Specialized apply_N wrappers ----------------------------------------

/// Apply 1 argument to a closure.
///
/// # Safety
/// `f` must be a valid closure. `a1` must be a valid clean object.
#[must_use]
pub unsafe fn apply_1(f: *mut LeanObj, a1: *mut LeanObj) -> *mut LeanObj {
    apply_n(f, &[a1])
}

/// Apply 2 arguments to a closure.
///
/// # Safety
/// `f` must be a valid closure. All args must be valid clean objects.
#[must_use]
pub unsafe fn apply_2(f: *mut LeanObj, a1: *mut LeanObj, a2: *mut LeanObj) -> *mut LeanObj {
    apply_n(f, &[a1, a2])
}

/// Apply 3 arguments to a closure.
///
/// # Safety
/// `f` must be a valid closure. All args must be valid clean objects.
#[must_use]
pub unsafe fn apply_3(
    f: *mut LeanObj,
    a1: *mut LeanObj,
    a2: *mut LeanObj,
    a3: *mut LeanObj,
) -> *mut LeanObj {
    apply_n(f, &[a1, a2, a3])
}

/// Apply 4 arguments to a closure.
///
/// # Safety
/// `f` must be a valid closure. All args must be valid clean objects.
#[must_use]
pub unsafe fn apply_4(
    f: *mut LeanObj,
    a1: *mut LeanObj,
    a2: *mut LeanObj,
    a3: *mut LeanObj,
    a4: *mut LeanObj,
) -> *mut LeanObj {
    apply_n(f, &[a1, a2, a3, a4])
}

// -- Tests ---------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::alloc::alloc_closure;
    use crate::native::{box_val, is_scalar, unbox_val};

    unsafe extern "C" fn identity(a: *mut LeanObj) -> *mut LeanObj {
        a
    }

    unsafe extern "C" fn second(_a: *mut LeanObj, b: *mut LeanObj) -> *mut LeanObj {
        b
    }

    unsafe extern "C" fn add_scalars(a: *mut LeanObj, b: *mut LeanObj) -> *mut LeanObj {
        let x = unbox_val(a);
        let y = unbox_val(b);
        box_val(x + y)
    }

    unsafe extern "C" fn third(
        _a: *mut LeanObj,
        _b: *mut LeanObj,
        c: *mut LeanObj,
    ) -> *mut LeanObj {
        c
    }

    #[test]
    fn test_apply_1_exact_saturation() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let f = alloc_closure(identity as *mut (), 1, &[]);
            let result = apply_1(f, box_val(42));
            assert!(is_scalar(result));
            assert_eq!(unbox_val(result), 42);
        }
    }

    #[test]
    fn test_apply_2_exact_saturation() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let f = alloc_closure(second as *mut (), 2, &[]);
            let result = apply_2(f, box_val(10), box_val(20));
            assert!(is_scalar(result));
            assert_eq!(unbox_val(result), 20);
        }
    }

    #[test]
    fn test_apply_under_saturated_then_exact() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let f = alloc_closure(add_scalars as *mut (), 2, &[]);
            let partial = apply_1(f, box_val(10));
            assert!(!is_scalar(partial));
            let result = apply_1(partial, box_val(32));
            assert!(is_scalar(result));
            assert_eq!(unbox_val(result), 42);
        }
    }

    #[test]
    fn test_apply_n_over_application() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let inner = alloc_closure(identity as *mut (), 1, &[]);
            let outer = alloc_closure(second as *mut (), 2, &[]);
            let result = apply_n(outer, &[box_val(0), inner, box_val(99)]);
            assert!(is_scalar(result));
            assert_eq!(unbox_val(result), 99);
        }
    }

    #[test]
    fn test_apply_3_exact() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let f = alloc_closure(third as *mut (), 3, &[]);
            let result = apply_3(f, box_val(1), box_val(2), box_val(3));
            assert!(is_scalar(result));
            assert_eq!(unbox_val(result), 3);
        }
    }

    #[test]
    fn test_apply_with_pre_fixed_args() {
        // SAFETY: All pointers are valid heap objects allocated in this test.
        // They are uniquely owned unless explicitly shared via inc().
        unsafe {
            let f = alloc_closure(add_scalars as *mut (), 2, &[box_val(10)]);
            let result = apply_1(f, box_val(32));
            assert!(is_scalar(result));
            assert_eq!(unbox_val(result), 42);
        }
    }
}
