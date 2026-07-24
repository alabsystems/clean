// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closure allocation, field access, and application dispatch.
//!
//! Closures represent partial applications. The function pointer, arity, and
//! captured arguments are stored in a [`ClosureObj`] with a flexible tail.

use super::types::*;
use crate::object_model::alloc_closure_obj;

const MAX_STACK_CLOSURE_ARGS: usize = 16;

// ---------------------------------------------------------------------------
// Closure allocation
// ---------------------------------------------------------------------------

/// Allocate a closure (partial application).
///
/// `func` is the function pointer, `arity` is its total arity, and `args` are
/// the captured arguments so far.
pub(crate) fn alloc_closure(func: *const (), arity: u16, args: &[LeanObjPtr]) -> LeanObjPtr {
    alloc_closure_obj(func, arity, args)
}

// ---------------------------------------------------------------------------
// Closure field access
// ---------------------------------------------------------------------------

/// Get the function pointer from a closure.
pub(crate) fn closure_func(o: LeanObjPtr) -> *const () {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Closure,
            "closure_func: pointer is not a closure",
        );
    }
    // SAFETY: caller guarantees `o` is a non-scalar closure object.
    // Cast to ClosureObj is valid because the kind field is ObjKind::Closure.
    unsafe { (*(o as *const ClosureObj)).func }
}

/// Get the total arity of a closure.
pub(crate) fn closure_arity(o: LeanObjPtr) -> u16 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Closure,
            "closure_arity: pointer is not a closure",
        );
    }
    // SAFETY: same as closure_func — `o` is a non-scalar closure.
    unsafe { (*(o as *const ClosureObj)).arity }
}

/// Get the number of captured arguments in a closure.
pub(crate) fn closure_num_fixed(o: LeanObjPtr) -> u16 {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            o,
            ObjKind::Closure,
            "closure_num_fixed: pointer is not a closure",
        );
    }
    // SAFETY: same as closure_func — `o` is a non-scalar closure.
    unsafe { (*(o as *const ClosureObj)).num_fixed }
}

/// Get the `idx`-th captured argument from a closure.
pub(crate) fn closure_arg(o: LeanObjPtr, idx: usize) -> LeanObjPtr {
    // SAFETY: `o` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(o, ObjKind::Closure, "closure_arg: pointer is not a closure");
    }
    // SAFETY: the release-enforced checks above verify `o` is a closure and
    // `idx < num_fixed`, so args_ptr + add(idx) stays within the captured-arg
    // region.
    unsafe {
        let c = o as *mut ClosureObj;
        expect_index_lt(
            idx,
            (*c).num_fixed as usize,
            "closure_arg: index out of bounds",
        );
        *ClosureObj::args_ptr(c).add(idx)
    }
}

// ---------------------------------------------------------------------------
// Closure application
// ---------------------------------------------------------------------------

/// Apply `new_args` to a closure object (Lean 4 `lean_apply_n` equivalent).
///
/// Semantics mirror `src/runtime/apply.cpp` in the reference implementation:
/// - **Exact application** (`num_fixed + N == arity`): invoke the function pointer
///   directly with all captured + new arguments.
/// - **Under-application** (`num_fixed + N < arity`): create a bigger closure
///   capturing the additional arguments.
/// - **Over-application** (`num_fixed + N > arity`): invoke with enough args to
///   saturate, then recursively apply remaining args to the result (which must
///   itself be a closure).
pub(crate) fn closure_apply(closure: LeanObjPtr, new_args: &[LeanObjPtr]) -> LeanObjPtr {
    // SAFETY: `closure` is a non-scalar heap pointer (caller precondition).
    // Dereferencing the header to check the kind field is valid.
    unsafe {
        expect_obj_kind(
            closure,
            ObjKind::Closure,
            "closure_apply: pointer is not a closure",
        );
    }

    let arity = closure_arity(closure) as usize;
    let num_fixed = closure_num_fixed(closure) as usize;
    let total = num_fixed + new_args.len();

    if total < arity {
        // Under-application: extend the closure with more captured args.
        with_combined_closure_args(closure, new_args, total, |all_args| {
            alloc_closure(closure_func(closure), arity as u16, all_args)
        })
    } else if total == arity {
        // Exact application: invoke the function pointer.
        with_combined_closure_args(closure, new_args, arity, |all_args| {
            invoke_closure_func(closure_func(closure), all_args)
        })
    } else {
        // Over-application: saturate, then apply remainder to result.
        let needed = arity - num_fixed;
        let (saturate, remainder) = new_args.split_at(needed);

        let result = with_combined_closure_args(closure, saturate, arity, |all_args| {
            invoke_closure_func(closure_func(closure), all_args)
        });
        // Result must be a closure; apply remaining args recursively.
        closure_apply(result, remainder)
    }
}

fn with_combined_closure_args<R>(
    closure: LeanObjPtr,
    new_args: &[LeanObjPtr],
    total: usize,
    f: impl FnOnce(&[LeanObjPtr]) -> R,
) -> R {
    let num_fixed = closure_num_fixed(closure) as usize;

    if total <= MAX_STACK_CLOSURE_ARGS {
        let mut stack_args = [std::ptr::null_mut(); MAX_STACK_CLOSURE_ARGS];
        for (i, slot) in stack_args.iter_mut().enumerate().take(num_fixed) {
            *slot = closure_arg(closure, i);
        }
        stack_args[num_fixed..total].copy_from_slice(new_args);
        f(&stack_args[..total])
    } else {
        let mut heap_args = Vec::with_capacity(total);
        for i in 0..num_fixed {
            heap_args.push(closure_arg(closure, i));
        }
        heap_args.extend_from_slice(new_args);
        f(&heap_args)
    }
}

/// Invoke a raw function pointer with the given arguments.
///
/// The function pointer is cast to the appropriate `unsafe extern "C" fn(...)`
/// type based on the argument count. Supports up to 16 arguments (matching
/// Lean 4).
fn invoke_closure_func(func: *const (), args: &[LeanObjPtr]) -> LeanObjPtr {
    // SAFETY: The function pointer was stored by alloc_closure and the caller
    // guarantees the correct number of arguments. We transmute to the
    // appropriately-typed function pointer based on arity.
    //
    // ABI assumption: The stored function pointer must use the runtime's C ABI
    // and accept exactly `args.len()` parameters of type `LeanObjPtr`, returning
    // `LeanObjPtr`. This matches Lean 4's runtime surface and the FFI-facing
    // clean closure tests.
    unsafe {
        match args.len() {
            0 => {
                let f: unsafe extern "C" fn() -> LeanObjPtr = std::mem::transmute(func);
                f()
            }
            1 => {
                let f: unsafe extern "C" fn(LeanObjPtr) -> LeanObjPtr = std::mem::transmute(func);
                f(args[0])
            }
            2 => {
                let f: unsafe extern "C" fn(LeanObjPtr, LeanObjPtr) -> LeanObjPtr =
                    std::mem::transmute(func);
                f(args[0], args[1])
            }
            3 => {
                let f: unsafe extern "C" fn(LeanObjPtr, LeanObjPtr, LeanObjPtr) -> LeanObjPtr =
                    std::mem::transmute(func);
                f(args[0], args[1], args[2])
            }
            4 => {
                let f: unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr = std::mem::transmute(func);
                f(args[0], args[1], args[2], args[3])
            }
            5 => {
                let f: unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr = std::mem::transmute(func);
                f(args[0], args[1], args[2], args[3], args[4])
            }
            6 => {
                let f: unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr = std::mem::transmute(func);
                f(args[0], args[1], args[2], args[3], args[4], args[5])
            }
            7 => {
                let f: unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6],
                )
            }
            8 => {
                let f: unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                )
            }
            9 => {
                type F9 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F9 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8],
                )
            }
            10 => {
                type F10 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F10 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                    args[8], args[9],
                )
            }
            11 => {
                type F11 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F11 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                    args[8], args[9], args[10],
                )
            }
            12 => {
                type F12 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F12 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                    args[8], args[9], args[10], args[11],
                )
            }
            13 => {
                type F13 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F13 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                    args[8], args[9], args[10], args[11], args[12],
                )
            }
            14 => {
                type F14 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F14 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                    args[8], args[9], args[10], args[11], args[12], args[13],
                )
            }
            15 => {
                type F15 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F15 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                    args[8], args[9], args[10], args[11], args[12], args[13], args[14],
                )
            }
            16 => {
                type F16 = unsafe extern "C" fn(
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                    LeanObjPtr,
                ) -> LeanObjPtr;
                let f: F16 = std::mem::transmute(func);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7],
                    args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15],
                )
            }
            n => lean_panic(&format!(
                "closure_apply: arity {} exceeds maximum supported (16)",
                n
            )),
        }
    }
}
