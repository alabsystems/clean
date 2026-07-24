// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boxed version generation for declarations with scalar params/return.

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use crate::mangle::mangle_boxed_name;
use clean_kernel::Name;

use super::config::CLOSURE_MAX_ARGS;

pub fn requires_boxed_version(decl: &IRDecl) -> bool {
    if decl.params.is_empty() {
        return false;
    }
    decl.return_type.is_scalar()
        || decl
            .params
            .iter()
            .any(|(_, ty)| ty.is_scalar() || ty.is_void())
        || decl.params.len() > CLOSURE_MAX_ARGS
}

/// Build a chain of unbox operations for scalar parameters.
///
/// Recursion depth bounded by `original_params.len()` (max `CLOSURE_MAX_ARGS`).
fn build_unbox_chain(
    original_params: &[(VarId, IRType)],
    boxed_params: &[(VarId, IRType)],
    idx: usize,
    next_var: &mut u32,
    call_args: Vec<IRArg>,
    to_dec: Vec<VarId>,
    original_fn: &Name,
    result_type: &IRType,
) -> IRBody {
    if idx >= original_params.len() {
        return build_unbox_tail(*next_var, call_args, to_dec, original_fn, result_type);
    }
    let (_, orig_ty) = &original_params[idx];
    let (boxed_var, _) = &boxed_params[idx];
    if orig_ty.is_scalar() {
        let unboxed = VarId(*next_var);
        *next_var += 1;
        let mut new_args = call_args;
        new_args.push(IRArg::Var(unboxed));
        // PERCEUS OWNERSHIP (2026-07-12): a scalar param arrives as an OWNED
        // boxed `Object` whose only use here is `Unbox` (a READ). The box is
        // never forwarded to `original_fn` (only the extracted scalar is), so
        // the wrapper must `dec` it to consume the transferred ownership — else
        // a heap-boxed operand (every `clean_box_uint64`, and any
        // `UInt{32,64}`/`Float` >= the tagged-immediate boundary) LEAKS one
        // block per scalar param per call. Non-scalar params take the `else`
        // arm below: their box IS forwarded into the call, transferring
        // ownership to the callee, so they must NOT be dec'd here. This mirrors
        // the runtime's own boxed arithmetic entries (`clean_nat_add` &c.,
        // which `clean_dec(a); clean_dec(b)` after reading both operands).
        let mut new_to_dec = to_dec;
        new_to_dec.push(*boxed_var);
        IRBody::VDecl {
            var: unboxed,
            ty: orig_ty.clone(),
            value: IRExpr::Unbox {
                ty: orig_ty.clone(),
                arg: IRArg::Var(*boxed_var),
            },
            rest: Box::new(build_unbox_chain(
                original_params,
                boxed_params,
                idx + 1,
                next_var,
                new_args,
                new_to_dec,
                original_fn,
                result_type,
            )),
        }
    } else {
        let mut new_args = call_args;
        new_args.push(IRArg::Var(*boxed_var));
        build_unbox_chain(
            original_params,
            boxed_params,
            idx + 1,
            next_var,
            new_args,
            to_dec,
            original_fn,
            result_type,
        )
    }
}

/// Build the terminal call + optional box for the unbox chain.
///
/// `to_dec` are the boxed-param vars whose scalar payload was already unboxed
/// (see [`build_unbox_chain`]); each is `dec`'d here — AFTER every unbox has
/// read its scalar, and BEFORE the wrapped call — to consume the owned box
/// that is otherwise never forwarded.
fn build_unbox_tail(
    next_var: u32,
    call_args: Vec<IRArg>,
    to_dec: Vec<VarId>,
    original_fn: &Name,
    result_type: &IRType,
) -> IRBody {
    let result_var = VarId(next_var);
    let call = IRExpr::Apply {
        fn_id: FnId(original_fn.clone()),
        args: call_args,
    };
    // Consume every owned scalar box; the innermost body is the call + box/ret.
    let wrap_decs = |inner: IRBody| -> IRBody {
        to_dec.iter().rev().fold(inner, |acc, v| IRBody::Dec {
            var: *v,
            rest: Box::new(acc),
        })
    };
    if result_type.is_scalar() {
        let boxed_result = VarId(next_var + 1);
        wrap_decs(IRBody::VDecl {
            var: result_var,
            ty: result_type.clone(),
            value: call,
            rest: Box::new(IRBody::VDecl {
                var: boxed_result,
                ty: IRType::Object,
                value: IRExpr::Box {
                    ty: result_type.clone(),
                    arg: IRArg::Var(result_var),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(boxed_result))),
            }),
        })
    } else {
        wrap_decs(IRBody::VDecl {
            var: result_var,
            ty: result_type.clone(),
            value: call,
            rest: Box::new(IRBody::Ret(IRArg::Var(result_var))),
        })
    }
}

pub fn mk_boxed_version(decl: &IRDecl) -> IRDecl {
    let mangled = crate::mangle::mangle_name(&decl.name);
    let boxed_name = Name::from_string(&mangle_boxed_name(&mangled));
    let boxed_params: Vec<_> = decl
        .params
        .iter()
        .enumerate()
        .map(|(i, _)| (VarId(i as u32), IRType::Object))
        .collect();
    let mut next_var = boxed_params.len() as u32;
    let body = build_unbox_chain(
        &decl.params,
        &boxed_params,
        0,
        &mut next_var,
        Vec::new(),
        Vec::new(),
        &decl.name,
        &decl.return_type,
    );
    IRDecl {
        name: boxed_name,
        params: boxed_params,
        return_type: decl.return_type.boxed(),
        body,
    }
}
