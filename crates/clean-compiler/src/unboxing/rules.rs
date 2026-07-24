// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unboxing optimization rules — pattern-matching rewrite functions.
//!
//! Each `try_*` function attempts one specific optimization on a VDecl.
//! Returns `Some((type, expr))` if the optimization applies, `None` otherwise.
//!
//! Part of Epic #3084 — IO/FFI/Native.

use crate::ir::{eqv_types, IRArg, IRExpr, IRLiteral, IRType, VarId};

use super::UnboxingContext;

/// Well-known Lean 4 arithmetic function names that operate on boxed Nat/UInt.
const NAT_ADD: &str = "Nat.add";
const NAT_SUB: &str = "Nat.sub";
const NAT_MUL: &str = "Nat.mul";
const NAT_DIV: &str = "Nat.div";
const NAT_MOD: &str = "Nat.mod";
const UINT64_ADD: &str = "UInt64.add";
const UINT64_SUB: &str = "UInt64.sub";
const UINT64_MUL: &str = "UInt64.mul";
const UINT32_ADD: &str = "UInt32.add";
const UINT32_SUB: &str = "UInt32.sub";
const UINT32_MUL: &str = "UInt32.mul";

/// Well-known comparison function names.
const NAT_DEC_LT: &str = "Nat.decLt";
const NAT_DEC_LE: &str = "Nat.decLe";
const NAT_DEC_EQ: &str = "Nat.decEq";
const NAT_BEQ: &str = "Nat.beq";
const UINT64_DEC_LT: &str = "UInt64.decLt";
const UINT64_DEC_LE: &str = "UInt64.decLe";
const UINT64_DEC_EQ: &str = "UInt64.decEq";
const UINT32_DEC_LT: &str = "UInt32.decLt";
const UINT32_DEC_LE: &str = "UInt32.decLe";
const UINT32_DEC_EQ: &str = "UInt32.decEq";

/// Optimize a single VDecl, returning the possibly-rewritten (type, value).
///
/// Tries each optimization rule in priority order. First match wins.
pub(crate) fn optimize_vdecl(
    _var: VarId,
    ty: &IRType,
    value: &IRExpr,
    ctx: &mut UnboxingContext,
) -> (IRType, IRExpr) {
    if ctx.config.eliminate_box_unbox_pairs {
        if let Some(result) = try_eliminate_unbox_box(ty, value, ctx) {
            return result;
        }
        if let Some(result) = try_eliminate_box_unbox(ty, value, ctx) {
            return result;
        }
    }

    if ctx.config.unbox_arithmetic {
        if let Some(result) = try_unbox_arithmetic(ty, value, ctx) {
            return result;
        }
    }

    if ctx.config.unbox_comparisons {
        if let Some(result) = try_unbox_comparison(ty, value, ctx) {
            return result;
        }
    }

    if ctx.config.enable_type_flow {
        if let Some(result) = try_type_flow_optimization(ty, value) {
            return result;
        }
    }

    (ty.clone(), value.clone())
}

/// Eliminate `let y : T = unbox(x)` when x was defined as `box(z)`.
///
/// Pattern: `let x = box(z); ... let y = unbox(x)` => reuse `z` directly.
fn try_eliminate_unbox_box(
    _ty: &IRType,
    value: &IRExpr,
    ctx: &mut UnboxingContext,
) -> Option<(IRType, IRExpr)> {
    if let IRExpr::Unbox {
        ty: unbox_ty,
        arg: IRArg::Var(inner_var),
    } = value
    {
        let def = ctx.get_def(*inner_var).cloned();
        if let Some(IRExpr::Box {
            ty: box_ty,
            arg: original_arg,
        }) = def
        {
            if eqv_types(unbox_ty, &box_ty)
                || (unbox_ty.is_scalar() && box_ty.is_scalar() && *unbox_ty == box_ty)
            {
                ctx.stats.pairs_eliminated += 1;
                return Some((
                    unbox_ty.clone(),
                    IRExpr::Unbox {
                        ty: unbox_ty.clone(),
                        arg: original_arg,
                    },
                ));
            }
        }
    }
    None
}

/// Eliminate `let y : Object = box(x)` when x was defined as `unbox(z)`.
///
/// Pattern: `let x = unbox(z); ... let y = box(x)` => reuse `z` directly.
fn try_eliminate_box_unbox(
    _ty: &IRType,
    value: &IRExpr,
    ctx: &mut UnboxingContext,
) -> Option<(IRType, IRExpr)> {
    if let IRExpr::Box {
        ty: box_ty,
        arg: IRArg::Var(inner_var),
    } = value
    {
        let def = ctx.get_def(*inner_var).cloned();
        if let Some(IRExpr::Unbox {
            arg: original_arg, ..
        }) = def
        {
            if box_ty.is_scalar() {
                ctx.stats.pairs_eliminated += 1;
                return Some((
                    IRType::Object,
                    IRExpr::Box {
                        ty: box_ty.clone(),
                        arg: original_arg,
                    },
                ));
            }
        }
    }
    None
}

/// Check if a function name matches a known arithmetic operation.
/// Returns the result scalar type if it does.
pub(super) fn classify_arithmetic(name: &str) -> Option<IRType> {
    match name {
        NAT_ADD | NAT_SUB | NAT_MUL | NAT_DIV | NAT_MOD => Some(IRType::UInt64),
        UINT64_ADD | UINT64_SUB | UINT64_MUL => Some(IRType::UInt64),
        UINT32_ADD | UINT32_SUB | UINT32_MUL => Some(IRType::UInt32),
        _ => None,
    }
}

/// Check if a function name matches a known comparison operation.
pub(super) fn classify_comparison(name: &str) -> bool {
    matches!(
        name,
        NAT_DEC_LT
            | NAT_DEC_LE
            | NAT_DEC_EQ
            | NAT_BEQ
            | UINT64_DEC_LT
            | UINT64_DEC_LE
            | UINT64_DEC_EQ
            | UINT32_DEC_LT
            | UINT32_DEC_LE
            | UINT32_DEC_EQ
    )
}

/// Try to replace a boxed arithmetic call with a direct unboxed operation.
fn try_unbox_arithmetic(
    _ty: &IRType,
    value: &IRExpr,
    ctx: &mut UnboxingContext,
) -> Option<(IRType, IRExpr)> {
    if let IRExpr::Apply { fn_id, args } = value {
        let fn_name = format!("{}", fn_id.0);
        if let Some(result_ty) = classify_arithmetic(&fn_name) {
            let unboxed_args = try_unbox_args(args, ctx);
            if let Some(new_args) = unboxed_args {
                ctx.stats.arithmetic_unboxed += 1;
                return Some((
                    result_ty,
                    IRExpr::Apply {
                        fn_id: fn_id.clone(),
                        args: new_args,
                    },
                ));
            }
        }
    }
    None
}

/// Try to replace a boxed comparison call with a direct unboxed operation.
fn try_unbox_comparison(
    _ty: &IRType,
    value: &IRExpr,
    ctx: &mut UnboxingContext,
) -> Option<(IRType, IRExpr)> {
    if let IRExpr::Apply { fn_id, args } = value {
        let fn_name = format!("{}", fn_id.0);
        if classify_comparison(&fn_name) {
            let unboxed_args = try_unbox_args(args, ctx);
            if let Some(new_args) = unboxed_args {
                ctx.stats.comparisons_unboxed += 1;
                return Some((
                    IRType::UInt8,
                    IRExpr::Apply {
                        fn_id: fn_id.clone(),
                        args: new_args,
                    },
                ));
            }
        }
    }
    None
}

/// Try to unwrap boxed arguments: for each `box(x)` argument, return `x`.
///
/// Returns `None` if any non-erased argument is not a boxed scalar.
fn try_unbox_args(args: &[IRArg], ctx: &UnboxingContext) -> Option<Vec<IRArg>> {
    let mut result = Vec::with_capacity(args.len());
    for arg in args {
        match arg {
            IRArg::Var(v) => {
                if let Some(IRExpr::Box { arg: inner, .. }) = ctx.get_def(*v) {
                    result.push(inner.clone());
                } else {
                    return None;
                }
            }
            IRArg::Erased => {
                result.push(IRArg::Erased);
            }
        }
    }
    Some(result)
}

/// Type flow optimization: correct literal types declared as Object.
fn try_type_flow_optimization(ty: &IRType, value: &IRExpr) -> Option<(IRType, IRExpr)> {
    if *ty == IRType::Object {
        if let IRExpr::Lit(lit) = value {
            let actual_ty = literal_type(lit);
            return Some((actual_ty, value.clone()));
        }
    }
    None
}

/// Determine the concrete IRType of a literal value.
pub(super) fn literal_type(lit: &IRLiteral) -> IRType {
    match lit {
        IRLiteral::Bool(_) => IRType::Bool,
        IRLiteral::UInt8(_) => IRType::UInt8,
        IRLiteral::UInt16(_) => IRType::UInt16,
        IRLiteral::UInt32(_) => IRType::UInt32,
        IRLiteral::UInt64(_) => IRType::UInt64,
        IRLiteral::USize(_) => IRType::USize,
        IRLiteral::NatBig(_) => IRType::Object,
        IRLiteral::Float32(_) => IRType::Float32,
        IRLiteral::Float64(_) => IRType::Float64,
    }
}
