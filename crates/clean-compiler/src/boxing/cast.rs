// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cast and box utility functions for the boxing pass.

use crate::ir::{eqv_types, IRArg, IRBody, IRExpr, IRType, VarId};

use super::context::BoxingContext;

fn warn_scalar_scalar_mismatch(ctx: &BoxingContext<'_>, actual: &IRType, expected: &IRType) {
    if actual != expected {
        ctx.warnings.borrow_mut().push(format!(
            "unsupported scalar-scalar cast from {:?} to {:?}",
            actual, expected
        ));
    }
}

pub fn mk_cast(var: VarId, var_type: &IRType, expected: &IRType) -> IRExpr {
    if expected.is_scalar() {
        IRExpr::Unbox {
            ty: expected.clone(),
            arg: IRArg::Var(var),
        }
    } else {
        IRExpr::Box {
            ty: var_type.clone(),
            arg: IRArg::Var(var),
        }
    }
}

/// Make a cast expression, potentially using expensive_constant_boxing optimization.
pub(crate) fn mk_cast_optimized(
    var: VarId,
    var_type: &IRType,
    expected: &IRType,
    ctx: &mut BoxingContext<'_>,
) -> IRExpr {
    if expected.is_scalar() {
        IRExpr::Unbox {
            ty: expected.clone(),
            arg: IRArg::Var(var),
        }
    } else {
        // Try expensive constant boxing optimization if enabled
        if ctx.config.optimize_expensive_constants {
            if let Some(aux_call) = BoxingContext::expensive_constant_boxing(var, var_type, ctx) {
                return aux_call;
            }
        }
        IRExpr::Box {
            ty: var_type.clone(),
            arg: IRArg::Var(var),
        }
    }
}

pub fn cast_var_if_needed<F>(
    var: VarId,
    expected: &IRType,
    ctx: &mut BoxingContext<'_>,
    k: F,
) -> IRBody
where
    F: FnOnce(VarId) -> IRBody,
{
    let var_type = ctx.get_var_type(var);
    if eqv_types(&var_type, expected) {
        k(var)
    } else if var_type.is_scalar() && expected.is_scalar() {
        warn_scalar_scalar_mismatch(ctx, &var_type, expected);
        k(var)
    } else {
        let fresh = ctx.mk_fresh_var();
        ctx.set_var_type(fresh, expected.clone());
        let cast = mk_cast_optimized(var, &var_type, expected, ctx);
        IRBody::VDecl {
            var: fresh,
            ty: expected.clone(),
            value: cast,
            rest: Box::new(k(fresh)),
        }
    }
}

pub fn cast_arg_if_needed<F>(
    arg: &IRArg,
    expected: &IRType,
    ctx: &mut BoxingContext<'_>,
    k: F,
) -> IRBody
where
    F: FnOnce(IRArg) -> IRBody,
{
    match arg {
        IRArg::Var(var) => cast_var_if_needed(*var, expected, ctx, |v| k(IRArg::Var(v))),
        IRArg::Erased => k(IRArg::Erased),
    }
}

pub fn cast_args(
    args: &[IRArg],
    param_types: &[IRType],
    ctx: &mut BoxingContext<'_>,
) -> (Vec<IRArg>, Vec<(VarId, IRType, IRExpr)>) {
    let mut cast_args = Vec::with_capacity(args.len());
    let mut prefix = Vec::new();
    for (i, arg) in args.iter().enumerate() {
        let expected = param_types.get(i).cloned().unwrap_or(IRType::Object);
        match arg {
            IRArg::Var(var) => {
                let var_type = ctx.get_var_type(*var);
                if eqv_types(&var_type, &expected) {
                    cast_args.push(IRArg::Var(*var));
                } else if var_type.is_scalar() && expected.is_scalar() {
                    warn_scalar_scalar_mismatch(ctx, &var_type, &expected);
                    cast_args.push(IRArg::Var(*var));
                } else {
                    let fresh = ctx.mk_fresh_var();
                    ctx.set_var_type(fresh, expected.clone());
                    let cast = mk_cast_optimized(*var, &var_type, &expected, ctx);
                    prefix.push((fresh, expected, cast));
                    cast_args.push(IRArg::Var(fresh));
                }
            }
            IRArg::Erased => {
                cast_args.push(IRArg::Erased);
            }
        }
    }
    (cast_args, prefix)
}

pub fn wrap_with_prefix(prefix: Vec<(VarId, IRType, IRExpr)>, body: IRBody) -> IRBody {
    prefix
        .into_iter()
        .rev()
        .fold(body, |rest, (var, ty, value)| IRBody::VDecl {
            var,
            ty,
            value,
            rest: Box::new(rest),
        })
}

pub fn box_args(
    args: &[IRArg],
    ctx: &mut BoxingContext<'_>,
) -> (Vec<IRArg>, Vec<(VarId, IRType, IRExpr)>) {
    let obj_types: Vec<_> = args.iter().map(|_| IRType::Object).collect();
    cast_args(args, &obj_types, ctx)
}
