// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Argument readers shared by the pseudo-op lowerings: each one reads one
//! argument of a pseudo-op application in the shape the lowering needs, and
//! refuses any other shape as a malformed pseudo-op.

use super::super::state::ToIRState;
use crate::error::CompilerError;
use crate::ir::{IRArg, VarId};
use crate::lcnf::Arg;
use clean_kernel::{Expr, ExprKind, FVarId, Name};

pub(super) fn expect_fvar_arg(
    args: &[Arg],
    index: usize,
    op: &Name,
    detail: &'static str,
) -> Result<FVarId, CompilerError> {
    match args.get(index) {
        Some(Arg::FVar(fvar)) => Ok(*fvar),
        _ => Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail,
        }),
    }
}

pub(super) fn expect_index_arg(
    args: &[Arg],
    index: usize,
    op: &Name,
    detail: &'static str,
) -> Result<u32, CompilerError> {
    match args.get(index) {
        Some(Arg::Index(idx)) => Ok(*idx),
        _ => Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail,
        }),
    }
}

pub(super) fn expect_ctor_name_arg(
    args: &[Arg],
    index: usize,
    op: &Name,
) -> Result<Name, CompilerError> {
    let Some(Arg::Type(expr)) = args.get(index) else {
        return Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail: "expected constructor type argument",
        });
    };
    ctor_name_from_expr(expr).ok_or_else(|| CompilerError::MalformedPseudoOp {
        op: op.clone(),
        detail: "constructor type argument must be a constant head",
    })
}

fn ctor_name_from_expr(expr: &Expr) -> Option<Name> {
    match expr.strip_mdata().get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

pub(super) fn require_runtime_var(
    state: &ToIRState,
    fvar: FVarId,
    op: &Name,
    detail: &'static str,
) -> Result<VarId, CompilerError> {
    match state.get_var(fvar)? {
        IRArg::Var(var) => Ok(var),
        IRArg::Erased => Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail,
        }),
    }
}
