// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Literal, argument, and parameter conversion for L5CNF → L5IR.

use super::state::ToIRState;
use super::types::expr_to_ir_type;
use crate::error::CompilerError;
use crate::ir::{IRArg, IRLiteral, IRType, VarId};
use crate::lcnf::{Arg, Param};
use clean_kernel::Literal;

/// Convert an L5CNF Literal to IR literal and type.
pub(super) fn lower_literal(lit: &Literal) -> Result<(IRLiteral, IRType), CompilerError> {
    match lit {
        Literal::Nat(n) => {
            // Small nats can use tagged representation
            if let Some(value) = n.to_u64() {
                if value < u32::MAX as u64 {
                    Ok((IRLiteral::USize(value as usize), IRType::USize))
                } else {
                    Ok((IRLiteral::UInt64(value), IRType::UInt64))
                }
            } else {
                // A `Nat` literal that does not fit u64 (e.g. `UInt64.size = 2^64`).
                // RUNG B: values in [2^64, 2^128) fit two little-endian u64 limbs
                // and lower to a heap Nat cell; anything wider fails closed (never
                // truncated to a wrong value).
                let limbs = n.limbs();
                let lo = limbs.first().copied().unwrap_or(0);
                let hi = limbs.get(1).copied().unwrap_or(0);
                let fits_u128 = limbs.iter().skip(2).all(|&l| l == 0);
                if fits_u128 {
                    let v = ((hi as u128) << 64) | (lo as u128);
                    Ok((IRLiteral::NatBig(v), IRType::Object))
                } else {
                    Err(CompilerError::UnsupportedLiteral { kind: "Nat" })
                }
            }
        }
        Literal::String(_) => Err(CompilerError::UnsupportedLiteral { kind: "String" }),
    }
}

/// Convert an L5CNF Arg to IR argument.
pub(super) fn lower_arg(arg: &Arg, state: &ToIRState) -> Result<IRArg, CompilerError> {
    match arg {
        Arg::FVar(fvar) => state.get_var(*fvar),
        Arg::Erased => Ok(IRArg::Erased),
        Arg::Type(_) => Ok(IRArg::Erased), // Type arguments are erased at runtime
        Arg::Index(_) => Ok(IRArg::Erased), // Index literals handled specially in _set lowering
    }
}

/// Convert a list of L5CNF Args to IR arguments.
pub(super) fn lower_args(args: &[Arg], state: &ToIRState) -> Result<Vec<IRArg>, CompilerError> {
    args.iter().map(|a| lower_arg(a, state)).collect()
}

/// Convert constructor arguments, filtering erased entries.
///
/// Constructor args in LCNF may include `Arg::Type` or `Arg::Erased` for type
/// parameters that are erased at runtime. The IR-level `Ctor`/`Reuse` args
/// should only contain runtime fields. Part of #1965.
pub(super) fn lower_ctor_args(
    args: &[Arg],
    state: &ToIRState,
) -> Result<Vec<IRArg>, CompilerError> {
    let ir_args = args
        .iter()
        .map(|a| lower_arg(a, state))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ir_args
        .into_iter()
        .filter(|a| !matches!(a, IRArg::Erased))
        .collect())
}

/// Convert an L5CNF Param to IR parameter.
pub(super) fn lower_param(
    param: &Param,
    state: &mut ToIRState,
) -> Result<(VarId, IRType), CompilerError> {
    let var_id = state.bind_var(param.fvar_id);
    let ty = expr_to_ir_type(&param.ty)?;

    // Mark erased params
    if ty == IRType::Erased || ty == IRType::Void {
        state.bind_erased(param.fvar_id);
    }

    // Track param types for _sset scalar type inference. Part of #2123.
    state.record_var_type(var_id, ty.clone());

    Ok((var_id, ty))
}
