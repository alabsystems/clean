// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Evaluator for native type expressions.
//!
//! Takes a `NativeExpr` tree (produced by `compile_to_native`) and evaluates
//! it to a concrete `NativeValue`. All arithmetic wraps on overflow (matching
//! Lean 4 semantics for UInt), Float operations use IEEE 754, and division
//! by zero returns 0 for integers / NaN for floats.
//!
//! Part of #3084 - Native type compilation for UInt and Float.

use crate::native_types::{NativeExpr, NativeOp, NativeType};
use thiserror::Error;

// ---------------------------------------------------------------------------
// NativeValue
// ---------------------------------------------------------------------------

/// A concrete machine-level value.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum NativeValue {
    UInt8(u8),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    USize(u64),
    Float(f64),
    Bool(bool),
}

impl NativeValue {
    /// Extract as `u64`, widening smaller integer types.
    fn as_u64(&self) -> Option<u64> {
        match self {
            Self::UInt8(v) => Some(u64::from(*v)),
            Self::UInt16(v) => Some(u64::from(*v)),
            Self::UInt32(v) => Some(u64::from(*v)),
            Self::UInt64(v) | Self::USize(v) => Some(*v),
            Self::Bool(b) => Some(u64::from(*b)),
            Self::Float(_) => None,
        }
    }

    /// Extract as `f64`.
    fn as_f64(&self) -> Option<f64> {
        match self {
            Self::Float(v) => Some(*v),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// NativeEvalError
// ---------------------------------------------------------------------------

/// Errors during native expression evaluation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum NativeEvalError {
    /// Unresolved variable reference.
    #[error("unresolved variable: {0}")]
    UnresolvedVariable(String),

    /// Unresolved function call.
    #[error("unresolved call: {0}")]
    UnresolvedCall(String),

    /// Type mismatch in operation.
    #[error("type mismatch: cannot apply {op:?} to operands")]
    TypeMismatch { op: NativeOp },

    /// Operation not supported for the given type.
    #[error("unsupported operation {op:?} for type")]
    UnsupportedOp { op: NativeOp },
}

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------

/// Wrap a `u64` result to fit a target `NativeType`.
fn wrap_uint(val: u64, ty: NativeType) -> NativeValue {
    match ty {
        NativeType::UInt8 => NativeValue::UInt8(val as u8),
        NativeType::UInt16 => NativeValue::UInt16(val as u16),
        NativeType::UInt32 => NativeValue::UInt32(val as u32),
        NativeType::UInt64 => NativeValue::UInt64(val),
        NativeType::USize => NativeValue::USize(val),
        NativeType::Bool => NativeValue::Bool(val != 0),
        NativeType::Float => NativeValue::Float(val as f64),
    }
}

/// Determine the "result type" for a binary operation given the two operand types.
///
/// For comparisons the result is always `Bool`. For arithmetic/bitwise,
/// both operands should be the same type and the result is that type.
fn result_type_for_binop(op: NativeOp, lhs_ty: NativeType, _rhs_ty: NativeType) -> NativeType {
    match op {
        NativeOp::Eq | NativeOp::Ne | NativeOp::Lt | NativeOp::Le | NativeOp::Gt | NativeOp::Ge => {
            NativeType::Bool
        }
        _ => lhs_ty,
    }
}

/// Infer the `NativeType` of a `NativeValue`.
fn value_type(val: &NativeValue) -> NativeType {
    match val {
        NativeValue::UInt8(_) => NativeType::UInt8,
        NativeValue::UInt16(_) => NativeType::UInt16,
        NativeValue::UInt32(_) => NativeType::UInt32,
        NativeValue::UInt64(_) => NativeType::UInt64,
        NativeValue::USize(_) => NativeType::USize,
        NativeValue::Float(_) => NativeType::Float,
        NativeValue::Bool(_) => NativeType::Bool,
    }
}

/// Evaluate an integer binary operation on `u64` operands and wrap to `out_ty`.
fn eval_int_binop(
    op: NativeOp,
    a: u64,
    b: u64,
    out_ty: NativeType,
) -> Result<NativeValue, NativeEvalError> {
    let result = match op {
        NativeOp::Add => a.wrapping_add(b),
        NativeOp::Sub => a.wrapping_sub(b),
        NativeOp::Mul => a.wrapping_mul(b),
        NativeOp::Div => a.checked_div(b).unwrap_or(0),
        NativeOp::Mod => {
            if b == 0 {
                a
            } else {
                a % b
            }
        }
        NativeOp::And => a & b,
        NativeOp::Or => a | b,
        NativeOp::Xor => a ^ b,
        NativeOp::ShiftLeft => {
            let bits = out_ty.bit_width().unwrap_or(64);
            if b >= u64::from(bits) {
                0
            } else {
                a.wrapping_shl(b as u32)
            }
        }
        NativeOp::ShiftRight => {
            let bits = out_ty.bit_width().unwrap_or(64);
            if b >= u64::from(bits) {
                0
            } else {
                a >> b
            }
        }
        // Comparisons return a boolean wrapped into out_ty (which is Bool)
        NativeOp::Eq => return Ok(NativeValue::Bool(a == b)),
        NativeOp::Ne => return Ok(NativeValue::Bool(a != b)),
        NativeOp::Lt => return Ok(NativeValue::Bool(a < b)),
        NativeOp::Le => return Ok(NativeValue::Bool(a <= b)),
        NativeOp::Gt => return Ok(NativeValue::Bool(a > b)),
        NativeOp::Ge => return Ok(NativeValue::Bool(a >= b)),

        _ => return Err(NativeEvalError::UnsupportedOp { op }),
    };

    // Apply modulus for small types
    let wrapped = match out_ty.modulus() {
        Some(m) => result % m,
        None => result,
    };
    Ok(wrap_uint(wrapped, out_ty))
}

/// Evaluate a float binary operation.
fn eval_float_binop(op: NativeOp, a: f64, b: f64) -> Result<NativeValue, NativeEvalError> {
    match op {
        NativeOp::Add => Ok(NativeValue::Float(a + b)),
        NativeOp::Sub => Ok(NativeValue::Float(a - b)),
        NativeOp::Mul => Ok(NativeValue::Float(a * b)),
        NativeOp::Div => Ok(NativeValue::Float(a / b)), // IEEE 754: div-by-zero -> Inf/NaN
        NativeOp::Mod => Ok(NativeValue::Float(a % b)),
        NativeOp::Eq => Ok(NativeValue::Bool(a == b)),
        NativeOp::Ne => Ok(NativeValue::Bool(a != b)),
        NativeOp::Lt => Ok(NativeValue::Bool(a < b)),
        NativeOp::Le => Ok(NativeValue::Bool(a <= b)),
        NativeOp::Gt => Ok(NativeValue::Bool(a > b)),
        NativeOp::Ge => Ok(NativeValue::Bool(a >= b)),
        _ => Err(NativeEvalError::UnsupportedOp { op }),
    }
}

/// Evaluate a literal to a `NativeValue`.
fn eval_lit(ty: NativeType, bits: u64) -> NativeValue {
    match ty {
        NativeType::UInt8 => NativeValue::UInt8(bits as u8),
        NativeType::UInt16 => NativeValue::UInt16(bits as u16),
        NativeType::UInt32 => NativeValue::UInt32(bits as u32),
        NativeType::UInt64 => NativeValue::UInt64(bits),
        NativeType::USize => NativeValue::USize(bits),
        NativeType::Float => NativeValue::Float(f64::from_bits(bits)),
        NativeType::Bool => NativeValue::Bool(bits != 0),
    }
}

/// Evaluate a binary operation on two already-evaluated operands.
fn eval_binop(
    op: NativeOp,
    lv: NativeValue,
    rv: NativeValue,
) -> Result<NativeValue, NativeEvalError> {
    let lt = value_type(&lv);
    let rt = value_type(&rv);
    let out_ty = result_type_for_binop(op, lt, rt);

    // Float path
    if let (Some(a), Some(b)) = (lv.as_f64(), rv.as_f64()) {
        return eval_float_binop(op, a, b);
    }

    // Integer path
    let a = lv.as_u64().ok_or(NativeEvalError::TypeMismatch { op })?;
    let b = rv.as_u64().ok_or(NativeEvalError::TypeMismatch { op })?;
    eval_int_binop(op, a, b, out_ty)
}

/// Evaluate a unary operation on an already-evaluated operand.
fn eval_unaryop(op: NativeOp, val: NativeValue) -> Result<NativeValue, NativeEvalError> {
    match op {
        NativeOp::Complement => {
            let ty = value_type(&val);
            let v = val.as_u64().ok_or(NativeEvalError::TypeMismatch { op })?;
            let masked = match ty.modulus() {
                Some(m) => (!v) & (m - 1),
                None => !v,
            };
            Ok(wrap_uint(masked, ty))
        }
        NativeOp::ToNat | NativeOp::FromNat => {
            let v = val.as_u64().ok_or(NativeEvalError::TypeMismatch { op })?;
            Ok(NativeValue::UInt64(v))
        }
        NativeOp::ToFloat => {
            let v = val.as_u64().ok_or(NativeEvalError::TypeMismatch { op })?;
            Ok(NativeValue::Float(v as f64))
        }
        NativeOp::FromFloat => {
            let v = val.as_f64().ok_or(NativeEvalError::TypeMismatch { op })?;
            Ok(NativeValue::UInt64(v as u64))
        }
        _ => Err(NativeEvalError::UnsupportedOp { op }),
    }
}

/// Evaluate a `NativeExpr` to a concrete `NativeValue`.
///
/// Returns an error for unresolved variables/calls or type mismatches.
pub fn eval_native(expr: &NativeExpr) -> Result<NativeValue, NativeEvalError> {
    match expr {
        NativeExpr::Lit(ty, bits) => Ok(eval_lit(*ty, *bits)),
        NativeExpr::BinOp(op, lhs, rhs) => eval_binop(*op, eval_native(lhs)?, eval_native(rhs)?),
        NativeExpr::UnaryOp(op, operand) => eval_unaryop(*op, eval_native(operand)?),
        NativeExpr::Var(name) => Err(NativeEvalError::UnresolvedVariable(name.clone())),
        NativeExpr::Call(name, _) => Err(NativeEvalError::UnresolvedCall(name.clone())),
    }
}

#[cfg(test)]
#[path = "native_eval_tests.rs"]
mod tests;
