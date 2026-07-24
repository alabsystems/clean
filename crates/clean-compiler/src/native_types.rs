// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native type IR for compiling kernel-level numeric operations to
//! efficient machine operations.
//!
//! This module provides a lowered representation (`NativeExpr`) for
//! expressions that operate on fixed-width integer and floating-point
//! types. The `compile_to_native` function detects when a kernel `Expr`
//! tree represents a native operation and lowers it to this IR, enabling
//! direct evaluation without kernel reduction overhead.
//!
//! Part of #3084 - Native type compilation for UInt and Float.

use clean_kernel::expr::{Expr, ExprKind, Literal};
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// NativeType
// ---------------------------------------------------------------------------

/// Machine-level numeric types that can be evaluated natively.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NativeType {
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    USize,
    Float,
    Bool,
}

impl NativeType {
    /// The modulus for wrapping arithmetic, or `None` for non-integer types.
    #[must_use]
    pub fn modulus(self) -> Option<u64> {
        match self {
            Self::UInt8 => Some(1u64 << 8),
            Self::UInt16 => Some(1u64 << 16),
            Self::UInt32 => Some(1u64 << 32),
            // UInt64 and USize wrap at 2^64 (handled by Rust's wrapping ops).
            Self::UInt64 | Self::USize => None,
            Self::Float | Self::Bool => None,
        }
    }

    /// Bit width of the integer type, or `None` for Float/Bool.
    #[must_use]
    pub fn bit_width(self) -> Option<u32> {
        match self {
            Self::UInt8 => Some(8),
            Self::UInt16 => Some(16),
            Self::UInt32 => Some(32),
            Self::UInt64 | Self::USize => Some(64),
            Self::Float => Some(64),
            Self::Bool => None,
        }
    }
}

// ---------------------------------------------------------------------------
// NativeOp
// ---------------------------------------------------------------------------

/// Machine-level operations on native numeric types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NativeOp {
    // Arithmetic (binary)
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison (binary, result is Bool)
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Bitwise (binary, except Complement which is unary)
    And,
    Or,
    Xor,
    ShiftLeft,
    ShiftRight,
    Complement,

    // Conversion (unary)
    ToNat,
    FromNat,
    ToFloat,
    FromFloat,
}

// ---------------------------------------------------------------------------
// NativeExpr
// ---------------------------------------------------------------------------

/// A lowered expression tree over native numeric types.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum NativeExpr {
    /// Literal value. For integer types the bits are stored in `u64`;
    /// for `Float` the bits are an IEEE 754 double via `f64::to_bits`.
    Lit(NativeType, u64),

    /// Binary operation.
    BinOp(NativeOp, Box<NativeExpr>, Box<NativeExpr>),

    /// Unary operation (Complement, ToNat, FromNat, ToFloat, FromFloat).
    UnaryOp(NativeOp, Box<NativeExpr>),

    /// Variable reference (by name).
    Var(String),

    /// Function/operation call.
    Call(String, Vec<NativeExpr>),
}

// ---------------------------------------------------------------------------
// Name-matching helpers
// ---------------------------------------------------------------------------

/// Try to parse a Lean 4 UInt/Float operation name into (NativeType, NativeOp).
///
/// Returns `None` for names that are not native numeric operations.
fn classify_native_op(name: &Name) -> Option<(NativeType, NativeOp)> {
    let s = name.to_string();

    // Determine type prefix and strip it
    let (ty, suffix) = if let Some(rest) = s.strip_prefix("UInt8.") {
        (NativeType::UInt8, rest)
    } else if let Some(rest) = s.strip_prefix("UInt16.") {
        (NativeType::UInt16, rest)
    } else if let Some(rest) = s.strip_prefix("UInt32.") {
        (NativeType::UInt32, rest)
    } else if let Some(rest) = s.strip_prefix("UInt64.") {
        (NativeType::UInt64, rest)
    } else if let Some(rest) = s.strip_prefix("USize.") {
        (NativeType::USize, rest)
    } else {
        let rest = s.strip_prefix("Float.")?;
        (NativeType::Float, rest)
    };

    let op = match suffix {
        "add" => NativeOp::Add,
        "sub" => NativeOp::Sub,
        "mul" => NativeOp::Mul,
        "div" => NativeOp::Div,
        "mod" => NativeOp::Mod,
        "beq" => NativeOp::Eq,
        "blt" => NativeOp::Lt,
        "ble" => NativeOp::Le,
        "land" => NativeOp::And,
        "lor" => NativeOp::Or,
        "xor" => NativeOp::Xor,
        "shiftLeft" => NativeOp::ShiftLeft,
        "shiftRight" => NativeOp::ShiftRight,
        "complement" => NativeOp::Complement,
        "toNat" => NativeOp::ToNat,
        _ => return None,
    };

    Some((ty, op))
}

/// Check whether an operation is unary (takes one operand).
fn is_unary(op: NativeOp) -> bool {
    matches!(
        op,
        NativeOp::Complement
            | NativeOp::ToNat
            | NativeOp::FromNat
            | NativeOp::ToFloat
            | NativeOp::FromFloat
    )
}

// ---------------------------------------------------------------------------
// compile_to_native
// ---------------------------------------------------------------------------

/// Extract a `u64` from a Nat literal expression.
fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Attempt to compile a kernel `Expr` tree into a `NativeExpr`.
///
/// Succeeds when the expression head is a recognized native numeric
/// operation (e.g. `UInt32.add`) applied to literal or recursively
/// compilable arguments.
///
/// Returns `None` for expressions that cannot be lowered to native ops.
#[must_use]
pub fn compile_to_native(expr: &Expr) -> Option<NativeExpr> {
    // Check for literal Nat — treat as UInt64 literal
    if let Some(val) = get_nat_val(expr) {
        return Some(NativeExpr::Lit(NativeType::UInt64, val));
    }

    // Decompose application spine
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    let name = match head.kind() {
        ExprKind::Const(name, _) => name,
        _ => return None,
    };

    let (_ty, op) = classify_native_op(name)?;

    if is_unary(op) {
        if args.is_empty() {
            return None;
        }
        let operand = compile_to_native(args.last()?)?;
        Some(NativeExpr::UnaryOp(op, Box::new(operand)))
    } else {
        // Binary operation — needs at least 2 args
        if args.len() < 2 {
            return None;
        }
        let lhs = compile_to_native(args[args.len() - 2])?;
        let rhs = compile_to_native(args[args.len() - 1])?;
        Some(NativeExpr::BinOp(op, Box::new(lhs), Box::new(rhs)))
    }
}

#[cfg(test)]
#[path = "native_types_tests.rs"]
mod tests;
