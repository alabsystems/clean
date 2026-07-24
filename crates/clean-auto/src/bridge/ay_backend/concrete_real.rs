// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete constructor-form extraction for Real/Int kernel expressions (#2794).
//!
//! Provides helpers to decompose `Real.ofNat(NatLit(n))`, `Real.ofInt(Int.ofNat(n))`,
//! and `Real.ofInt(Int.negSucc(n))` into exact integer values. Used by the native
//! ay translator to produce Real-sorted terms from elaborated constructor forms.

use clean_kernel::expr::Literal;
use clean_kernel::{Expr, ExprKind};

/// Extract a concrete Nat value from a literal expression.
///
/// Returns `None` for non-literal or non-Nat expressions.
pub(crate) fn try_extract_concrete_nat(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Check if an expression is a concrete Real divisor suitable for strict QF_LRA.
///
/// Accepts only exact constant forms that preserve the linear arithmetic
/// contract: Nat literals, `Real.ofNat n`, and `Real.ofInt i` with concrete
/// arguments. Symbolic denominators are rejected to prevent silent nonlinear
/// widening. Part of #2795.
pub(crate) fn is_concrete_real_divisor(expr: &Expr) -> bool {
    // Direct Nat literal
    if try_extract_concrete_nat(expr).is_some() {
        return true;
    }
    // Constructor-form Real: Real.ofNat n or Real.ofInt i
    if let ExprKind::App(f, a) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            match name.to_string().as_str() {
                "Real.ofNat" => return try_extract_concrete_nat(a).is_some(),
                "Real.ofInt" => return try_extract_concrete_int(a).is_some(),
                _ => {}
            }
        }
    }
    false
}

/// Extract a concrete Int value from an Int constructor expression.
///
/// Recognized forms:
/// - `NatLit(n)` → `n` (non-negative)
/// - `Int.ofNat(NatLit(n))` → `n`
/// - `Int.negSucc(NatLit(n))` → `-(n+1)`
///
/// Returns `None` for non-concrete or unrecognized forms.
pub(crate) fn try_extract_concrete_int(expr: &Expr) -> Option<i64> {
    // Direct Nat literal (non-negative)
    if let ExprKind::Lit(Literal::Nat(n)) = expr.kind() {
        return n.to_u64().and_then(|v| i64::try_from(v).ok());
    }
    // Int constructor forms
    if let ExprKind::App(f, a) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            let name_str = name.to_string();
            match name_str.as_str() {
                "Int.ofNat" => {
                    return try_extract_concrete_nat(a).and_then(|n| i64::try_from(n).ok());
                }
                "Int.negSucc" => {
                    return try_extract_concrete_nat(a).and_then(|n| {
                        i64::try_from(n)
                            .ok()
                            .and_then(|n| n.checked_add(1).map(|v| -v))
                    });
                }
                _ => {}
            }
        }
    }
    None
}
