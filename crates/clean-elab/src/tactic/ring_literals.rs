// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, ExprKind};

use super::nat_expr_eval::read_nat_numeral;

/// Recognize a non-negative ring constant.
///
/// The Nat spellings come from the shared `nat_expr_eval::read_nat_numeral`
/// reader, which is what makes the `@OfNat.ofNat α k inst` form the elaborator
/// builds for a source numeral fold here. Before that (RC-H) this file carried
/// its own reader that saw only `Nat.zero` / a `Nat.succ` chain / a raw
/// `Lit(Nat)`, so `ring_normalize` mapped every source numeral to an opaque
/// `RingExpr::Unknown` atom and `ring` could not prove `0 + x = x` or
/// `1 * x = x`.
pub(crate) fn nonnegative_ring_const_value(expr: &Expr) -> Option<u64> {
    read_nat_numeral(expr).or_else(|| match expr.kind() {
        ExprKind::Const(name, _) => {
            let name = name.to_string();
            match name.as_str() {
                "Int.zero" | "Rat.zero" => Some(0),
                "Int.one" | "Rat.one" => Some(1),
                _ => None,
            }
        }
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) if name.to_string() == "Int.ofNat" => read_nat_numeral(arg),
            _ => None,
        },
        _ => None,
    })
}
