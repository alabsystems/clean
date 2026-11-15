// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! The shared batched beta step for an already exposed lambda telescope.

use crate::expr::{Expr, ExprKind};

/// Consume only the literal lambdas at `function`'s head, substituting all
/// matched arguments in one existing capture-avoiding instantiation. This
/// performs no head reduction, environment lookup, or new computation rule.
/// Unconsumed arguments remain applications, in their original order.
pub(super) fn apply_lambdas(function: &Expr, args: &[&Expr]) -> Expr {
    let mut body = function;
    let mut consumed = 0;
    while consumed < args.len() {
        let ExprKind::Lam(_, _, inner) = &body.kind else {
            break;
        };
        body = inner;
        consumed += 1;
    }
    let mut result = if consumed == 0 {
        function.clone()
    } else {
        // The last consumed lambda is BVar(0); the first is BVar(m - 1).
        let values: smallvec::SmallVec<[Expr; 8]> = args[..consumed]
            .iter()
            .rev()
            .map(|arg| (**arg).clone())
            .collect();
        body.instantiate_rev(&values)
    };
    for arg in &args[consumed..] {
        result = Expr::app(result, (**arg).clone());
    }
    result
}
