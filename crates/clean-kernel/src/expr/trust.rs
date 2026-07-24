// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust recognizers on expressions.

use super::sorry::push_expr_children;
use super::{Expr, ExprKind};
use crate::name::Name;

impl Expr {
    /// Scan the expression tree for trust-bearing terms in a single pass.
    ///
    /// Returns `(has_explicit_sorry, has_synthetic_sorry, trusted_arith_count,
    /// trusted_ay_count)`.
    pub(crate) fn trust_scan(&self) -> (bool, bool, usize, usize) {
        let trusted_arith_name = Name::from_string("trustedArith");
        let trusted_ay_name = Name::from_string("trustedAy");
        let mut has_explicit_sorry = false;
        let mut has_synthetic_sorry = false;
        let mut trusted_arith_count = 0;
        let mut trusted_ay_count = 0;
        let mut stack = vec![self];

        while let Some(curr) = stack.pop() {
            has_explicit_sorry |= curr.is_non_synthetic_sorry();
            has_synthetic_sorry |= curr.is_synthetic_sorry();

            if let ExprKind::Const(name, _) = curr.kind() {
                if *name == trusted_arith_name {
                    trusted_arith_count += 1;
                } else if *name == trusted_ay_name {
                    trusted_ay_count += 1;
                }
            }

            push_expr_children(&mut stack, curr);
        }

        (
            has_explicit_sorry,
            has_synthetic_sorry,
            trusted_arith_count,
            trusted_ay_count,
        )
    }
}
