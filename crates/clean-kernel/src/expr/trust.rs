// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust recognizers on expressions.

use super::sorry::push_sorry_scan_children;
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
            // A sorry-headed spine is ONE occurrence whatever its arguments
            // (see `expr/sorry.rs`); only its literal-`true` flag makes it
            // synthetic, and every other occurrence is counted as explicit.
            if let Some(occurrence) = push_sorry_scan_children(&mut stack, curr) {
                if occurrence.is_synthetic_sorry() {
                    has_synthetic_sorry = true;
                } else {
                    has_explicit_sorry = true;
                }
                continue;
            }

            if let ExprKind::Const(name, _) = curr.kind() {
                if *name == trusted_arith_name {
                    trusted_arith_count += 1;
                } else if *name == trusted_ay_name {
                    trusted_ay_count += 1;
                }
            }
        }

        (
            has_explicit_sorry,
            has_synthetic_sorry,
            trusted_arith_count,
            trusted_ay_count,
        )
    }
}
