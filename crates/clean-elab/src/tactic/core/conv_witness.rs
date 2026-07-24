// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::Expr;

/// Explicit equality witness produced by a focused `conv` body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConvFocusWitness {
    /// Original focused expression before the body rewrite.
    pub(crate) before: Expr,
    /// Final focused expression after the body rewrite.
    pub(crate) after: Expr,
    /// Proof term witnessing `before = after`.
    pub(crate) eq_proof: Expr,
}
