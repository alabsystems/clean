// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean_kernel::Expr;

use super::super::expr_builders_arith::{self, CmpOp};
use super::{exprs_syntactically_equal, extract_int_literal, mk_int_cancel_add_right, IntAddNf};

/// Close a concrete contradiction after directly cancelling identical raw
/// `Int.add` right suffixes.
///
/// A common solver shape is a pair of left-associated sums such as
/// `(((4 + x) + y) + z) <= (((3 + x) + y) + z)`. Reassociating both complete
/// trees into additive normal form builds a much larger equality-transport
/// proof than necessary. Instead, the kernel cancellation lemma can remove
/// `z`, `y`, and `x` directly, leaving the concrete `4 <= 3` contradiction.
///
/// This fast path is deliberately narrow and fail-closed:
///
/// - only raw `Int.add` applications are peeled (not overloaded aliases);
/// - each right operand must be syntactically identical on both sides;
/// - at least one suffix must be cancelled; and
/// - both residual endpoints must be concrete literals whose comparison is
///   contradictory.
///
/// Any mismatch returns `None`, so the caller falls back to the general
/// normalization/transport path.
pub(super) fn try_close_identical_raw_add_suffix(
    op: CmpOp,
    acc_lhs: &Expr,
    acc_rhs: &Expr,
    acc_proof: &Expr,
) -> Option<Expr> {
    let mut lhs = acc_lhs.clone();
    let mut rhs = acc_rhs.clone();
    let mut proof = acc_proof.clone();
    let mut cancelled = false;

    loop {
        let next = match (
            IntAddNf::as_raw_int_add(&lhs),
            IntAddNf::as_raw_int_add(&rhs),
        ) {
            (Some((lhs_prefix, lhs_suffix)), Some((rhs_prefix, rhs_suffix)))
                if exprs_syntactically_equal(lhs_suffix, rhs_suffix) =>
            {
                Some((lhs_prefix.clone(), rhs_prefix.clone(), lhs_suffix.clone()))
            }
            _ => None,
        };
        let Some((lhs_prefix, rhs_prefix, shared_suffix)) = next else {
            break;
        };

        proof = mk_int_cancel_add_right(op, &lhs_prefix, &shared_suffix, &rhs_prefix, &proof);
        lhs = lhs_prefix;
        rhs = rhs_prefix;
        cancelled = true;
    }

    if !cancelled {
        return None;
    }

    let lhs_value = extract_int_literal(&lhs)?;
    let rhs_value = extract_int_literal(&rhs)?;
    let contradictory = match op {
        CmpOp::Le => lhs_value > rhs_value,
        CmpOp::Lt => lhs_value >= rhs_value,
    };
    if !contradictory {
        return None;
    }

    Some(expr_builders_arith::mk_int_concrete_false(
        op, &lhs, &rhs, &proof,
    ))
}
