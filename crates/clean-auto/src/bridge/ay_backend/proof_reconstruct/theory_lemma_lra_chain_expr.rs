// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-Expr arithmetic helpers for LRA chain closing.

use clean_kernel::Expr;

use super::expr_builders_arith::{self, CmpOp};
use super::expr_builders_real_downcast::{
    extract_concrete_int_from_real_expr, extract_int_from_real_endpoint,
};
use super::real_downcast_normalize::normalize_real_cmp_proof_to_ofint;

pub(crate) fn extract_concrete_int_from_kernel_expr(expr: &Expr) -> Option<num_bigint::BigInt> {
    expr_builders_arith::extract_concrete_int_from_expr(expr)
}

pub(crate) fn is_concrete_violation_by_kernel_expr(
    start_expr: &Expr,
    end_expr: &Expr,
    op: CmpOp,
) -> bool {
    let start = match extract_concrete_int_from_kernel_expr(start_expr) {
        Some(value) => value,
        None => return false,
    };
    let end = match extract_concrete_int_from_kernel_expr(end_expr) {
        Some(value) => value,
        None => return false,
    };
    match op {
        CmpOp::Le => start > end,
        CmpOp::Lt => start >= end,
    }
}

/// Close a Real-sort non-cyclic chain using concrete values extracted from
/// the kernel Expr patterns of the chain endpoints.
///
/// This is a fallback for cases where ay represents concrete Real numbers as
/// named variables mapped to kernel expressions like `Real.ofNat 5`. The ay
/// term-level extraction fails (the term is a Var, not a Constant), but the
/// underlying kernel Expr IS concrete.
///
/// Dispatches to the `Nat.ble`-based closer for non-negative endpoints or
/// the `Real.not_ofInt_le/lt` bridge for any integer endpoints. Part of #302.
pub(crate) fn close_real_chain_by_expr(
    op: CmpOp,
    start_expr: &Expr,
    end_expr: &Expr,
    chain_proof: &Expr,
) -> Option<Expr> {
    let start_val = extract_concrete_int_from_real_expr(start_expr)?;
    let end_val = extract_concrete_int_from_real_expr(end_expr)?;
    let violated = match op {
        CmpOp::Le => start_val > end_val,
        CmpOp::Lt => start_val >= end_val,
    };
    if !violated {
        return None;
    }
    // Prefer nonneg Nat path (uses Nat.ble kernel reduction, no bridge axioms)
    if start_val.sign() != num_bigint::Sign::Minus && end_val.sign() != num_bigint::Sign::Minus {
        if let (Ok(m), Ok(n)) = (u64::try_from(&start_val), u64::try_from(&end_val)) {
            return Some(expr_builders_arith::mk_real_concrete_false(
                op,
                m,
                n,
                chain_proof,
            ));
        }
    }
    // Fall back to ofInt path (handles negative endpoints)
    let (lhs_norm, rhs_norm, normalized_chain_proof) =
        normalize_real_cmp_proof_to_ofint(op, start_expr, end_expr, chain_proof)?;
    let a_int = extract_int_from_real_endpoint(&lhs_norm)?;
    let b_int = extract_int_from_real_endpoint(&rhs_norm)?;
    Some(expr_builders_arith::mk_real_ofint_concrete_false(
        op,
        &a_int,
        &b_int,
        &normalized_chain_proof,
    ))
}

#[cfg(test)]
mod tests {
    use super::{extract_concrete_int_from_kernel_expr, is_concrete_violation_by_kernel_expr};
    use crate::bridge::ay_backend::proof_reconstruct::expr_builders_arith::CmpOp;
    use clean_kernel::name::Name;
    use clean_kernel::Expr;

    fn int_of_nat(value: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(value),
        )
    }

    fn int_neg_succ(value: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(value),
        )
    }

    fn nat_zero() -> Expr {
        Expr::const_(Name::from_string("Nat.zero"), vec![])
    }

    fn nat_succ(arg: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            arg.clone(),
        )
    }

    fn int_of_nat_ctor(arg: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            arg.clone(),
        )
    }

    fn int_neg_succ_ctor(arg: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            arg.clone(),
        )
    }

    #[test]
    fn test_extract_concrete_int_from_kernel_expr_handles_int_literals() {
        assert_eq!(
            extract_concrete_int_from_kernel_expr(&int_of_nat(5)),
            Some(num_bigint::BigInt::from(5_u64))
        );
        assert_eq!(
            extract_concrete_int_from_kernel_expr(&int_neg_succ(2)),
            Some(num_bigint::BigInt::from(-3_i64))
        );
    }

    #[test]
    fn test_extract_concrete_int_from_kernel_expr_handles_constructor_form_nats() {
        let one = nat_succ(&nat_zero());
        let two = nat_succ(&one);

        assert_eq!(
            extract_concrete_int_from_kernel_expr(&int_of_nat_ctor(&two)),
            Some(num_bigint::BigInt::from(2_u64))
        );
        assert_eq!(
            extract_concrete_int_from_kernel_expr(&int_neg_succ_ctor(&nat_zero())),
            Some(num_bigint::BigInt::from(-1_i64))
        );
    }

    #[test]
    fn test_is_concrete_violation_by_kernel_expr_detects_int_ordering_contradictions() {
        assert!(is_concrete_violation_by_kernel_expr(
            &int_of_nat(5),
            &int_of_nat(3),
            CmpOp::Le,
        ));
        assert!(is_concrete_violation_by_kernel_expr(
            &int_neg_succ(0),
            &int_neg_succ(2),
            CmpOp::Le,
        ));
        assert!(!is_concrete_violation_by_kernel_expr(
            &int_of_nat(2),
            &int_of_nat(4),
            CmpOp::Le,
        ));
        assert!(is_concrete_violation_by_kernel_expr(
            &int_of_nat(4),
            &int_of_nat(4),
            CmpOp::Lt,
        ));
    }

    #[test]
    fn test_is_concrete_violation_by_kernel_expr_handles_constructor_form_nats() {
        let zero = nat_zero();
        let one = nat_succ(&zero);

        assert!(is_concrete_violation_by_kernel_expr(
            &int_of_nat_ctor(&one),
            &int_of_nat_ctor(&zero),
            CmpOp::Le,
        ));
        assert!(is_concrete_violation_by_kernel_expr(
            &int_neg_succ_ctor(&zero),
            &int_neg_succ_ctor(&one),
            CmpOp::Le,
        ));
    }
}
