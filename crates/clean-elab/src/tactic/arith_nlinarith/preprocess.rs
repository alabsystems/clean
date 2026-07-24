// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, ExprKind};

use super::super::arithmetic::{expr_is_nat_lit, LinearExpr};

/// Try to compute the product of two linear expressions if they are "simple" enough.
///
/// REQUIRES: `e1` and `e2` are valid `LinearExpr` values
/// ENSURES: Returns `Some(product)` only when the result is representable as a `LinearExpr`
/// ENSURES: constant * constant → `LinearExpr::constant(e1.constant * e2.constant)`
/// ENSURES: constant * linear → exact scalar multiple when it fits in `i64`
/// ENSURES: Returns `None` for general nonlinear products (non-constant × non-constant)
pub(crate) fn try_compute_linear_product(e1: &LinearExpr, e2: &LinearExpr) -> Option<LinearExpr> {
    if e1.is_constant() && e2.is_constant() {
        return Some(LinearExpr::constant(e1.constant.checked_mul(e2.constant)?));
    }

    if e1.is_constant() {
        return e2.try_scale(e1.constant);
    }

    if e2.is_constant() {
        return e1.try_scale(e2.constant);
    }

    None
}

/// Check if an expression is zero (literal 0, Nat.zero, etc.)
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `true` for Nat literal 0, `Nat.zero`, `*.zero`, and `OfNat.ofNat 0`
/// ENSURES: Returns `false` for all non-zero expressions
pub(crate) fn is_zero_expr(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(0) => true,
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            s == "Nat.zero" || s == "0" || s.ends_with(".zero")
        }
        ExprKind::App(f, _arg) => {
            if let ExprKind::App(f2, _) = f.kind() {
                if let ExprKind::App(f3, n) = f2.kind() {
                    if let ExprKind::Const(name, _) = f3.kind() {
                        if name.to_string().contains("OfNat.ofNat")
                            && expr_is_nat_lit(n.as_ref(), 0)
                        {
                            return true;
                        }
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if two expressions are syntactically equal for nlinarith (simple check).
///
/// REQUIRES: `e1` and `e2` are well-formed Lean expressions
/// ENSURES: Returns `true` iff `e1 == e2` (Rust structural equality)
/// ENSURES: Does not handle alpha equivalence or definitional equality
pub(crate) fn nlinarith_exprs_equal(e1: &Expr, e2: &Expr) -> bool {
    e1 == e2
}

/// Check if a goal is of the form x² ≥ 0, 0 ≤ x², x * x ≥ 0, etc.
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `true` only for `0 ≤ e²`, `e² ≥ 0`, `0 ≤ e*e`, or `e*e ≥ 0` patterns
/// ENSURES: Returns `false` for all non-matching expressions (no false positives)
pub(super) fn is_square_nonnegative_goal(expr: &Expr) -> bool {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return false;
    }

    let lhs = args[args.len() - 2];
    let rhs = args[args.len() - 1];
    if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
        let name_str = name.to_string();

        if (name_str.contains("LE.le") || name_str.contains("Nat.le"))
            && is_zero_expr(lhs)
            && is_square_expr(rhs)
        {
            return true;
        }

        if name_str.contains("GE.ge") && is_zero_expr(rhs) && is_square_expr(lhs) {
            return true;
        }
    }

    false
}

fn is_square_expr(expr: &Expr) -> bool {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return false;
    }

    let lhs = args[args.len() - 2];
    let rhs = args[args.len() - 1];
    if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
        let name_str = name.to_string();

        if name_str.contains("HMul.hMul")
            || name_str.contains("Mul.mul")
            || name_str.contains("Nat.mul")
        {
            return nlinarith_exprs_equal(lhs, rhs);
        }

        if name_str.contains("HPow.hPow") && expr_is_nat_lit(rhs, 2) {
            return true;
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::tc_app;
    use clean_kernel::name::Name;
    use clean_kernel::Level;

    fn nat_hmul(lhs: Expr, rhs: Expr) -> Expr {
        tc_app::mk_tc_hbinop(
            Expr::const_(Name::from_string("HMul.hMul"), vec![]),
            tc_app::nat_type(),
            tc_app::nat_type(),
            tc_app::nat_type(),
            tc_app::nat_arith_inst("HMul.hMul"),
            lhs,
            rhs,
        )
    }

    fn nat_hpow(base: Expr, exp: Expr) -> Expr {
        tc_app::mk_tc_hbinop(
            Expr::const_(Name::from_string("HPow.hPow"), vec![]),
            tc_app::nat_type(),
            tc_app::nat_type(),
            tc_app::nat_type(),
            tc_app::nat_arith_inst("HPow.hPow"),
            base,
            exp,
        )
    }

    fn nat_ge(lhs: Expr, rhs: Expr) -> Expr {
        tc_app::mk_tc_rel(
            Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
            tc_app::nat_type(),
            tc_app::nat_rel_inst("GE.ge"),
            lhs,
            rhs,
        )
    }

    #[test]
    fn test_is_square_expr_handles_fully_applied_tc_mul_and_pow() {
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let square_mul = nat_hmul(x.clone(), x.clone());
        let square_pow = nat_hpow(x, Expr::nat_lit(2));

        assert!(is_square_expr(&square_mul));
        assert!(is_square_expr(&square_pow));
    }

    #[test]
    fn test_is_square_nonnegative_goal_handles_fully_applied_relations() {
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let square = nat_hmul(x.clone(), x);
        let le_goal = tc_app::nat_le_tc(Expr::nat_lit(0), square.clone());
        let ge_goal = nat_ge(square, Expr::nat_lit(0));

        assert!(is_square_nonnegative_goal(&le_goal));
        assert!(is_square_nonnegative_goal(&ge_goal));
    }

    #[test]
    fn test_try_compute_linear_product_constant_and_affine_expr() {
        let scalar = LinearExpr::constant(3);
        let affine = LinearExpr::from_coeffs(2, [(0, 1), (1, -2)]);
        let product = try_compute_linear_product(&scalar, &affine)
            .expect("constant-times-affine product should stay linear");

        assert_eq!(product.constant, 6);
        assert_eq!(product.coeff(0), 3);
        assert_eq!(product.coeff(1), -6);
    }
}
