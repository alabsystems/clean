// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic simplification and ring normalization for TLA+ tactics.
//!
//! This module provides:
//! - Identity-based simplification (n + 0 = n, n * 1 = n, etc.)
//! - Polynomial normalization (ring tactic)
//! - Arithmetic expression normalization

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Literal};

use crate::tactic::helpers::{
    expr_debug, exprs_equal, extract_binary_arith, extract_equality, extract_succ, is_one, is_zero,
    make_add, make_mul, substitute,
};

/// Normalize arithmetic expression by applying identity rules.
///
/// Handles:
/// - Int.ofNat normalization
/// - Binary operator identities (x + 0 = x, x * 1 = x, etc.)
/// - Distributivity
pub fn normalize_arith(expr: &Expr) -> Expr {
    // First: normalize numeric representations
    // Int.ofNat 0 → Nat.zero, Int.ofNat 1 → Nat.succ Nat.zero, etc.
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            let s = name.to_string();
            if s == "Int.ofNat" || s == "TLA.int" {
                // Int.ofNat n → Nat literal n
                if let ExprKind::Lit(Literal::Nat(n)) = arg.kind() {
                    if n.to_u64() == Some(0) {
                        return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                    }
                    if n.to_u64() == Some(1) {
                        return Expr::app(
                            Expr::const_(Name::from_string("Nat.succ"), vec![]),
                            Expr::const_(Name::from_string("Nat.zero"), vec![]),
                        );
                    }
                    // For other numbers, keep as literal
                    return Expr::from_kind(ExprKind::Lit(Literal::Nat(n.clone())));
                }
            }
        }
    }

    // Pattern: App(App(TLA.op, a), b) for binary ops
    if let ExprKind::App(f, b) = expr.kind() {
        if let ExprKind::App(op_with_a, a) = f.kind() {
            if let ExprKind::Const(op_name, levels) = op_with_a.kind() {
                let op_str = op_name.to_string();

                // Recursively normalize operands
                let a_norm = normalize_arith(a);
                let b_norm = normalize_arith(b);

                // Apply identity rules
                match op_str.as_str() {
                    "TLA.add" | "Nat.add" | "Add.add" => {
                        // x + 0 = x
                        if is_zero(&b_norm) {
                            return a_norm;
                        }
                        // 0 + x = x
                        if is_zero(&a_norm) {
                            return b_norm;
                        }
                    }
                    "TLA.mul" | "Nat.mul" | "Mul.mul" => {
                        // x * 0 = 0
                        if is_zero(&b_norm) {
                            return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                        }
                        // 0 * x = 0
                        if is_zero(&a_norm) {
                            return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                        }
                        // x * 1 = x
                        if is_one(&b_norm) {
                            return a_norm;
                        }
                        // 1 * x = x
                        if is_one(&a_norm) {
                            return b_norm;
                        }
                        // Left distributivity: k * (a + b) → k*a + k*b
                        if let Some((inner_op, c, d)) = extract_binary_arith(&b_norm) {
                            if inner_op == "TLA.add"
                                || inner_op == "Nat.add"
                                || inner_op == "Add.add"
                            {
                                let k_times_c = make_mul(&a_norm, &c);
                                let k_times_d = make_mul(&a_norm, &d);
                                let result = make_add(&k_times_c, &k_times_d);
                                return normalize_arith(&result);
                            }
                        }
                        // Handle k * succ(n) → k*n + k
                        if let Some(inner) = extract_succ(&b_norm) {
                            let k_times_inner = make_mul(&a_norm, &inner);
                            let result = make_add(&k_times_inner, &a_norm);
                            return normalize_arith(&result);
                        }
                        // Right distributivity: (a + b) * k → a*k + b*k
                        if let Some((inner_op, c, d)) = extract_binary_arith(&a_norm) {
                            if inner_op == "TLA.add"
                                || inner_op == "Nat.add"
                                || inner_op == "Add.add"
                            {
                                let c_times_k = make_mul(&c, &b_norm);
                                let d_times_k = make_mul(&d, &b_norm);
                                let result = make_add(&c_times_k, &d_times_k);
                                return normalize_arith(&result);
                            }
                        }
                        // Handle succ(n) * k → n*k + k
                        if let Some(inner) = extract_succ(&a_norm) {
                            let inner_times_k = make_mul(&inner, &b_norm);
                            let result = make_add(&inner_times_k, &b_norm);
                            return normalize_arith(&result);
                        }
                    }
                    "TLA.sub" | "Nat.sub" | "Sub.sub"
                        // x - 0 = x
                        if is_zero(&b_norm) => {
                            return a_norm;
                        }
                    "TLA.div" | "Nat.div" | "Div.div" => {
                        // 0 / x = 0
                        if is_zero(&a_norm) {
                            return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                        }
                        // x / 1 = x
                        if is_one(&b_norm) {
                            return a_norm;
                        }
                    }
                    "TLA.mod" | "Nat.mod" | "Mod.mod" => {
                        // 0 % x = 0
                        if is_zero(&a_norm) {
                            return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                        }
                        // x % 1 = 0
                        if is_one(&b_norm) {
                            return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                        }
                    }
                    _ => {}
                }

                // Rebuild with normalized operands
                return Expr::app(
                    Expr::app(Expr::const_(op_name.clone(), levels.clone()), a_norm),
                    b_norm,
                );
            }
        }
    }

    // Fallback: for any App not handled above, recursively normalize subexpressions
    if let ExprKind::App(f, arg) = expr.kind() {
        let f_norm = normalize_arith(f);
        let arg_norm = normalize_arith(arg);
        if !exprs_equal(&f_norm, f) || !exprs_equal(&arg_norm, arg) {
            return Expr::app(f_norm, arg_norm);
        }
    }

    // No simplification - return as-is
    expr.clone()
}

/// Check if an equality matches a known arithmetic identity.
///
/// Returns the identity name if matched.
pub fn check_arith_identity(lhs: &Expr, rhs: &Expr) -> Option<&'static str> {
    // n + 0 = n (add_zero_right)
    if let Some((op, a, b)) = extract_binary_arith(lhs) {
        if (op == "TLA.add" || op == "Nat.add" || op == "Add.add")
            && is_zero(&b)
            && exprs_equal(&a, rhs)
        {
            return Some("add_zero_right");
        }
    }

    // 0 + n = n (add_zero_left)
    if let Some((op, a, b)) = extract_binary_arith(lhs) {
        if (op == "TLA.add" || op == "Nat.add" || op == "Add.add")
            && is_zero(&a)
            && exprs_equal(&b, rhs)
        {
            return Some("add_zero_left");
        }
    }

    // n * 1 = n (mul_one_right)
    if let Some((op, a, b)) = extract_binary_arith(lhs) {
        if (op == "TLA.mul" || op == "Nat.mul" || op == "Mul.mul")
            && is_one(&b)
            && exprs_equal(&a, rhs)
        {
            return Some("mul_one_right");
        }
    }

    // 1 * n = n (mul_one_left)
    if let Some((op, a, b)) = extract_binary_arith(lhs) {
        if (op == "TLA.mul" || op == "Nat.mul" || op == "Mul.mul")
            && is_one(&a)
            && exprs_equal(&b, rhs)
        {
            return Some("mul_one_left");
        }
    }

    // n * 0 = 0 (mul_zero_right)
    if let Some((op, _a, b)) = extract_binary_arith(lhs) {
        if (op == "TLA.mul" || op == "Nat.mul" || op == "Mul.mul") && is_zero(&b) && is_zero(rhs) {
            return Some("mul_zero_right");
        }
    }

    // 0 * n = 0 (mul_zero_left)
    if let Some((op, a, _b)) = extract_binary_arith(lhs) {
        if (op == "TLA.mul" || op == "Nat.mul" || op == "Mul.mul") && is_zero(&a) && is_zero(rhs) {
            return Some("mul_zero_left");
        }
    }

    // n - 0 = n (sub_zero)
    if let Some((op, a, b)) = extract_binary_arith(lhs) {
        if (op == "TLA.sub" || op == "Nat.sub" || op == "Sub.sub")
            && is_zero(&b)
            && exprs_equal(&a, rhs)
        {
            return Some("sub_zero");
        }
    }

    None
}

/// Convert an expression to canonical polynomial form.
///
/// A polynomial is represented as a sorted list of monomials.
/// Each monomial is (coefficient, sorted variable names).
///
/// Examples:
/// - `n` → [(1, ["n"])]
/// - `2*n` → [(2, ["n"])]
/// - `n + 1` → [(1, []), (1, ["n"])]
/// - `n*(n+1)` → [(0, []), (1, ["n"]), (1, ["n", "n"])] = n + n²
pub fn expr_to_polynomial(expr: &Expr) -> Vec<(i64, Vec<String>)> {
    let poly = expr_to_poly_internal(expr);
    combine_like_terms(poly)
}

/// Internal recursive conversion to polynomial.
fn expr_to_poly_internal(expr: &Expr) -> Vec<(i64, Vec<String>)> {
    match expr.kind() {
        // Constant zero
        ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => {
            vec![(0, vec![])]
        }
        // Integer literal
        ExprKind::Lit(Literal::Nat(n)) => n
            .to_u64()
            .and_then(|v| i64::try_from(v).ok())
            .map(|value| vec![(value, vec![])])
            .unwrap_or_else(|| vec![(1, vec![format!("const_{n}")])]),
        // Named constant (variable)
        ExprKind::Const(name, _) => {
            vec![(1, vec![name.to_string()])]
        }
        // Bound variable
        ExprKind::BVar(i) => {
            vec![(1, vec![format!("BVar({})", i)])]
        }
        // Application
        ExprKind::App(f, arg) => {
            // Check for Nat.succ
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    // succ(n) = n + 1
                    let mut inner = expr_to_poly_internal(arg);
                    inner.push((1, vec![]));
                    return combine_like_terms(inner);
                }
            }

            // Check for binary operations
            if let ExprKind::App(op_app, a) = f.kind() {
                if let ExprKind::Const(op_name, _) = op_app.kind() {
                    let op_str = op_name.to_string();

                    match op_str.as_str() {
                        "TLA.add" | "Nat.add" | "Add.add" => {
                            let mut poly_a = expr_to_poly_internal(a);
                            let poly_b = expr_to_poly_internal(arg);
                            poly_a.extend(poly_b);
                            return combine_like_terms(poly_a);
                        }
                        "TLA.mul" | "Nat.mul" | "Mul.mul" => {
                            let poly_a = expr_to_poly_internal(a);
                            let poly_b = expr_to_poly_internal(arg);
                            let mut result = Vec::new();

                            for (coeff_a, vars_a) in &poly_a {
                                for (coeff_b, vars_b) in &poly_b {
                                    let new_coeff = coeff_a * coeff_b;
                                    let mut new_vars = vars_a.clone();
                                    new_vars.extend(vars_b.iter().cloned());
                                    new_vars.sort();
                                    result.push((new_coeff, new_vars));
                                }
                            }
                            return combine_like_terms(result);
                        }
                        _ => {}
                    }
                }
            }

            // Treat as opaque function application
            vec![(1, vec![expr_debug(expr)])]
        }
        // Default: treat as opaque term
        _ => {
            vec![(1, vec![expr_debug(expr)])]
        }
    }
}

/// Combine like terms in a polynomial.
fn combine_like_terms(poly: Vec<(i64, Vec<String>)>) -> Vec<(i64, Vec<String>)> {
    use std::collections::BTreeMap;
    let mut combined: BTreeMap<Vec<String>, i64> = BTreeMap::new();

    for (coeff, vars) in poly {
        *combined.entry(vars).or_insert(0) += coeff;
    }

    combined
        .into_iter()
        .filter(|(_, coeff)| *coeff != 0)
        .map(|(vars, coeff)| (coeff, vars))
        .collect()
}

/// Try to prove an equality by arithmetic simplification.
///
/// Returns Some(certificate) if the equality is provable by simplification.
pub fn try_arith_simplify(goal: &Expr, trace: bool) -> Option<String> {
    let (lhs, rhs) = extract_equality(goal)?;

    if trace {
        eprintln!(
            "[TLA] arith_simplify: checking {} = {}",
            expr_debug(&lhs),
            expr_debug(&rhs)
        );
    }

    // Normalize both sides and check if they become equal
    let lhs_norm = normalize_arith(&lhs);
    let rhs_norm = normalize_arith(&rhs);

    if exprs_equal(&lhs_norm, &rhs_norm) {
        if trace {
            eprintln!("[TLA] arith_simplify: normalized to equal expressions");
        }
        return Some(
            "{\"tactic\":\"arith_simplify\",\"method\":\"normalize\",\"status\":\"proved\"}"
                .to_string(),
        );
    }

    // Try identity-specific rules
    if let Some(rule) = check_arith_identity(&lhs, &rhs) {
        if trace {
            eprintln!("[TLA] arith_simplify: applied rule {}", rule);
        }
        return Some(format!(
            "{{\"tactic\":\"arith_simplify\",\"rule\":\"{}\",\"status\":\"proved\"}}",
            rule
        ));
    }

    // Try polynomial normalization (ring) for algebraic equality
    let lhs_poly = expr_to_polynomial(&lhs);
    let rhs_poly = expr_to_polynomial(&rhs);
    if lhs_poly == rhs_poly {
        if trace {
            eprintln!("[TLA] arith_simplify: ring proved via polynomial equality");
        }
        return Some(
            "{\"tactic\":\"arith_simplify\",\"method\":\"ring\",\"status\":\"proved\"}".to_string(),
        );
    }

    None
}

/// Try to prove an induction step case for arithmetic identities.
///
/// For properties like `n + 0 = n`, the step case is:
///   P(n) → P(succ n)
/// which becomes:
///   (n + 0 = n) → (succ n + 0 = succ n)
pub fn try_arith_step_case(step_body: &Expr) -> Option<String> {
    use crate::tactic::helpers::extract_implication;

    // Extract P(n) → P(succ n) structure
    let (ih, goal) = extract_implication(step_body)?;

    // Try to extract equalities from both sides
    let (ih_lhs, ih_rhs) = extract_equality(&ih)?;
    let (goal_lhs, goal_rhs) = extract_equality(&goal)?;

    // Check if this is an arithmetic identity step case
    // Pattern: (f(n) = g(n)) → (f(succ n) = g(succ n))
    // where f and g simplify to the same form

    // Normalize both sides of the goal
    let goal_lhs_norm = normalize_arith(&goal_lhs);
    let goal_rhs_norm = normalize_arith(&goal_rhs);

    if exprs_equal(&goal_lhs_norm, &goal_rhs_norm) {
        return Some(
            "{\"tactic\":\"arith_step\",\"method\":\"normalize\",\"status\":\"proved\"}"
                .to_string(),
        );
    }

    // Try using the IH to prove the goal
    // Pattern: if IH says lhs = rhs, and goal has lhs' that can be rewritten using IH
    let goal_lhs_with_ih = substitute(&goal_lhs, &ih_lhs, &ih_rhs);
    let goal_rhs_with_ih = substitute(&goal_rhs, &ih_lhs, &ih_rhs);

    let goal_lhs_final = normalize_arith(&goal_lhs_with_ih);
    let goal_rhs_final = normalize_arith(&goal_rhs_with_ih);

    if exprs_equal(&goal_lhs_final, &goal_rhs_final) {
        return Some(
            "{\"tactic\":\"arith_step\",\"method\":\"ih_subst\",\"status\":\"proved\"}".to_string(),
        );
    }

    // Try polynomial comparison
    let lhs_poly = expr_to_polynomial(&goal_lhs);
    let rhs_poly = expr_to_polynomial(&goal_rhs);

    if lhs_poly == rhs_poly {
        return Some(
            "{\"tactic\":\"arith_step\",\"method\":\"ring\",\"status\":\"proved\"}".to_string(),
        );
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::BigNat;

    #[test]
    fn test_normalize_arith_add_zero() {
        // n + 0 should normalize to n
        let n = Expr::const_(Name::from_string("n"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let add = Expr::const_(Name::from_string("TLA.add"), vec![]);
        let expr = Expr::app(Expr::app(add, n.clone()), zero);

        let result = normalize_arith(&expr);
        assert_eq!(result, n);
    }

    #[test]
    fn test_normalize_arith_mul_zero() {
        // n * 0 should normalize to 0
        let n = Expr::const_(Name::from_string("n"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let mul = Expr::const_(Name::from_string("TLA.mul"), vec![]);
        let expr = Expr::app(Expr::app(mul, n), zero);

        let result = normalize_arith(&expr);
        let expected_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        assert_eq!(result, expected_zero);
    }

    #[test]
    fn test_normalize_arith_mul_one() {
        // n * 1 should normalize to n
        let n = Expr::const_(Name::from_string("n"), vec![]);
        let one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        let mul = Expr::const_(Name::from_string("TLA.mul"), vec![]);
        let expr = Expr::app(Expr::app(mul, n.clone()), one);

        let result = normalize_arith(&expr);
        assert_eq!(result, n);
    }

    #[test]
    fn test_check_arith_identity_add_zero() {
        // n + 0 = n should match add_zero_right
        let n = Expr::const_(Name::from_string("n"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let add = Expr::const_(Name::from_string("TLA.add"), vec![]);
        let lhs = Expr::app(Expr::app(add, n.clone()), zero);

        let result = check_arith_identity(&lhs, &n);
        assert_eq!(result, Some("add_zero_right"));
    }

    #[test]
    fn test_expr_to_polynomial_constant() {
        let n = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(5))));
        let poly = expr_to_polynomial(&n);
        assert_eq!(poly, vec![(5, vec![])]);
    }

    #[test]
    fn test_expr_to_polynomial_variable() {
        let n = Expr::const_(Name::from_string("n"), vec![]);
        let poly = expr_to_polynomial(&n);
        assert_eq!(poly, vec![(1, vec!["n".to_string()])]);
    }

    #[test]
    fn test_expr_to_polynomial_addition() {
        // n + 1
        let n = Expr::const_(Name::from_string("n"), vec![]);
        let one = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(1))));
        let add = Expr::const_(Name::from_string("TLA.add"), vec![]);
        let expr = Expr::app(Expr::app(add, n), one);

        let poly = expr_to_polynomial(&expr);
        // Should have constant 1 and variable n with coeff 1
        assert!(poly.contains(&(1, vec![])));
        assert!(poly.contains(&(1, vec!["n".to_string()])));
    }
}
