// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helper utilities for TLA+ tactics.
//!
//! This module provides common expression manipulation, pattern matching,
//! and proof state utilities used across different tactic implementations.

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

/// Peel off non-dependent Pi bindings to get the innermost goal.
pub fn peel_pis_to_innermost(expr: &Expr) -> Option<Expr> {
    let mut current = expr.clone();
    let mut peeled = false;

    while let ExprKind::Pi(_, _, body) = current.kind() {
        if !body.has_loose_bvars() {
            let next = (**body).clone();
            current = next;
            peeled = true;
        } else {
            break;
        }
    }

    if peeled {
        Some(current)
    } else {
        None
    }
}

/// Peel off hypothesis bindings and collect their types.
///
/// For a sequent-encoded goal like:
/// ```text
/// Pi(Implicit, TLA.Value,    -- declaration (skip)
///    Pi(Default, h1_type,    -- hypothesis (collect)
///       Pi(Default, h2_type, -- hypothesis (collect)
///          goal)))           -- inner goal
/// ```
///
/// This returns `([h1_type, h2_type], goal)`.
///
/// Key insight: Implicit Pis are declarations (constants, variables),
/// non-implicit non-dependent Pis are hypotheses (implications).
pub fn peel_hypotheses_with_context(expr: &Expr) -> (Vec<Expr>, Expr) {
    let mut current = expr.clone();
    let mut hypothesis_types = Vec::new();

    loop {
        match current.kind() {
            // Skip implicit declarations (constants, variables)
            // These are dependent Pis that introduce names used in the body
            ExprKind::Pi(bd, _, body) if bd.info == BinderInfo::Implicit => {
                let next = (**body).clone();
                current = next;
            }
            // Non-implicit, non-dependent Pi = hypothesis (implication)
            ExprKind::Pi(_, ty, body) if !body.has_loose_bvars() => {
                hypothesis_types.push((**ty).clone());
                let next = (**body).clone();
                current = next;
            }
            // Anything else: stop peeling
            _ => break,
        }
    }

    (hypothesis_types, current)
}

/// Wrap an expression with hypotheses as implications (Pi bindings).
///
/// Given hypotheses [h1, h2, ...] and a goal G, produces:
/// h1 → h2 → ... → G
///
/// This allows subgoals (like induction cases) to use the hypotheses
/// from the original obligation.
pub fn wrap_with_hypotheses(hypotheses: &[Expr], goal: Expr) -> Expr {
    let mut result = goal;
    for hyp in hypotheses.iter().rev() {
        result = Expr::pi(BinderInfo::Default, hyp.clone(), result);
    }
    result
}

/// Check if expression is trivially true (Bool.true, True constant, etc.)
pub fn is_trivially_true(expr: &Expr) -> bool {
    match expr.kind() {
        // Bool.true
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            name_str == "Bool.true" || name_str == "True" || name_str == "trivial"
        }
        // Application of True.intro or similar
        ExprKind::App(f, _) => {
            if let ExprKind::Const(name, _) = f.kind() {
                name.to_string() == "True.intro"
            } else {
                false
            }
        }
        // For pi-wrapped True, check innermost
        ExprKind::Pi(_, _, body) if !body.has_loose_bvars() => is_trivially_true(body),
        _ => false,
    }
}

/// Check if expression is trivially false (Bool.false or False)
pub fn is_trivially_false(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let name_str = name.to_string();
        name_str == "Bool.false" || name_str == "False"
    } else {
        false
    }
}

/// Check if two expressions are structurally equal
pub fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    a == b
}

/// Check if an implication P → Q is trivially true.
///
/// An implication is trivially true if:
/// - Q is trivially true (True → True, P → True)
/// - P is trivially false (False → Q)
/// - P and Q are structurally equal (P → P)
pub fn is_implication_trivially_true(antecedent: &Expr, consequent: &Expr) -> bool {
    is_trivially_true(consequent)
        || is_trivially_false(antecedent)
        || exprs_equal(antecedent, consequent)
}

/// Check if expression is zero (Nat.zero, TLA.zero, Int 0, etc.)
pub fn is_zero(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            name_str == "Nat.zero" || name_str == "TLA.zero" || name_str == "Int.zero"
        }
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(0) => true,
        // Int.ofNat 0 or TLA.int 0
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Int.ofNat" || s == "TLA.int" {
                    return is_zero(arg);
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is one (Nat.succ Nat.zero, etc.)
pub fn is_one(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(1) => true,
        // Nat.succ Nat.zero or Int.ofNat 1 or TLA.int 1
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Nat.succ" {
                    return is_zero(arg);
                }
                if s == "Int.ofNat" || s == "TLA.int" {
                    return is_one(arg);
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is 2 (in various forms)
pub fn is_two(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(2) => true,
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Nat.succ" {
                    return is_one(arg);
                }
                if s == "Int.ofNat" || s == "TLA.int" {
                    return is_two(arg);
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if type is Nat
pub fn is_nat_type(ty: &Expr) -> bool {
    if let ExprKind::Const(name, _) = ty.kind() {
        name.to_string() == "Nat"
    } else {
        false
    }
}

/// Check if expression represents the Nat set (TLA.Nat)
pub fn is_nat_set(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let name_str = name.to_string();
        name_str == "TLA.Nat" || name_str == "Nat"
    } else {
        false
    }
}

/// Check if expression is Nat.succ(something)
pub fn is_succ_expr(expr: &Expr) -> bool {
    if let ExprKind::App(f, _) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            return name.to_string() == "Nat.succ";
        }
    }
    false
}

/// Extract inner expression from Nat.succ(x) -> Some(x)
pub fn extract_succ(expr: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Nat.succ" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

/// Check if expression is a positive constant (1, 2, 3, etc.)
pub fn is_positive_constant(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n.to_u64().is_some_and(|v| v > 0),
        // Nat.succ anything is positive
        ExprKind::App(f, _) => {
            if let ExprKind::Const(name, _) = f.kind() {
                name.to_string() == "Nat.succ"
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if expression is n + k where k is a positive constant.
/// This is always > 0 for natural numbers since n >= 0.
pub fn is_add_positive(expr: &Expr) -> bool {
    // Pattern: App(App(TLA.add, n), k) where k is positive
    if let ExprKind::App(f, arg2) = expr.kind() {
        if let ExprKind::App(op, _arg1) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                if name.to_string() == "TLA.add" {
                    return is_positive_constant(arg2);
                }
            }
        }
    }
    false
}

/// Check if rhs is lhs + k where k is positive.
/// Returns true if rhs = lhs + k and k > 0.
pub fn is_expr_plus_positive(lhs: &Expr, rhs: &Expr) -> bool {
    // Pattern: rhs = App(App(TLA.add, lhs), k) where k > 0
    if let ExprKind::App(f, k) = rhs.kind() {
        if let ExprKind::App(op, arg) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                if name.to_string() == "TLA.add" && exprs_equal(arg, lhs) {
                    return is_positive_constant(k);
                }
            }
        }
    }
    false
}

/// Extract equality from goal (Eq or TLA.eq)
pub fn extract_equality(goal: &Expr) -> Option<(Expr, Expr)> {
    // Pattern 1: Eq ty lhs rhs
    // Pattern 2: App(App(TLA.eq, lhs), rhs)
    if let ExprKind::App(f, rhs) = goal.kind() {
        if let ExprKind::App(f2, lhs) = f.kind() {
            // Check for Eq _ lhs rhs
            if let ExprKind::App(eq, _ty) = f2.kind() {
                if let ExprKind::Const(name, _) = eq.kind() {
                    if name.to_string() == "Eq" {
                        return Some(((**lhs).clone(), (**rhs).clone()));
                    }
                }
            }
            // Check for TLA.eq lhs rhs
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "TLA.eq" {
                    return Some(((**lhs).clone(), (**rhs).clone()));
                }
            }
        }
    }
    None
}

/// Extract binary arithmetic operation: returns (op_name, arg1, arg2)
pub fn extract_binary_arith(expr: &Expr) -> Option<(String, Expr, Expr)> {
    if let ExprKind::App(f, arg2) = expr.kind() {
        if let ExprKind::App(op, arg1) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                return Some((name.to_string(), (**arg1).clone(), (**arg2).clone()));
            }
        }
    }
    None
}

/// Extract P and Q from implication P -> Q.
///
/// Implications can be encoded as:
/// 1. Or(Not(P), Q) - classical encoding
/// 2. Pi(_, P, Q) where Q doesn't depend on the binding - non-dependent implication
pub fn extract_implication(expr: &Expr) -> Option<(Expr, Expr)> {
    // First try: non-dependent Pi encoding (P -> Q as Pi(_, P, Q))
    if let ExprKind::Pi(_, ty, body) = expr.kind() {
        if !body.has_loose_bvars() {
            return Some(((**ty).clone(), (**body).clone()));
        }
    }

    // Second try: Or(Not(P), Q) encoding
    if let Some((left, right)) = extract_or(expr) {
        if let Some(p) = extract_not(&left) {
            return Some((p, right));
        }
    }

    None
}

/// Extract P from Not(P)
pub fn extract_not(expr: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Not" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

/// Extract P and Q from Or(P, Q)
pub fn extract_or(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f, q) = expr.kind() {
        if let ExprKind::App(or, p) = f.kind() {
            if let ExprKind::Const(name, _) = or.kind() {
                if name.to_string() == "Or" {
                    return Some(((**p).clone(), (**q).clone()));
                }
            }
        }
    }
    None
}

/// Extract comparison from expression: returns (op, lhs, rhs)
/// Pattern: App(App(TLA.op, lhs), rhs) where op is gt/lt/ge/le
pub fn extract_comparison(expr: &Expr) -> Option<(String, Expr, Expr)> {
    if let ExprKind::App(f, rhs) = expr.kind() {
        if let ExprKind::App(op, lhs) = f.kind() {
            if let ExprKind::Const(name, _) = op.kind() {
                let name_str = name.to_string();
                if let Some(op_name) = name_str.strip_prefix("TLA.") {
                    if matches!(op_name, "gt" | "lt" | "ge" | "le") {
                        return Some((op_name.to_string(), (**lhs).clone(), (**rhs).clone()));
                    }
                }
            }
        }
    }
    None
}

/// Extract the body of a forall over Nat.
///
/// Returns Some(body) if goal has form `forall n : Nat, P(n)` (Pi over Nat).
/// The body contains BVar(0) which refers to the bound variable.
pub fn extract_forall_nat(goal: &Expr) -> Option<Expr> {
    if let ExprKind::Pi(_, ty, body) = goal.kind() {
        if is_nat_type(ty) {
            return Some((**body).clone());
        }
    }
    None
}

/// Extract (set, var_name, body) from TLA.forallIn S (lambda x. P(x))
pub fn extract_tla_forall_in(goal: &Expr) -> Option<(Expr, String, Expr)> {
    // Pattern: App(App(TLA.forallIn, set), lambda)
    if let ExprKind::App(f, lambda) = goal.kind() {
        if let ExprKind::App(forall_in, set) = f.kind() {
            if let ExprKind::Const(name, _) = forall_in.kind() {
                if name.to_string() == "TLA.forallIn" {
                    // Extract the lambda body
                    if let ExprKind::Lam(_, _, body) = lambda.kind() {
                        // For now, use a placeholder name since Lam doesn't store it
                        return Some(((**set).clone(), "_x".to_string(), (**body).clone()));
                    }
                }
            }
        }
    }
    None
}

/// Check if expression is a product type (A x B)
///
/// Returns Some((A, B)) if it's a product type.
pub fn extract_product_type(expr: &Expr) -> Option<(Expr, Expr)> {
    // Pattern: App(App(Prod, A), B)
    if let ExprKind::App(f, b) = expr.kind() {
        if let ExprKind::App(prod, a) = f.kind() {
            if let ExprKind::Const(name, _) = prod.kind() {
                let name_str = name.to_string();
                if name_str == "Prod" || name_str == "TLA.Prod" {
                    return Some(((**a).clone(), (**b).clone()));
                }
            }
        }
    }
    None
}

/// Create a multiplication expression: a * b using TLA.mul
pub fn make_mul(a: &Expr, b: &Expr) -> Expr {
    let mul = Expr::const_(Name::from_string("TLA.mul"), vec![]);
    Expr::app(Expr::app(mul, a.clone()), b.clone())
}

/// Create an addition expression: a + b using TLA.add
pub fn make_add(a: &Expr, b: &Expr) -> Expr {
    let add = Expr::const_(Name::from_string("TLA.add"), vec![]);
    Expr::app(Expr::app(add, a.clone()), b.clone())
}

/// Debug string for an expression (for tracing)
pub fn expr_debug(expr: &Expr) -> String {
    match expr.kind() {
        ExprKind::Const(n, _) => format!("Const({})", n),
        ExprKind::BVar(i) => format!("BVar({})", i),
        ExprKind::Lit(l) => format!("Lit({:?})", l),
        ExprKind::App(f, a) => format!("App({}, {})", expr_debug(f), expr_debug(a)),
        ExprKind::Lam(_, ty, body) => format!("Lam({}, {})", expr_debug(ty), expr_debug(body)),
        ExprKind::Pi(_, ty, body) => format!("Pi({}, {})", expr_debug(ty), expr_debug(body)),
        _ => format!("{:?}", expr),
    }
}

/// Substitute occurrences of pattern with replacement in expr.
pub fn substitute(expr: &Expr, pattern: &Expr, replacement: &Expr) -> Expr {
    if exprs_equal(expr, pattern) {
        return replacement.clone();
    }

    match expr.kind() {
        ExprKind::App(f, a) => Expr::app(
            substitute(f, pattern, replacement),
            substitute(a, pattern, replacement),
        ),
        ExprKind::Lam(bi, ty, body) => Expr::lam(
            *bi,
            substitute(ty, pattern, replacement),
            substitute(body, pattern, replacement),
        ),
        ExprKind::Pi(bi, ty, body) => Expr::pi(
            *bi,
            substitute(ty, pattern, replacement),
            substitute(body, pattern, replacement),
        ),
        _ => expr.clone(),
    }
}

/// Extract a natural number literal from an expression.
pub fn extract_nat_lit(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n.to_u64(),
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if s == "Nat.zero" || s == "TLA.zero" || s == "Int.zero" {
                Some(0)
            } else {
                None
            }
        }
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Nat.succ" {
                    return extract_nat_lit(arg).map(|n| n + 1);
                }
                // Handle Int.ofNat and TLA.int wrappers
                if s == "Int.ofNat" || s == "TLA.int" {
                    return extract_nat_lit(arg);
                }
            }
            None
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_zero_variants() {
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        assert!(is_zero(&nat_zero));

        let lit_zero = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(0),
        )));
        assert!(is_zero(&lit_zero));

        let nat_one = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(1),
        )));
        assert!(!is_zero(&nat_one));
    }

    #[test]
    fn test_is_one_variants() {
        let lit_one = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(1),
        )));
        assert!(is_one(&lit_one));

        let succ_zero = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        assert!(is_one(&succ_zero));

        let lit_zero = Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
            clean_kernel::BigNat::Small(0),
        )));
        assert!(!is_one(&lit_zero));
    }

    #[test]
    fn test_is_nat_set() {
        let tla_nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
        assert!(is_nat_set(&tla_nat));

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(is_nat_set(&nat));

        let other = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(!is_nat_set(&other));
    }

    #[test]
    fn test_peel_pis_to_innermost() {
        // Single non-dependent Pi: A -> B
        let b = Expr::const_(Name::from_string("B"), vec![]);
        let a = Expr::const_(Name::from_string("A"), vec![]);
        let impl_goal = Expr::pi(BinderInfo::Default, a.clone(), b.clone());

        let peeled = peel_pis_to_innermost(&impl_goal)
            .expect("peel_pis_to_innermost on A -> B should return innermost");
        assert_eq!(peeled, b);
    }

    #[test]
    fn test_extract_equality() {
        // TLA.eq lhs rhs
        let lhs = Expr::const_(Name::from_string("x"), vec![]);
        let rhs = Expr::const_(Name::from_string("y"), vec![]);
        let eq = Expr::const_(Name::from_string("TLA.eq"), vec![]);
        let eq_expr = Expr::app(Expr::app(eq, lhs.clone()), rhs.clone());

        let (l, r) = extract_equality(&eq_expr)
            .expect("extract_equality on TLA.eq x y should return (x, y)");
        assert_eq!(l, lhs);
        assert_eq!(r, rhs);
    }

    #[test]
    fn test_tla_int_pattern_matching() {
        // TLA.int 0 should be zero
        let tla_int_zero = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(0),
            ))),
        );
        assert!(is_zero(&tla_int_zero), "TLA.int 0 should be zero");

        // TLA.int 1 should be one
        let tla_int_one = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(1),
            ))),
        );
        assert!(is_one(&tla_int_one), "TLA.int 1 should be one");

        // TLA.int 2 should be two
        let tla_int_two = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(2),
            ))),
        );
        assert!(is_two(&tla_int_two), "TLA.int 2 should be two");

        // extract_nat_lit should work with TLA.int
        assert_eq!(extract_nat_lit(&tla_int_zero), Some(0));
        assert_eq!(extract_nat_lit(&tla_int_one), Some(1));
        assert_eq!(extract_nat_lit(&tla_int_two), Some(2));

        // TLA.int 42 should extract to 42
        let tla_int_42 = Expr::app(
            Expr::const_(Name::from_string("TLA.int"), vec![]),
            Expr::from_kind(ExprKind::Lit(clean_kernel::expr::Literal::Nat(
                clean_kernel::BigNat::Small(42),
            ))),
        );
        assert_eq!(extract_nat_lit(&tla_int_42), Some(42));
    }
}
