// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression builders for linear combination proof reconstruction (#2526).
//!
//! Provides helpers to construct arithmetic expressions (add, mul, neg)
//! and equality types for the proof accumulator.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

/// Build `@Eq.{u} α a b` type expression.
pub(super) fn make_eq_type(alpha: &Expr, a: &Expr, b: &Expr, u: &Level) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u.clone()]),
                alpha.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build a Lean expression for a coefficient in the given carrier type.
pub(super) fn make_coeff_expr(alpha: &Expr, num: i64, den: u64) -> Option<Expr> {
    match carrier_name(alpha)? {
        "Nat" if den == 1 && num >= 0 => Some(Expr::nat_lit(num as u64)),
        "Nat" => None,
        "Int" if den == 1 => Some(make_int_expr(num)),
        "Int" => None,
        "Rat" => make_rat_coeff_expr(num, den),
        "Real" if den == 1 => Some(Expr::app(
            Expr::const_(Name::from_string("Real.ofInt"), vec![]),
            make_int_expr(num),
        )),
        "Real" => make_real_fractional_expr(num, den),
        _ => None,
    }
}

fn make_rat_coeff_expr(num: i64, den: u64) -> Option<Expr> {
    if den == 0 {
        return None;
    }

    let numerator = make_rat_of_int_expr(num);
    if den == 1 {
        return Some(numerator);
    }

    let denominator = make_rat_of_nat_expr(den);
    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Rat.div"), vec![]),
            numerator,
        ),
        denominator,
    ))
}

fn make_real_fractional_expr(num: i64, den: u64) -> Option<Expr> {
    if den == 0 {
        return None;
    }
    let int_part = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        make_int_expr(num),
    );
    let nat_part = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(den),
    );
    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.div"), vec![]),
            int_part,
        ),
        nat_part,
    ))
}

/// Build `fun (x : α) => c * x` as a lambda expression.
pub(super) fn make_mul_lambda(alpha: &Expr, coeff: &Expr) -> Option<Expr> {
    let mul_body = make_mul_app_bvar(alpha, coeff)?;
    Some(Expr::lam(BinderInfo::Default, alpha.clone(), mul_body))
}

/// Build `c * x` where x is BVar(0).
fn make_mul_app_bvar(alpha: &Expr, coeff: &Expr) -> Option<Expr> {
    make_binary_carrier_app(alpha, "mul", coeff, &Expr::bvar(0))
}

/// Build `c * x` application.
pub(super) fn make_mul_app(alpha: &Expr, coeff: &Expr, x: &Expr) -> Option<Expr> {
    make_binary_carrier_app(alpha, "mul", coeff, x)
}

/// Build `fun (x : α) => x + rhs_fixed` as a lambda expression.
pub(super) fn make_add_left_lambda(alpha: &Expr, rhs_fixed: &Expr) -> Option<Expr> {
    let body = make_add_app(alpha, &Expr::bvar(0), rhs_fixed)?;
    Some(Expr::lam(BinderInfo::Default, alpha.clone(), body))
}

/// Build `fun (y : α) => lhs_fixed + y` as a lambda expression.
pub(super) fn make_add_right_lambda(alpha: &Expr, lhs_fixed: &Expr) -> Option<Expr> {
    let body = make_add_app(alpha, lhs_fixed, &Expr::bvar(0))?;
    Some(Expr::lam(BinderInfo::Default, alpha.clone(), body))
}

/// Build `a + b` application.
pub(super) fn make_add_app(alpha: &Expr, a: &Expr, b: &Expr) -> Option<Expr> {
    make_binary_carrier_app(alpha, "add", a, b)
}

fn make_binary_carrier_app(alpha: &Expr, op: &str, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let op_name = match (carrier_name(alpha)?, op) {
        ("Nat", "add") => "Nat.add",
        ("Nat", "mul") => "Nat.mul",
        ("Int", "add") => "Int.add",
        ("Int", "mul") => "Int.mul",
        ("Rat", "add") => "Rat.add",
        ("Rat", "mul") => "Rat.mul",
        ("Real", "add") => "Real.add",
        ("Real", "mul") => "Real.mul",
        _ => return None,
    };
    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(op_name), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    ))
}

fn make_rat_of_int_expr(n: i64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
        make_int_expr(n),
    )
}

fn make_rat_of_nat_expr(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n),
        ),
    )
}

pub(super) fn carrier_name(alpha: &Expr) -> Option<&'static str> {
    match alpha.kind() {
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Nat" => Some("Nat"),
            "Int" => Some("Int"),
            "Rat" => Some("Rat"),
            "Real" => Some("Real"),
            _ => None,
        },
        _ => None,
    }
}

fn make_int_expr(n: i64) -> Expr {
    if n >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n as u64),
        )
    } else {
        // Match the constructor family handled by polynomial parsing so
        // scratch `ring_nf` normalization sees the same negative-literal shape
        // on both the reconstructed proof and the original goal.
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n.unsigned_abs() - 1),
        )
    }
}
