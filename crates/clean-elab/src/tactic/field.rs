// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Field expression normalization (pure, no `ProofState` dependency).
//!
//! Extends the ring normalizer (`ring_helpers.rs`) with division (`Div`) and
//! multiplicative inverse (`Inv`). The tactic entry point lives in
//! `field_tactic.rs` (split per 500-line limit, #307).

use clean_kernel::{Expr, ExprKind};

use super::ring_literals::nonnegative_ring_const_value;
use crate::stack_safe;

/// Representation of a field expression in normalized form.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FieldExpr {
    /// A constant (natural number for now).
    Const(u64),
    /// A variable (identified by name or fvar).
    Var(String),
    /// Addition of terms.
    Add(Vec<FieldExpr>),
    /// Multiplication of factors.
    Mul(Vec<FieldExpr>),
    /// Power (base, exponent).
    Pow(Box<FieldExpr>, u64),
    /// Negation.
    Neg(Box<FieldExpr>),
    /// Division.
    Div(Box<FieldExpr>, Box<FieldExpr>),
    /// Multiplicative inverse.
    Inv(Box<FieldExpr>),
    /// Unknown expression (treated as atomic).
    Unknown(String),
}

fn is_named_op(name: &str, exact: &[&str], suffixes: &[&str]) -> bool {
    exact.contains(&name) || suffixes.iter().any(|suffix| name.ends_with(suffix))
}

fn is_add_head(name: &str) -> bool {
    is_named_op(name, &["HAdd.hAdd", "Add.add"], &[".hAdd", ".add"])
}

fn is_mul_head(name: &str) -> bool {
    is_named_op(name, &["HMul.hMul", "Mul.mul"], &[".hMul", ".mul"])
}

fn is_sub_head(name: &str) -> bool {
    is_named_op(name, &["HSub.hSub", "Sub.sub"], &[".hSub", ".sub"])
}

pub(crate) fn is_div_head(name: &str) -> bool {
    is_named_op(name, &["HDiv.hDiv", "Div.div"], &[".hDiv", ".div"])
}

pub(crate) fn is_pow_head(name: &str) -> bool {
    is_named_op(
        name,
        &["HPow.hPow", "Pow.pow", "Nat.pow"],
        &[".hPow", ".pow"],
    )
}

fn is_neg_head(name: &str) -> bool {
    is_named_op(name, &["Neg.neg"], &[".neg"])
}

pub(crate) fn is_inv_head(name: &str) -> bool {
    is_named_op(name, &["Inv.inv"], &[".inv"])
}

pub(crate) fn field_negate(expr: FieldExpr) -> FieldExpr {
    match expr {
        FieldExpr::Const(0) => FieldExpr::Const(0),
        FieldExpr::Neg(inner) => *inner,
        other => FieldExpr::Neg(Box::new(other)),
    }
}

pub(crate) fn field_pow_expr(base: FieldExpr, exp: u64) -> FieldExpr {
    if exp == 0 {
        return FieldExpr::Const(1);
    }
    if exp == 1 {
        return base;
    }

    match base {
        FieldExpr::Const(n) => match u32::try_from(exp).ok().and_then(|e| n.checked_pow(e)) {
            Some(pow) => FieldExpr::Const(pow),
            None => FieldExpr::Pow(Box::new(FieldExpr::Const(n)), exp),
        },
        FieldExpr::Pow(inner, inner_exp) => match inner_exp.checked_mul(exp) {
            Some(total_exp) => FieldExpr::Pow(inner, total_exp),
            None => FieldExpr::Pow(Box::new(FieldExpr::Pow(inner, inner_exp)), exp),
        },
        other => FieldExpr::Pow(Box::new(other), exp),
    }
}

fn field_inv_expr(expr: FieldExpr) -> FieldExpr {
    match expr {
        FieldExpr::Const(1) => FieldExpr::Const(1),
        FieldExpr::Inv(inner) => *inner,
        FieldExpr::Div(numer, denom) => field_div_expr(*denom, *numer),
        FieldExpr::Mul(factors) => {
            let inverted = factors.into_iter().rev().map(field_inv_expr).collect();
            field_mul_factors(inverted)
        }
        other => FieldExpr::Inv(Box::new(other)),
    }
}

fn field_div_expr(numer: FieldExpr, denom: FieldExpr) -> FieldExpr {
    if numer == FieldExpr::Const(0) {
        return FieldExpr::Const(0);
    }
    if denom == FieldExpr::Const(1) {
        return numer;
    }
    if numer == denom {
        return FieldExpr::Const(1);
    }
    match denom {
        FieldExpr::Inv(inner) => field_mul_factors(vec![numer, *inner]),
        other => FieldExpr::Div(Box::new(numer), Box::new(other)),
    }
}

fn field_pow_signed(base: FieldExpr, exp: i64) -> FieldExpr {
    if exp == 0 {
        return FieldExpr::Const(1);
    }
    if exp > 0 {
        return if let Ok(n) = u64::try_from(exp) {
            field_pow_expr(base, n)
        } else {
            FieldExpr::Pow(Box::new(base), 1)
        };
    }

    let Some(abs_exp) = exp.checked_abs().and_then(|n| u64::try_from(n).ok()) else {
        return field_inv_expr(base);
    };
    if abs_exp == 1 {
        field_inv_expr(base)
    } else {
        field_inv_expr(field_pow_expr(base, abs_exp))
    }
}

pub(crate) fn field_add_terms(terms: Vec<FieldExpr>) -> FieldExpr {
    terms
        .into_iter()
        .reduce(field_flatten_add)
        .unwrap_or(FieldExpr::Const(0))
}

pub(crate) fn field_mul_factors(factors: Vec<FieldExpr>) -> FieldExpr {
    factors
        .into_iter()
        .reduce(field_flatten_mul)
        .unwrap_or(FieldExpr::Const(1))
}

fn field_collect_like_terms(terms: Vec<FieldExpr>) -> Vec<FieldExpr> {
    use std::collections::HashMap;

    let mut const_sum: i64 = 0;
    let mut counts: HashMap<FieldExpr, i64> = HashMap::new();

    for term in terms {
        match term {
            FieldExpr::Const(n) => {
                if let Ok(n_i64) = i64::try_from(n) {
                    const_sum += n_i64;
                } else {
                    *counts.entry(FieldExpr::Const(n)).or_insert(0) += 1;
                }
            }
            FieldExpr::Neg(inner) => match *inner {
                FieldExpr::Const(n) => {
                    if let Ok(n_i64) = i64::try_from(n) {
                        const_sum -= n_i64;
                    } else {
                        *counts
                            .entry(FieldExpr::Neg(Box::new(FieldExpr::Const(n))))
                            .or_insert(0) += 1;
                    }
                }
                other => {
                    *counts.entry(other).or_insert(0) -= 1;
                }
            },
            other => {
                *counts.entry(other).or_insert(0) += 1;
            }
        }
    }

    let mut result = Vec::new();

    if const_sum > 0 {
        result.push(FieldExpr::Const(const_sum as u64));
    } else if const_sum < 0 {
        result.push(FieldExpr::Neg(Box::new(FieldExpr::Const(
            (-const_sum) as u64,
        ))));
    }

    for (term, count) in counts {
        if count > 0 {
            for _ in 0..(count as usize) {
                result.push(term.clone());
            }
        } else if count < 0 {
            for _ in 0..((-count) as usize) {
                result.push(FieldExpr::Neg(Box::new(term.clone())));
            }
        }
    }

    result
}

pub(crate) fn field_flatten_add(left: FieldExpr, right: FieldExpr) -> FieldExpr {
    let mut terms = Vec::new();

    match left {
        FieldExpr::Add(items) => terms.extend(items),
        other => terms.push(other),
    }

    match right {
        FieldExpr::Add(items) => terms.extend(items),
        other => terms.push(other),
    }

    terms = field_collect_like_terms(terms);

    match terms.len() {
        0 => FieldExpr::Const(0),
        1 => terms.into_iter().next().unwrap_or(FieldExpr::Const(0)),
        _ => {
            terms.sort();
            FieldExpr::Add(terms)
        }
    }
}

pub(crate) fn field_flatten_mul(left: FieldExpr, right: FieldExpr) -> FieldExpr {
    let mut factors = Vec::new();

    match left {
        FieldExpr::Mul(items) => factors.extend(items),
        other => factors.push(other),
    }

    match right {
        FieldExpr::Mul(items) => factors.extend(items),
        other => factors.push(other),
    }

    let mut const_product = 1_u64;
    let mut const_factors = Vec::new();
    let mut other_factors = Vec::new();

    for factor in factors {
        match factor {
            FieldExpr::Const(0) => return FieldExpr::Const(0),
            FieldExpr::Const(1) => {}
            FieldExpr::Const(n) => match const_product.checked_mul(n) {
                Some(product) => const_product = product,
                None => {
                    if const_product != 1 {
                        const_factors.push(FieldExpr::Const(const_product));
                        const_product = 1;
                    }
                    const_factors.push(FieldExpr::Const(n));
                }
            },
            other => other_factors.push(other),
        }
    }

    if const_product != 1 {
        const_factors.push(FieldExpr::Const(const_product));
    }

    let mut result = const_factors;
    result.extend(other_factors);

    match result.len() {
        0 => FieldExpr::Const(1),
        1 => result.into_iter().next().unwrap_or(FieldExpr::Const(1)),
        _ => {
            result.sort();
            FieldExpr::Mul(result)
        }
    }
}

fn nat_like_value(expr: &Expr) -> Option<u64> {
    nonnegative_ring_const_value(expr)
}

pub(crate) fn expr_to_signed_int(expr: &Expr) -> Option<i64> {
    let expr = expr.strip_mdata();

    if let Some(n) = nat_like_value(expr) {
        return i64::try_from(n).ok();
    }

    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.strip_mdata().kind() {
            let name = name.to_string();
            if name == "Int.negSucc" {
                return nat_like_value(arg)
                    .and_then(|n| i64::try_from(n).ok())
                    .and_then(|n| n.checked_add(1))
                    .map(|n| -n);
            }
            if name == "Int.negOfNat" {
                return nat_like_value(arg)
                    .and_then(|n| i64::try_from(n).ok())
                    .map(|n| -n);
            }
        }
    }

    let head = expr.get_app_fn().strip_mdata();
    if let ExprKind::Const(name, _) = head.kind() {
        let name = name.to_string();
        if is_neg_head(&name) {
            let args = expr.get_app_args();
            let last = args.last()?;
            return expr_to_signed_int(last).and_then(|n| n.checked_neg());
        }
    }

    None
}

fn field_match_binop(op_name: &str, args: &[&Expr]) -> Option<FieldExpr> {
    let nargs = args.len();
    if nargs < 2 {
        return None;
    }

    let left = field_normalize(args[nargs - 2]);
    let right = field_normalize(args[nargs - 1]);

    if is_add_head(op_name) {
        return Some(field_flatten_add(left, right));
    }
    if is_mul_head(op_name) {
        return Some(field_flatten_mul(left, right));
    }
    if is_sub_head(op_name) {
        return Some(field_flatten_add(left, field_negate(right)));
    }
    if is_div_head(op_name) {
        return Some(field_div_expr(left, right));
    }
    if is_pow_head(op_name) {
        let exp = expr_to_signed_int(args[nargs - 1])?;
        return Some(field_pow_signed(left, exp));
    }

    None
}

fn field_match_unop(op_name: &str, args: &[&Expr]) -> Option<FieldExpr> {
    if args.is_empty() {
        return None;
    }

    let last = field_normalize(args[args.len() - 1]);

    if is_neg_head(op_name) {
        return Some(field_negate(last));
    }
    if is_inv_head(op_name) {
        return Some(field_inv_expr(last));
    }
    if op_name == "Nat.succ" {
        return Some(match last {
            FieldExpr::Const(n) => FieldExpr::Const(n + 1),
            other => field_flatten_add(other, FieldExpr::Const(1)),
        });
    }

    None
}

/// Normalize a field expression.
pub(crate) fn field_normalize(expr: &Expr) -> FieldExpr {
    stack_safe(|| {
        let expr = expr.strip_mdata();

        if let Some(value) = nonnegative_ring_const_value(expr) {
            return FieldExpr::Const(value);
        }

        match expr.kind() {
            ExprKind::Const(name, _) => FieldExpr::Var(name.to_string()),
            ExprKind::FVar(id) => FieldExpr::Var(format!("fvar_{}", id.as_u64())),
            ExprKind::App(_, _) => {
                let head = expr.get_app_fn().strip_mdata();
                if let ExprKind::Const(op_name, _) = head.kind() {
                    let op_name = op_name.to_string();
                    let args = expr.get_app_args();
                    if let Some(expr) = field_match_binop(&op_name, &args) {
                        return expr;
                    }
                    if let Some(expr) = field_match_unop(&op_name, &args) {
                        return expr;
                    }
                }
                FieldExpr::Unknown(format!("{expr:?}"))
            }
            _ => FieldExpr::Unknown(format!("{expr:?}")),
        }
    })
}
