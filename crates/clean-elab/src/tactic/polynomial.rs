// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial data structures and expression-to-polynomial conversion.
//!
//! Split from `polyrith.rs` (#307). Provides the `Polynomial` type used by
//! the polyrith tactic and any future polynomial-based tactics.

use std::collections::HashMap;

use clean_kernel::{BigNat, Expr, ExprKind};

use crate::stack_safe;

fn big_nat_to_i64(n: &BigNat) -> Option<i64> {
    n.to_u64().and_then(|v| i64::try_from(v).ok())
}

fn nat_expr_to_u64(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => n.to_u64(),
        ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => Some(0),
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) if name.to_string() == "Nat.succ" => {
                nat_expr_to_u64(arg)?.checked_add(1)
            }
            _ => None,
        },
        _ => None,
    }
}

fn int_expr_to_i64(expr: &Expr) -> Option<i64> {
    match expr.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Int.zero" => Some(0),
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) => match name.to_string().as_str() {
                "Int.ofNat" => nat_expr_to_u64(arg).and_then(|n| i64::try_from(n).ok()),
                "Int.negSucc" => nat_expr_to_u64(arg)
                    .and_then(|n| i64::try_from(n).ok())
                    .and_then(|n| n.checked_add(1))
                    .and_then(|n| n.checked_neg()),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn parse_rat_of_int_constant(expr: &Expr) -> Option<i64> {
    let ExprKind::App(f, arg) = expr.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = f.kind() else {
        return None;
    };
    (name.to_string() == "Rat.ofInt")
        .then(|| int_expr_to_i64(arg))
        .flatten()
}

fn parse_rat_inv_of_int_constant(expr: &Expr) -> Option<i64> {
    let ExprKind::App(f, arg) = expr.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = f.kind() else {
        return None;
    };
    (name.to_string() == "Rat.inv")
        .then(|| parse_rat_of_int_constant(arg))
        .flatten()
}

fn normalize_constant_fraction(num: i64, den: i64) -> Option<Polynomial> {
    if den == 0 {
        return None;
    }

    let mut normalized_num = i128::from(num);
    let mut normalized_den = i128::from(den);
    if normalized_den < 0 {
        normalized_num = normalized_num.checked_neg()?;
        normalized_den = normalized_den.checked_neg()?;
    }

    let normalized_den = u128::try_from(normalized_den).ok()?;
    let gcd = gcd_u128(normalized_num.unsigned_abs(), normalized_den);
    let normalized_num = normalized_num.checked_div(i128::try_from(gcd).ok()?)?;
    let normalized_den = normalized_den / gcd;

    Some(Polynomial::constant(
        i64::try_from(normalized_num).ok()?,
        u64::try_from(normalized_den).ok()?,
    ))
}

fn parse_rat_constant_fraction(expr: &Expr) -> Option<Polynomial> {
    let ExprKind::App(f, arg2) = expr.kind() else {
        return None;
    };
    let ExprKind::App(op, arg1) = f.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = op.kind() else {
        return None;
    };

    match name.to_string().as_str() {
        "Rat.div" => {
            let num = parse_rat_of_int_constant(arg1)?;
            let den = parse_rat_of_int_constant(arg2)?;
            normalize_constant_fraction(num, den)
        }
        "Rat.mul" => {
            let num = parse_rat_of_int_constant(arg1)?;
            let den = parse_rat_inv_of_int_constant(arg2)?;
            normalize_constant_fraction(num, den)
        }
        _ => None,
    }
}

fn parse_scalar_coercion(expr: &Expr) -> Option<Polynomial> {
    if let Some(poly) = parse_rat_constant_fraction(expr) {
        return Some(poly);
    }

    let ExprKind::App(f, arg) = expr.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = f.kind() else {
        return None;
    };
    match name.to_string().as_str() {
        "Rat.ofInt" | "Real.ofInt" => {
            int_expr_to_i64(arg).map(|value| Polynomial::constant(value, 1))
        }
        "Real.ofNat" => nat_expr_to_u64(arg)
            .and_then(|value| i64::try_from(value).ok())
            .map(|value| Polynomial::constant(value, 1)),
        _ => None,
    }
}

/// A monomial represented as variable indices with exponents
pub(crate) type Monomial = Vec<(usize, u64)>;
/// A rational coefficient as (numerator, denominator)
pub(crate) type Coefficient = (i64, u64);
/// A polynomial over multiple variables with rational coefficients.
/// Represented as a map from monomial (variable exponent vectors) to coefficient.
///
/// Uses HashMap for O(1) monomial lookup (#2042 F1).
///
/// REQUIRES: denominators in coefficients are always > 0
/// ENSURES: `is_zero()` is true iff all coefficients are zero or terms is empty
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial {
    /// Terms: maps variable exponent vectors to coefficients
    pub(crate) terms: HashMap<Monomial, Coefficient>,
}

impl Polynomial {
    /// Create a zero polynomial
    pub fn zero() -> Self {
        Polynomial {
            terms: HashMap::new(),
        }
    }

    /// Create a constant polynomial
    ///
    /// REQUIRES: `d > 0`
    /// ENSURES: if `n == 0`, result is zero polynomial
    pub fn constant(n: i64, d: u64) -> Self {
        if n == 0 {
            Polynomial::zero()
        } else {
            let mut terms = HashMap::with_capacity(1);
            terms.insert(vec![], (n, d));
            Polynomial { terms }
        }
    }

    /// Create a polynomial representing a single variable: x_i
    pub fn var(i: usize) -> Self {
        let mut terms = HashMap::with_capacity(1);
        terms.insert(vec![(i, 1)], (1, 1));
        Polynomial { terms }
    }

    /// Add two polynomials — O(n+m) via HashMap lookup (#2042 F1).
    ///
    /// ENSURES: result contains no zero-coefficient terms
    #[must_use]
    pub fn add(&self, other: &Polynomial) -> Polynomial {
        let mut result = self.terms.clone();

        for (mono, coef) in &other.terms {
            match result.entry(mono.clone()) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let (n1, d1) = *entry.get();
                    let (n2, d2) = *coef;
                    let new_num = n1 * (d2 as i64) + n2 * (d1 as i64);
                    let new_den = d1 * d2;
                    let g = gcd_u64(new_num.unsigned_abs(), new_den);
                    if new_num == 0 {
                        entry.remove();
                    } else {
                        *entry.get_mut() = (new_num / (g as i64), new_den / g);
                    }
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(*coef);
                }
            }
        }

        Polynomial { terms: result }
    }

    /// Subtract two polynomials
    #[must_use]
    pub fn sub(&self, other: &Polynomial) -> Polynomial {
        self.add(&other.negate())
    }

    /// Negate a polynomial
    #[must_use]
    pub fn negate(&self) -> Polynomial {
        Polynomial {
            terms: self
                .terms
                .iter()
                .map(|(m, (n, d))| (m.clone(), (-n, *d)))
                .collect(),
        }
    }

    /// Multiply two polynomials
    #[must_use]
    pub fn mul(&self, other: &Polynomial) -> Polynomial {
        let mut result = Polynomial::zero();

        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                // Multiply coefficients
                let new_num = c1.0 * c2.0;
                let new_den = c1.1 * c2.1;
                let g = gcd_u64(new_num.unsigned_abs(), new_den);
                let coef = (new_num / (g as i64), new_den / g);

                // Multiply monomials (add exponents) by merging sorted lists
                let new_mono = merge_monomials(m1, m2);

                // Insert directly into result map
                match result.terms.entry(new_mono) {
                    std::collections::hash_map::Entry::Occupied(mut entry) => {
                        let (n1, d1) = *entry.get();
                        let sum_num = n1 * (coef.1 as i64) + coef.0 * (d1 as i64);
                        let sum_den = d1 * coef.1;
                        let sg = gcd_u64(sum_num.unsigned_abs(), sum_den);
                        if sum_num == 0 {
                            entry.remove();
                        } else {
                            *entry.get_mut() = (sum_num / (sg as i64), sum_den / sg);
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        if coef.0 != 0 {
                            entry.insert(coef);
                        }
                    }
                }
            }
        }

        result
    }

    /// Raise a polynomial to a natural-number power.
    #[must_use]
    pub fn pow(&self, exp: u64) -> Polynomial {
        if exp == 0 {
            return Polynomial::constant(1, 1);
        }
        if exp == 1 {
            return self.clone();
        }

        let mut result = Polynomial::constant(1, 1);
        let mut base = self.clone();
        let mut exp = exp;
        while exp > 0 {
            if exp & 1 == 1 {
                result = result.mul(&base);
            }
            exp >>= 1;
            if exp > 0 {
                base = base.mul(&base);
            }
        }
        result
    }

    /// Check if polynomial is zero
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty() || self.terms.values().all(|(n, _)| *n == 0)
    }

    /// Extract constant rational coefficient `(numerator, denominator)` if this
    /// polynomial is a true constant (no variables). Returns `None` for polynomials
    /// with variable terms or coefficients that overflow the current `(i64, u64)`
    /// representation.
    ///
    /// ENSURES: On `Some((n, d))`, `self` represents the constant `n/d` with `d > 0`
    /// ENSURES: On `None`, `self` has at least one variable term or an intermediate
    ///          sum/product exceeded the supported coefficient width
    pub(crate) fn as_constant_coeff(&self) -> Option<(i64, u64)> {
        if self.is_zero() {
            return Some((0, 1));
        }
        // All terms must have empty monomial (no variables)
        for mono in self.terms.keys() {
            if !mono.is_empty() {
                return None;
            }
        }
        // Sum all constant terms (should be at most one after normalization)
        let mut num: i128 = 0;
        let mut den: u128 = 1;
        for (n, d) in self.terms.values() {
            // num/den + n/d = (num*d + n*den) / (den*d)
            let next_num = num
                .checked_mul(i128::from(*d))?
                .checked_add(i128::from(*n).checked_mul(i128::try_from(den).ok()?)?)?;
            let next_den = den.checked_mul(u128::from(*d))?;
            let g = gcd_u128(next_num.unsigned_abs(), next_den);
            if g > 0 {
                num = next_num.checked_div(i128::try_from(g).ok()?)?;
                den = next_den / g;
            } else {
                num = next_num;
                den = next_den;
            }
        }
        Some((i64::try_from(num).ok()?, u64::try_from(den).ok()?))
    }

    /// Evaluate degree (total degree of highest monomial)
    pub fn degree(&self) -> u64 {
        self.terms
            .keys()
            .map(|m| m.iter().map(|(_, e)| e).sum::<u64>())
            .max()
            .unwrap_or(0)
    }
}

/// Merge two sorted monomials by adding exponents for matching variables.
fn merge_monomials(m1: &[(usize, u64)], m2: &[(usize, u64)]) -> Monomial {
    let mut result = Vec::with_capacity(m1.len() + m2.len());
    let mut i = 0;
    let mut j = 0;
    while i < m1.len() && j < m2.len() {
        if m1[i].0 < m2[j].0 {
            result.push(m1[i]);
            i += 1;
        } else if m1[i].0 > m2[j].0 {
            result.push(m2[j]);
            j += 1;
        } else {
            result.push((m1[i].0, m1[i].1 + m2[j].1));
            i += 1;
            j += 1;
        }
    }
    result.extend_from_slice(&m1[i..]);
    result.extend_from_slice(&m2[j..]);
    result
}

/// GCD for u64
pub(crate) fn gcd_u64(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd_u64(b, a % b)
    }
}

pub(crate) fn gcd_u128(a: u128, b: u128) -> u128 {
    if b == 0 {
        a
    } else {
        gcd_u128(b, a % b)
    }
}

/// Variable interning map with O(1) lookup (#2042 F2).
///
/// Wraps a Vec (for index→name) and HashMap (for name→index) to provide
/// O(1) amortized variable interning instead of O(V) linear scan.
pub(crate) struct VarMap {
    names: Vec<String>,
    index: HashMap<String, usize>,
}

impl VarMap {
    pub(crate) fn new() -> Self {
        VarMap {
            names: Vec::new(),
            index: HashMap::new(),
        }
    }

    pub(crate) fn name(&self, idx: usize) -> Option<&str> {
        self.names.get(idx).map(String::as_str)
    }

    fn intern(&mut self, name: String) -> usize {
        if let Some(&idx) = self.index.get(&name) {
            idx
        } else {
            let idx = self.names.len();
            self.index.insert(name.clone(), idx);
            self.names.push(name);
            idx
        }
    }
}

fn intern_polynomial_var(name: String, var_map: &mut VarMap) -> Polynomial {
    Polynomial::var(var_map.intern(name))
}

fn parse_binary_polynomial_app(f: &Expr, arg: &Expr, var_map: &mut VarMap) -> Option<Polynomial> {
    let ExprKind::App(f2, arg1) = f.kind() else {
        return None;
    };
    let (op, _) = extract_binary_op(f2)?;
    let p1 = expr_to_polynomial(arg1, var_map)?;
    let p2 = expr_to_polynomial(arg, var_map)?;
    match op.as_str() {
        "HAdd.hAdd" | "Nat.add" | "Int.add" | "Rat.add" | "Real.add" | "Add.add" => {
            Some(p1.add(&p2))
        }
        "HSub.hSub" | "Nat.sub" | "Int.sub" | "Rat.sub" | "Real.sub" | "Sub.sub" => {
            Some(p1.sub(&p2))
        }
        "HMul.hMul" | "Nat.mul" | "Int.mul" | "Rat.mul" | "Real.mul" | "Mul.mul" => {
            Some(p1.mul(&p2))
        }
        "HPow.hPow" | "Nat.pow" | "Int.pow" | "Pow.pow" => {
            nat_expr_to_u64(arg).map(|exp| p1.pow(exp))
        }
        _ => None,
    }
}

fn parse_negated_polynomial(f: &Expr, arg: &Expr, var_map: &mut VarMap) -> Option<Polynomial> {
    let ExprKind::App(f2, inner) = f.kind() else {
        return None;
    };
    if matches!(f2.kind(), ExprKind::Const(name, _) if name.to_string() == "Neg.neg") {
        return expr_to_polynomial(arg, var_map).map(|p| p.negate());
    }
    expr_to_polynomial(inner, var_map)
}

/// Convert an expression to a polynomial (if possible).
/// Returns `Some(polynomial)` using `var_map` to assign indices to variables.
///
/// REQUIRES: `var_map` may be pre-populated with existing variable names
/// ENSURES: new variables encountered are appended to `var_map`
/// ENSURES: On None, expression could not be interpreted as a polynomial
pub(crate) fn expr_to_polynomial(expr: &Expr, var_map: &mut VarMap) -> Option<Polynomial> {
    stack_safe(|| {
        if let Some(value) = int_expr_to_i64(expr) {
            return Some(Polynomial::constant(value, 1));
        }
        if let Some(poly) = parse_scalar_coercion(expr) {
            return Some(poly);
        }

        match expr.kind() {
            ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => {
                big_nat_to_i64(n).map(|value| Polynomial::constant(value, 1))
            }
            ExprKind::FVar(fvar) => {
                let name = format!("fvar_{}", fvar.as_u64());
                Some(intern_polynomial_var(name, var_map))
            }
            ExprKind::Const(name, _) => {
                let name_str = name.to_string();
                if name_str == "Nat.zero" {
                    Some(Polynomial::constant(0, 1))
                } else {
                    Some(intern_polynomial_var(name_str, var_map))
                }
            }
            ExprKind::App(f, arg) => parse_binary_polynomial_app(f, arg, var_map)
                .or_else(|| parse_negated_polynomial(f, arg, var_map)),
            _ => None,
        }
    })
}

/// Extract binary operation name from nested application
pub(crate) fn extract_binary_op(expr: &Expr) -> Option<(String, Vec<Expr>)> {
    let mut args = Vec::new();
    let mut current = expr;

    while let ExprKind::App(f, arg) = current.kind() {
        args.push(arg.as_ref().clone());
        current = f;
    }

    if let ExprKind::Const(name, _) = current.kind() {
        Some((name.to_string(), args))
    } else {
        None
    }
}
