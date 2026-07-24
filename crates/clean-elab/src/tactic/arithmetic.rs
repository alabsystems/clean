// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic decision tactics
//!
//! This module contains tactics for automated linear and non-linear arithmetic reasoning:
//! - `linarith`: Linear arithmetic (Fourier-Motzkin elimination)
//! - `nlinarith`: Non-linear arithmetic (polynomial multiplication)
//! - `mathverse`: Integer linear arithmetic (Omega test)
//! - `positivity`: Positivity checking for expressions
//! - `field_simp`: Field simplification
//! - `norm_cast`: Cast normalization
//! - `push_neg`: Negation pushing
//! - `contrapose`: Contraposition tactics
//!
//! Shared types (`LinearExpr`, `LinearConstraint`) live here.
//! Each tactic family is in its own submodule.

use clean_kernel::{BigNat, Expr, ExprKind, Literal};

// ============================================================================
// Shared utility helpers
// ============================================================================

/// Convert a `BigNat` to `i64`, returning `None` on overflow.
///
/// REQUIRES: `n` is a valid `BigNat`
/// ENSURES: Returns `Some(v)` iff `n` fits in `[0, i64::MAX]`
/// ENSURES: Returns `None` for values exceeding `i64::MAX`
pub(crate) fn big_nat_to_i64(n: &BigNat) -> Option<i64> {
    n.to_u64().and_then(|v| i64::try_from(v).ok())
}

/// Extract a `u64` from a natural number literal expression.
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `Some(n)` iff `expr` is `Lit(Nat(n))` and `n` fits in `u64`
/// ENSURES: Returns `None` for non-literal or non-Nat expressions
pub(crate) fn expr_nat_lit_u64(expr: &Expr) -> Option<u64> {
    if let ExprKind::Lit(Literal::Nat(n)) = expr.kind() {
        n.to_u64()
    } else {
        None
    }
}

/// Check if an expression is a specific natural number literal.
///
/// ENSURES: Returns `true` iff `expr` is `Lit(Nat(value))`
pub(crate) fn expr_is_nat_lit(expr: &Expr, value: u64) -> bool {
    expr_nat_lit_u64(expr) == Some(value)
}

// ============================================================================
// Shared types: LinearExpr and LinearConstraint
// ============================================================================

/// A linear expression: c0 + c1*x1 + c2*x2 + ... where ci are rational coefficients
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearExpr {
    /// Constant term
    pub constant: i64,
    /// Coefficients for variables as a sparse sorted `(variable index, coefficient)` list.
    ///
    /// Invariant: entries are sorted by variable index, contain no duplicates,
    /// and never store zero coefficients.
    pub coeffs: Vec<(usize, i64)>,
}

impl LinearExpr {
    fn normalize_coeffs<I>(coeffs: I) -> Vec<(usize, i64)>
    where
        I: IntoIterator<Item = (usize, i64)>,
    {
        let mut coeffs: Vec<_> = coeffs
            .into_iter()
            .filter(|&(_, coeff)| coeff != 0)
            .collect();
        coeffs.sort_by_key(|&(var, _)| var);

        let mut normalized = Vec::with_capacity(coeffs.len());
        for (var, coeff) in coeffs {
            if let Some((last_var, last_coeff)) = normalized.last_mut() {
                if *last_var == var {
                    *last_coeff = coeff;
                    continue;
                }
            }
            normalized.push((var, coeff));
        }
        normalized
    }

    fn coeff_pos(&self, var: usize) -> Result<usize, usize> {
        self.coeffs
            .binary_search_by_key(&var, |&(candidate, _)| candidate)
    }

    /// Get the coefficient for a variable, or 0 if not present.
    pub fn get_coeff(&self, var: usize) -> i64 {
        match self.coeff_pos(var) {
            Ok(idx) => self.coeffs[idx].1,
            Err(_) => 0,
        }
    }

    /// Remove a variable from the coefficient list.
    pub fn remove_var(&mut self, var: usize) {
        if let Ok(idx) = self.coeff_pos(var) {
            self.coeffs.remove(idx);
        }
    }

    fn combine_coeffs<F>(
        lhs: &[(usize, i64)],
        rhs: &[(usize, i64)],
        mut combine: F,
    ) -> Option<Vec<(usize, i64)>>
    where
        F: FnMut(i64, i64) -> Option<i64>,
    {
        let mut result = Vec::with_capacity(lhs.len() + rhs.len());
        let (mut li, mut ri) = (0, 0);

        while li < lhs.len() || ri < rhs.len() {
            match (lhs.get(li), rhs.get(ri)) {
                (Some(&(lvar, lcoeff)), Some(&(rvar, rcoeff))) if lvar == rvar => {
                    let coeff = combine(lcoeff, rcoeff)?;
                    if coeff != 0 {
                        result.push((lvar, coeff));
                    }
                    li += 1;
                    ri += 1;
                }
                (Some(&(lvar, lcoeff)), Some(&(rvar, _))) if lvar < rvar => {
                    let coeff = combine(lcoeff, 0)?;
                    if coeff != 0 {
                        result.push((lvar, coeff));
                    }
                    li += 1;
                }
                (Some(_), Some(&(rvar, rcoeff))) => {
                    let coeff = combine(0, rcoeff)?;
                    if coeff != 0 {
                        result.push((rvar, coeff));
                    }
                    ri += 1;
                }
                (Some(&(lvar, lcoeff)), None) => {
                    let coeff = combine(lcoeff, 0)?;
                    if coeff != 0 {
                        result.push((lvar, coeff));
                    }
                    li += 1;
                }
                (None, Some(&(rvar, rcoeff))) => {
                    let coeff = combine(0, rcoeff)?;
                    if coeff != 0 {
                        result.push((rvar, coeff));
                    }
                    ri += 1;
                }
                (None, None) => break,
            }
        }

        Some(result)
    }

    /// Create a linear expression from sparse coefficients.
    ///
    /// ENSURES: `result.coeffs` is sorted by variable index
    /// ENSURES: Zero coefficients are removed
    /// ENSURES: Duplicate variables keep the last coefficient, matching `BTreeMap` collection semantics
    pub fn from_coeffs<I>(constant: i64, coeffs: I) -> Self
    where
        I: IntoIterator<Item = (usize, i64)>,
    {
        Self {
            constant,
            coeffs: Self::normalize_coeffs(coeffs),
        }
    }

    /// Create a constant linear expression
    ///
    /// ENSURES: `result.is_constant() == true`
    /// ENSURES: `result.constant == c`
    /// ENSURES: `result.coeffs.is_empty()`
    pub fn constant(c: i64) -> Self {
        Self {
            constant: c,
            coeffs: Vec::new(),
        }
    }

    /// Create a variable linear expression (coefficient 1)
    ///
    /// ENSURES: `result.constant == 0`
    /// ENSURES: `result.coeffs[idx] == 1`
    /// ENSURES: `result.coeffs.len() == 1`
    pub fn var(idx: usize) -> Self {
        Self {
            constant: 0,
            coeffs: vec![(idx, 1)],
        }
    }

    /// Get the coefficient of a variable, or zero when absent.
    ///
    /// ENSURES: Returns the unique coefficient stored for `var`, or `0` if absent
    pub fn coeff(&self, var: usize) -> i64 {
        self.coeff_ref(var).copied().unwrap_or(0)
    }

    /// Get a shared reference to a variable coefficient.
    ///
    /// ENSURES: Returns `Some(&c)` iff `self` contains variable `var` with coefficient `c`
    pub fn coeff_ref(&self, var: usize) -> Option<&i64> {
        self.coeff_pos(var).ok().map(|idx| &self.coeffs[idx].1)
    }

    /// Insert, update, or remove a coefficient while maintaining sorted order.
    ///
    /// ENSURES: `self.coeffs` remains sorted, unique, and zero-free
    pub fn set_coeff(&mut self, var: usize, coeff: i64) {
        match self.coeff_pos(var) {
            Ok(idx) if coeff == 0 => {
                self.coeffs.remove(idx);
            }
            Ok(idx) => {
                self.coeffs[idx].1 = coeff;
            }
            Err(idx) if coeff != 0 => {
                self.coeffs.insert(idx, (var, coeff));
            }
            Err(_) => {}
        }
    }

    /// Remove a coefficient by variable index.
    ///
    /// ENSURES: Returns the removed coefficient when present
    /// ENSURES: `self.coeffs` remains sorted and unique
    pub fn remove_coeff(&mut self, var: usize) -> Option<i64> {
        self.coeff_pos(var)
            .ok()
            .map(|idx| self.coeffs.remove(idx).1)
    }

    /// Add to a single coefficient, returning `None` on overflow.
    ///
    /// ENSURES: On `Some(())`, `self[var]` increases by `delta`
    /// ENSURES: Zero coefficients are removed
    pub fn try_add_to_coeff(&mut self, var: usize, delta: i64) -> Option<()> {
        let next = self.coeff(var).checked_add(delta)?;
        self.set_coeff(var, next);
        Some(())
    }

    /// Return the only variable term, when the expression is one-hot.
    ///
    /// ENSURES: Returns `Some((var, coeff))` iff `self.coeffs.len() == 1`
    pub fn single_term(&self) -> Option<(usize, i64)> {
        match self.coeffs.as_slice() {
            &[(var, coeff)] => Some((var, coeff)),
            _ => None,
        }
    }

    /// Add two linear expressions.
    ///
    /// Uses saturating arithmetic to prevent silent wrapping in release mode.
    ///
    /// ENSURES: `result.constant == self.constant +_sat other.constant`
    /// ENSURES: For each variable `v`, `result.coeffs[v] == self.coeffs[v] +_sat other.coeffs[v]`
    /// ENSURES: Zero coefficients are removed from the result
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self {
            constant: self.constant.saturating_add(other.constant),
            coeffs: Self::combine_coeffs(&self.coeffs, &other.coeffs, |lhs, rhs| {
                Some(lhs.saturating_add(rhs))
            })
            .expect("saturating coefficient merge cannot fail"),
        }
    }

    /// Subtract: self - other.
    ///
    /// Uses saturating arithmetic to prevent silent wrapping in release mode.
    ///
    /// ENSURES: `result.constant == self.constant -_sat other.constant`
    /// ENSURES: For each variable `v`, `result.coeffs[v] == self.coeffs[v] -_sat other.coeffs[v]`
    /// ENSURES: Zero coefficients are removed from the result
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        Self {
            constant: self.constant.saturating_sub(other.constant),
            coeffs: Self::combine_coeffs(&self.coeffs, &other.coeffs, |lhs, rhs| {
                Some(lhs.saturating_sub(rhs))
            })
            .expect("saturating coefficient merge cannot fail"),
        }
    }

    /// Multiply by a scalar
    ///
    /// ENSURES: When `k == 0`, returns `LinearExpr::constant(0)`
    /// ENSURES: `result.constant == self.constant *_sat k`
    /// ENSURES: For each variable `v`, `result.coeffs[v] == self.coeffs[v] *_sat k`
    /// ENSURES: Zero coefficients are removed from the result
    #[must_use]
    pub fn scale(&self, k: i64) -> Self {
        if k == 0 {
            return Self::constant(0);
        }
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for &(var, coeff) in &self.coeffs {
            let new_coeff = coeff.saturating_mul(k);
            if new_coeff != 0 {
                coeffs.push((var, new_coeff));
            }
        }
        Self {
            constant: self.constant.saturating_mul(k),
            coeffs,
        }
    }

    /// Multiply by a scalar, returning `None` on overflow.
    ///
    /// Used in certified Fourier-Motzkin where silent wrapping would produce
    /// incorrect Farkas certificates and potentially unsound proofs.
    ///
    /// ENSURES: Returns `None` if any coefficient or constant overflows `i64` on multiplication
    /// ENSURES: On `Some`, result is exact (no saturation or wrapping)
    pub fn try_scale(&self, k: i64) -> Option<Self> {
        if k == 0 {
            return Some(Self::constant(0));
        }
        let constant = self.constant.checked_mul(k)?;
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for &(var, coeff) in &self.coeffs {
            let new_coeff = coeff.checked_mul(k)?;
            if new_coeff != 0 {
                coeffs.push((var, new_coeff));
            }
        }
        Some(Self { constant, coeffs })
    }

    /// Subtract: self - other, returning `None` on overflow.
    ///
    /// ENSURES: Returns `None` if any coefficient or constant overflows `i64` on subtraction
    /// ENSURES: On `Some`, result is exact (no saturation or wrapping)
    pub fn try_sub(&self, other: &Self) -> Option<Self> {
        Some(Self {
            constant: self.constant.checked_sub(other.constant)?,
            coeffs: Self::combine_coeffs(&self.coeffs, &other.coeffs, i64::checked_sub)?,
        })
    }

    /// Substitute a variable with another linear expression.
    ///
    /// Uses saturating arithmetic to match the rest of the non-certified arithmetic path.
    ///
    /// ENSURES: Replaces every occurrence of `var` with `replacement`
    /// ENSURES: The result remains sparse, sorted, and zero-free
    #[must_use]
    pub fn substitute(&self, var: usize, replacement: &Self) -> Self {
        let coeff = self.coeff(var);
        if coeff == 0 {
            return self.clone();
        }

        let mut result = self.clone();
        result.remove_coeff(var);
        result.add(&replacement.scale(coeff))
    }

    /// Evaluate a linear expression with a sparse sorted assignment vector.
    ///
    /// REQUIRES: `values` is sorted by variable index and contains at most one entry per variable
    /// ENSURES: Returns `Some(total)` iff every variable in `self` has an assignment and no arithmetic overflows
    /// ENSURES: Returns `None` when a variable is missing or evaluation overflows `i64`
    pub fn evaluate(&self, values: &[(usize, i64)]) -> Option<i64> {
        let mut total = self.constant;
        for &(var, coeff) in &self.coeffs {
            let value = values
                .binary_search_by_key(&var, |&(candidate, _)| candidate)
                .ok()
                .map(|idx| values[idx].1)?;
            total = total.checked_add(coeff.checked_mul(value)?)?;
        }
        Some(total)
    }

    /// Check if this is a constant (no variables)
    ///
    /// ENSURES: Returns `true` iff `self.coeffs` is empty (no variable terms)
    pub fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Get all variables used
    ///
    /// ENSURES: Returns the sorted set of variable indices with non-zero coefficients
    /// ENSURES: `result.is_empty()` iff `self.is_constant()`
    pub fn variables(&self) -> Vec<usize> {
        self.coeffs.iter().map(|&(var, _)| var).collect()
    }
}

/// A linear constraint: expr ≤ 0, expr < 0, expr = 0, expr ≠ 0, or modular
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinearConstraint {
    /// expr ≤ 0
    Le(LinearExpr),
    /// expr < 0
    Lt(LinearExpr),
    /// expr = 0
    Eq(LinearExpr),
    /// expr ≠ 0 (disequality)
    Ne(LinearExpr),
    /// expr ≡ 0 (mod modulus), where expr encodes var - remainder
    Mod { expr: LinearExpr, modulus: i64 },
    /// ¬(modulus ∣ expr), i.e., expr % modulus ≠ 0
    NotMod { expr: LinearExpr, modulus: i64 },
}

impl LinearConstraint {
    /// Negate a constraint (for proof by contradiction)
    ///
    /// ENSURES: `self.negate().negate()` is logically equivalent to `self`
    /// ENSURES: Le ↔ Lt, Eq ↔ Ne, Mod ↔ NotMod (with negated expression for Le/Lt)
    #[must_use]
    pub fn negate(&self) -> Self {
        match self {
            // ¬(e ≤ 0) ≡ e > 0 ≡ -e < 0
            LinearConstraint::Le(e) => LinearConstraint::Lt(e.scale(-1)),
            // ¬(e < 0) ≡ e ≥ 0 ≡ -e ≤ 0
            LinearConstraint::Lt(e) => LinearConstraint::Le(e.scale(-1)),
            // ¬(e = 0) ≡ e ≠ 0
            LinearConstraint::Eq(e) => LinearConstraint::Ne(e.clone()),
            // ¬(e ≠ 0) ≡ e = 0
            LinearConstraint::Ne(e) => LinearConstraint::Eq(e.clone()),
            // ¬(e ≡ 0 (mod m)) ≡ m ∤ e
            LinearConstraint::Mod { expr, modulus } => LinearConstraint::NotMod {
                expr: expr.clone(),
                modulus: *modulus,
            },
            // ¬(m ∤ e) ≡ e ≡ 0 (mod m)
            LinearConstraint::NotMod { expr, modulus } => LinearConstraint::Mod {
                expr: expr.clone(),
                modulus: *modulus,
            },
        }
    }

    /// Get the linear expression
    ///
    /// ENSURES: Returns the inner `LinearExpr` regardless of constraint kind
    pub fn expr(&self) -> &LinearExpr {
        match self {
            LinearConstraint::Le(e)
            | LinearConstraint::Lt(e)
            | LinearConstraint::Eq(e)
            | LinearConstraint::Ne(e)
            | LinearConstraint::Mod { expr: e, .. }
            | LinearConstraint::NotMod { expr: e, .. } => e,
        }
    }

    /// Check if constraint is trivially satisfied (e.g., -5 ≤ 0)
    ///
    /// REQUIRES: constraint is well-formed
    /// ENSURES: Returns `true` only when `self.expr().is_constant()` and the constant satisfies the constraint
    /// ENSURES: Returns `false` for non-constant expressions (conservative)
    pub fn is_trivially_true(&self) -> bool {
        let e = self.expr();
        if !e.is_constant() {
            return false;
        }
        match self {
            LinearConstraint::Le(_) => e.constant <= 0,
            LinearConstraint::Lt(_) => e.constant < 0,
            LinearConstraint::Eq(_) => e.constant == 0,
            LinearConstraint::Ne(_) => e.constant != 0,
            LinearConstraint::Mod { modulus, .. } => e.constant % modulus == 0,
            LinearConstraint::NotMod { modulus, .. } => e.constant % modulus != 0,
        }
    }

    /// Check if constraint is trivially unsatisfiable (e.g., 5 ≤ 0)
    ///
    /// REQUIRES: constraint is well-formed
    /// ENSURES: Returns `true` only when `self.expr().is_constant()` and the constant violates the constraint
    /// ENSURES: Returns `false` for non-constant expressions (conservative)
    pub fn is_trivially_false(&self) -> bool {
        let e = self.expr();
        if !e.is_constant() {
            return false;
        }
        match self {
            LinearConstraint::Le(_) => e.constant > 0,
            LinearConstraint::Lt(_) => e.constant >= 0,
            LinearConstraint::Eq(_) => e.constant != 0,
            LinearConstraint::Ne(_) => e.constant == 0,
            LinearConstraint::Mod { modulus, .. } => e.constant % modulus != 0,
            LinearConstraint::NotMod { modulus, .. } => e.constant % modulus == 0,
        }
    }
}
