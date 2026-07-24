// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Converts Farkas certificates into clean Expr proof terms.
//!
//! Given an [`ExternalFarkasCert`] (verified as valid), builds clean kernel
//! `Expr` trees representing the formal proof term for the Farkas lemma
//! application. The generated proof term encodes:
//!
//! ```text
//! theorem farkas_cert :
//!   (∀ x : Fin n → ℝ,
//!     (∀ i, A_in[i] • x ≤ b_in[i]) →
//!     (∀ j, A_out[j] • x ≤ b_out[j]))
//! ```
//!
//! via the Farkas lemma witness: non-negative multipliers `λ` such that
//! `Σ λ_i · A_in[i] = A_out[j]` and `Σ λ_i · b_in[i] ≤ b_out[j]`.
//!
//! Floating-point coefficients are encoded as rational approximations
//! using `Rat.mk` (numerator/denominator pair).

use super::certificate::farkas_bridge::ExternalFarkasCert;
use clean_kernel::{BinderInfo, Expr, Level};
use thiserror::Error;

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from building Expr proof terms from Farkas certificates.
#[derive(Debug, Clone, PartialEq, Error)]
#[non_exhaustive]
pub enum CertExprError {
    /// The certificate has zero input or output dimensions.
    #[error("empty certificate: {context}")]
    EmptyCertificate {
        /// What was empty (e.g., "input_dim", "output_dim").
        context: String,
    },

    /// A coefficient cannot be represented as a rational number.
    #[error("non-finite coefficient at ({row}, {col}): {value}")]
    NonFiniteCoefficient {
        /// Row index.
        row: usize,
        /// Column index.
        col: usize,
        /// The problematic value.
        value: f64,
    },

    /// A bound value is not finite.
    #[error("non-finite bound at index {index}: {value}")]
    NonFiniteBound {
        /// Bound index.
        index: usize,
        /// The problematic value.
        value: f64,
    },
}

// ---------------------------------------------------------------------------
// Rational approximation
// ---------------------------------------------------------------------------

/// Maximum denominator for rational approximation.
const MAX_DENOMINATOR: u64 = 1_000_000;

/// Approximate a finite f64 as (numerator, denominator) with `denom <= MAX_DENOMINATOR`.
///
/// Uses the continued fraction algorithm for best rational approximation.
pub(crate) fn f64_to_rational(x: f64) -> (i64, u64) {
    if x == 0.0 {
        return (0, 1);
    }

    let negative = x < 0.0;
    let x = x.abs();

    // Special case: integer values.
    if (x - x.round()).abs() < 1e-12 && x.round() < i64::MAX as f64 {
        let n = x.round() as i64;
        return if negative { (-n, 1) } else { (n, 1) };
    }

    let (b_num, b_den) = continued_fraction_search(x);
    let den = if b_den == 0 { 1 } else { b_den };
    if negative {
        (-b_num, den)
    } else {
        (b_num, den)
    }
}

/// Stern-Brocot / continued fraction mediant search.
fn continued_fraction_search(x: f64) -> (i64, u64) {
    let mut a_num: i64 = 0;
    let mut a_den: u64 = 1;
    let mut b_num: i64 = 1;
    let mut b_den: u64 = 0;

    let mut remaining = x;
    for _ in 0..64 {
        let floor = remaining.floor() as u64;
        let new_num = a_num + floor as i64 * b_num;
        let new_den = a_den + floor * b_den;

        if new_den > MAX_DENOMINATOR {
            break;
        }

        a_num = b_num;
        a_den = b_den;
        b_num = new_num;
        b_den = new_den;

        let frac = remaining - floor as f64;
        if frac.abs() < 1e-12 {
            break;
        }
        remaining = 1.0 / frac;

        if remaining > MAX_DENOMINATOR as f64 {
            break;
        }
    }

    (b_num, b_den)
}

// ---------------------------------------------------------------------------
// Expr builders (private helpers)
// ---------------------------------------------------------------------------

/// Build `Real` type.
pub(crate) fn mk_real() -> Expr {
    Expr::const_str("Real")
}

/// Build `Fin n` type.
fn mk_fin(n: u64) -> Expr {
    Expr::app(Expr::const_str("Fin"), Expr::nat_lit(n))
}

/// Build a rational literal as `@Rat.mk num den`.
fn mk_rat_lit(num: i64, den: u64) -> Expr {
    let rat_mk = Expr::const_str("Rat.mk");
    let num_expr = if num >= 0 {
        Expr::app(Expr::const_str("Int.ofNat"), Expr::nat_lit(num as u64))
    } else {
        Expr::app(
            Expr::const_str("Int.negSucc"),
            Expr::nat_lit((-num - 1) as u64),
        )
    };
    Expr::apps(rat_mk, [num_expr, Expr::nat_lit(den)])
}

/// Build `@Real.ofRat r` to embed a rational in Real.
pub(crate) fn mk_real_of_rat(num: i64, den: u64) -> Expr {
    Expr::app(Expr::const_str("Real.ofRat"), mk_rat_lit(num, den))
}

/// Build `@LE.le Real _ a b` (a <= b).
fn mk_le_real(a: Expr, b: Expr) -> Expr {
    let le = Expr::const_str_levels("LE.le", vec![Level::zero()]);
    Expr::apps(le, [mk_real(), Expr::const_str("Real.instLE"), a, b])
}

/// Build a dot product `Σ_k coeffs[k] * x(k)` as an Expr.
fn mk_dot_product(coeffs: &[f64], x_var: Expr) -> Result<Expr, CertExprError> {
    let mut sum: Option<Expr> = None;
    let real_mul = Expr::const_str("HMul.hMul");
    let real_add = Expr::const_str("HAdd.hAdd");

    for (k, &c) in coeffs.iter().enumerate() {
        if !c.is_finite() {
            return Err(CertExprError::NonFiniteCoefficient {
                row: 0,
                col: k,
                value: c,
            });
        }
        if c.abs() < 1e-15 {
            continue;
        }
        let (num, den) = f64_to_rational(c);
        let coeff_expr = mk_real_of_rat(num, den);
        let x_k = Expr::app(x_var.clone(), Expr::nat_lit(k as u64));
        let term = Expr::apps(real_mul.clone(), [coeff_expr, x_k]);
        sum = Some(match sum {
            None => term,
            Some(acc) => Expr::apps(real_add.clone(), [acc, term]),
        });
    }

    Ok(sum.unwrap_or_else(|| mk_real_of_rat(0, 1)))
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// A Farkas certificate encoded as clean Expr proof terms.
#[derive(Debug, Clone)]
pub struct FarkasCertExpr {
    /// The proposition type: `forall x, input_constraints x -> output_constraints x`.
    pub prop_type: Expr,
    /// The proof term (lambda encoding the Farkas multiplier witness).
    pub proof_term: Expr,
    /// Number of input constraints.
    pub num_input_constraints: usize,
    /// Number of output constraints.
    pub num_output_constraints: usize,
    /// Input dimension.
    pub input_dim: usize,
    /// Output dimension.
    pub output_dim: usize,
}

/// Build a `FarkasCertExpr` from a verified [`ExternalFarkasCert`].
///
/// # Errors
///
/// Returns [`CertExprError`] if the certificate has zero dimensions or
/// contains non-finite coefficients/bounds.
pub fn farkas_cert_to_expr(cert: &ExternalFarkasCert) -> Result<FarkasCertExpr, CertExprError> {
    validate_cert_finiteness(cert)?;

    let n = cert.input_dim as u64;
    let m_in = cert.input_matrix.len();
    let m_out = cert.output_matrix.len();

    let vec_type = Expr::arrow(mk_fin(n), mk_real());
    let x_var = Expr::bvar(0);

    let input_props = build_constraint_props(&cert.input_matrix, &cert.input_bounds, &x_var)?;
    let output_props = build_constraint_props(&cert.output_matrix, &cert.output_bounds, &x_var)?;

    let input_conj = conjoin_props(&input_props);
    let output_conj = conjoin_props(&output_props);

    let implication = Expr::arrow(input_conj.clone(), output_conj);
    let prop_type = Expr::pi(BinderInfo::Default, vec_type.clone(), implication);

    let witness = build_farkas_witness(cert, m_in, m_out)?;
    let proof_inner = Expr::lam(BinderInfo::Default, input_conj, witness);
    let proof_term = Expr::lam(BinderInfo::Default, vec_type, proof_inner);

    Ok(FarkasCertExpr {
        prop_type,
        proof_term,
        num_input_constraints: m_in,
        num_output_constraints: m_out,
        input_dim: cert.input_dim,
        output_dim: cert.output_dim,
    })
}

/// Validate that a certificate has non-zero dimensions and finite bounds.
fn validate_cert_finiteness(cert: &ExternalFarkasCert) -> Result<(), CertExprError> {
    if cert.input_dim == 0 {
        return Err(CertExprError::EmptyCertificate {
            context: "input_dim is 0".into(),
        });
    }
    if cert.output_dim == 0 {
        return Err(CertExprError::EmptyCertificate {
            context: "output_dim is 0".into(),
        });
    }
    for (i, &b) in cert.input_bounds.iter().enumerate() {
        if !b.is_finite() {
            return Err(CertExprError::NonFiniteBound { index: i, value: b });
        }
    }
    for (i, &b) in cert.output_bounds.iter().enumerate() {
        if !b.is_finite() {
            return Err(CertExprError::NonFiniteBound { index: i, value: b });
        }
    }
    Ok(())
}

/// Build constraint propositions: `A[i] . x <= b[i]` for each row.
fn build_constraint_props(
    matrix: &[Vec<f64>],
    bounds: &[f64],
    x_var: &Expr,
) -> Result<Vec<Expr>, CertExprError> {
    let mut props = Vec::with_capacity(matrix.len());
    for (i, row) in matrix.iter().enumerate() {
        let dot = mk_dot_product(row, x_var.clone())?;
        let (bnum, bden) = f64_to_rational(bounds[i]);
        props.push(mk_le_real(dot, mk_real_of_rat(bnum, bden)));
    }
    Ok(props)
}

/// Build the Farkas witness term encoding multiplier data.
fn build_farkas_witness(
    cert: &ExternalFarkasCert,
    m_in: usize,
    m_out: usize,
) -> Result<Expr, CertExprError> {
    if m_out == 0 {
        return Ok(Expr::const_str("True.intro"));
    }
    let block_size = m_in / m_out;
    let mut witnesses = Vec::with_capacity(m_out);
    for j in 0..m_out {
        let block_start = j * block_size;
        let mult_exprs: Vec<Expr> = (0..block_size)
            .map(|local_i| {
                let (num, den) = f64_to_rational(cert.multipliers[block_start + local_i]);
                mk_real_of_rat(num, den)
            })
            .collect();
        let mult_list = build_list_real(&mult_exprs);
        let witness_j = Expr::apps(
            Expr::const_str("FarkasWitness.mk"),
            [
                Expr::nat_lit(block_size as u64),
                Expr::nat_lit(j as u64),
                mult_list,
            ],
        );
        witnesses.push(witness_j);
    }
    Ok(conjoin_exprs(&witnesses))
}

/// Build `@ListType.cons Real a (ListType.cons b ... ListType.nil)`.
pub(crate) fn build_list_real(elems: &[Expr]) -> Expr {
    let mut list = Expr::app(
        Expr::const_str_levels("ListType.nil", vec![Level::zero()]),
        mk_real(),
    );
    for elem in elems.iter().rev() {
        list = Expr::apps(
            Expr::const_str_levels("ListType.cons", vec![Level::zero()]),
            [mk_real(), elem.clone(), list],
        );
    }
    list
}

/// Build `AndType P1 (AndType P2 ... Pn)` for n propositions.
pub(crate) fn conjoin_props(props: &[Expr]) -> Expr {
    match props.len() {
        0 => Expr::const_str("True"),
        1 => props[0].clone(),
        _ => {
            let mut result = props.last().cloned().expect("non-empty slice");
            for prop in props[..props.len() - 1].iter().rev() {
                result = Expr::apps(
                    Expr::const_str_levels("AndType", vec![]),
                    [prop.clone(), result],
                );
            }
            result
        }
    }
}

/// Build `AndType.intro e1 (AndType.intro e2 ... en)` for n expressions.
fn conjoin_exprs(exprs: &[Expr]) -> Expr {
    match exprs.len() {
        0 => Expr::const_str("True.intro"),
        1 => exprs[0].clone(),
        _ => {
            let mut result = exprs.last().cloned().expect("non-empty slice");
            for expr in exprs[..exprs.len() - 1].iter().rev() {
                result = Expr::apps(Expr::const_str("AndType.intro"), [expr.clone(), result]);
            }
            result
        }
    }
}
