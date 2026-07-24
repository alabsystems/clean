// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Executable Boolean Fourier Analysis
//!
//! Boolean Fourier analysis represents functions f: {-1,1}^n -> R in the
//! Fourier basis {chi_S}_{S subset [n]}, where chi_S(x) = prod_{i in S} x_i.
//!
//! Every such function has a unique multilinear expansion:
//!   f(x) = Sum_S f_hat(S) chi_S(x)
//!
//! This module provides executable verification of:
//! - Parseval's identity (S41): Sum_S f_hat(S)^2 = E[f^2]
//! - Influence identity (S42): Inf_i(f) = Sum_{S containing i} f_hat(S)^2
//!
//! ## References
//!
//! R. O'Donnell, *Analysis of Boolean Functions*, Cambridge, 2014, Ch. 1-2.

use thiserror::Error;

/// Maximum number of variables supported (truth table = 2^n entries).
const MAX_VARS: usize = 16;

/// Tolerance for floating-point identity checks.
const EPSILON: f64 = 1e-10;

/// Errors from Boolean Fourier analysis operations.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum FourierError {
    /// Number of variables exceeds the supported limit.
    #[error("variable count {0} exceeds maximum {MAX_VARS}")]
    TooManyVariables(usize),

    /// Truth table length does not match 2^n.
    #[error("truth table length {got} does not match 2^{n} = {expected}")]
    BadTableLength {
        n: usize,
        expected: usize,
        got: usize,
    },

    /// Variable index out of range.
    #[error("variable index {index} out of range for {n}-variable function")]
    VariableOutOfRange { index: usize, n: usize },

    /// Subset bitmask references variables beyond n.
    #[error("subset 0x{subset:x} references bits beyond {n} variables")]
    SubsetOutOfRange { subset: u32, n: usize },

    /// Parseval identity verification failed.
    #[error(
        "Parseval identity failed: sum of f_hat(S)^2 = {fourier_sum}, \
         E[f^2] = {expectation}, diff = {diff}"
    )]
    ParsevalFailed {
        fourier_sum: f64,
        expectation: f64,
        diff: f64,
    },

    /// Influence-Fourier identity verification failed.
    #[error(
        "Influence-Fourier identity failed for variable {variable}: \
         combinatorial = {combinatorial}, Fourier = {fourier}, diff = {diff}"
    )]
    InfluenceFourierFailed {
        variable: usize,
        combinatorial: f64,
        fourier: f64,
        diff: f64,
    },
}

/// A Boolean function f: {-1,1}^n -> R stored as a truth table.
///
/// The truth table has 2^n entries indexed by the binary representation
/// of the assignment x in {0,1}^n (mapped to {-1,1}^n via x_i -> (-1)^{b_i}).
/// Index bits: bit 0 = variable 0, bit 1 = variable 1, etc.
#[derive(Debug, Clone, PartialEq)]
pub struct BooleanFunction {
    /// Number of variables.
    n: usize,
    /// Truth table: `values[x]` = f(x) for x in 0..2^n.
    values: Vec<f64>,
}

impl BooleanFunction {
    /// Number of variables.
    #[must_use]
    pub fn num_vars(&self) -> usize {
        self.n
    }

    /// The truth table values.
    #[must_use]
    pub fn values(&self) -> &[f64] {
        &self.values
    }

    /// Construct from an explicit truth table.
    ///
    /// `table` must have length 2^n for some n <= [`MAX_VARS`].
    pub fn from_truth_table(table: &[f64]) -> Result<Self, FourierError> {
        let len = table.len();
        if len == 0 || (len & (len - 1)) != 0 {
            let n = (usize::BITS - len.leading_zeros()) as usize;
            return Err(FourierError::BadTableLength {
                n,
                expected: 1 << n,
                got: len,
            });
        }
        let n = len.trailing_zeros() as usize;
        if n > MAX_VARS {
            return Err(FourierError::TooManyVariables(n));
        }
        Ok(Self {
            n,
            values: table.to_vec(),
        })
    }

    /// Dictator function on variable `i`: f(x) = x_i.
    ///
    /// In {-1,1} encoding, f(x) = (-1)^{b_i} where b_i is the i-th bit.
    pub fn dictator(i: usize, n: usize) -> Result<Self, FourierError> {
        if n > MAX_VARS {
            return Err(FourierError::TooManyVariables(n));
        }
        if i >= n {
            return Err(FourierError::VariableOutOfRange { index: i, n });
        }
        let size = 1usize << n;
        let values: Vec<f64> = (0..size)
            .map(|x| if (x >> i) & 1 == 0 { 1.0 } else { -1.0 })
            .collect();
        Ok(Self { n, values })
    }

    /// Parity function: f(x) = x_1 * x_2 * ... * x_n = chi_{[n]}(x).
    pub fn parity(n: usize) -> Result<Self, FourierError> {
        if n > MAX_VARS {
            return Err(FourierError::TooManyVariables(n));
        }
        let size = 1usize << n;
        let values: Vec<f64> = (0..size)
            .map(|x| {
                let bits_set = (x as u32).count_ones();
                if bits_set.is_multiple_of(2) {
                    1.0
                } else {
                    -1.0
                }
            })
            .collect();
        Ok(Self { n, values })
    }

    /// Majority function for odd n: f(x) = sign(sum x_i).
    ///
    /// For even n, ties (sum = 0) map to +1.
    pub fn majority(n: usize) -> Result<Self, FourierError> {
        if n > MAX_VARS {
            return Err(FourierError::TooManyVariables(n));
        }
        let size = 1usize << n;
        let values: Vec<f64> = (0..size)
            .map(|x| {
                let ones = (x as u32).count_ones() as i32;
                let sum = (n as i32) - 2 * ones;
                if sum >= 0 {
                    1.0
                } else {
                    -1.0
                }
            })
            .collect();
        Ok(Self { n, values })
    }

    /// Constant function: f(x) = c for all x.
    pub fn constant(c: f64, n: usize) -> Result<Self, FourierError> {
        if n > MAX_VARS {
            return Err(FourierError::TooManyVariables(n));
        }
        let size = 1usize << n;
        Ok(Self {
            n,
            values: vec![c; size],
        })
    }

    /// AND of the first two variables in {-1,1} encoding.
    ///
    /// f(x) = 1 iff both x_0 = +1 and x_1 = +1 (both bits 0), else -1.
    pub fn and2(n: usize) -> Result<Self, FourierError> {
        if n < 2 {
            return Err(FourierError::VariableOutOfRange { index: 1, n });
        }
        if n > MAX_VARS {
            return Err(FourierError::TooManyVariables(n));
        }
        let size = 1usize << n;
        let values: Vec<f64> = (0..size)
            .map(|x| if (x & 0b11) == 0 { 1.0 } else { -1.0 })
            .collect();
        Ok(Self { n, values })
    }

    /// OR of the first two variables in {-1,1} encoding.
    ///
    /// f(x) = -1 only when both x_0 = -1 and x_1 = -1, else +1.
    pub fn or2(n: usize) -> Result<Self, FourierError> {
        if n < 2 {
            return Err(FourierError::VariableOutOfRange { index: 1, n });
        }
        if n > MAX_VARS {
            return Err(FourierError::TooManyVariables(n));
        }
        let size = 1usize << n;
        let values: Vec<f64> = (0..size)
            .map(|x| if (x & 0b11) == 0b11 { -1.0 } else { 1.0 })
            .collect();
        Ok(Self { n, values })
    }
}

// ---------------------------------------------------------------------------
// Fourier analysis core
// ---------------------------------------------------------------------------

/// Character function chi_S(x) = prod_{i in S} x_i.
///
/// `subset` is a bitmask where bit i means variable i is in S.
/// `assignment` is a bitmask of the input x in {0,1}^n (bit=1 means x_i = -1).
///
/// chi_S(x) = (-1)^{popcount(subset & assignment)}.
#[must_use]
pub fn chi(subset: u32, assignment: u32) -> f64 {
    let parity = (subset & assignment).count_ones();
    if parity.is_multiple_of(2) {
        1.0
    } else {
        -1.0
    }
}

/// Compute a single Fourier coefficient f_hat(S).
///
/// f_hat(S) = 2^{-n} Sum_{x in {0,1}^n} f(x) chi_S(x)
pub fn fourier_coefficient(f: &BooleanFunction, subset: u32) -> Result<f64, FourierError> {
    let n = f.num_vars();
    if subset >= (1u32 << n) {
        return Err(FourierError::SubsetOutOfRange { subset, n });
    }
    let size = 1usize << n;
    let inv = 1.0 / (size as f64);
    let sum: f64 = (0..size).map(|x| f.values[x] * chi(subset, x as u32)).sum();
    Ok(sum * inv)
}

/// Compute all 2^n Fourier coefficients of f.
///
/// Returns a vector indexed by subset bitmask.
pub fn compute_all_fourier(f: &BooleanFunction) -> Result<Vec<f64>, FourierError> {
    let n = f.num_vars();
    let size = 1usize << n;
    let mut coeffs = Vec::with_capacity(size);
    for s in 0..size {
        coeffs.push(fourier_coefficient(f, s as u32)?);
    }
    Ok(coeffs)
}

/// Verify Parseval's identity (S41): Sum_S f_hat(S)^2 = E[f^2].
///
/// Returns `Ok(())` if the identity holds within floating-point tolerance.
pub fn verify_parseval(f: &BooleanFunction) -> Result<(), FourierError> {
    let coeffs = compute_all_fourier(f)?;
    let fourier_sum: f64 = coeffs.iter().map(|c| c * c).sum();

    let size = f.values.len();
    let expectation: f64 = f.values.iter().map(|v| v * v).sum::<f64>() / (size as f64);

    let diff = (fourier_sum - expectation).abs();
    if diff > EPSILON {
        return Err(FourierError::ParsevalFailed {
            fourier_sum,
            expectation,
            diff,
        });
    }
    Ok(())
}

/// Compute the influence of variable i on f.
///
/// For real-valued f: Inf_i(f) = E_x[(f(x) - f(x xor e_i))^2 / 4].
/// For {-1,1}-valued f this equals Pr[f(x) != f(x xor e_i)].
pub fn compute_influence(f: &BooleanFunction, i: usize) -> Result<f64, FourierError> {
    let n = f.num_vars();
    if i >= n {
        return Err(FourierError::VariableOutOfRange { index: i, n });
    }
    let size = 1usize << n;
    let mask = 1usize << i;
    let sum: f64 = (0..size)
        .map(|x| {
            let diff = f.values[x] - f.values[x ^ mask];
            diff * diff
        })
        .sum();
    Ok(sum / (4.0 * size as f64))
}

/// Verify the influence-Fourier identity (S42):
///   Inf_i(f) = Sum_{S containing i} f_hat(S)^2
pub fn verify_influence_fourier(f: &BooleanFunction, i: usize) -> Result<(), FourierError> {
    let n = f.num_vars();
    if i >= n {
        return Err(FourierError::VariableOutOfRange { index: i, n });
    }
    let combinatorial = compute_influence(f, i)?;
    let coeffs = compute_all_fourier(f)?;
    let bit = 1u32 << i;
    let fourier: f64 = coeffs
        .iter()
        .enumerate()
        .filter(|(s, _)| (*s as u32) & bit != 0)
        .map(|(_, c)| c * c)
        .sum();

    let diff = (combinatorial - fourier).abs();
    if diff > EPSILON {
        return Err(FourierError::InfluenceFourierFailed {
            variable: i,
            combinatorial,
            fourier,
            diff,
        });
    }
    Ok(())
}

/// Total influence of f: I(f) = Sum_i Inf_i(f) = Sum_S |S| f_hat(S)^2.
pub fn total_influence(f: &BooleanFunction) -> Result<f64, FourierError> {
    let coeffs = compute_all_fourier(f)?;
    let total: f64 = coeffs
        .iter()
        .enumerate()
        .map(|(s, c)| {
            let weight = (s as u32).count_ones() as f64;
            weight * c * c
        })
        .sum();
    Ok(total)
}
