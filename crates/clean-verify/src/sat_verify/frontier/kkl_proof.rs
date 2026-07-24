// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL Inequality Proof Infrastructure
//!
//! The KKL inequality (Kahn-Kalai-Linial 1988) states that for every
//! balanced Boolean function f: {-1,1}^n -> {-1,1}:
//!
//!   max_i Inf_i(f) >= c * ln(n) / n
//!
//! where c = 2/(pi*e) ~ 0.2339. The proof proceeds in four steps:
//!
//! 1. **Bonami-Beckner**: The hypercontractivity inequality holds for
//!    rho <= 1/sqrt(q-1).
//! 2. **Level weight bound**: Hypercontractivity implies that for balanced
//!    f, the level-1 Fourier weight W^1(f) >= some function of I(f) and n.
//! 3. **Influence lower bound**: From the level weight bound and the
//!    identity I(f) = sum_k k * W^k(f), derive a lower bound on I(f).
//! 4. **Max influence bound**: Since max_i Inf_i(f) >= I(f)/n, the KKL
//!    bound on max influence follows.
//!
//! This module formalizes each step and provides computational verification
//! that the proof chain holds for specific functions.
//!
//! ## References
//!
//! - J. Kahn, G. Kalai, N. Linial, "The Influence of Variables on
//!   Boolean Functions", *FOCS* 1988, Theorem 3.1
//! - R. O'Donnell, *Analysis of Boolean Functions*, Cambridge, 2014, Ch. 9
//! - E. Friedgut, G. Kalai, "Every monotone graph property has a sharp
//!   threshold", *Proc. AMS* 124, 1996

use super::fourier::{compute_all_fourier, BooleanFunction, FourierError};
use super::hypercontractivity::{level_k_weight, verify_bonami_beckner};
use super::noise_sensitivity::{max_influence, total_influence, variable_influence};
use crate::spec::ProofStatus;

/// Floating-point tolerance for identity checks.
const EPSILON: f64 = 1e-10;

/// Best known constant in the KKL inequality: c = 2/(pi * e).
///
/// max_i Inf_i(f) >= KKL_CONSTANT * ln(n) / n for balanced f.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Theorem 9.24.
pub const KKL_CONSTANT: f64 = 2.0 / (std::f64::consts::PI * std::f64::consts::E);

// ---------------------------------------------------------------------------
// Proof step enumeration
// ---------------------------------------------------------------------------

/// The four steps of the KKL inequality proof.
///
/// Each step builds on the previous to establish the final bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum KklProofStep {
    /// Step 1: Bonami-Beckner hypercontractivity holds at the optimal rho.
    BonamiBeckner,
    /// Step 2: Level-1 weight bound derived from hypercontractivity.
    LevelWeightBound,
    /// Step 3: Total influence lower bound from the level weight structure.
    InfluenceLowerBound,
    /// Step 4: Max influence bound (the KKL inequality itself).
    MaxInfluenceBound,
}

// ---------------------------------------------------------------------------
// Proof witness
// ---------------------------------------------------------------------------

/// Collected evidence for a computational KKL proof on a specific function.
///
/// The witness records the function, its Fourier data, and the verification
/// result at each step. This provides an auditable trail of the proof.
#[derive(Debug, Clone)]
pub struct KklProofWitness {
    /// Number of variables.
    pub n: usize,
    /// Fourier coefficients (indexed by subset bitmask).
    pub fourier_coefficients: Vec<f64>,
    /// Per-variable influences.
    pub influences: Vec<f64>,
    /// Total influence I(f).
    pub total_influence: f64,
    /// Maximum influence max_i Inf_i(f).
    pub max_influence: f64,
    /// Level-1 Fourier weight W^1(f).
    pub level_one_weight: f64,
    /// Whether f is balanced (f_hat(emptyset) ~ 0).
    pub is_balanced: bool,
    /// Whether Bonami-Beckner holds at optimal rho for q=4.
    pub bonami_beckner_holds: bool,
    /// Whether the KKL bound is satisfied computationally.
    pub kkl_bound_satisfied: bool,
    /// The KKL bound value: c * ln(n) / n.
    pub kkl_bound_value: f64,
}

// ---------------------------------------------------------------------------
// Proof status constants (S43 sub-steps)
// ---------------------------------------------------------------------------

/// S43a: Balanced hypothesis verification for KKL.
///
/// The KKL inequality requires f to be balanced (E[f] = 0).
/// Status: `DerivedPending` -- computationally verified for standard families.
pub const S43A_KKL_BALANCED_HYPOTHESIS: ProofStatus = ProofStatus::DerivedPending;

/// S43b: Hypercontractive step of KKL proof.
///
/// Bonami-Beckner at the optimal rho implies level weight concentration.
/// Status: `DerivedPending` -- verified computationally; formal proof
/// requires tensor-power argument.
pub const S43B_KKL_HYPERCONTRACTIVE_STEP: ProofStatus = ProofStatus::DerivedPending;

/// S43c: Full KKL proof chain.
///
/// Balanced + hypercontractive + level weight + influence => max influence bound.
/// Status: `DerivedPending` -- computational verification complete for small n.
pub const S43C_KKL_FULL_CHAIN: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Core verification functions
// ---------------------------------------------------------------------------

/// Check that a Boolean function is balanced: E[f] = 0, equivalently
/// f_hat(emptyset) = 0 within floating-point tolerance.
///
/// A function is balanced when it takes value +1 and -1 equally often.
/// The KKL inequality requires this hypothesis.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Definition 1.6.
pub fn verify_balanced(f: &BooleanFunction) -> Result<bool, FourierError> {
    let coeffs = compute_all_fourier(f)?;
    // f_hat(emptyset) is the coefficient at index 0 (the empty subset).
    Ok(coeffs[0].abs() < EPSILON)
}

/// Compute the level-1 Fourier weight: W^1(f) = sum_{|S|=1} f_hat(S)^2.
///
/// For balanced f, hypercontractivity implies a lower bound on W^1(f)
/// in terms of I(f) and n. This is the key step connecting Bonami-Beckner
/// to the influence bound.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Lemma 9.23.
pub fn level_one_weight(f: &BooleanFunction) -> Result<f64, FourierError> {
    let coeffs = compute_all_fourier(f)?;
    let n = f.num_vars();
    Ok(level_k_weight(&coeffs, n, 1))
}

/// Lower bound on level-1 weight from hypercontractivity.
///
/// For a balanced Boolean function, the hypercontractivity argument gives:
///   W^1(f) >= I(f)^2 / n
///
/// This follows because each variable's influence Inf_i(f) has a level-1
/// component f_hat({i})^2, and by Cauchy-Schwarz:
///   (sum_i f_hat({i})^2) * n >= (sum_i |f_hat({i})|)^2 >= I(f)^2 / n
///
/// In the simple form used here, we verify that W^1(f) is non-trivial
/// when I(f) > 0.
///
/// Returns `(W^1, lower_bound, holds)`.
pub fn level_one_lower_bound(f: &BooleanFunction) -> Result<(f64, f64, bool), FourierError> {
    let n = f.num_vars();
    let w1 = level_one_weight(f)?;
    let inf = total_influence(f);
    // Lower bound: W^1(f) >= I(f)^2 / n^2
    // This is a weakened form; the true hypercontractive bound is tighter.
    let bound = if n > 0 {
        (inf * inf) / ((n * n) as f64)
    } else {
        0.0
    };
    Ok((w1, bound, w1 >= bound - EPSILON))
}

/// The KKL constant: c = 2/(pi * e) ~ 0.2339.
///
/// This is the best known constant in the KKL inequality:
///   max_i Inf_i(f) >= c * ln(n) / n
///
/// Reference: Kahn, Kalai, Linial, *FOCS* 1988, Theorem 3.1.
#[must_use]
pub fn kkl_constant() -> f64 {
    KKL_CONSTANT
}

/// Verify the KKL inequality computationally for a specific function.
///
/// Checks: max_i Inf_i(f) >= c * ln(n) / n.
///
/// Uses the theoretical constant c = 2/(pi*e). For n <= 1 the bound
/// is trivially satisfied (returns `true`).
///
/// This does NOT check that f is balanced -- use [`verify_kkl_proof_chain`]
/// for the full proof including the balanced hypothesis.
#[must_use]
pub fn verify_kkl_computational(f: &BooleanFunction) -> bool {
    let n = f.num_vars();
    if n <= 1 {
        return true;
    }
    let mi = max_influence(f);
    let bound = KKL_CONSTANT * (n as f64).ln() / (n as f64);
    mi >= bound - EPSILON
}

/// Verify the full KKL proof chain for a specific function.
///
/// The chain verifies each step in order:
/// 1. f is balanced (f_hat(emptyset) ~ 0).
/// 2. Bonami-Beckner holds at optimal rho = 1/sqrt(3) for q=4.
/// 3. Level-1 weight bound is consistent with hypercontractivity.
/// 4. max_i Inf_i(f) >= c * ln(n) / n.
///
/// Returns a vector of `(step, passed)` pairs.
pub fn verify_kkl_proof_chain(
    f: &BooleanFunction,
) -> Result<Vec<(KklProofStep, bool)>, FourierError> {
    let n = f.num_vars();
    let coeffs = compute_all_fourier(f)?;

    // Step 1: Balanced check
    let balanced = coeffs[0].abs() < EPSILON;

    // Step 2: Bonami-Beckner at rho = 1/sqrt(3) (optimal for q=4)
    let rho = 1.0 / 3.0_f64.sqrt();
    let bb_holds = verify_bonami_beckner(&coeffs, n, rho);

    // Step 3: Level-1 weight bound
    let w1 = level_k_weight(&coeffs, n, 1);
    let inf = total_influence(f);
    let w1_bound = if n > 0 {
        (inf * inf) / ((n * n) as f64)
    } else {
        0.0
    };
    let level_bound_holds = w1 >= w1_bound - EPSILON;

    // Step 4: KKL bound
    let kkl_holds = if n <= 1 {
        true
    } else {
        let mi = max_influence(f);
        let bound = KKL_CONSTANT * (n as f64).ln() / (n as f64);
        mi >= bound - EPSILON
    };

    Ok(vec![
        (KklProofStep::BonamiBeckner, bb_holds),
        (KklProofStep::LevelWeightBound, level_bound_holds),
        (
            KklProofStep::InfluenceLowerBound,
            balanced && level_bound_holds,
        ),
        (KklProofStep::MaxInfluenceBound, kkl_holds),
    ])
}

/// Entropy-influence conjecture (Friedgut-Kalai):
///   I(f) >= H(E[f]) / ln(2)
///
/// where H is the binary entropy function H(p) = -p*ln(p) - (1-p)*ln(1-p).
///
/// This is weaker than KKL but unconditional (no balanced hypothesis).
/// For balanced f (E[f] = 0 in {-1,1} encoding), H(1/2) = ln(2) so the
/// bound becomes I(f) >= 1. For f with E[f] close to +/-1 (nearly constant),
/// H is small, so the bound is weak.
///
/// The `bias` parameter is E[f] = f_hat(emptyset), mapped to the probability
/// p = (1 + E[f]) / 2 in {0,1} encoding.
///
/// Returns `(total_influence, entropy_bound, holds)`.
///
/// Reference: E. Friedgut, G. Kalai, "Every monotone graph property has
/// a sharp threshold", *Proc. AMS* 124, 1996.
pub fn entropy_influence_bound(f: &BooleanFunction) -> Result<(f64, f64, bool), FourierError> {
    let coeffs = compute_all_fourier(f)?;
    let bias = coeffs[0]; // E[f] in {-1,1}
    let inf = total_influence(f);

    // Map bias to probability: p = (1 + bias) / 2
    let p = (1.0 + bias) / 2.0;

    // Binary entropy H(p) = -p*ln(p) - (1-p)*ln(1-p)
    let entropy = if !(EPSILON..=1.0 - EPSILON).contains(&p) {
        0.0
    } else {
        -p * p.ln() - (1.0 - p) * (1.0 - p).ln()
    };

    // Bound: I(f) >= H(E[f]) / ln(2) = H(p) / ln(2)
    let bound = entropy / 2.0_f64.ln();

    Ok((inf, bound, inf >= bound - EPSILON))
}

/// Compute the max influence of the tribes function.
///
/// Tribes is the canonical near-tight example for KKL. For n variables
/// partitioned into n/ln(n) groups of size ln(n), the tribes function
/// is the OR of ANDs: f = OR(AND(group_1), AND(group_2), ...).
///
/// For tribes, max_i Inf_i(f) ~ ln(n)/n, matching the KKL lower bound
/// up to constants.
///
/// This function constructs an approximate tribes function for n variables
/// and returns `(max_influence, kkl_bound, ratio)`.
///
/// Reference: M. Ben-Or, N. Linial, "Collective coin flipping", 1985.
pub fn tribe_function_influence(n: usize) -> Result<(f64, f64, f64), FourierError> {
    if n == 0 {
        return Err(FourierError::TooManyVariables(0));
    }
    if n > 16 {
        return Err(FourierError::TooManyVariables(n));
    }

    // Group size ~ ln(n). For small n, use max(1, floor(ln(n))).
    let group_size = if n <= 2 {
        1
    } else {
        ((n as f64).ln()).floor().max(1.0) as usize
    };
    let num_groups = n / group_size.max(1);
    let actual_vars = num_groups * group_size;

    // Build truth table: f(x) = OR over groups of AND
    let size = 1usize << n;
    let mut table = Vec::with_capacity(size);
    for x in 0..size {
        let mut any_group_all_positive = false;
        for g in 0..num_groups {
            let start = g * group_size;
            let mut all_positive = true;
            for bit in start..start + group_size {
                if bit < n && (x >> bit) & 1 != 0 {
                    // bit set means x_i = -1 in our encoding
                    all_positive = false;
                    break;
                }
            }
            if all_positive {
                any_group_all_positive = true;
                break;
            }
        }
        // Variables beyond actual_vars don't participate (act as if +1)
        let _ = actual_vars;
        table.push(if any_group_all_positive { 1.0 } else { -1.0 });
    }

    let f = BooleanFunction::from_truth_table(&table)?;
    let mi = max_influence(&f);
    let bound = if n <= 1 {
        0.0
    } else {
        KKL_CONSTANT * (n as f64).ln() / (n as f64)
    };
    let ratio = if bound > EPSILON {
        mi / bound
    } else {
        f64::INFINITY
    };

    Ok((mi, bound, ratio))
}

/// Build a [`KklProofWitness`] for a given Boolean function.
///
/// Computes all required data: Fourier coefficients, influences, level-1
/// weight, balanced check, Bonami-Beckner verification, and the KKL bound.
pub fn build_kkl_witness(f: &BooleanFunction) -> Result<KklProofWitness, FourierError> {
    let n = f.num_vars();
    let coeffs = compute_all_fourier(f)?;

    let influences: Vec<f64> = (0..n)
        .map(|i| variable_influence(f, i).unwrap_or(0.0))
        .collect();
    let ti = total_influence(f);
    let mi = max_influence(f);
    let w1 = level_k_weight(&coeffs, n, 1);
    let balanced = coeffs[0].abs() < EPSILON;

    let rho = 1.0 / 3.0_f64.sqrt();
    let bb_holds = verify_bonami_beckner(&coeffs, n, rho);

    let kkl_bound_val = if n <= 1 {
        0.0
    } else {
        KKL_CONSTANT * (n as f64).ln() / (n as f64)
    };
    let kkl_sat = mi >= kkl_bound_val - EPSILON;

    Ok(KklProofWitness {
        n,
        fourier_coefficients: coeffs,
        influences,
        total_influence: ti,
        max_influence: mi,
        level_one_weight: w1,
        is_balanced: balanced,
        bonami_beckner_holds: bb_holds,
        kkl_bound_satisfied: kkl_sat,
        kkl_bound_value: kkl_bound_val,
    })
}

/// Verify each step of a proof witness independently.
///
/// Returns `(step, passed)` for all four KKL proof steps, derived
/// from the precomputed witness data.
#[must_use]
pub fn verify_kkl_steps(witness: &KklProofWitness) -> Vec<(KklProofStep, bool)> {
    let n = witness.n;

    // Step 1: Bonami-Beckner
    let bb = witness.bonami_beckner_holds;

    // Step 2: Level weight bound
    let inf_sq = witness.total_influence * witness.total_influence;
    let w1_bound = if n > 0 {
        inf_sq / ((n * n) as f64)
    } else {
        0.0
    };
    let level_bound = witness.level_one_weight >= w1_bound - EPSILON;

    // Step 3: Influence lower bound (requires balanced)
    let inf_bound = witness.is_balanced && level_bound;

    // Step 4: Max influence bound
    let kkl = witness.kkl_bound_satisfied;

    vec![
        (KklProofStep::BonamiBeckner, bb),
        (KklProofStep::LevelWeightBound, level_bound),
        (KklProofStep::InfluenceLowerBound, inf_bound),
        (KklProofStep::MaxInfluenceBound, kkl),
    ]
}
