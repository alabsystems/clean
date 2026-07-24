// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Frontier SAT Research
//!
//! Beyond-resolution proof systems and Boolean function analysis:
//!
//! - [`extension_rule`]: Extended Resolution (ER) -- introduce auxiliary
//!   variables defined as functions of existing variables. Preserves
//!   satisfiability while enabling exponentially shorter proofs than
//!   standard resolution for some formula families.
//!
//! - [`polynomial_calculus`]: Polynomial Calculus over GF(2) -- encode
//!   clauses as multilinear polynomials over the two-element field and
//!   derive contradictions via algebraic rules (addition, variable
//!   multiplication, weakening).
//!
//! - [`cnf_to_poly`]: CNF-to-polynomial translation with structured
//!   metadata, XOR constraint generation, and exhaustive verification.
//!
//! - [`pc_proof_system`]: Interactive proof system builder for constructing
//!   Polynomial Calculus derivations step by step with immediate feedback.
//!
//! - [`pc_certificate`]: Text and binary certificate formats for PC proofs,
//!   with serialization, deserialization, and replay verification.
//!
//! - [`fourier`]: Boolean Fourier analysis -- represent Boolean functions
//!   in the Fourier basis and verify identities (Parseval, influence).
//!
//! ## Proof Status Constants
//!
//! | ID  | Name                          | Status         |
//! |-----|-------------------------------|----------------|
//! | S40 | Haken tree-resolution PHP     | DerivedPending |
//! | S41 | Fourier-Parseval identity     | DerivedPending |
//! | S42 | Influence-Fourier identity    | DerivedPending |
//! | S43 | KKL inequality statement      | DerivedPending |
//! | S44 | Polynomial Calculus GF(2)     | DerivedPending |
//! | S45 | Noise sensitivity Fourier     | DerivedPending |
//! | S46 | Total influence identity      | DerivedPending |
//! | S47 | KKL computational             | DerivedPending |
//! | S50 | Bonami-Beckner inequality     | DerivedPending |
//! | S51 | Hypercontractive norm         | DerivedPending |
//!
//! ## References
//!
//! - R. O'Donnell, *Analysis of Boolean Functions*, Cambridge, 2014
//! - A. Haken, "The Intractability of Resolution", *TCS* 39, 1985
//! - J. Kahn, G. Kalai, N. Linial, "The Influence of Variables on
//!   Boolean Functions", *FOCS* 1988

pub mod cnf_to_poly;
pub mod extension_rule;
pub mod extension_variable;
pub mod fourier;
pub mod gf2_algebra;
pub mod hypercontractivity;
pub mod kkl_proof;
pub mod noise_sensitivity;
pub mod pc_certificate;
pub mod pc_degree;
pub mod pc_proof_system;
pub mod polynomial_calculus;
pub(crate) mod spec_registration;

#[cfg(test)]
mod tests_cnf_to_poly;
#[cfg(test)]
mod tests_extension;
#[cfg(test)]
mod tests_extension_var;
#[cfg(test)]
mod tests_fourier;
#[cfg(test)]
mod tests_gf2;
#[cfg(test)]
mod tests_gf2_algebra;
#[cfg(test)]
mod tests_gf2_soundness_forgery;
#[cfg(test)]
mod tests_hypercontractivity;
#[cfg(test)]
mod tests_kkl_proof;
#[cfg(test)]
mod tests_noise;
#[cfg(test)]
mod tests_pc;
#[cfg(test)]
mod tests_pc_certificate;
#[cfg(test)]
mod tests_pc_degree;
#[cfg(test)]
mod tests_pc_ext;
#[cfg(test)]
mod tests_pc_proof_system;

pub use fourier::{BooleanFunction, FourierError};
pub use noise_sensitivity::{
    low_degree_energy, max_influence, noise_sensitivity, noise_stability, spectral_entropy,
    total_influence, variable_influence, verify_kkl_bound, verify_level_parseval,
};

use crate::spec::ProofStatus;

/// Proof status entry for the frontier SAT research registry.
#[derive(Debug, Clone)]
pub struct FrontierEntry {
    /// Entry identifier (e.g., "S40").
    pub id: &'static str,
    /// Human-readable description.
    pub description: &'static str,
    /// Current proof status.
    pub status: ProofStatus,
}

// ---------------------------------------------------------------------------
// S40: Haken's exponential lower bound for tree-like Resolution on PHP
// ---------------------------------------------------------------------------

/// Haken (1985): Every tree-like Resolution refutation of PHP_{n+1}^n
/// requires size 2^{Mathverse(n)}.
///
/// Status: `DerivedPending` -- the combinatorial argument is encoded but
/// the formal size bound depends on the Prover inequality infrastructure.
pub const S40_HAKEN_TREE_RESOLUTION_PHP: FrontierEntry = FrontierEntry {
    id: "S40",
    description: "Exponential lower bound for tree-like Resolution on PHP",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S41: Fourier-Parseval identity
// ---------------------------------------------------------------------------

/// Parseval's identity for Boolean functions:
///   Sum_{S subset [n]} f_hat(S)^2 = E[f^2]
///
/// Status: `DerivedPending` -- verified computationally for n <= 16 via
/// [`fourier::verify_parseval`]; formal proof term not yet constructed.
pub const S41_FOURIER_PARSEVAL_IDENTITY: FrontierEntry = FrontierEntry {
    id: "S41",
    description: "Sum of squared Fourier coefficients = expectation of f^2",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S42: Influence-Fourier identity
// ---------------------------------------------------------------------------

/// For Boolean f: {-1,1}^n -> R and variable i in [n]:
///   Inf_i(f) = Sum_{S containing i} f_hat(S)^2
///
/// Status: `DerivedPending` -- verified computationally for n <= 16.
pub const S42_INFLUENCE_FOURIER_IDENTITY: FrontierEntry = FrontierEntry {
    id: "S42",
    description: "Inf_i(f) = sum of f_hat(S)^2 over S containing i",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S43: KKL inequality statement
// ---------------------------------------------------------------------------

/// Kahn-Kalai-Linial (1988): For every balanced Boolean function f,
///   max_i Inf_i(f) >= Mathverse(log(n) / n).
///
/// Status: `DerivedPending` -- statement only; the full proof requires
/// hypercontractivity (Bonami-Beckner), which is open-problem hard to
/// formalize from scratch.
pub const S43_KKL_INEQUALITY_STATEMENT: FrontierEntry = FrontierEntry {
    id: "S43",
    description: "Statement of KKL inequality (not proof -- requires hypercontractivity)",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S44: Polynomial Calculus over GF(2)
// ---------------------------------------------------------------------------

/// x^2 = x reduction in GF(2) Polynomial Calculus.
///
/// Every variable satisfies x^2 = x in GF(2), so multilinear reduction
/// is sound. The proof system allows addition (XOR), multiplication (AND
/// with reduction), the Boolean axiom x^2 - x, and weakening.
///
/// Status: `DerivedPending` -- GF(2) derivation checker is executable
/// via [`polynomial_calculus::verify_pc_proof`]; formal proof term pending.
pub const S44_POLYNOMIAL_CALCULUS_GF2: FrontierEntry = FrontierEntry {
    id: "S44",
    description: "x^2=x reduction in GF(2) Polynomial Calculus",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S45: Noise sensitivity Fourier formula
// ---------------------------------------------------------------------------

/// Noise sensitivity expressed via Fourier coefficients:
///   Noise_delta(f) = (1/2)(1 - sum_S (1-2*delta)^{|S|} f_hat(S)^2)
///
/// Status: `DerivedPending` -- verified computationally; formal proof
/// term depends on inner-product linearity infrastructure.
pub const S45_NOISE_SENSITIVITY_FOURIER: FrontierEntry = FrontierEntry {
    id: "S45",
    description: "Noise sensitivity Fourier formula",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S46: Total influence = sum of level weights * level
// ---------------------------------------------------------------------------

/// Total influence identity:
///   I(f) = sum_{k=0}^{n} k * W^k(f)
///
/// Status: `DerivedPending` -- verified computationally; formal proof
/// term depends on the level decomposition lemma.
pub const S46_TOTAL_INFLUENCE_IDENTITY: FrontierEntry = FrontierEntry {
    id: "S46",
    description: "I(f) = sum_k k * W^k(f) (total influence = weighted level sum)",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S47: KKL inequality computational verification
// ---------------------------------------------------------------------------

/// Computational verification of the KKL inequality:
///   max_i Inf_i(f) >= c * ln(n) / n  for balanced f.
///
/// Status: `DerivedPending` -- computational verification for small n;
/// the full proof requires hypercontractivity (Bonami-Beckner).
pub const S47_KKL_COMPUTATIONAL: FrontierEntry = FrontierEntry {
    id: "S47",
    description: "KKL inequality computational verification",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S48: Extension variable preserves satisfiability
// ---------------------------------------------------------------------------

/// Extended Resolution preserves satisfiability:
///   For any CNF F and extension definition z <-> (a AND b),
///   F is satisfiable iff F AND encode(z <-> (a AND b)) is satisfiable.
///
/// Status: `DerivedPending` -- verified computationally for small instances.
pub const S48_EXTENSION_PRESERVES_SAT: FrontierEntry = FrontierEntry {
    id: "S48",
    description: "Extension variable introduction preserves satisfiability",
    status: ProofStatus::DerivedPending,
};

// ---------------------------------------------------------------------------
// S49: Extension proof compression
// ---------------------------------------------------------------------------

/// Extended Resolution can yield exponentially shorter proofs:
///   There exist formula families where ER proofs are exponentially shorter
///   than standard Resolution proofs.
///
/// Status: `DerivedPending` -- statement and computational verification only.
pub const S49_EXTENSION_PROOF_COMPRESSION: FrontierEntry = FrontierEntry {
    id: "S49",
    description: "Extension variable proof compression",
    status: ProofStatus::DerivedPending,
};

/// Bonami-Beckner (1970/1975): For any Boolean function f and rho <= 1/sqrt(q-1):
///   ||T_rho f||_q <= ||f||_2
///
/// Status: `DerivedPending` -- verified computationally for small n and
/// standard function families; formal proof requires tensor-power machinery.
pub const S50_BONAMI_BECKNER: FrontierEntry = FrontierEntry {
    id: "S50",
    description: "Bonami-Beckner hypercontractivity: ||T_rho f||_q <= ||f||_2",
    status: ProofStatus::DerivedPending,
};

/// Hypercontractive norm computation via Fourier:
///   ||T_rho f||_q computed from dampened Fourier coefficients.
///
/// Status: `DerivedPending` -- executable computation verified against
/// direct truth-table evaluation for n <= 10.
pub const S51_HYPERCONTRACTIVE_NORM: FrontierEntry = FrontierEntry {
    id: "S51",
    description: "Hypercontractive norm ||T_rho f||_q via Fourier",
    status: ProofStatus::DerivedPending,
};

/// All frontier proof entries, for registry enumeration.
#[must_use]
pub fn all_entries() -> Vec<FrontierEntry> {
    vec![
        S40_HAKEN_TREE_RESOLUTION_PHP,
        S41_FOURIER_PARSEVAL_IDENTITY,
        S42_INFLUENCE_FOURIER_IDENTITY,
        S43_KKL_INEQUALITY_STATEMENT,
        S44_POLYNOMIAL_CALCULUS_GF2,
        S45_NOISE_SENSITIVITY_FOURIER,
        S46_TOTAL_INFLUENCE_IDENTITY,
        S47_KKL_COMPUTATIONAL,
        S48_EXTENSION_PRESERVES_SAT,
        S49_EXTENSION_PROOF_COMPRESSION,
        S50_BONAMI_BECKNER,
        S51_HYPERCONTRACTIVE_NORM,
    ]
}
