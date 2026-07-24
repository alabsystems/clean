// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Orbit-CROWN: Symmetry Quotienting for CNN Verification (C030)
//!
//! Exploits symmetries in neural network weight matrices to reduce the
//! dimensionality of CROWN-style verification. When a weight matrix W
//! is equivariant under a group action G (i.e., W * g(x) = g(W * x)
//! for all group elements g), the verification problem can be quotiented
//! by G, reducing the number of variables by a factor of |G|.
//!
//! ## Core Idea
//!
//! CROWN computes backward linear bounds of the form:
//!   `lower_bias + lower_coeffs * x <= f(x) <= upper_bias + upper_coeffs * x`
//!
//! If the network is equivariant, these bounds must also be equivariant.
//! This means the coefficient matrices lie in the commutant algebra of G,
//! which has dimension `dim / |orbit|` instead of `dim`. Orbit-CROWN
//! computes bounds directly in the quotient space.
//!
//! ## Theorems (all `DerivedPending`, Phase 3)
//!
//! - **C030a (equivariance verification):** Given W and group generators,
//!   verify `||W * rho(g) - rho(g) * W|| < eps` for all generators g.
//! - **C030b (orbit-CROWN soundness):** If W is equivariant under G, then
//!   the quotient CROWN bounds are sound: they contain the true output
//!   for all inputs in the orbit-quotiented input region.
//! - **C030c (orbit-CROWN tightness):** The quotient bounds are at least
//!   as tight as full CROWN restricted to the fundamental domain.
//!
//! ## Architecture
//!
//! - [`symmetry`]: Symmetry group trait and concrete groups
//! - [`equivariance`]: Weight equivariance verification
//! - [`quotient_bounds`]: Orbit-quotiented CROWN bound computation
//! - [`c030_spec`]: C030 theorem specification with proof status tracking
//!
//! ## References
//!
//! - Cohen & Welling, "Group Equivariant CNNs" (ICML 2016)
//! - Maron et al., "Invariant and Equivariant Graph Networks" (ICLR 2019)
//! - Xu et al., "Auto-LiRPA" (NeurIPS 2020)

pub mod c030_spec;
pub mod equivariance;
pub mod quotient_bounds;
pub mod symmetry;

#[cfg(test)]
mod tests_equivariance;
#[cfg(test)]
mod tests_quotient_bounds;
#[cfg(test)]
mod tests_symmetry;

pub use c030_spec::{
    c030_theorem_entries, C030_EQUIVARIANCE_VERIFICATION, C030_ORBIT_CROWN_SOUNDNESS,
    C030_ORBIT_CROWN_TIGHTNESS,
};
pub use equivariance::{
    verify_equivariance, verify_equivariance_generators, EquivarianceError, EquivarianceResult,
};
pub use quotient_bounds::{
    orbit_crown_bounds, quotient_crown_bound, QuotientBound, QuotientBoundResult,
};
pub use symmetry::{GroupElement, Orbit, PermutationGroup, SymmetryGroup, TranslationGroup};
