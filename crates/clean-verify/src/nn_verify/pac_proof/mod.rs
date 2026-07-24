// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PAC-to-Proof: certify PGD adversarial search results via Lipschitz-Hessian bounds (C029).
//!
//! PGD (Projected Gradient Descent) finds adversarial examples empirically but
//! provides no optimality guarantee. This module bridges the gap: given a
//! PGD-found adversarial example x_adv and Lipschitz/Hessian bounds on the
//! network, we certify a region around x_adv where no better adversarial exists.
//!
//! ## Architecture
//!
//! - [`certification`]: Core certification logic — Lipschitz bounds, Hessian bounds,
//!   certified region computation, and region verification.
//! - [`c029_spec`]: C029 theorem specification with proof status tracking.
//!
//! ## Mathematical Foundation
//!
//! Given a network f, adversarial example x_adv, and robustness threshold t:
//!
//! 1. **First-order (Lipschitz) certification**: If f has Lipschitz constant L,
//!    then for all x in B(x_adv, r): |f(x) - f(x_adv)| <= L * r.
//!    Setting r = (f(x_adv) - t) / L gives a ball where f(x) >= t, meaning
//!    no adversarial in this ball can reduce the output below threshold.
//!
//! 2. **Second-order (Hessian) refinement**: With Hessian bound H on ||nabla^2 f||,
//!    Taylor remainder gives a tighter radius via the quadratic formula:
//!    r = (-||grad f(x_adv)|| + sqrt(||grad f||^2 + 2*H*(f(x_adv) - t))) / H
//!
//! ## References
//!
//! - Hein & Andriushchenko, "Formal Guarantees on the Robustness of a Classifier
//!   against Adversarial Manipulation" (NeurIPS 2017)
//! - Weng et al., "Evaluating the Robustness of Neural Networks: An Extreme Value
//!   Theory Approach" (ICLR 2018)
//! - Fazlyab et al., "Efficient and Accurate Estimation of Lipschitz Constants for
//!   Deep Neural Networks" (NeurIPS 2019)

pub mod c029_spec;
pub mod certification;

#[cfg(test)]
mod tests_certification;

pub use c029_spec::{
    c029_theorem_entries, C029_HESSIAN_QUADRATIC_REFINEMENT, C029_LIPSCHITZ_CERTIFIED_RADIUS,
    C029_REGION_VERIFICATION_SOUND,
};
pub use certification::{
    certify_pgd_result, verify_certified_region, CertificationError, CertificationMode,
    CertifiedRegion, HessianBound, LipschitzBound, PacProofCertifier,
};
