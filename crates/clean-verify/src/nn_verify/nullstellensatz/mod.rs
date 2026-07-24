// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Neural Nullstellensatz: SoS polynomial certificates for NN verification (C028).
//!
//! This module implements sum-of-squares (SoS) certificate verification for
//! neural network properties. When a ReLU network has known stable activation
//! patterns, the network function is polynomial (degree 1 / affine). A
//! Positivstellensatz certificate then proves `output >= threshold` (or any
//! polynomial inequality) without branch-and-bound search.
//!
//! ## Architecture
//!
//! - [`polynomial`]: Convert ReLU networks with stable patterns to polynomial
//!   representation. Provides `PolynomialNetwork`, `AffineLayer`,
//!   `NnSosCertificate`, and `box_domain_constraints`.
//! - [`verify`]: Verify SoS certificates via Gram matrix PSD check and
//!   exact polynomial identity. Main entry points: `verify_nn_sos_certificate`
//!   and `verify_network_property`.
//! - [`c028_spec`]: C028 theorem specification with proof status tracking.
//!
//! ## Relationship to Other Modules
//!
//! - `smt_verify::nra`: Provides the core `Polynomial`, `Monomial`, and
//!   `SosCertificate` types with exact rational arithmetic. This module
//!   builds NN-specific types on top and delegates SoS verification to NRA.
//! - `nn_verify::relu::stability`: Determines which neurons are stable.
//!   Stable patterns are the prerequisite for polynomial representation.
//! - `nn_verify::certificate`: Farkas certificate composition for
//!   bound propagation. Nullstellensatz is complementary -- it handles
//!   cases where BaB is unnecessary.
//!
//! ## Workflow
//!
//! 1. Run stability analysis (`relu::stability`) to classify neurons
//! 2. If all neurons are stable, convert to `PolynomialNetwork`
//! 3. Express property as `PolynomialProperty`
//! 4. Obtain SoS certificate (from external SDP solver or gamma-crown)
//! 5. Verify via `verify_nn_sos_certificate` or `verify_network_property`
//!
//! ## References
//!
//! - Parrilo, "Semidefinite programming relaxations for semialgebraic
//!   problems" (Math. Programming, 2003)
//! - Stengle, "A Nullstellensatz and a Positivstellensatz in semialgebraic
//!   geometry" (Math. Ann., 1974)

pub mod c028_spec;
pub(crate) mod polynomial;
pub(crate) mod verify;

pub use c028_spec::{
    c028_theorem_entries, C028_SOS_CERTIFICATE_SOUNDNESS, C028_SOS_IMPLIES_NO_BAB,
    C028_STABLE_NETWORK_IS_POLYNOMIAL,
};
pub(crate) use polynomial::{
    box_domain_constraints, evaluate_network, network_to_polynomials, AffineLayer, LayerPattern,
    NeuronPattern, NnSosCertificate, PolynomialNetwork, PolynomialProperty,
};
pub(crate) use verify::{verify_network_property, verify_nn_sos_certificate, NnSosVerdict};
