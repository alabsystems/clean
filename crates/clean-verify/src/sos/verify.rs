// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic verification of SOS certificates.
//!
//! Given a [`SageSosCertificate`] claiming `target = sum_i q_i^2`, this
//! module expands the sum of squares and checks exact polynomial equality
//! with the target using the NRA polynomial arithmetic.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use crate::smt_verify::nra::Polynomial;

use super::parse::SageSosCertificate;

/// Result of verifying an SOS certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum SosVerdict {
    /// The certificate is valid: `target == sum_i q_i^2`.
    Valid,
    /// The certificate is invalid with a reason.
    Invalid(String),
}

/// Errors during SOS certificate verification.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
#[allow(dead_code)] // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
pub(crate) enum SosVerifyError {
    #[error("SOS decomposition does not equal target polynomial: residual is non-zero")]
    DecompositionMismatch,
    #[error("certificate has no square terms")]
    EmptyDecomposition,
}

/// Algebraically verify an SOS certificate.
///
/// Checks that `sum_i squares[i]^2 == target` by expanding the sum of
/// squares and comparing with exact polynomial arithmetic.
#[must_use]
pub(crate) fn verify_sos_certificate(cert: &SageSosCertificate) -> SosVerdict {
    if cert.squares.is_empty() {
        // A zero-term SOS decomposition can only represent the zero polynomial.
        if cert.target.is_zero() {
            return SosVerdict::Valid;
        }
        return SosVerdict::Invalid("no square terms but target is non-zero".into());
    }

    let sos_sum = expand_sum_of_squares(&cert.squares);
    let residual = sos_sum.sub(&cert.target);

    if residual.is_zero() {
        SosVerdict::Valid
    } else {
        SosVerdict::Invalid(format!(
            "decomposition mismatch: sum of squares has {} terms, target has {} terms",
            sos_sum.0.len(),
            cert.target.0.len()
        ))
    }
}

/// Expand `sum_i q_i^2` into a single polynomial.
#[must_use]
pub(crate) fn expand_sum_of_squares(squares: &[Polynomial]) -> Polynomial {
    let mut result = Polynomial::zero();
    for q in squares {
        let q_squared = q.mul(q);
        result = result.add(&q_squared);
    }
    result
}

/// Compute the polynomial `q^2` for a single factor.
#[must_use]
pub(crate) fn square_polynomial(q: &Polynomial) -> Polynomial {
    q.mul(q)
}
