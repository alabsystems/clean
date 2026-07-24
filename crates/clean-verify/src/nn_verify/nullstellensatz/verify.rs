// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification of Neural Nullstellensatz SoS certificates.
//!
//! Given a neural network property expressed as a polynomial inequality
//! `p(x) >= 0` over a box domain `x in [l, u]`, and an SoS certificate
//! (Positivstellensatz refutation of the negation), this module verifies
//! the certificate is valid.
//!
//! ## Algorithm
//!
//! The Positivstellensatz certificate for `p(x) >= 0` on `[l, u]` works by
//! expressing the property polynomial as a non-negative combination of:
//! 1. Domain constraints: `g_i(x) = x_i - l_i >= 0` and `h_i(x) = u_i - x_i >= 0`
//! 2. SoS multipliers: `s_i(x)` for each constraint (certified PSD via Gram matrix)
//! 3. A free SoS term: `s_0(x)` (non-negative everywhere)
//!
//! Verification checks:
//! `p(x) = s_0(x) + sum_i s_i(x) * g_i(x) + sum_i t_i(x) * h_i(x)`
//!
//! Since each `s_i, t_i, s_0` is SoS (non-negative) and each `g_i, h_i`
//! is non-negative on the domain, the right side is non-negative on `[l, u]`,
//! proving `p(x) >= 0`.
//!
//! ## References
//!
//! - Parrilo, "Semidefinite programming relaxations for semialgebraic
//!   problems" (Math. Programming, 2003)
//! - Stengle, "A Nullstellensatz and a Positivstellensatz in semialgebraic
//!   geometry" (Math. Ann., 1974)

use num_rational::Rational64;

use crate::smt_verify::nra::{verify_sos, Polynomial};

use super::polynomial::{
    box_domain_constraints, network_to_polynomials, NnSosCertificate, PolynomialNetwork,
    PolynomialProperty,
};

/// Result of verifying a Neural Nullstellensatz certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NnSosVerdict {
    /// Certificate is valid: the property holds on the domain.
    Valid,
    /// Certificate is invalid with a reason.
    Invalid(String),
}

/// Verify a complete Neural Nullstellensatz certificate.
///
/// This is the main entry point. Given an `NnSosCertificate`, it checks:
/// 1. Dimension consistency (multiplier counts match domain dimensions)
/// 2. All SoS multipliers have valid Gram decompositions (PSD)
/// 3. The polynomial identity holds exactly
#[must_use]
pub(crate) fn verify_nn_sos_certificate(cert: &NnSosCertificate) -> NnSosVerdict {
    let n = cert.property.input_vars.len();

    // Check dimension consistency
    if cert.lower_bounds.len() != n {
        return NnSosVerdict::Invalid(format!(
            "lower_bounds dimension mismatch: expected {n}, got {}",
            cert.lower_bounds.len()
        ));
    }
    if cert.upper_bounds.len() != n {
        return NnSosVerdict::Invalid(format!(
            "upper_bounds dimension mismatch: expected {n}, got {}",
            cert.upper_bounds.len()
        ));
    }
    if cert.lower_multipliers.len() != n {
        return NnSosVerdict::Invalid(format!(
            "lower_multipliers count mismatch: expected {n}, got {}",
            cert.lower_multipliers.len()
        ));
    }
    if cert.upper_multipliers.len() != n {
        return NnSosVerdict::Invalid(format!(
            "upper_multipliers count mismatch: expected {n}, got {}",
            cert.upper_multipliers.len()
        ));
    }

    // Verify bounds are consistent: lower <= upper
    for i in 0..n {
        if cert.lower_bounds[i] > cert.upper_bounds[i] {
            return NnSosVerdict::Invalid(format!(
                "lower_bound[{i}] > upper_bound[{i}]: {} > {}",
                cert.lower_bounds[i], cert.upper_bounds[i]
            ));
        }
    }

    // Verify all SoS multipliers are PSD
    if !verify_sos(&cert.free_sos) {
        return NnSosVerdict::Invalid("free SoS term is not PSD".to_string());
    }
    for (i, mult) in cert.lower_multipliers.iter().enumerate() {
        if !verify_sos(mult) {
            return NnSosVerdict::Invalid(format!("lower_multiplier[{i}] is not PSD"));
        }
    }
    for (i, mult) in cert.upper_multipliers.iter().enumerate() {
        if !verify_sos(mult) {
            return NnSosVerdict::Invalid(format!("upper_multiplier[{i}] is not PSD"));
        }
    }

    // Build domain constraint polynomials
    let domain_constraints = match box_domain_constraints(&cert.lower_bounds, &cert.upper_bounds) {
        Some(c) => c,
        None => return NnSosVerdict::Invalid("failed to build domain constraints".to_string()),
    };

    // Compute the certificate polynomial:
    // cert_poly = s_0(x) + sum_i s_i(x) * (x_i - l_i) + sum_i t_i(x) * (u_i - x_i)
    let cert_poly = assemble_certificate_polynomial(
        &cert.free_sos,
        &cert.lower_multipliers,
        &cert.upper_multipliers,
        &domain_constraints,
    );

    let cert_poly = match cert_poly {
        Some(p) => p,
        None => {
            return NnSosVerdict::Invalid("failed to assemble certificate polynomial".to_string())
        }
    };

    // Verify: cert_poly == property polynomial (exact polynomial equality)
    let diff = cert_poly.sub(&cert.property.polynomial);
    if !diff.is_zero() {
        return NnSosVerdict::Invalid(
            "certificate polynomial does not match property polynomial".to_string(),
        );
    }

    NnSosVerdict::Valid
}

/// Verify a property of a neural network using an SoS certificate.
///
/// Higher-level API that takes a network + property + certificate and
/// verifies end-to-end:
/// 1. Convert network to polynomial representation
/// 2. Verify the SoS certificate matches the property
#[must_use]
pub(crate) fn verify_network_property(
    network: &PolynomialNetwork,
    output_index: usize,
    threshold: Rational64,
    cert: &NnSosCertificate,
) -> NnSosVerdict {
    // Convert network to polynomials
    let polys = match network_to_polynomials(network) {
        Some(p) => p,
        None => {
            return NnSosVerdict::Invalid("failed to convert network to polynomials".to_string())
        }
    };

    // Check output index is valid
    if output_index >= polys.len() {
        return NnSosVerdict::Invalid(format!(
            "output_index {output_index} >= network outputs {}",
            polys.len()
        ));
    }

    // Property: output[output_index] - threshold >= 0
    let property_poly = polys[output_index].sub(&Polynomial::constant(threshold));

    // Verify the certificate's property matches the network property
    let diff = cert.property.polynomial.sub(&property_poly);
    if !diff.is_zero() {
        return NnSosVerdict::Invalid(
            "certificate property does not match network property".to_string(),
        );
    }

    // Delegate to certificate verification
    verify_nn_sos_certificate(cert)
}

/// Assemble the certificate polynomial from SoS multipliers and domain constraints.
///
/// Computes: `s_0(x) + sum_{i=0}^{2n-1} s_i(x) * g_i(x)`
/// where `g_0, g_1, ..., g_{2n-1}` are the domain constraints
/// (alternating lower and upper for each dimension).
fn assemble_certificate_polynomial(
    free_sos: &crate::smt_verify::nra::SosCertificate,
    lower_mults: &[crate::smt_verify::nra::SosCertificate],
    upper_mults: &[crate::smt_verify::nra::SosCertificate],
    domain_constraints: &[Polynomial],
) -> Option<Polynomial> {
    // Expand free SoS to polynomial
    let mut result = sos_to_polynomial(free_sos)?;

    // Add lower-bound terms: s_i(x) * (x_i - l_i)
    for (i, cert) in lower_mults.iter().enumerate() {
        let mult_poly = sos_to_polynomial(cert)?;
        // Domain constraints are interleaved: [x_0-l_0, u_0-x_0, x_1-l_1, u_1-x_1, ...]
        let constraint_idx = 2 * i;
        if constraint_idx >= domain_constraints.len() {
            return None;
        }
        result = result.add(&mult_poly.mul(&domain_constraints[constraint_idx]));
    }

    // Add upper-bound terms: t_i(x) * (u_i - x_i)
    for (i, cert) in upper_mults.iter().enumerate() {
        let mult_poly = sos_to_polynomial(cert)?;
        let constraint_idx = 2 * i + 1;
        if constraint_idx >= domain_constraints.len() {
            return None;
        }
        result = result.add(&mult_poly.mul(&domain_constraints[constraint_idx]));
    }

    Some(result)
}

/// Expand an SoS certificate to its polynomial representation.
///
/// For Gram matrix G and basis m(x), computes m(x)^T G m(x).
fn sos_to_polynomial(cert: &crate::smt_verify::nra::SosCertificate) -> Option<Polynomial> {
    let dimension = cert.basis.len();
    if cert.gram_matrix.len() != dimension {
        return None;
    }
    if cert.gram_matrix.iter().any(|row| row.len() != dimension) {
        return None;
    }

    let zero = Rational64::from_integer(0);
    let mut terms = Vec::new();
    for i in 0..dimension {
        for j in 0..dimension {
            let coeff = cert.gram_matrix[i][j];
            if coeff == zero {
                continue;
            }
            terms.push((coeff, cert.basis[i].mul(&cert.basis[j])));
        }
    }
    Some(Polynomial::new(terms))
}

#[cfg(test)]
mod tests {
    use super::super::polynomial::{AffineLayer, LayerPattern, NeuronPattern, PolynomialNetwork};
    use super::*;
    use crate::smt_verify::nra::{Monomial, SosCertificate};

    fn rat(n: i64) -> Rational64 {
        Rational64::from_integer(n)
    }

    /// Build a trivial network: y = 2*x + 1 (single input, single output, no hidden)
    fn trivial_network() -> PolynomialNetwork {
        PolynomialNetwork {
            layers: vec![AffineLayer {
                weights: vec![vec![rat(2)]],
                bias: vec![rat(1)],
            }],
            patterns: vec![],
        }
    }

    /// Create an SoS certificate for a constant polynomial (value >= 0).
    fn sos_constant(value: i64) -> SosCertificate {
        SosCertificate {
            gram_matrix: vec![vec![rat(value)]],
            basis: vec![Monomial::one()],
        }
    }

    /// Build a zero SoS certificate.
    fn sos_zero() -> SosCertificate {
        SosCertificate {
            gram_matrix: vec![vec![rat(0)]],
            basis: vec![Monomial::one()],
        }
    }

    #[test]
    fn test_verify_trivial_constant_property() {
        // Property: 3 >= 0 (constant polynomial)
        // Certificate: free_sos = 3, no domain constraints needed (0 input vars)
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::constant(rat(3)),
                input_vars: vec![],
            },
            lower_bounds: vec![],
            upper_bounds: vec![],
            lower_multipliers: vec![],
            upper_multipliers: vec![],
            free_sos: sos_constant(3),
        };

        assert_eq!(verify_nn_sos_certificate(&cert), NnSosVerdict::Valid);
    }

    #[test]
    fn test_verify_linear_property_on_interval() {
        // Property: 2*x_0 + 1 >= 0 for x_0 in [0, 5]
        // This means: 2*x_0 + 1 = s_0 + s_1*(x_0 - 0) + s_2*(5 - x_0)
        //
        // Choose: s_0 = 1 (constant), s_1 = 2 (constant), s_2 = 0
        // Check: 1 + 2*(x_0) + 0*(5 - x_0) = 2*x_0 + 1. Correct!
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::new(vec![
                    (rat(2), Monomial::variable("x_0")),
                    (rat(1), Monomial::one()),
                ]),
                input_vars: vec!["x_0".to_string()],
            },
            lower_bounds: vec![rat(0)],
            upper_bounds: vec![rat(5)],
            lower_multipliers: vec![sos_constant(2)],
            upper_multipliers: vec![sos_zero()],
            free_sos: sos_constant(1),
        };

        assert_eq!(verify_nn_sos_certificate(&cert), NnSosVerdict::Valid);
    }

    #[test]
    fn test_verify_invalid_sos_not_psd() {
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::constant(rat(1)),
                input_vars: vec![],
            },
            lower_bounds: vec![],
            upper_bounds: vec![],
            lower_multipliers: vec![],
            upper_multipliers: vec![],
            free_sos: SosCertificate {
                gram_matrix: vec![vec![rat(-1)]],
                basis: vec![Monomial::one()],
            },
        };

        assert_eq!(
            verify_nn_sos_certificate(&cert),
            NnSosVerdict::Invalid("free SoS term is not PSD".to_string())
        );
    }

    #[test]
    fn test_verify_dimension_mismatch() {
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::constant(rat(1)),
                input_vars: vec!["x_0".to_string()],
            },
            lower_bounds: vec![], // should be length 1
            upper_bounds: vec![rat(1)],
            lower_multipliers: vec![sos_zero()],
            upper_multipliers: vec![sos_zero()],
            free_sos: sos_constant(1),
        };

        match verify_nn_sos_certificate(&cert) {
            NnSosVerdict::Invalid(msg) => {
                assert!(msg.contains("lower_bounds dimension mismatch"));
            }
            NnSosVerdict::Valid => panic!("should be invalid"),
        }
    }

    #[test]
    fn test_verify_bounds_inconsistent() {
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::constant(rat(1)),
                input_vars: vec!["x_0".to_string()],
            },
            lower_bounds: vec![rat(5)],
            upper_bounds: vec![rat(1)], // lower > upper
            lower_multipliers: vec![sos_zero()],
            upper_multipliers: vec![sos_zero()],
            free_sos: sos_constant(1),
        };

        match verify_nn_sos_certificate(&cert) {
            NnSosVerdict::Invalid(msg) => {
                assert!(msg.contains("lower_bound[0] > upper_bound[0]"));
            }
            NnSosVerdict::Valid => panic!("should be invalid"),
        }
    }

    #[test]
    fn test_verify_polynomial_mismatch() {
        // Certificate claims property is 1, but assembled polynomial is 2
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::constant(rat(1)),
                input_vars: vec![],
            },
            lower_bounds: vec![],
            upper_bounds: vec![],
            lower_multipliers: vec![],
            upper_multipliers: vec![],
            free_sos: sos_constant(2),
        };

        match verify_nn_sos_certificate(&cert) {
            NnSosVerdict::Invalid(msg) => {
                assert!(msg.contains("does not match"));
            }
            NnSosVerdict::Valid => panic!("should be invalid"),
        }
    }

    #[test]
    fn test_verify_network_property_end_to_end() {
        // Network: y = 2*x + 1
        // Property: y >= 1 for x in [0, 5], i.e., 2*x + 1 - 1 = 2*x >= 0
        //
        // Certificate: 2*x = 0 + 2*(x - 0) + 0*(5 - x)
        // free_sos = 0, lower_mult = 2, upper_mult = 0
        let net = trivial_network();
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::new(vec![(rat(2), Monomial::variable("x_0"))]),
                input_vars: vec!["x_0".to_string()],
            },
            lower_bounds: vec![rat(0)],
            upper_bounds: vec![rat(5)],
            lower_multipliers: vec![sos_constant(2)],
            upper_multipliers: vec![sos_zero()],
            free_sos: sos_zero(),
        };

        let verdict = verify_network_property(&net, 0, rat(1), &cert);
        assert_eq!(verdict, NnSosVerdict::Valid);
    }

    #[test]
    fn test_verify_network_property_invalid_output_index() {
        let net = trivial_network();
        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::constant(rat(0)),
                input_vars: vec!["x_0".to_string()],
            },
            lower_bounds: vec![rat(0)],
            upper_bounds: vec![rat(1)],
            lower_multipliers: vec![sos_zero()],
            upper_multipliers: vec![sos_zero()],
            free_sos: sos_zero(),
        };

        let verdict = verify_network_property(&net, 5, rat(0), &cert);
        match verdict {
            NnSosVerdict::Invalid(msg) => {
                assert!(msg.contains("output_index"));
            }
            NnSosVerdict::Valid => panic!("should be invalid"),
        }
    }

    #[test]
    fn test_sos_to_polynomial_identity() {
        // SoS for x^2: Gram = [[1]], basis = [x]
        let cert = SosCertificate {
            gram_matrix: vec![vec![rat(1)]],
            basis: vec![Monomial::variable("x_0")],
        };
        let poly = sos_to_polynomial(&cert).expect("should expand");
        assert_eq!(
            poly,
            Polynomial::new(vec![(rat(1), Monomial::new(vec![("x_0".to_string(), 2)]))])
        );
    }

    #[test]
    fn test_two_layer_network_certificate() {
        // Network: 2 inputs -> 2 hidden (all active) -> 1 output
        // W1 = [[1, 0], [0, 1]], b1 = [0, 0]
        // W2 = [[1, 1]], b2 = [0]
        // Pattern: both active
        // Output: x_0 + x_1
        // Property: x_0 + x_1 >= 0 on [0, 1]^2
        // Certificate: 0 + 1*(x_0 - 0) + 0*(1 - x_0) + 1*(x_1 - 0) + 0*(1 - x_1)
        let net = PolynomialNetwork {
            layers: vec![
                AffineLayer {
                    weights: vec![vec![rat(1), rat(0)], vec![rat(0), rat(1)]],
                    bias: vec![rat(0), rat(0)],
                },
                AffineLayer {
                    weights: vec![vec![rat(1), rat(1)]],
                    bias: vec![rat(0)],
                },
            ],
            patterns: vec![LayerPattern(vec![
                NeuronPattern::Active,
                NeuronPattern::Active,
            ])],
        };

        let cert = NnSosCertificate {
            property: PolynomialProperty {
                polynomial: Polynomial::new(vec![
                    (rat(1), Monomial::variable("x_0")),
                    (rat(1), Monomial::variable("x_1")),
                ]),
                input_vars: vec!["x_0".to_string(), "x_1".to_string()],
            },
            lower_bounds: vec![rat(0), rat(0)],
            upper_bounds: vec![rat(1), rat(1)],
            lower_multipliers: vec![sos_constant(1), sos_constant(1)],
            upper_multipliers: vec![sos_zero(), sos_zero()],
            free_sos: sos_zero(),
        };

        let verdict = verify_network_property(&net, 0, rat(0), &cert);
        assert_eq!(verdict, NnSosVerdict::Valid);
    }
}
