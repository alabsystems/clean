// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial representation of ReLU network outputs.
//!
//! When a ReLU network has a known activation pattern (all neurons are
//! either stably active or stably inactive), the network function is
//! piecewise linear and can be expressed as a polynomial of degree 1 in
//! the input variables. More generally, when we consider quadratic or
//! higher-degree relaxations, network outputs can be expressed as
//! polynomials of bounded degree.
//!
//! This module provides the bridge between neural network structure and
//! polynomial representation, which is the prerequisite for applying
//! Nullstellensatz / SoS certificate verification.
//!
//! ## Relationship to `smt_verify::nra`
//!
//! The NRA module provides general-purpose `Polynomial`, `Monomial`, and
//! `SosCertificate` types for SMT proof checking. This module provides
//! NN-specific types that *produce* polynomials from network structure,
//! then delegates to NRA for SoS verification.

use std::collections::BTreeMap;

use num_rational::Rational64;

use crate::smt_verify::nra::{Monomial, Polynomial, SosCertificate};

/// A linear layer represented as an affine map: y = Wx + b.
///
/// Weights and biases are exact rationals for sound polynomial arithmetic.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct AffineLayer {
    /// Weight matrix, row-major: `weights[i][j]` is the weight from input j
    /// to output i.
    pub(crate) weights: Vec<Vec<Rational64>>,
    /// Bias vector.
    pub(crate) bias: Vec<Rational64>,
}

/// Activation pattern for a ReLU layer.
///
/// Each neuron is classified as stably active (identity), stably inactive
/// (zero), or unknown (crossing). For Nullstellensatz certificates, we
/// require all neurons to have known patterns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NeuronPattern {
    /// Pre-activation is always non-negative: ReLU is identity.
    Active,
    /// Pre-activation is always non-positive: ReLU outputs zero.
    Inactive,
}

/// A full activation pattern for a ReLU layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LayerPattern(pub(crate) Vec<NeuronPattern>);

/// A ReLU network with known activation patterns, representable as a
/// polynomial map from inputs to outputs.
///
/// Given:
/// - L affine layers (weight matrices + biases)
/// - L-1 activation patterns (one per hidden layer)
///
/// The network computes: `y = W_L * diag(p_{L-1}) * ... * W_2 * diag(p_1) * W_1 * x + b_combined`
/// where `p_i` is the diagonal matrix encoding the activation pattern
/// (1 for active, 0 for inactive).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PolynomialNetwork {
    /// Affine layers (at least 2: input layer + output layer).
    pub(crate) layers: Vec<AffineLayer>,
    /// Activation patterns for hidden layers.
    /// `patterns.len() == layers.len() - 1`
    pub(crate) patterns: Vec<LayerPattern>,
}

/// A verification property expressed as a polynomial inequality.
///
/// The property `p(x) >= 0` must hold for all inputs x in the input domain.
/// For NN verification, this typically encodes `output_i - threshold >= 0`
/// or `output_i - output_j >= 0` (robustness).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct PolynomialProperty {
    /// The polynomial that must be non-negative on the domain.
    pub(crate) polynomial: Polynomial,
    /// Variable names for the input dimensions.
    pub(crate) input_vars: Vec<String>,
}

/// An SoS certificate for a neural network verification property.
///
/// Proves that `property(x) >= 0` for all `x` in `[lower, upper]` by
/// providing:
/// 1. Domain constraints: `x_i - l_i >= 0` and `u_i - x_i >= 0`
/// 2. SoS multipliers for each constraint (Positivstellensatz)
///
/// The certificate is valid if:
/// `sum_i s_i(x) * (x_i - l_i) + sum_i t_i(x) * (u_i - x_i) + s_0(x) = property(x)`
/// where all `s_i, t_i, s_0` are SoS polynomials.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct NnSosCertificate {
    /// The property being verified: `p(x) >= 0`.
    pub(crate) property: PolynomialProperty,
    /// Lower bounds on input variables.
    pub(crate) lower_bounds: Vec<Rational64>,
    /// Upper bounds on input variables.
    pub(crate) upper_bounds: Vec<Rational64>,
    /// SoS multiplier for each lower-bound constraint `x_i - l_i >= 0`.
    pub(crate) lower_multipliers: Vec<SosCertificate>,
    /// SoS multiplier for each upper-bound constraint `u_i - x_i >= 0`.
    pub(crate) upper_multipliers: Vec<SosCertificate>,
    /// Free SoS polynomial (non-negative everywhere).
    pub(crate) free_sos: SosCertificate,
}

/// Convert a stable ReLU network into its polynomial representation.
///
/// For a network with known activation patterns, the output is an affine
/// function of the input. This computes the effective weight matrix and
/// bias by composing all layers with their activation patterns.
///
/// Returns one `Polynomial` per output dimension, each expressed in terms
/// of input variables `x_0, x_1, ..., x_{n-1}`.
#[must_use]
pub(crate) fn network_to_polynomials(network: &PolynomialNetwork) -> Option<Vec<Polynomial>> {
    if network.layers.is_empty() {
        return None;
    }
    if network.patterns.len() + 1 != network.layers.len() {
        return None;
    }

    let input_dim = network.layers[0].weights.first()?.len();

    // Start with identity: effective_weight[i][j] = delta_{ij}, effective_bias = 0
    // We'll compose forward: after layer k, effective_weight and effective_bias
    // describe the mapping from input to post-layer-k output.

    // Initialize with first layer
    let first = &network.layers[0];
    let mut eff_weight = first.weights.clone();
    let mut eff_bias = first.bias.clone();

    // Apply each hidden activation pattern + next layer
    for (layer_idx, pattern) in network.patterns.iter().enumerate() {
        // Apply activation pattern (diagonal mask)
        apply_activation_pattern(&mut eff_weight, &mut eff_bias, pattern);

        // Apply next affine layer
        let next_layer = &network.layers[layer_idx + 1];
        let (new_weight, new_bias) = compose_affine(
            &next_layer.weights,
            &next_layer.bias,
            &eff_weight,
            &eff_bias,
        );
        eff_weight = new_weight;
        eff_bias = new_bias;
    }

    // Convert to polynomials: for each output i,
    // p_i(x) = sum_j eff_weight[i][j] * x_j + eff_bias[i]
    let zero = Rational64::from_integer(0);
    let mut result = Vec::with_capacity(eff_weight.len());

    for (i, row) in eff_weight.iter().enumerate() {
        let mut terms = Vec::new();
        for (j, w) in row.iter().enumerate() {
            if *w != zero {
                terms.push((*w, Monomial::variable(format!("x_{j}"))));
            }
        }
        if i < eff_bias.len() && eff_bias[i] != zero {
            terms.push((eff_bias[i], Monomial::one()));
        }
        result.push(Polynomial::new(terms));
    }

    // Verify dimensions are consistent
    if eff_weight.iter().any(|row| row.len() != input_dim) {
        return None;
    }

    Some(result)
}

/// Apply activation pattern as a diagonal mask on weight and bias.
fn apply_activation_pattern(
    weights: &mut [Vec<Rational64>],
    bias: &mut [Rational64],
    pattern: &LayerPattern,
) {
    let zero = Rational64::from_integer(0);

    for (neuron_idx, pat) in pattern.0.iter().enumerate() {
        match pat {
            NeuronPattern::Active => {
                // Identity: keep weights and bias as-is
            }
            NeuronPattern::Inactive => {
                // Zero out this neuron's row in the weight matrix and bias
                if neuron_idx < weights.len() {
                    for w in &mut weights[neuron_idx] {
                        *w = zero;
                    }
                }
                if neuron_idx < bias.len() {
                    bias[neuron_idx] = zero;
                }
            }
        }
    }
}

/// Compose two affine maps: (A2, b2) . (A1, b1) = (A2*A1, A2*b1 + b2).
fn compose_affine(
    a2: &[Vec<Rational64>],
    b2: &[Rational64],
    a1: &[Vec<Rational64>],
    b1: &[Rational64],
) -> (Vec<Vec<Rational64>>, Vec<Rational64>) {
    let zero = Rational64::from_integer(0);
    let out_dim = a2.len();
    let in_dim = a1.first().map_or(0, |r| r.len());

    let mut result_weight = vec![vec![zero; in_dim]; out_dim];
    let mut result_bias = vec![zero; out_dim];

    for i in 0..out_dim {
        // result_weight[i][j] = sum_k a2[i][k] * a1[k][j]
        for (k, a1_row) in a1.iter().enumerate() {
            if k >= a2[i].len() {
                continue;
            }
            let a2_ik = &a2[i][k];
            if *a2_ik == zero {
                continue;
            }
            for (j, a1_kj) in a1_row.iter().enumerate() {
                if *a1_kj != zero {
                    result_weight[i][j] += *a2_ik * *a1_kj;
                }
            }
        }

        // result_bias[i] = sum_k a2[i][k] * b1[k] + b2[i]
        let mut bias_sum = if i < b2.len() { b2[i] } else { zero };
        for (k, b1_k) in b1.iter().enumerate() {
            if k < a2[i].len() && a2[i][k] != zero {
                bias_sum += a2[i][k] * *b1_k;
            }
        }
        result_bias[i] = bias_sum;
    }

    (result_weight, result_bias)
}

/// Build domain constraint polynomials for a box domain.
///
/// For input variables `x_0, ..., x_{n-1}` in `[lower, upper]`, produces:
/// - `x_i - lower_i >= 0` (n polynomials)
/// - `upper_i - x_i >= 0` (n polynomials)
#[must_use]
pub(crate) fn box_domain_constraints(
    lower: &[Rational64],
    upper: &[Rational64],
) -> Option<Vec<Polynomial>> {
    if lower.len() != upper.len() {
        return None;
    }
    let n = lower.len();
    let mut constraints = Vec::with_capacity(2 * n);

    for i in 0..n {
        // x_i - lower_i >= 0
        let var = Monomial::variable(format!("x_{i}"));
        let lower_constraint = Polynomial::new(vec![
            (Rational64::from_integer(1), var.clone()),
            (-lower[i], Monomial::one()),
        ]);
        constraints.push(lower_constraint);

        // upper_i - x_i >= 0
        let upper_constraint = Polynomial::new(vec![
            (Rational64::from_integer(-1), var),
            (upper[i], Monomial::one()),
        ]);
        constraints.push(upper_constraint);
    }

    Some(constraints)
}

/// Evaluate a polynomial network at a specific input point.
///
/// This is used for testing: we verify that the polynomial representation
/// produces the same output as direct network evaluation.
#[must_use]
pub(crate) fn evaluate_network(
    network: &PolynomialNetwork,
    input: &[Rational64],
) -> Option<Vec<Rational64>> {
    let zero = Rational64::from_integer(0);
    let mut current = input.to_vec();

    for (layer_idx, layer) in network.layers.iter().enumerate() {
        // Affine: y = Wx + b
        let mut output = Vec::with_capacity(layer.weights.len());
        for (i, row) in layer.weights.iter().enumerate() {
            let mut sum = if i < layer.bias.len() {
                layer.bias[i]
            } else {
                zero
            };
            for (j, w) in row.iter().enumerate() {
                if j < current.len() {
                    sum += *w * current[j];
                }
            }
            output.push(sum);
        }

        // Apply activation (except after last layer)
        if layer_idx < network.patterns.len() {
            let pattern = &network.patterns[layer_idx];
            for (neuron_idx, pat) in pattern.0.iter().enumerate() {
                if neuron_idx < output.len() {
                    match pat {
                        NeuronPattern::Active => {} // identity
                        NeuronPattern::Inactive => {
                            output[neuron_idx] = zero;
                        }
                    }
                }
            }
        }

        current = output;
    }

    Some(current)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> Rational64 {
        Rational64::from_integer(n)
    }

    fn simple_network() -> PolynomialNetwork {
        // Single hidden layer: 2 inputs -> 2 hidden -> 1 output
        // W1 = [[1, 2], [3, 4]], b1 = [0, 0]
        // Pattern: [Active, Active]
        // W2 = [[1, 1]], b2 = [1]
        PolynomialNetwork {
            layers: vec![
                AffineLayer {
                    weights: vec![vec![rat(1), rat(2)], vec![rat(3), rat(4)]],
                    bias: vec![rat(0), rat(0)],
                },
                AffineLayer {
                    weights: vec![vec![rat(1), rat(1)]],
                    bias: vec![rat(1)],
                },
            ],
            patterns: vec![LayerPattern(vec![
                NeuronPattern::Active,
                NeuronPattern::Active,
            ])],
        }
    }

    #[test]
    fn test_network_to_polynomials_simple() {
        let net = simple_network();
        let polys = network_to_polynomials(&net).expect("should produce polynomials");
        assert_eq!(polys.len(), 1, "single output");

        // Output = (1*x0 + 2*x1) + (3*x0 + 4*x1) + 1 = 4*x0 + 6*x1 + 1
        let assignment = {
            let mut m = BTreeMap::new();
            m.insert("x_0".to_string(), rat(1));
            m.insert("x_1".to_string(), rat(1));
            m
        };
        let value = polys[0].evaluate(&assignment).expect("should evaluate");
        assert_eq!(value, rat(11)); // 4*1 + 6*1 + 1 = 11
    }

    #[test]
    fn test_network_to_polynomials_with_inactive() {
        // Same as simple_network but second hidden neuron is inactive
        let net = PolynomialNetwork {
            layers: vec![
                AffineLayer {
                    weights: vec![vec![rat(1), rat(2)], vec![rat(3), rat(4)]],
                    bias: vec![rat(0), rat(0)],
                },
                AffineLayer {
                    weights: vec![vec![rat(1), rat(1)]],
                    bias: vec![rat(1)],
                },
            ],
            patterns: vec![LayerPattern(vec![
                NeuronPattern::Active,
                NeuronPattern::Inactive,
            ])],
        };

        let polys = network_to_polynomials(&net).expect("should produce polynomials");
        // Output = (1*x0 + 2*x1) + 0 + 1 = x0 + 2*x1 + 1
        let assignment = {
            let mut m = BTreeMap::new();
            m.insert("x_0".to_string(), rat(1));
            m.insert("x_1".to_string(), rat(1));
            m
        };
        let value = polys[0].evaluate(&assignment).expect("should evaluate");
        assert_eq!(value, rat(4)); // 1 + 2 + 1 = 4
    }

    #[test]
    fn test_network_polynomial_matches_direct_eval() {
        let net = simple_network();
        let polys = network_to_polynomials(&net).expect("should produce polynomials");

        // Test at several points
        for (x0, x1) in [(0, 0), (1, 0), (0, 1), (2, 3), (-1, 5)] {
            let input = vec![rat(x0), rat(x1)];
            let direct = evaluate_network(&net, &input).expect("should evaluate directly");

            let assignment = {
                let mut m = BTreeMap::new();
                m.insert("x_0".to_string(), rat(x0));
                m.insert("x_1".to_string(), rat(x1));
                m
            };
            let poly_value = polys[0]
                .evaluate(&assignment)
                .expect("should evaluate poly");

            assert_eq!(
                direct[0], poly_value,
                "polynomial should match direct eval at ({x0}, {x1})"
            );
        }
    }

    #[test]
    fn test_box_domain_constraints() {
        let lower = vec![rat(-1), rat(0)];
        let upper = vec![rat(1), rat(2)];
        let constraints =
            box_domain_constraints(&lower, &upper).expect("should produce constraints");
        assert_eq!(constraints.len(), 4);

        // Verify at interior point (0, 1)
        let assignment = {
            let mut m = BTreeMap::new();
            m.insert("x_0".to_string(), rat(0));
            m.insert("x_1".to_string(), rat(1));
            m
        };
        for (i, c) in constraints.iter().enumerate() {
            let val = c.evaluate(&assignment).expect("should evaluate");
            assert!(
                val >= rat(0),
                "constraint {i} should be non-negative at interior point, got {val}"
            );
        }
    }

    #[test]
    fn test_empty_network() {
        let net = PolynomialNetwork {
            layers: vec![],
            patterns: vec![],
        };
        assert!(
            network_to_polynomials(&net).is_none(),
            "empty network should return None"
        );
    }

    #[test]
    fn test_mismatched_patterns_layers() {
        let net = PolynomialNetwork {
            layers: vec![AffineLayer {
                weights: vec![vec![rat(1)]],
                bias: vec![rat(0)],
            }],
            patterns: vec![LayerPattern(vec![NeuronPattern::Active])],
        };
        assert!(
            network_to_polynomials(&net).is_none(),
            "patterns.len() + 1 != layers.len() should return None"
        );
    }
}
