// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based tests for IBP core specs (T80, T81, T82, T83).
//!
//! Uses proptest to generate random weight matrices, biases, and input
//! bounds, then verifies that IBP soundness invariants hold universally:
//! - Output bounds always contain the concrete evaluation (soundness)
//! - Output lower <= output upper (interval validity)
//! - Composition of linear+ReLU layers preserves soundness

use proptest::prelude::*;

use super::ibp::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec, Interval};
use super::ibp_extensions::IbpSigmoidSpec;

/// Strategy for a valid interval with bounds in [-10, 10].
fn interval_strategy() -> impl Strategy<Value = Interval> {
    (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(a, b)| {
        let lo = a.min(b);
        let hi = a.max(b);
        Interval::new(lo, hi)
    })
}

/// Strategy for a 2x2 weight matrix with entries in [-10, 10].
fn weights_2x2_strategy() -> impl Strategy<Value = Vec<Vec<f64>>> {
    prop::collection::vec(prop::collection::vec(-10.0f64..10.0, 2..=2), 2..=2)
}

/// Strategy for a 3x3 weight matrix with entries in [-10, 10].
fn weights_3x3_strategy() -> impl Strategy<Value = Vec<Vec<f64>>> {
    prop::collection::vec(prop::collection::vec(-10.0f64..10.0, 3..=3), 3..=3)
}

/// Strategy for a bias vector of length n with entries in [-5, 5].
fn bias_strategy(n: usize) -> impl Strategy<Value = Vec<f64>> {
    prop::collection::vec(-5.0f64..5.0, n..=n)
}

/// Strategy for input bounds of length n.
fn input_bounds_strategy(n: usize) -> impl Strategy<Value = Vec<Interval>> {
    prop::collection::vec(interval_strategy(), n..=n)
}

// ---------------------------------------------------------------------------
// T80: IBP Linear -- soundness properties
// ---------------------------------------------------------------------------

proptest! {
    /// For any 2x2 weight matrix, bias, and input bounds:
    /// the output interval lower <= upper (interval validity).
    #[test]
    fn test_ibp_linear_2x2_interval_validity(
        weights in weights_2x2_strategy(),
        bias in bias_strategy(2),
        input_bounds in input_bounds_strategy(2),
    ) {
        let spec = IbpLinearSpec::new();
        let output = spec.propagate(&weights, &bias, &input_bounds);
        for (i, iv) in output.iter().enumerate() {
            prop_assert!(
                iv.lower <= iv.upper + f64::EPSILON,
                "output[{i}] lower {} > upper {}",
                iv.lower,
                iv.upper,
            );
        }
    }

    /// For any 3x3 weight matrix, bias, and input bounds:
    /// the output interval lower <= upper.
    #[test]
    fn test_ibp_linear_3x3_interval_validity(
        weights in weights_3x3_strategy(),
        bias in bias_strategy(3),
        input_bounds in input_bounds_strategy(3),
    ) {
        let spec = IbpLinearSpec::new();
        let output = spec.propagate(&weights, &bias, &input_bounds);
        for (i, iv) in output.iter().enumerate() {
            prop_assert!(
                iv.lower <= iv.upper + f64::EPSILON,
                "output[{i}] lower {} > upper {}",
                iv.lower,
                iv.upper,
            );
        }
    }

    /// For any 2x2 weight matrix W, bias b, and input x within bounds:
    /// W*x+b falls within the propagated output bounds (soundness).
    #[test]
    fn test_ibp_linear_2x2_soundness(
        weights in weights_2x2_strategy(),
        bias in bias_strategy(2),
        input_bounds in input_bounds_strategy(2),
    ) {
        let spec = IbpLinearSpec::new();
        // Sample a concrete point: midpoint of each input interval
        let x: Vec<f64> = input_bounds
            .iter()
            .map(|iv| (iv.lower + iv.upper) / 2.0)
            .collect();
        spec.verify_concrete(&weights, &bias, &input_bounds, &x)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }

    /// Soundness at interval endpoints: x = lower.
    #[test]
    fn test_ibp_linear_2x2_soundness_at_lower(
        weights in weights_2x2_strategy(),
        bias in bias_strategy(2),
        input_bounds in input_bounds_strategy(2),
    ) {
        let spec = IbpLinearSpec::new();
        let x_lower: Vec<f64> = input_bounds.iter().map(|iv| iv.lower).collect();
        spec.verify_concrete(&weights, &bias, &input_bounds, &x_lower)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }

    /// Soundness at interval endpoints: x = upper.
    #[test]
    fn test_ibp_linear_2x2_soundness_at_upper(
        weights in weights_2x2_strategy(),
        bias in bias_strategy(2),
        input_bounds in input_bounds_strategy(2),
    ) {
        let spec = IbpLinearSpec::new();
        let x_upper: Vec<f64> = input_bounds.iter().map(|iv| iv.upper).collect();
        spec.verify_concrete(&weights, &bias, &input_bounds, &x_upper)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }
}

// ---------------------------------------------------------------------------
// T81: IBP ReLU -- soundness properties
// ---------------------------------------------------------------------------

proptest! {
    /// ReLU output bounds always have lower <= upper.
    #[test]
    fn test_ibp_relu_interval_validity(input in interval_strategy()) {
        let spec = IbpReluSpec::new();
        let output = spec.propagate(&input);
        prop_assert!(
            output.lower <= output.upper + f64::EPSILON,
            "ReLU output lower {} > upper {}",
            output.lower,
            output.upper,
        );
    }

    /// ReLU output lower bound is always >= 0.
    #[test]
    fn test_ibp_relu_output_nonnegative(input in interval_strategy()) {
        let spec = IbpReluSpec::new();
        let output = spec.propagate(&input);
        prop_assert!(
            output.lower >= -f64::EPSILON,
            "ReLU output lower {} is negative",
            output.lower,
        );
    }

    /// For any x in input bounds, ReLU(x) is within the propagated bounds.
    #[test]
    fn test_ibp_relu_soundness_at_midpoint(input in interval_strategy()) {
        let spec = IbpReluSpec::new();
        let x = (input.lower + input.upper) / 2.0;
        spec.verify_concrete(&input, x)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }

    /// ReLU soundness at the lower bound of the input interval.
    #[test]
    fn test_ibp_relu_soundness_at_lower(input in interval_strategy()) {
        let spec = IbpReluSpec::new();
        spec.verify_concrete(&input, input.lower)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }

    /// ReLU soundness at the upper bound of the input interval.
    #[test]
    fn test_ibp_relu_soundness_at_upper(input in interval_strategy()) {
        let spec = IbpReluSpec::new();
        spec.verify_concrete(&input, input.upper)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }

    /// ReLU vector propagation preserves interval validity for all elements.
    #[test]
    fn test_ibp_relu_vector_validity(inputs in input_bounds_strategy(4)) {
        let spec = IbpReluSpec::new();
        let outputs = spec.propagate_vector(&inputs);
        for (i, iv) in outputs.iter().enumerate() {
            prop_assert!(
                iv.lower <= iv.upper + f64::EPSILON,
                "vector ReLU output[{i}] lower {} > upper {}",
                iv.lower,
                iv.upper,
            );
            prop_assert!(
                iv.lower >= -f64::EPSILON,
                "vector ReLU output[{i}] lower {} is negative",
                iv.lower,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// T82: IBP Composition -- linear + ReLU chain soundness
// ---------------------------------------------------------------------------

proptest! {
    /// Composing linear + ReLU preserves interval validity.
    #[test]
    fn test_ibp_composition_linear_relu_validity(
        weights in weights_2x2_strategy(),
        bias in bias_strategy(2),
        input_bounds in input_bounds_strategy(2),
    ) {
        let comp = IbpCompositionSpec::new();
        let linear = IbpLinearSpec::new();
        let relu = IbpReluSpec::new();
        let output = comp.compose_linear_relu(&linear, &relu, &weights, &bias, &input_bounds);
        for (i, iv) in output.iter().enumerate() {
            prop_assert!(
                iv.lower <= iv.upper + f64::EPSILON,
                "composed output[{i}] lower {} > upper {}",
                iv.lower,
                iv.upper,
            );
            prop_assert!(
                iv.lower >= -f64::EPSILON,
                "composed output[{i}] lower {} is negative (post-ReLU)",
                iv.lower,
            );
        }
    }

    /// Two-layer composition: linear+ReLU -> linear+ReLU.
    /// Output bounds stay valid through both layers.
    #[test]
    fn test_ibp_two_layer_composition_validity(
        w1 in weights_2x2_strategy(),
        b1 in bias_strategy(2),
        w2 in weights_2x2_strategy(),
        b2 in bias_strategy(2),
        input_bounds in input_bounds_strategy(2),
    ) {
        let comp = IbpCompositionSpec::new();
        let linear = IbpLinearSpec::new();
        let relu = IbpReluSpec::new();

        let hidden = comp.compose_linear_relu(&linear, &relu, &w1, &b1, &input_bounds);
        let output = comp.compose_linear_relu(&linear, &relu, &w2, &b2, &hidden);

        for (i, iv) in output.iter().enumerate() {
            prop_assert!(
                iv.lower <= iv.upper + f64::EPSILON,
                "layer-2 output[{i}] lower {} > upper {}",
                iv.lower,
                iv.upper,
            );
        }
    }

    /// Chain validation: any non-empty layer bounds should pass verify_chain.
    #[test]
    fn test_ibp_composition_chain_non_empty_valid(
        bounds0 in input_bounds_strategy(2),
        bounds1 in input_bounds_strategy(3),
        bounds2 in input_bounds_strategy(2),
    ) {
        let comp = IbpCompositionSpec::new();
        let layer_bounds = vec![bounds0, bounds1, bounds2];
        comp.verify_chain(&layer_bounds)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }
}

// ---------------------------------------------------------------------------
// T83: IBP Sigmoid -- monotone activation soundness
// ---------------------------------------------------------------------------

proptest! {
    /// Sigmoid output bounds are valid (lower <= upper) and in (0, 1).
    #[test]
    fn test_ibp_sigmoid_interval_validity(input in interval_strategy()) {
        let spec = IbpSigmoidSpec::new();
        let output = spec.propagate_sigmoid(&input);
        prop_assert!(
            output.lower <= output.upper + f64::EPSILON,
            "sigmoid output lower {} > upper {}",
            output.lower,
            output.upper,
        );
        prop_assert!(output.lower >= -f64::EPSILON, "sigmoid lower {} < 0", output.lower);
        prop_assert!(output.upper <= 1.0 + f64::EPSILON, "sigmoid upper {} > 1", output.upper);
    }

    /// Sigmoid soundness: sigma(midpoint) is within propagated bounds.
    #[test]
    fn test_ibp_sigmoid_soundness_midpoint(input in interval_strategy()) {
        let spec = IbpSigmoidSpec::new();
        let x = (input.lower + input.upper) / 2.0;
        spec.verify_concrete_sigmoid(&input, x)
            .map_err(|e| TestCaseError::Fail(e.into()))?;
    }

    /// Tanh output bounds are valid and in [-1, 1].
    #[test]
    fn test_ibp_tanh_interval_validity(input in interval_strategy()) {
        let spec = IbpSigmoidSpec::new();
        let output = spec.propagate_tanh(&input);
        prop_assert!(
            output.lower <= output.upper + f64::EPSILON,
            "tanh output lower {} > upper {}",
            output.lower,
            output.upper,
        );
        prop_assert!(output.lower >= -1.0 - f64::EPSILON);
        prop_assert!(output.upper <= 1.0 + f64::EPSILON);
    }
}
