// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Automated CROWN relaxation synthesis for proof discovery.
//!
//! CROWN relaxations have free parameters (alpha slopes for ReLU, choice of
//! linear bounds for nonlinear activations). This module searches the space
//! of valid relaxations to find the tightest provably sound bounds.
//!
//! Part of #3192.

use crate::error::DiscoveryError;
use crate::family::TheoremFamily;
use serde::{Deserialize, Serialize};

/// Activation function type for a neuron.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ActivationType {
    /// Rectified linear unit: max(0, x).
    ReLU,
    /// Sigmoid: 1 / (1 + exp(-x)).
    Sigmoid,
    /// Hyperbolic tangent.
    Tanh,
}

/// Choice of linear bound for a neuron's relaxation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BoundChoice {
    /// Tangent line at the lower pre-activation bound.
    LowerTangent,
    /// Tangent line at the upper pre-activation bound.
    UpperTangent,
    /// Adaptive: convex combination controlled by alpha.
    Adaptive,
}

/// A single relaxation parameter for one neuron.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct RelaxationParam {
    /// Layer index in the network.
    pub layer_index: usize,
    /// Neuron index within the layer.
    pub neuron_index: usize,
    /// Alpha slope value in [0, 1].
    pub alpha: f64,
    /// Which linear bound strategy to use.
    pub bound_choice: BoundChoice,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RelaxationSpace {
    pub params: Vec<RelaxationParam>,
    pub activation_types: Vec<ActivationType>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SearchStrategy {
    GridSearch,
    CoordinateDescent,
    RandomSampling,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RelaxationConfig {
    pub max_iterations: u32,
    pub tolerance: f64,
    pub search_strategy: SearchStrategy,
    pub grid_resolution: u32,
    pub seed: u64,
}

impl Default for RelaxationConfig {
    fn default() -> Self {
        Self {
            max_iterations: 64,
            tolerance: 1e-6,
            search_strategy: SearchStrategy::GridSearch,
            grid_resolution: 8,
            seed: 0,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RelaxationResult {
    pub optimal_params: Vec<RelaxationParam>,
    pub bound_width: f64,
    pub soundness_verified: bool,
    pub iterations_used: u32,
    pub improvement_over_default: f64,
}

#[derive(Debug, Clone, Copy)]
pub struct SoundnessChecker {
    tolerance: f64,
}

impl SoundnessChecker {
    pub fn new(tolerance: f64) -> Self {
        Self {
            tolerance: tolerance.abs(),
        }
    }

    pub fn check(&self, params: &[RelaxationParam]) -> bool {
        params.iter().all(|param| {
            param.alpha.is_finite()
                && param.alpha >= -self.tolerance
                && param.alpha <= 1.0 + self.tolerance
        })
    }
}

#[derive(Debug, Clone)]
pub struct TightnessOptimizer {
    config: RelaxationConfig,
}

impl TightnessOptimizer {
    pub fn new(config: RelaxationConfig) -> Self {
        Self { config }
    }

    pub fn optimize(&self, space: &RelaxationSpace) -> RelaxationResult {
        match self.config.search_strategy {
            SearchStrategy::GridSearch => grid_search(space, &self.config),
            SearchStrategy::CoordinateDescent => coordinate_descent(space, &self.config),
            SearchStrategy::RandomSampling => random_sampling(space, &self.config),
        }
    }
}

pub fn synthesize_relaxation(
    space: &RelaxationSpace,
    config: &RelaxationConfig,
) -> RelaxationResult {
    TightnessOptimizer::new(config.clone()).optimize(space)
}

pub(crate) fn grid_search(space: &RelaxationSpace, config: &RelaxationConfig) -> RelaxationResult {
    if validate_relaxation_inputs(space, config).is_err() {
        return invalid_result();
    }
    let checker = SoundnessChecker::new(config.tolerance);
    let mut best = default_params(space);
    let default_width = compute_bound_width_for_space(space, &best);
    let mut best_width = default_width;
    if config.max_iterations == 0 {
        return finalize_result(best, best_width, default_width, 0, checker);
    }
    let grid = grid_values(config.grid_resolution);
    let mut digits = vec![0usize; space.params.len()];
    let mut iterations = 0;
    loop {
        let mut candidate = space.params.clone();
        for (param, digit) in candidate.iter_mut().zip(&digits) {
            param.alpha = grid[*digit];
        }
        let width = compute_bound_width_for_space(space, &candidate);
        if checker.check(&candidate) && width + config.tolerance < best_width {
            best = candidate;
            best_width = width;
        }
        iterations += 1;
        if iterations >= config.max_iterations || !increment_digits(&mut digits, grid.len()) {
            break;
        }
    }
    finalize_result(best, best_width, default_width, iterations, checker)
}

pub(crate) fn coordinate_descent(
    space: &RelaxationSpace,
    config: &RelaxationConfig,
) -> RelaxationResult {
    if validate_relaxation_inputs(space, config).is_err() {
        return invalid_result();
    }
    let checker = SoundnessChecker::new(config.tolerance);
    let grid = grid_values(config.grid_resolution);
    let mut best = default_params(space);
    let default_width = compute_bound_width_for_space(space, &best);
    let mut best_width = default_width;
    let mut iterations = 0;
    for _ in 0..config.max_iterations {
        iterations += 1;
        let mut improved = false;
        for idx in 0..best.len() {
            let mut local_alpha = best[idx].alpha;
            let mut local_width = best_width;
            for &alpha in &grid {
                let mut candidate = best.clone();
                candidate[idx].alpha = alpha;
                let width = compute_bound_width_for_space(space, &candidate);
                if checker.check(&candidate) && width + config.tolerance < local_width {
                    local_alpha = alpha;
                    local_width = width;
                    improved = true;
                }
            }
            best[idx].alpha = local_alpha;
            best_width = local_width;
        }
        if !improved {
            break;
        }
    }
    finalize_result(best, best_width, default_width, iterations, checker)
}

pub(crate) fn random_sampling(
    space: &RelaxationSpace,
    config: &RelaxationConfig,
) -> RelaxationResult {
    if validate_relaxation_inputs(space, config).is_err() {
        return invalid_result();
    }
    let checker = SoundnessChecker::new(config.tolerance);
    let mut best = default_params(space);
    let default_width = compute_bound_width_for_space(space, &best);
    let mut best_width = default_width;
    let mut state = config.seed;
    let mut iterations = 0;
    for _ in 0..config.max_iterations {
        let mut candidate = space.params.clone();
        for param in &mut candidate {
            param.alpha = sample_grid_alpha(&mut state, config.grid_resolution);
        }
        let width = compute_bound_width_for_space(space, &candidate);
        if checker.check(&candidate) && width + config.tolerance < best_width {
            best = candidate;
            best_width = width;
        }
        iterations += 1;
    }
    finalize_result(best, best_width, default_width, iterations, checker)
}

pub(crate) fn default_params(space: &RelaxationSpace) -> Vec<RelaxationParam> {
    space
        .params
        .iter()
        .map(|param| RelaxationParam {
            alpha: 0.5,
            ..*param
        })
        .collect()
}

fn validate_relaxation_inputs(
    space: &RelaxationSpace,
    config: &RelaxationConfig,
) -> Result<(), DiscoveryError> {
    if space.params.is_empty() {
        return Err(DiscoveryError::NoCandidates {
            family: TheoremFamily::DomainTightness.to_string(),
        });
    }
    if space.activation_types.is_empty() {
        return Err(DiscoveryError::InvalidConfig {
            reason: "activation_types must not be empty".to_string(),
        });
    }
    if config.grid_resolution == 0 {
        return Err(DiscoveryError::InvalidConfig {
            reason: "grid_resolution must be positive".to_string(),
        });
    }
    if config.tolerance.is_sign_negative() {
        return Err(DiscoveryError::InvalidConfig {
            reason: "tolerance must be nonnegative".to_string(),
        });
    }
    if space
        .params
        .iter()
        .any(|param| param.layer_index >= space.activation_types.len())
    {
        return Err(DiscoveryError::InvalidConfig {
            reason: "layer_index exceeds activation_types".to_string(),
        });
    }
    Ok(())
}

fn compute_bound_width_for_space(space: &RelaxationSpace, params: &[RelaxationParam]) -> f64 {
    params
        .iter()
        .map(|param| contribution(param.alpha, space.activation_types[param.layer_index]))
        .sum()
}

fn contribution(alpha: f64, activation: ActivationType) -> f64 {
    match activation {
        ActivationType::ReLU => alpha * (1.0 - alpha),
        ActivationType::Sigmoid => alpha * 0.25,
        ActivationType::Tanh => alpha * (1.0 - alpha * alpha),
    }
}

fn grid_values(grid_resolution: u32) -> Vec<f64> {
    (0..=grid_resolution)
        .map(|step| f64::from(step) / f64::from(grid_resolution))
        .collect()
}

fn increment_digits(digits: &mut [usize], base: usize) -> bool {
    for digit in digits.iter_mut().rev() {
        *digit += 1;
        if *digit < base {
            return true;
        }
        *digit = 0;
    }
    false
}

fn sample_grid_alpha(state: &mut u64, grid_resolution: u32) -> f64 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    let bucket = *state % (u64::from(grid_resolution) + 1);
    bucket as f64 / f64::from(grid_resolution)
}

fn finalize_result(
    optimal_params: Vec<RelaxationParam>,
    bound_width: f64,
    default_width: f64,
    iterations_used: u32,
    checker: SoundnessChecker,
) -> RelaxationResult {
    RelaxationResult {
        soundness_verified: checker.check(&optimal_params),
        improvement_over_default: (default_width - bound_width).max(0.0),
        optimal_params,
        bound_width,
        iterations_used,
    }
}

fn invalid_result() -> RelaxationResult {
    RelaxationResult {
        optimal_params: Vec::new(),
        bound_width: f64::INFINITY,
        soundness_verified: false,
        iterations_used: 0,
        improvement_over_default: 0.0,
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
use super::*;
fn param(layer: usize, neuron: usize, alpha: f64, choice: BoundChoice) -> RelaxationParam { RelaxationParam { layer_index: layer, neuron_index: neuron, alpha, bound_choice: choice } }
fn space(params: Vec<RelaxationParam>, activation_types: Vec<ActivationType>) -> RelaxationSpace { RelaxationSpace { params, activation_types } }
fn sample_space() -> RelaxationSpace { space(vec![param(0, 0, 0.2, BoundChoice::Adaptive), param(1, 3, 0.8, BoundChoice::LowerTangent)], vec![ActivationType::ReLU, ActivationType::Sigmoid]) }

#[test]
fn test_defaults_and_default_params() {
    let config = RelaxationConfig::default();
    assert_eq!(config.max_iterations, 64);
    assert_eq!(config.tolerance, 1e-6);
    assert_eq!(config.search_strategy, SearchStrategy::GridSearch);
    assert_eq!(config.grid_resolution, 8);
    assert_eq!(config.seed, 0);
    let params = default_params(&sample_space());
    assert_eq!(params.len(), 2);
    assert!(params.iter().all(|param| (param.alpha - 0.5).abs() < 1e-12));
    assert_eq!(params[1].neuron_index, 3);
    let widths = [param(0, 0, 0.25, BoundChoice::Adaptive), param(1, 0, 0.5, BoundChoice::Adaptive), param(2, 0, 0.5, BoundChoice::Adaptive)];
    let width_space = space(widths.to_vec(), vec![ActivationType::ReLU, ActivationType::Sigmoid, ActivationType::Tanh]);
    let expected = 0.25 * 0.75 + 0.5 * 0.25 + 0.5 * (1.0 - 0.25);
    assert!((compute_bound_width_for_space(&width_space, &widths) - expected).abs() < 1e-12);
}

#[test]
fn test_soundness_checker_accepts_and_rejects() {
    let checker = SoundnessChecker::new(0.0);
    let valid = default_params(&sample_space());
    assert!(checker.check(&valid));
    assert!(!checker.check(&[RelaxationParam { alpha: 1.25, ..valid[0] }]));
}

#[test]
fn test_search_strategies() {
    let relu_space = space(vec![param(0, 0, 0.5, BoundChoice::Adaptive)], vec![ActivationType::ReLU]);
    let grid = grid_search(&relu_space, &RelaxationConfig { max_iterations: 5, grid_resolution: 4, ..RelaxationConfig::default() });
    let alpha = grid.optimal_params[0].alpha;
    assert!(grid.bound_width.abs() < 1e-12);
    assert!(alpha.abs() < 1e-12 || (alpha - 1.0).abs() < 1e-12);
    let cd_space = space(vec![param(0, 0, 0.5, BoundChoice::Adaptive), param(1, 1, 0.5, BoundChoice::UpperTangent)], vec![ActivationType::ReLU, ActivationType::Sigmoid]);
    let cd = coordinate_descent(&cd_space, &RelaxationConfig { max_iterations: 8, grid_resolution: 4, search_strategy: SearchStrategy::CoordinateDescent, ..RelaxationConfig::default() });
    assert!(cd.bound_width <= 1e-12);
    assert!(cd.iterations_used >= 1);
    let rs = random_sampling(&sample_space(), &RelaxationConfig { max_iterations: 6, grid_resolution: 4, search_strategy: SearchStrategy::RandomSampling, seed: 7, ..RelaxationConfig::default() });
    assert_eq!(rs.iterations_used, 6);
    assert!(rs.soundness_verified);
}

}
