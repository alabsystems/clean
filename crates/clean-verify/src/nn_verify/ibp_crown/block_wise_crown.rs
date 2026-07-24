// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Block-wise CROWN equivalence formalization (C006).
//!
//! C006 tracks the claim that, for transformer-style networks with LayerNorm at
//! block boundaries, running CROWN independently on each block and composing
//! the resulting concrete intervals through LayerNorm is equivalent to an
//! end-to-end monolithic execution that respects the same boundaries.
//!
//! Each block is a `Linear + ReLU` stack consumed by CROWN, while LayerNorm is
//! handled as interval transfer via [`verify_layernorm_forward`]. The proof
//! status is currently `DerivedPending`.

use crate::spec::ProofStatus;

use super::crown::{crown_concretize, CrownBound, CrownResult};
use super::crown_backward::{crown_linear_backward, crown_relu_backward, verify_crown_bounds};
use super::ibp::Interval;
use super::layernorm::{verify_layernorm_forward, LayerNormBounds};

type LinearLayer = (Vec<Vec<f64>>, Vec<f64>);

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct TransformerBlock {
    pub layers: Vec<(Vec<Vec<f64>>, Vec<f64>)>,
    pub layernorm_gamma: Vec<f64>,
    pub layernorm_beta: Vec<f64>,
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct BlockWiseResult {
    pub per_block: Vec<CrownResult>,
    pub composed: CrownResult,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct BlockWiseCrownSpec {
    status: ProofStatus,
}

impl BlockWiseCrownSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for BlockWiseCrownSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct BlockWiseEquivalenceProof {
    pub block_wise: CrownResult,
    pub monolithic: CrownResult,
    pub max_lower_diff: f64,
    pub max_upper_diff: f64,
    pub equivalent: bool,
}

#[must_use]
pub(crate) fn flatten_blocks(
    blocks: &[TransformerBlock],
) -> (Vec<LinearLayer>, Vec<(usize, usize)>) {
    let mut flat_layers = Vec::new();
    let mut ranges = Vec::with_capacity(blocks.len());

    for block in blocks {
        let start = flat_layers.len();
        flat_layers.extend(block.layers.iter().cloned());
        ranges.push((start, flat_layers.len()));
    }

    (flat_layers, ranges)
}

#[must_use]
pub(crate) fn output_dim(network: &[LinearLayer], fallback: usize) -> usize {
    network.last().map_or(fallback, |(weight, _)| weight.len())
}

pub(crate) fn debug_assert_valid_network(network: &[LinearLayer], input_dim: usize) {
    let mut current_dim = input_dim;

    for (layer_idx, (weight, bias)) in network.iter().enumerate() {
        debug_assert_eq!(
            weight.len(),
            bias.len(),
            "layer {layer_idx} row count must match bias length"
        );
        for row in weight {
            debug_assert_eq!(
                row.len(),
                current_dim,
                "layer {layer_idx} input dimension mismatch"
            );
        }
        current_dim = weight.len();
    }
}

pub(crate) fn debug_assert_valid_blocks(blocks: &[TransformerBlock], input_dim: usize) {
    let mut current_dim = input_dim;

    for (block_idx, block) in blocks.iter().enumerate() {
        debug_assert_valid_network(&block.layers, current_dim);
        current_dim = output_dim(&block.layers, current_dim);
        debug_assert_eq!(
            block.layernorm_gamma.len(),
            current_dim,
            "block {block_idx} gamma dimension mismatch"
        );
        debug_assert_eq!(
            block.layernorm_beta.len(),
            current_dim,
            "block {block_idx} beta dimension mismatch"
        );
    }
}

#[must_use]
pub(crate) fn intervals_from_bounds(lower: &[f64], upper: &[f64]) -> Vec<Interval> {
    debug_assert_eq!(lower.len(), upper.len(), "interval vectors must align");

    lower
        .iter()
        .zip(upper.iter())
        .map(|(&lo, &hi)| Interval::new(lo, hi))
        .collect()
}

#[must_use]
pub(crate) fn split_intervals(intervals: &[Interval]) -> (Vec<f64>, Vec<f64>) {
    let mut lower = Vec::with_capacity(intervals.len());
    let mut upper = Vec::with_capacity(intervals.len());

    for interval in intervals {
        lower.push(interval.lower);
        upper.push(interval.upper);
    }

    (lower, upper)
}

#[must_use]
pub(crate) fn layernorm_bounds_to_intervals(bounds: &LayerNormBounds) -> Vec<Interval> {
    intervals_from_bounds(&bounds.lower, &bounds.upper)
}

#[must_use]
pub(crate) fn crown_network_manual(
    network: &[LinearLayer],
    input_lower: &[f64],
    input_upper: &[f64],
) -> CrownResult {
    debug_assert_eq!(
        input_lower.len(),
        input_upper.len(),
        "input bounds must align"
    );
    debug_assert_valid_network(network, input_lower.len());

    if network.is_empty() {
        return CrownResult {
            lower: input_lower.to_vec(),
            upper: input_upper.to_vec(),
        };
    }

    let mut pre_act_lower = Vec::with_capacity(network.len());
    let mut pre_act_upper = Vec::with_capacity(network.len());
    let mut current_lower = input_lower.to_vec();
    let mut current_upper = input_upper.to_vec();

    for (layer_idx, (weight, bias)) in network.iter().enumerate() {
        let mut out_lower = Vec::with_capacity(weight.len());
        let mut out_upper = Vec::with_capacity(weight.len());

        for (row, b) in weight.iter().zip(bias.iter()) {
            let mut layer_lower = *b;
            let mut layer_upper = *b;

            for (j, coeff) in row.iter().enumerate() {
                if *coeff >= 0.0 {
                    layer_lower += coeff * current_lower[j];
                    layer_upper += coeff * current_upper[j];
                } else {
                    layer_lower += coeff * current_upper[j];
                    layer_upper += coeff * current_lower[j];
                }
            }

            out_lower.push(layer_lower);
            out_upper.push(layer_upper);
        }

        pre_act_lower.push(out_lower.clone());
        pre_act_upper.push(out_upper.clone());

        if layer_idx + 1 < network.len() {
            current_lower = out_lower.into_iter().map(|v| v.max(0.0)).collect();
            current_upper = out_upper.into_iter().map(|v| v.max(0.0)).collect();
        } else {
            current_lower = out_lower;
            current_upper = out_upper;
        }
    }

    let mut bound = CrownBound::identity(output_dim(network, input_lower.len()));
    debug_assert_eq!(
        bound.num_inputs(),
        bound.num_outputs(),
        "identity bound must be square"
    );

    for layer_idx in (0..network.len()).rev() {
        if layer_idx + 1 < network.len() {
            debug_assert_eq!(
                bound.num_inputs(),
                pre_act_lower[layer_idx].len(),
                "ReLU backward dimension mismatch"
            );
            bound =
                crown_relu_backward(&pre_act_lower[layer_idx], &pre_act_upper[layer_idx], &bound);
        }

        let (weight, bias) = &network[layer_idx];
        bound = crown_linear_backward(weight, bias, &bound);
    }

    let (lower, upper) = crown_concretize(&bound, input_lower, input_upper);
    CrownResult { lower, upper }
}

#[must_use]
pub(crate) fn max_abs_diff(left: &[f64], right: &[f64]) -> f64 {
    debug_assert_eq!(left.len(), right.len(), "difference vectors must align");

    left.iter()
        .zip(right.iter())
        .map(|(lhs, rhs)| (lhs - rhs).abs())
        .fold(0.0, f64::max)
}

#[must_use]
pub fn crown_single_block(
    network: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
) -> CrownResult {
    debug_assert_eq!(
        input_lower.len(),
        input_upper.len(),
        "input bounds must align"
    );
    debug_assert_valid_network(network, input_lower.len());

    let result = verify_crown_bounds(network, input_lower, input_upper);
    let manual = crown_network_manual(network, input_lower, input_upper);
    debug_assert!(
        max_abs_diff(&result.lower, &manual.lower) <= 1e-12
            && max_abs_diff(&result.upper, &manual.upper) <= 1e-12,
        "single-block CROWN implementations diverged"
    );
    result
}

#[must_use]
pub fn layernorm_interval_transfer(
    concrete_lower: &[f64],
    concrete_upper: &[f64],
    gamma: &[f64],
    beta: &[f64],
) -> (Vec<f64>, Vec<f64>) {
    debug_assert_eq!(
        concrete_lower.len(),
        concrete_upper.len(),
        "input bounds must align"
    );
    debug_assert_eq!(
        concrete_lower.len(),
        gamma.len(),
        "gamma dimension mismatch"
    );
    debug_assert_eq!(gamma.len(), beta.len(), "beta dimension mismatch");

    let bounds: LayerNormBounds =
        verify_layernorm_forward(concrete_lower, concrete_upper, gamma, beta);
    let intervals = layernorm_bounds_to_intervals(&bounds);
    split_intervals(&intervals)
}

#[must_use]
pub fn block_wise_crown(
    blocks: &[TransformerBlock],
    input_lower: &[f64],
    input_upper: &[f64],
) -> BlockWiseResult {
    debug_assert_eq!(
        input_lower.len(),
        input_upper.len(),
        "input bounds must align"
    );
    debug_assert_valid_blocks(blocks, input_lower.len());

    if blocks.is_empty() {
        let identity = CrownResult {
            lower: input_lower.to_vec(),
            upper: input_upper.to_vec(),
        };
        return BlockWiseResult {
            per_block: Vec::new(),
            composed: identity,
        };
    }

    let mut current_lower = input_lower.to_vec();
    let mut current_upper = input_upper.to_vec();
    let mut per_block = Vec::with_capacity(blocks.len());

    for (block_idx, block) in blocks.iter().enumerate() {
        let block_result = crown_single_block(&block.layers, &current_lower, &current_upper);
        current_lower = block_result.lower.clone();
        current_upper = block_result.upper.clone();
        per_block.push(block_result);

        if block_idx + 1 < blocks.len() {
            (current_lower, current_upper) = layernorm_interval_transfer(
                &current_lower,
                &current_upper,
                &block.layernorm_gamma,
                &block.layernorm_beta,
            );
        }
    }

    BlockWiseResult {
        per_block,
        composed: CrownResult {
            lower: current_lower,
            upper: current_upper,
        },
    }
}

#[must_use]
pub fn monolithic_crown(
    blocks: &[TransformerBlock],
    input_lower: &[f64],
    input_upper: &[f64],
) -> CrownResult {
    debug_assert_eq!(
        input_lower.len(),
        input_upper.len(),
        "input bounds must align"
    );
    debug_assert_valid_blocks(blocks, input_lower.len());

    if blocks.is_empty() {
        return CrownResult {
            lower: input_lower.to_vec(),
            upper: input_upper.to_vec(),
        };
    }

    let (flat_layers, ranges) = flatten_blocks(blocks);
    debug_assert_eq!(ranges.len(), blocks.len(), "block ranges must align");

    let mut current_lower = input_lower.to_vec();
    let mut current_upper = input_upper.to_vec();

    for (block_idx, (start, end)) in ranges.iter().copied().enumerate() {
        let segment = &flat_layers[start..end];
        let result = crown_network_manual(segment, &current_lower, &current_upper);
        current_lower = result.lower;
        current_upper = result.upper;

        if block_idx + 1 < blocks.len() {
            (current_lower, current_upper) = layernorm_interval_transfer(
                &current_lower,
                &current_upper,
                &blocks[block_idx].layernorm_gamma,
                &blocks[block_idx].layernorm_beta,
            );
        }
    }

    CrownResult {
        lower: current_lower,
        upper: current_upper,
    }
}

#[must_use]
pub fn verify_blockwise_equals_monolithic(
    blocks: &[TransformerBlock],
    input_lower: &[f64],
    input_upper: &[f64],
    tolerance: f64,
) -> BlockWiseEquivalenceProof {
    debug_assert!(tolerance >= 0.0, "tolerance must be nonnegative");

    let block_wise = block_wise_crown(blocks, input_lower, input_upper).composed;
    let monolithic = monolithic_crown(blocks, input_lower, input_upper);
    debug_assert_eq!(
        block_wise.lower.len(),
        monolithic.lower.len(),
        "lower bounds must align"
    );
    debug_assert_eq!(
        block_wise.upper.len(),
        monolithic.upper.len(),
        "upper bounds must align"
    );

    let max_lower_diff = max_abs_diff(&block_wise.lower, &monolithic.lower);
    let max_upper_diff = max_abs_diff(&block_wise.upper, &monolithic.upper);

    BlockWiseEquivalenceProof {
        block_wise,
        monolithic,
        max_lower_diff,
        max_upper_diff,
        equivalent: max_lower_diff <= tolerance && max_upper_diff <= tolerance,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_block(layers: Vec<LinearLayer>, gamma: Vec<f64>, beta: Vec<f64>) -> TransformerBlock {
        TransformerBlock {
            layers,
            layernorm_gamma: gamma,
            layernorm_beta: beta,
        }
    }

    #[test]
    fn test_block_wise_spec_is_derived_pending() {
        let spec = BlockWiseCrownSpec::new();
        assert_eq!(spec.status(), ProofStatus::DerivedPending);
    }

    #[test]
    fn test_block_wise_matches_monolithic() {
        let blocks = vec![
            test_block(
                vec![
                    (
                        vec![vec![0.4, -0.2], vec![0.1, 0.3], vec![-0.2, 0.5]],
                        vec![0.1, -0.1, 0.0],
                    ),
                    (
                        vec![vec![0.2, -0.1, 0.4], vec![-0.3, 0.5, 0.1]],
                        vec![0.0, 0.05],
                    ),
                ],
                vec![1.0, 0.75],
                vec![0.0, 0.1],
            ),
            test_block(
                vec![(vec![vec![0.6, -0.4], vec![0.2, 0.3]], vec![-0.05, 0.2])],
                vec![1.0, 1.0],
                vec![0.0, 0.0],
            ),
        ];
        let input_lower = vec![-0.4, -0.2];
        let input_upper = vec![0.7, 0.5];

        let block_result = block_wise_crown(&blocks, &input_lower, &input_upper);
        let proof = verify_blockwise_equals_monolithic(&blocks, &input_lower, &input_upper, 1e-10);

        assert_eq!(block_result.per_block.len(), 2);
        assert!(proof.equivalent, "expected proof to hold: {proof:?}");
        assert!(proof.max_lower_diff <= 1e-10);
        assert!(proof.max_upper_diff <= 1e-10);
    }
}
