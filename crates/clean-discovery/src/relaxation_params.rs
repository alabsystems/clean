// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::relaxation::{ActivationType, BoundChoice, RelaxationParam};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct NeuronAlpha {
    pub(crate) layer: usize,
    pub(crate) neuron: usize,
    pub(crate) alpha: f64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LayerRelaxation {
    pub layer_index: usize,
    pub neuron_alphas: Vec<f64>,
    pub activation: ActivationType,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MultiLayerRelaxation {
    pub layers: Vec<LayerRelaxation>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct RelaxationCache {
    entries: HashMap<String, MultiLayerRelaxation>,
}

#[rustfmt::skip]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SigmoidBound { pub contact_point: f64, pub slope: f64, pub intercept: f64 }

#[rustfmt::skip]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TanhBound { pub contact_point: f64, pub slope: f64, pub intercept: f64 }

pub fn compose_layers(layers: &[LayerRelaxation]) -> Vec<RelaxationParam> {
    let mut params = Vec::with_capacity(layers.iter().map(|layer| layer.neuron_alphas.len()).sum());
    for layer in layers {
        for (neuron, alpha) in layer.neuron_alphas.iter().copied().enumerate() {
            let neuron_alpha = NeuronAlpha {
                layer: layer.layer_index,
                neuron,
                alpha,
            };
            params.push(RelaxationParam {
                layer_index: neuron_alpha.layer,
                neuron_index: neuron_alpha.neuron,
                alpha: neuron_alpha.alpha,
                bound_choice: bound_choice_for_activation(&layer.activation),
            });
        }
    }
    params
}

#[rustfmt::skip]
pub fn architecture_key(layer_widths: &[usize]) -> String {
    layer_widths.iter().map(usize::to_string).collect::<Vec<_>>().join("x")
}

pub fn sigmoid_tangent(x0: f64) -> SigmoidBound {
    let value = 1.0 / (1.0 + (-x0).exp());
    let slope = value * (1.0 - value);
    SigmoidBound {
        contact_point: x0,
        slope,
        intercept: value - slope * x0,
    }
}

pub fn tanh_tangent(x0: f64) -> TanhBound {
    let value = x0.tanh();
    let slope = 1.0 - value * value;
    TanhBound {
        contact_point: x0,
        slope,
        intercept: value - slope * x0,
    }
}

pub fn relu_alpha_bounds(lower: f64, upper: f64) -> (f64, f64) {
    if lower >= 0.0 {
        (1.0, 1.0)
    } else if upper <= 0.0 {
        (0.0, 0.0)
    } else {
        (0.0, 1.0)
    }
}

impl MultiLayerRelaxation {
    pub fn total_params(&self) -> usize {
        self.layers
            .iter()
            .map(|layer| layer.neuron_alphas.len())
            .sum()
    }

    pub fn flatten_alphas(&self) -> Vec<f64> {
        self.layers
            .iter()
            .flat_map(|layer| layer.neuron_alphas.iter().copied())
            .collect()
    }

    pub fn from_flat_alphas(
        layer_widths: &[usize],
        activations: &[ActivationType],
        alphas: &[f64],
    ) -> Result<Self, String> {
        if layer_widths.len() != activations.len() {
            return Err(format!(
                "layer width count {} does not match activation count {}",
                layer_widths.len(),
                activations.len()
            ));
        }
        let expected: usize = layer_widths.iter().sum();
        if expected != alphas.len() {
            return Err(format!(
                "expected {expected} alpha values for architecture {}, got {}",
                architecture_key(layer_widths),
                alphas.len()
            ));
        }
        let mut offset = 0;
        let mut layers = Vec::with_capacity(layer_widths.len());
        for (layer_index, (&width, activation)) in layer_widths.iter().zip(activations).enumerate()
        {
            let end = offset + width;
            layers.push(LayerRelaxation {
                layer_index,
                neuron_alphas: alphas[offset..end].to_vec(),
                activation: *activation,
            });
            offset = end;
        }
        Ok(Self { layers })
    }
}

impl Default for RelaxationCache {
    fn default() -> Self {
        Self::new()
    }
}

impl RelaxationCache {
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }
    pub fn get(&self, key: &str) -> Option<&MultiLayerRelaxation> {
        self.entries.get(key)
    }
    pub fn insert(&mut self, key: String, relaxation: MultiLayerRelaxation) {
        self.entries.insert(key, relaxation);
    }
    pub fn save_to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
    pub fn load_from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

#[rustfmt::skip]
fn bound_choice_for_activation(_activation: &ActivationType) -> BoundChoice { BoundChoice::Adaptive }

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    fn layer(
        layer_index: usize,
        neuron_alphas: &[f64],
        activation: ActivationType,
    ) -> LayerRelaxation {
        LayerRelaxation {
            layer_index,
            neuron_alphas: neuron_alphas.to_vec(),
            activation,
        }
    }

    fn sample_relaxation() -> MultiLayerRelaxation {
        MultiLayerRelaxation {
            layers: vec![
                layer(0, &[0.1, 0.2], ActivationType::ReLU),
                layer(1, &[0.3, 0.4, 0.5], ActivationType::Sigmoid),
            ],
        }
    }

    #[test]
    fn compose_single_layer() {
        let params = compose_layers(&[layer(1, &[0.25, 0.75], ActivationType::ReLU)]);
        assert_eq!(
            params,
            vec![
                RelaxationParam {
                    layer_index: 1,
                    neuron_index: 0,
                    alpha: 0.25,
                    bound_choice: BoundChoice::Adaptive
                },
                RelaxationParam {
                    layer_index: 1,
                    neuron_index: 1,
                    alpha: 0.75,
                    bound_choice: BoundChoice::Adaptive
                },
            ]
        );
    }

    #[test]
    fn compose_multi_layer() {
        let params = compose_layers(&[
            layer(0, &[0.1, 0.2], ActivationType::ReLU),
            layer(2, &[0.3], ActivationType::Sigmoid),
        ]);
        assert_eq!(params.len(), 3);
        assert_eq!(params[2].layer_index, 2);
        assert_eq!(params[2].neuron_index, 0);
    }

    #[test]
    fn architecture_key_is_deterministic() {
        assert_eq!(architecture_key(&[2, 4, 1]), architecture_key(&[2, 4, 1]));
        assert_eq!(architecture_key(&[2, 4, 1]), "2x4x1");
    }

    #[test]
    fn sigmoid_tangent_at_zero_has_expected_slope() {
        let bound = sigmoid_tangent(0.0);
        assert!((bound.slope - 0.25).abs() < EPS);
        assert!((bound.intercept - 0.5).abs() < EPS);
    }

    #[test]
    fn tanh_tangent_at_zero_has_expected_slope() {
        let bound = tanh_tangent(0.0);
        assert!((bound.slope - 1.0).abs() < EPS);
        assert!(bound.intercept.abs() < EPS);
    }

    #[test]
    fn relu_alpha_bounds_cover_cases() {
        assert_eq!(relu_alpha_bounds(1.0, 2.0), (1.0, 1.0));
        assert_eq!(relu_alpha_bounds(-2.0, -1.0), (0.0, 0.0));
        assert_eq!(relu_alpha_bounds(-1.0, 2.0), (0.0, 1.0));
    }

    #[test]
    fn flatten_and_unflatten_roundtrip() {
        let widths = [2, 1, 2];
        #[rustfmt::skip]
        let activations = [ActivationType::ReLU, ActivationType::Sigmoid, ActivationType::Tanh];
        let alphas = [0.1, 0.2, 0.3, 0.4, 0.5];
        let relaxation = MultiLayerRelaxation::from_flat_alphas(&widths, &activations, &alphas)
            .expect("valid flatten/unflatten roundtrip");
        assert_eq!(relaxation.flatten_alphas(), alphas.to_vec());
        assert_eq!(relaxation.layers[1].activation, ActivationType::Sigmoid);
    }

    #[test]
    fn cache_insert_and_get() {
        let key = architecture_key(&[2, 3]);
        let relaxation = sample_relaxation();
        let mut cache = RelaxationCache::new();
        cache.insert(key.clone(), relaxation.clone());
        assert_eq!(cache.get(&key), Some(&relaxation));
    }

    #[test]
    fn json_serialization_roundtrip() {
        let mut cache = RelaxationCache::new();
        cache.insert(architecture_key(&[2, 3]), sample_relaxation());
        let json = cache.save_to_json().expect("serialize cache");
        assert_eq!(
            RelaxationCache::load_from_json(&json).expect("deserialize cache"),
            cache
        );
    }

    #[test]
    fn total_params_count_matches_flattened_length() {
        let relaxation = sample_relaxation();
        assert_eq!(relaxation.total_params(), 5);
        assert_eq!(relaxation.flatten_alphas().len(), 5);
    }
}
