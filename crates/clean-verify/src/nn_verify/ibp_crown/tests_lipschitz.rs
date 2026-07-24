// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Lipschitz specs (T30, T31, T32, T33).

use super::lipschitz::*;
use crate::spec::ProofStatus;

// ---- T30: Lipschitz Compose ----

#[test]
fn test_lipschitz_compose_basic() {
    let spec = LipschitzComposeSpec::new();
    let f = LayerLipschitz::new(2.0, LipschitzSource::SpectralNorm);
    let g = LayerLipschitz::new(3.0, LipschitzSource::SpectralNorm);
    let composed = spec.compose(&f, &g);
    assert!((composed.constant() - 6.0).abs() < 1e-10);
    assert_eq!(composed.source(), LipschitzSource::Composition);
}

#[test]
fn test_lipschitz_compose_chain() {
    let spec = LipschitzComposeSpec::new();
    let layers = vec![
        LayerLipschitz::new(2.0, LipschitzSource::SpectralNorm),
        LayerLipschitz::relu(),
        LayerLipschitz::new(3.0, LipschitzSource::SpectralNorm),
        LayerLipschitz::relu(),
    ];
    let composed = spec.compose_chain(&layers);
    assert!((composed.constant() - 6.0).abs() < 1e-10);
}

#[test]
fn test_lipschitz_compose_identity() {
    let spec = LipschitzComposeSpec::new();
    let f = LayerLipschitz::new(5.0, LipschitzSource::SpectralNorm);
    let id = LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm);
    let composed = spec.compose(&f, &id);
    assert!((composed.constant() - 5.0).abs() < 1e-10);
}

#[test]
fn test_lipschitz_compose_verify_concrete() {
    let spec = LipschitzComposeSpec::new();
    let l_f = LayerLipschitz::new(2.0, LipschitzSource::SpectralNorm);
    let l_g = LayerLipschitz::new(3.0, LipschitzSource::SpectralNorm);
    spec.verify_concrete(&l_f, &l_g, 1.0, 1.5, 4.0)
        .expect("should satisfy composed bound");
}

#[test]
fn test_lipschitz_compose_verify_violation() {
    let spec = LipschitzComposeSpec::new();
    let l_f = LayerLipschitz::new(2.0, LipschitzSource::SpectralNorm);
    let l_g = LayerLipschitz::new(3.0, LipschitzSource::SpectralNorm);
    assert!(spec.verify_concrete(&l_f, &l_g, 1.0, 1.5, 7.0).is_err());
}

#[test]
fn test_lipschitz_compose_status() {
    let spec = LipschitzComposeSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

// ---- T33: Residual Lipschitz ----

#[test]
fn test_residual_lipschitz_basic() {
    let spec = ResidualLipschitzSpec::new();
    let f = LayerLipschitz::new(2.0, LipschitzSource::SpectralNorm);
    let residual = spec.residual_bound(&f);
    assert!((residual.constant() - 3.0).abs() < 1e-10);
    assert_eq!(residual.source(), LipschitzSource::Residual);
}

#[test]
fn test_residual_lipschitz_identity_branch() {
    let spec = ResidualLipschitzSpec::new();
    let f = LayerLipschitz::new(0.0, LipschitzSource::SpectralNorm);
    let residual = spec.residual_bound(&f);
    assert!((residual.constant() - 1.0).abs() < 1e-10);
}

#[test]
fn test_residual_lipschitz_verify_concrete() {
    let spec = ResidualLipschitzSpec::new();
    let f_lip = LayerLipschitz::new(2.0, LipschitzSource::SpectralNorm);
    spec.verify_concrete(&[1.0, 0.0], &[0.0, 1.0], &[2.0, 0.0], &[0.0, 2.0], &f_lip)
        .expect("residual bound should hold");
}

#[test]
fn test_residual_lipschitz_dimension_mismatch() {
    let spec = ResidualLipschitzSpec::new();
    let f_lip = LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm);
    assert!(spec
        .verify_concrete(&[1.0], &[0.0, 0.0], &[1.0], &[0.0], &f_lip)
        .is_err());
}

#[test]
fn test_residual_lipschitz_status() {
    let spec = ResidualLipschitzSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

// ---- T31: Eclipse Block Lipschitz ----

#[test]
fn test_eclipse_block_basic() {
    let spec = EclipseLipschitzSpec::new();
    let attn = LayerLipschitz::new(2.0, LipschitzSource::SpectralNorm);
    let ffn = LayerLipschitz::new(3.0, LipschitzSource::SpectralNorm);
    let block = spec.block_bound(&attn, &ffn);
    assert!((block.constant() - 12.0).abs() < 1e-10);
}

#[test]
fn test_eclipse_block_unit_lipschitz_layers() {
    let spec = EclipseLipschitzSpec::new();
    let attn = LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm);
    let ffn = LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm);
    let block = spec.block_bound(&attn, &ffn);
    assert!((block.constant() - 4.0).abs() < 1e-10);
}

#[test]
fn test_eclipse_stacked_blocks() {
    let spec = EclipseLipschitzSpec::new();
    let blocks = vec![
        (
            LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm),
            LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm),
        ),
        (
            LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm),
            LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm),
        ),
    ];
    let stacked = spec.stacked_blocks_bound(&blocks);
    assert!((stacked.constant() - 16.0).abs() < 1e-10);
}

#[test]
fn test_eclipse_block_status() {
    let spec = EclipseLipschitzSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

// ---- LayerLipschitz helpers ----

#[test]
fn test_layer_lipschitz_relu() {
    let relu = LayerLipschitz::relu();
    assert!((relu.constant() - 1.0).abs() < 1e-10);
    assert_eq!(relu.source(), LipschitzSource::Relu);
}

#[test]
fn test_layer_lipschitz_sigmoid() {
    let sig = LayerLipschitz::sigmoid();
    assert!((sig.constant() - 0.25).abs() < 1e-10);
    assert_eq!(sig.source(), LipschitzSource::Sigmoid);
}

// ---- T32: Spectral norm ----

#[test]
fn test_spectral_norm_lipschitz_source() {
    let l = LayerLipschitz::new(5.0, LipschitzSource::SpectralNorm);
    assert_eq!(l.source(), LipschitzSource::SpectralNorm);
    assert!((l.constant() - 5.0).abs() < 1e-10);
}
