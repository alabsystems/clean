// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based tests for Interval and Lipschitz types.
//!
//! Verifies mathematical invariants:
//! - Interval subset relation is reflexive
//! - Point intervals have zero width
//! - Lipschitz composition is associative and has identity element
//! - Residual Lipschitz bound is always >= 1

use proptest::prelude::*;

use super::ibp::Interval;
use super::lipschitz::{
    EclipseLipschitzSpec, LayerLipschitz, LipschitzComposeSpec, LipschitzSource,
    ResidualLipschitzSpec,
};

/// Strategy for a valid interval with bounds in [-100, 100].
fn interval_strategy() -> impl Strategy<Value = Interval> {
    (-100.0f64..100.0, -100.0f64..100.0).prop_map(|(a, b)| {
        let lo = a.min(b);
        let hi = a.max(b);
        Interval::new(lo, hi)
    })
}

/// Strategy for a non-negative Lipschitz constant in [0, 50].
fn lipschitz_strategy() -> impl Strategy<Value = LayerLipschitz> {
    (0.0f64..50.0).prop_map(|c| LayerLipschitz::new(c, LipschitzSource::SpectralNorm))
}

// ---------------------------------------------------------------------------
// Interval properties
// ---------------------------------------------------------------------------

proptest! {
    /// Subset is reflexive: every interval is a subset of itself.
    #[test]
    fn test_interval_subset_reflexive(iv in interval_strategy()) {
        prop_assert!(
            iv.is_subset_of(&iv),
            "interval [{}, {}] should be a subset of itself",
            iv.lower,
            iv.upper,
        );
    }

    /// Point intervals have zero width.
    #[test]
    fn test_interval_point_zero_width(v in -100.0f64..100.0) {
        let p = Interval::point(v);
        prop_assert!(
            p.width().abs() < f64::EPSILON,
            "point interval should have zero width, got {}",
            p.width(),
        );
    }

    /// A narrower interval is a subset of a wider one containing it.
    #[test]
    fn test_interval_inner_subset_outer(
        center in -50.0f64..50.0,
        half_inner in 0.0f64..20.0,
        extra in 0.0f64..20.0,
    ) {
        let inner = Interval::new(center - half_inner, center + half_inner);
        let outer = Interval::new(
            center - half_inner - extra,
            center + half_inner + extra,
        );
        prop_assert!(
            inner.is_subset_of(&outer),
            "[{}, {}] should be subset of [{}, {}]",
            inner.lower, inner.upper, outer.lower, outer.upper,
        );
    }

    /// Width is always non-negative.
    #[test]
    fn test_interval_width_nonneg(iv in interval_strategy()) {
        prop_assert!(
            iv.width() >= -f64::EPSILON,
            "interval width should be non-negative, got {}",
            iv.width(),
        );
    }

    /// A point inside an interval: midpoint is always contained.
    #[test]
    fn test_interval_midpoint_contained(iv in interval_strategy()) {
        let mid = (iv.lower + iv.upper) / 2.0;
        let mid_iv = Interval::point(mid);
        prop_assert!(
            mid_iv.is_subset_of(&iv),
            "midpoint {} should be in [{}, {}]",
            mid, iv.lower, iv.upper,
        );
    }
}

// ---------------------------------------------------------------------------
// Lipschitz composition properties
// ---------------------------------------------------------------------------

proptest! {
    /// Composition with identity (L=1): composed constant equals the other.
    #[test]
    fn test_lipschitz_compose_identity(lip in lipschitz_strategy()) {
        let spec = LipschitzComposeSpec::new();
        let id = LayerLipschitz::new(1.0, LipschitzSource::SpectralNorm);
        let composed = spec.compose(&lip, &id);
        prop_assert!(
            (composed.constant() - lip.constant()).abs() < f64::EPSILON * lip.constant().max(1.0),
            "compose with identity should preserve constant: {} vs {}",
            composed.constant(),
            lip.constant(),
        );
    }

    /// Composition with zero (L=0): composed constant is 0.
    #[test]
    fn test_lipschitz_compose_zero(lip in lipschitz_strategy()) {
        let spec = LipschitzComposeSpec::new();
        let zero = LayerLipschitz::new(0.0, LipschitzSource::SpectralNorm);
        let composed = spec.compose(&lip, &zero);
        prop_assert!(
            composed.constant().abs() < f64::EPSILON,
            "compose with zero should give 0, got {}",
            composed.constant(),
        );
    }

    /// Composition is associative: (a . b) . c == a . (b . c).
    #[test]
    fn test_lipschitz_compose_associative(
        a in lipschitz_strategy(),
        b in lipschitz_strategy(),
        c in lipschitz_strategy(),
    ) {
        let spec = LipschitzComposeSpec::new();
        let ab = spec.compose(&a, &b);
        let ab_c = spec.compose(&ab, &c);

        let bc = spec.compose(&b, &c);
        let a_bc = spec.compose(&a, &bc);

        let tol = f64::EPSILON * ab_c.constant().max(a_bc.constant()).max(1.0) * 10.0;
        prop_assert!(
            (ab_c.constant() - a_bc.constant()).abs() < tol,
            "(a.b).c = {} != a.(b.c) = {}",
            ab_c.constant(),
            a_bc.constant(),
        );
    }

    /// Chain composition equals product of all constants.
    #[test]
    fn test_lipschitz_chain_product(
        constants in prop::collection::vec(0.0f64..10.0, 1..=5),
    ) {
        let spec = LipschitzComposeSpec::new();
        let layers: Vec<LayerLipschitz> = constants
            .iter()
            .map(|&c| LayerLipschitz::new(c, LipschitzSource::SpectralNorm))
            .collect();
        let composed = spec.compose_chain(&layers);
        let expected: f64 = constants.iter().product();
        let tol = f64::EPSILON * expected.max(1.0) * 100.0;
        prop_assert!(
            (composed.constant() - expected).abs() < tol,
            "chain product {} != expected {}",
            composed.constant(),
            expected,
        );
    }

    /// Composed constant is always non-negative.
    #[test]
    fn test_lipschitz_compose_nonneg(
        a in lipschitz_strategy(),
        b in lipschitz_strategy(),
    ) {
        let spec = LipschitzComposeSpec::new();
        let composed = spec.compose(&a, &b);
        prop_assert!(
            composed.constant() >= -f64::EPSILON,
            "composed Lipschitz constant should be non-negative, got {}",
            composed.constant(),
        );
    }
}

// ---------------------------------------------------------------------------
// Residual Lipschitz properties
// ---------------------------------------------------------------------------

proptest! {
    /// Residual bound is always >= 1 (identity contributes L=1).
    #[test]
    fn test_residual_lipschitz_at_least_one(lip in lipschitz_strategy()) {
        let spec = ResidualLipschitzSpec::new();
        let residual = spec.residual_bound(&lip);
        prop_assert!(
            residual.constant() >= 1.0 - f64::EPSILON,
            "residual Lipschitz constant should be >= 1, got {}",
            residual.constant(),
        );
    }

    /// Residual bound equals 1 + L_f exactly.
    #[test]
    fn test_residual_lipschitz_value(lip in lipschitz_strategy()) {
        let spec = ResidualLipschitzSpec::new();
        let residual = spec.residual_bound(&lip);
        let expected = 1.0 + lip.constant();
        prop_assert!(
            (residual.constant() - expected).abs() < f64::EPSILON * expected.max(1.0),
            "residual constant {} != 1 + {} = {}",
            residual.constant(),
            lip.constant(),
            expected,
        );
    }
}

// ---------------------------------------------------------------------------
// Eclipse block Lipschitz properties
// ---------------------------------------------------------------------------

proptest! {
    /// Eclipse block bound equals (1+L_attn) * (1+L_ffn).
    #[test]
    fn test_eclipse_block_formula(
        attn in lipschitz_strategy(),
        ffn in lipschitz_strategy(),
    ) {
        let spec = EclipseLipschitzSpec::new();
        let block = spec.block_bound(&attn, &ffn);
        let expected = (1.0 + attn.constant()) * (1.0 + ffn.constant());
        let tol = f64::EPSILON * expected.max(1.0) * 10.0;
        prop_assert!(
            (block.constant() - expected).abs() < tol,
            "eclipse block {} != (1+{})(1+{}) = {}",
            block.constant(),
            attn.constant(),
            ffn.constant(),
            expected,
        );
    }

    /// Stacking N identical blocks: result == block_bound^N.
    #[test]
    fn test_eclipse_stacked_power(
        attn_c in 0.0f64..5.0,
        ffn_c in 0.0f64..5.0,
        n in 1usize..=4,
    ) {
        let spec = EclipseLipschitzSpec::new();
        let attn = LayerLipschitz::new(attn_c, LipschitzSource::SpectralNorm);
        let ffn = LayerLipschitz::new(ffn_c, LipschitzSource::SpectralNorm);

        let blocks: Vec<(LayerLipschitz, LayerLipschitz)> =
            (0..n).map(|_| (attn, ffn)).collect();
        let stacked = spec.stacked_blocks_bound(&blocks);

        let single = (1.0 + attn_c) * (1.0 + ffn_c);
        let expected = single.powi(n as i32);
        let tol = f64::EPSILON * expected.max(1.0) * 100.0;
        prop_assert!(
            (stacked.constant() - expected).abs() < tol,
            "stacked({n}) {} != {}^{n} = {}",
            stacked.constant(),
            single,
            expected,
        );
    }
}
