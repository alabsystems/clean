// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The formalized-source bundle — the aggregate honesty artifact for one source.
//!
//! Mirrors the shape of `clean_rust_sem`'s `RustProofBundle`: it bundles the
//! per-source verification products. Here those products are the two never-fused
//! meters (proof depth lives inside the [`BadgeReport`]; inference is carried
//! separately), the divergence closure, the phase, and the computed badge.

use crate::badge::{compute_badge, BadgeReport, TrustedModels};
use crate::divergence::DivergenceClosure;
use crate::inference_meter::InferenceMeter;
use crate::phase::Phase;
use clean_cake::goodness::Goodness;

/// The aggregate honesty artifact produced for a single formalized source.
///
/// `#[non_exhaustive]`: more products may be added; build via [`Self::assemble`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct FormalizedSourceBundle {
    /// Stable identifier for the source being formalized.
    pub source_id: String,
    /// The refinement-divergence closure (mechanical VCs + disclosed intent tags).
    pub divergence: DivergenceClosure,
    /// The inference meter (validated-never-proved disclosure channel).
    pub inference: InferenceMeter,
    /// The computed two-meter badge report. The phase is carried inside this
    /// report ([`BadgeReport::phase`]); read it via [`Self::phase`].
    pub badge: BadgeReport,
    /// The trusted models the claim rides on.
    pub trusted_models: TrustedModels,
}

impl FormalizedSourceBundle {
    /// Assemble a bundle, computing the badge from the supplied inputs. The
    /// proof-depth meter is sourced from `goodness` (`None` => fail-closed).
    #[must_use]
    pub fn assemble(
        source_id: impl Into<String>,
        goodness: Option<&Goodness>,
        phase: Phase,
        trusted_models: TrustedModels,
        inference: InferenceMeter,
        divergence: DivergenceClosure,
    ) -> Self {
        let badge = compute_badge(goodness, phase, &trusted_models, &inference, &divergence);
        Self {
            source_id: source_id.into(),
            divergence,
            inference,
            badge,
            trusted_models,
        }
    }

    /// The temporal scope the claim is allowed to make. Sourced from the single
    /// owner of the phase — the computed [`BadgeReport`] — so it can never desync
    /// from the badge.
    #[must_use]
    pub fn phase(&self) -> Phase {
        self.badge.phase
    }
}
