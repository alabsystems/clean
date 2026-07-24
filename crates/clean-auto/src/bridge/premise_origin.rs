// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise origin tracking for E-matching relevance scoring.

use crate::premise::PremiseId;
use clean_kernel::{name::Name, FVarId};
use std::collections::HashMap;

/// Maximum premise bonus for a highly relevant named theorem.
const PREMISE_BONUS_WEIGHT: i32 = 30;

/// Minimum premise bonus for a named theorem with zero relevance.
const PREMISE_MIN_BONUS: i32 = -15;

/// Origin information for quantifiers participating in E-matching.
///
/// Named theorems can be correlated with premise selection scores, local
/// hypotheses remain neutral, and synthesized quantifiers are explicitly
/// identified rather than overloading "missing metadata".
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum QuantifierOrigin {
    /// From a named theorem/lemma with an optional premise ID.
    ///
    /// `premise_id = None` preserves backward compatibility with the older
    /// name-only constructor surface.
    Named {
        name: Name,
        premise_id: Option<PremiseId>,
    },
    /// From a local hypothesis introduced by the caller or proof search.
    Local { fvar_id: FVarId },
    /// Synthesized during proof search (skolemization, goal translation, etc.).
    #[default]
    Synthesized,
}

/// Backward-compatible public alias for the legacy API surface.
pub type PremiseOrigin = QuantifierOrigin;

impl QuantifierOrigin {
    /// Create a new named origin with both name and ID.
    ///
    /// REQUIRES: `name` and `premise_id` are valid identifiers in the
    ///   current environment's PremiseDatabase.
    /// ENSURES: `matches!(self, Self::Named { premise_id: Some(_), .. })`
    pub fn new(name: Name, premise_id: PremiseId) -> Self {
        Self::Named {
            name,
            premise_id: Some(premise_id),
        }
    }

    /// Create a named origin with a name only.
    ///
    /// ENSURES: `matches!(self, Self::Named { premise_id: None, .. })`
    pub fn from_name(name: Name) -> Self {
        Self::Named {
            name,
            premise_id: None,
        }
    }

    /// Create a named origin with a premise ID only.
    ///
    /// Uses `Name::anon()` internally as a compatibility shim for the old
    /// struct-based API, while [`Self::name`] continues to report `None`.
    ///
    /// ENSURES: `self.name().is_none() && self.premise_id() == Some(premise_id)`
    pub fn from_premise_id(premise_id: PremiseId) -> Self {
        Self::Named {
            name: Name::anon(),
            premise_id: Some(premise_id),
        }
    }

    /// Create an origin for a local hypothesis.
    pub fn local(fvar_id: FVarId) -> Self {
        Self::Local { fvar_id }
    }

    /// Create an explicitly synthesized origin.
    pub fn synthesized() -> Self {
        Self::Synthesized
    }

    /// Return the named theorem, if any.
    pub fn name(&self) -> Option<&Name> {
        match self {
            Self::Named { name, .. } if !name.is_anon() => Some(name),
            Self::Named { .. } | Self::Local { .. } | Self::Synthesized => None,
        }
    }

    /// Return the premise ID, if any.
    pub fn premise_id(&self) -> Option<PremiseId> {
        match self {
            Self::Named { premise_id, .. } => *premise_id,
            Self::Local { .. } | Self::Synthesized => None,
        }
    }

    /// Return the local hypothesis ID, if any.
    pub fn fvar_id(&self) -> Option<FVarId> {
        match self {
            Self::Local { fvar_id } => Some(*fvar_id),
            Self::Named { .. } | Self::Synthesized => None,
        }
    }

    /// Check if this origin carries any identifying metadata.
    ///
    /// Legacy compatibility:
    /// - `Synthesized` counts as empty metadata
    /// - `Named { anon, None }` counts as empty metadata
    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Synthesized)
            || matches!(self, Self::Named { name, premise_id: None } if name.is_anon())
    }

    /// Prefer an explicit origin, otherwise derive a local origin from `fvar_id`.
    pub(crate) fn inherit_or_local(origin: Option<Self>, fvar_id: Option<FVarId>) -> Option<Self> {
        origin.or(fvar_id.map(Self::local))
    }

    /// Compute the additive relevance bonus for this origin.
    pub(crate) fn relevance_bonus(&self, premise_scores: &HashMap<PremiseId, f64>) -> i32 {
        match self {
            Self::Named {
                premise_id: Some(premise_id),
                ..
            } => premise_scores.get(premise_id).map_or(0, |score| {
                let range = (PREMISE_BONUS_WEIGHT - PREMISE_MIN_BONUS) as f64;
                let scaled = PREMISE_MIN_BONUS as f64 + (score * range);
                scaled.round() as i32
            }),
            Self::Named {
                premise_id: None, ..
            }
            | Self::Local { .. }
            | Self::Synthesized => 0,
        }
    }
}
