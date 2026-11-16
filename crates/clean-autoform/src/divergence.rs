// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Refinement divergence — what it *means* when a target program refines its
//! source differently than the source's apparent intent.
//!
//! Honesty rail 4: a divergence is only a [`RefinementDivergenceKind::LatentBugExposed`]
//! when a **concrete counterexample** is in hand. A refinement VC that merely
//! failed to prove, with no witness, is *unknown* — never a FLAW.
//!
//! Honesty rail 5: IMPROVEMENT vs FLAW is **intent-relative**, not
//! kernel-decidable. The mechanical fact (the [`trust_ir_contract::translation_validation::RefinementVc`])
//! is shipped checked; the intent tag ([`RefinementDivergenceKind`]) is shipped
//! as a *separate, disclosed* annotation hung off the VC directly. There is no
//! `CheckKind::Refinement` variant to key off — the tag rides on the VC.

use serde::{Deserialize, Serialize};
use trust_ir_contract::translation_validation::RefinementVc;

/// The disclosed, intent-relative interpretation of a single refinement divergence.
///
/// `#[non_exhaustive]`: more divergence interpretations may be added.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RefinementDivergenceKind {
    /// The target's behavior is a deliberate improvement over the source's
    /// (intent-relative; disclosed, not kernel-decided). Clean-core compatible.
    Improvement,
    /// A concrete counterexample witnesses that the target exposes a latent bug
    /// in the source. Per rail 4, this variant requires the witness string.
    LatentBugExposed {
        /// The concrete counterexample witnessing the exposed bug.
        counterexample: String,
    },
    /// The divergence is coupled to external state (I/O, FFI, environment) and
    /// therefore cannot be auto-adjudicated; it blocks an automatic verdict.
    ExternallyCoupled,
    /// The target elaborated/strengthened a precondition relative to the source.
    ElaboratedPrecondition,
}

/// A refinement VC paired with its disclosed, intent-relative divergence tag.
///
/// The tag hangs off the [`RefinementVc`] **directly** (rail 5) — the mechanical
/// VC and the intent interpretation are kept distinct.
///
/// `#[non_exhaustive]`: more disclosure fields may be added; build via
/// [`TaggedRefinement::new`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct TaggedRefinement {
    /// The mechanical, checked refinement verification condition.
    pub vc: RefinementVc,
    /// The disclosed, intent-relative interpretation of the divergence.
    pub kind: RefinementDivergenceKind,
}

impl TaggedRefinement {
    /// Construct a tagged refinement.
    #[must_use]
    pub fn new(vc: RefinementVc, kind: RefinementDivergenceKind) -> Self {
        Self { vc, kind }
    }

    /// True when this divergence is compatible with a clean-core verdict — i.e.
    /// it is an [`RefinementDivergenceKind::Improvement`].
    #[must_use]
    pub fn is_clean_core_compatible(&self) -> bool {
        matches!(self.kind, RefinementDivergenceKind::Improvement)
    }
}

/// The full set of tagged refinement divergences for one formalization.
///
/// `#[non_exhaustive]`: the inner storage is private — build via [`Self::new`],
/// [`Self::from_vec`], or [`Self::push`], and read via [`Self::iter`] /
/// [`Self::as_slice`].
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct DivergenceClosure {
    refinements: Vec<TaggedRefinement>,
}

impl DivergenceClosure {
    /// An empty closure.
    #[must_use]
    pub fn new() -> Self {
        Self {
            refinements: Vec::new(),
        }
    }

    /// Construct from a vector of tagged refinements.
    #[must_use]
    pub fn from_vec(refinements: Vec<TaggedRefinement>) -> Self {
        Self { refinements }
    }

    /// Borrow the tagged refinements as a slice.
    #[must_use]
    pub fn as_slice(&self) -> &[TaggedRefinement] {
        &self.refinements
    }

    /// Iterate over the tagged refinements.
    pub fn iter(&self) -> std::slice::Iter<'_, TaggedRefinement> {
        self.refinements.iter()
    }

    /// Add a tagged refinement.
    pub fn push(&mut self, refinement: TaggedRefinement) {
        self.refinements.push(refinement);
    }

    /// Number of tagged refinements.
    #[must_use]
    pub fn len(&self) -> usize {
        self.refinements.len()
    }

    /// True when there are no refinements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.refinements.is_empty()
    }

    /// A closure is *clean-core* when it is empty OR every divergence is an
    /// [`RefinementDivergenceKind::Improvement`]. A clean-core closure does not,
    /// on its own, deny a certified verdict.
    #[must_use]
    pub fn is_clean_core(&self) -> bool {
        self.refinements
            .iter()
            .all(TaggedRefinement::is_clean_core_compatible)
    }

    /// True when any divergence is [`RefinementDivergenceKind::ExternallyCoupled`].
    /// An externally-coupled divergence **blocks** an automatic verdict.
    #[must_use]
    pub fn has_externally_coupled(&self) -> bool {
        self.refinements
            .iter()
            .any(|r| matches!(r.kind, RefinementDivergenceKind::ExternallyCoupled))
    }

    /// Count of divergences witnessed by a concrete counterexample (rail 4) — a
    /// FLAW. Per design §5b a non-zero count FORBIDS any certified/proven label.
    #[must_use]
    pub fn latent_bug_count(&self) -> usize {
        self.refinements
            .iter()
            .filter(|r| matches!(r.kind, RefinementDivergenceKind::LatentBugExposed { .. }))
            .count()
    }

    /// True when at least one divergence is a witnessed FLAW
    /// ([`RefinementDivergenceKind::LatentBugExposed`]). Per design §5b a FLAW
    /// FORBIDS any certified/proven label on the affected path.
    #[must_use]
    pub fn has_latent_bug(&self) -> bool {
        self.refinements
            .iter()
            .any(|r| matches!(r.kind, RefinementDivergenceKind::LatentBugExposed { .. }))
    }
}
