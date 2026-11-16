// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust badge computation — the two-meter trust label.
//!
//! Honesty rail 2 (cardinal error): the **proof-depth meter** ([`ProofDepthSummary`])
//! and the **inference meter** ([`InferenceSummary`]) are SEPARATE fields of
//! [`BadgeReport`] and are **never combined into one score**. A `*Certified*`
//! label gates on **proof-depth + phase ONLY**; the inference meter is
//! disclosure, never an IFF precondition.

use serde::{Deserialize, Serialize};

use crate::divergence::DivergenceClosure;
use crate::inference_meter::InferenceMeter;
use crate::phase::Phase;
use clean_cake::goodness::{FloorLevel, Goodness};

/// The trust label assigned to a formalization.
///
/// `#[non_exhaustive]`: labels may be added as the trust lattice grows.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Label {
    /// The strongest label: a static-universal proof discharged to the binary
    /// modulo the three named trusted models and the foundational axioms.
    RustCertifiedToBinary,
    /// Certified to the spec, but modulo inferred facts / divergences that are
    /// disclosed (not fused into the proof-depth claim).
    CertifiedToSpecModuloInferred {
        /// Number of inferred bindings disclosed by the inference meter.
        inferred_facts: usize,
        /// Number of refinement divergences disclosed.
        divergences: usize,
    },
    /// An SMT-backed result against the spec (weaker than a binary-level proof).
    SmtBackedToSpec,
    /// A FLAW was witnessed: at least one divergence is a
    /// [`crate::divergence::RefinementDivergenceKind::LatentBugExposed`] backed by
    /// a concrete counterexample (rail 4). Per design §5b, a FLAW FORBIDS any
    /// certified/proven label on the affected path — this is the only label such a
    /// path may carry.
    FlawWitnessed {
        /// Number of latent-bug counterexamples witnessed on this path.
        counterexamples: usize,
    },
    /// Only intent-level validation was achieved; no proof claim is made.
    IntentValidatedOnly,
}

/// The three named trusted models — the only trust the `RustCertifiedToBinary`
/// label rides on: the ISA model, the runtime model, and the
/// **semantic-reflection model** (the verified meaning-map `<<.>> : trust-ir -> CIC`
/// reflecting trust-ir operational semantics into the kernel's logic).
///
/// Honesty rail 3: the SemanticReflection + MIR-op-sem map is TRUSTED/UNVERIFIED
/// for the GENERAL case; this struct records *which* trusted models a claim
/// relies on, never that the general map is "verified".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustedModels {
    /// The formal ISA model is in the trusted base.
    pub isa: bool,
    /// The runtime model is in the trusted base.
    pub runtime: bool,
    /// The semantic-reflection model (`<<.>>`) is in the trusted base.
    pub semantic_reflection: bool,
}

impl TrustedModels {
    /// The exact trusted base required by `RustCertifiedToBinary`:
    /// `{isa, runtime, semantic_reflection}` all present, with nothing extra.
    #[must_use]
    pub fn all_three() -> Self {
        Self {
            isa: true,
            runtime: true,
            semantic_reflection: true,
        }
    }

    /// True when exactly the three named models are present (and only those).
    ///
    /// NOTE: this pins the trusted base to *exactly* `{isa, runtime,
    /// semantic_reflection}`. If a 4th trusted model is ever added to
    /// [`TrustedModels`], this method (and [`Self::all_three`], and the positive
    /// regression test pinning the set) MUST be revisited so the certified gate
    /// keeps pinning the full, intended trusted base.
    #[must_use]
    pub fn is_exactly_three(self) -> bool {
        self == Self::all_three()
    }
}

/// A serde-serializable mirror of [`clean_cake::goodness::FloorLevel`].
///
/// `clean_cake::goodness::FloorLevel` carries no serde derives, so the proof-depth
/// summary records the floor through this local mirror. A single source of truth
/// for the floor (instead of a `String` + `bool` pair) removes any desync risk on
/// deserialize — [`Self::is_foundational`] is *derived* from the variant, never
/// stored alongside it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofFloor {
    /// Mirrors [`FloorLevel::Unsound`].
    Unsound,
    /// Mirrors [`FloorLevel::AxiomDependent`].
    AxiomDependent,
    /// Mirrors [`FloorLevel::Foundational`].
    Foundational,
}

impl ProofFloor {
    /// True iff this floor is [`ProofFloor::Foundational`].
    #[must_use]
    pub fn is_foundational(self) -> bool {
        matches!(self, Self::Foundational)
    }
}

impl From<FloorLevel> for ProofFloor {
    fn from(floor: FloorLevel) -> Self {
        match floor {
            FloorLevel::Unsound => Self::Unsound,
            FloorLevel::AxiomDependent => Self::AxiomDependent,
            FloorLevel::Foundational => Self::Foundational,
        }
    }
}

/// A side-by-side summary of the **proof-depth** meter (one of the two never-fused
/// meters). Mirrors the relevant [`Goodness`] fields without exposing the score.
///
/// `#[non_exhaustive]`: more disclosure fields may be added.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ProofDepthSummary {
    /// The soundness floor (weakest link) of the proof closure.
    pub floor: ProofFloor,
    /// Distinct non-foundational (domain) axioms the closure depends on.
    pub domain_axioms: Vec<String>,
    /// Distinct trust markers (`sorry`/`native_decide`/…) reachable.
    pub trust_markers: Vec<String>,
    /// Number of distinct constants in the closure.
    pub closure_size: usize,
}

impl ProofDepthSummary {
    fn from_goodness(g: &Goodness) -> Self {
        Self {
            floor: g.floor.into(),
            domain_axioms: g.domain_axioms.clone(),
            trust_markers: g.trust_markers.clone(),
            closure_size: g.closure_size,
        }
    }

    /// True iff the proof-depth floor is foundational. Derived from [`Self::floor`]
    /// (the single source of truth), never stored separately.
    #[must_use]
    pub fn is_foundational(&self) -> bool {
        self.floor.is_foundational()
    }
}

/// A side-by-side summary of the **inference** meter (the other never-fused
/// meter). Pure disclosure; never a gate.
///
/// `#[non_exhaustive]`: more disclosure fields may be added.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct InferenceSummary {
    /// Count of inferred bindings.
    pub inferred_count: usize,
    /// Whether a standing faithfulness obligation is open.
    pub faithfulness_obligation_open: bool,
}

impl InferenceSummary {
    fn from_meter(m: &InferenceMeter) -> Self {
        Self {
            inferred_count: m.count(),
            faithfulness_obligation_open: m.faithfulness_obligation_open(),
        }
    }
}

/// A summary of the refinement-divergence closure for the report.
///
/// `#[non_exhaustive]`: more disclosure fields may be added.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct DivergenceSummary {
    /// Total tagged divergences.
    pub total: usize,
    /// Whether the closure is clean-core (empty or improvement-only).
    pub clean_core: bool,
    /// Whether any divergence is externally coupled (blocks auto-verdict).
    pub externally_coupled: bool,
    /// Number of latent bugs witnessed by a concrete counterexample.
    pub latent_bugs: usize,
}

impl DivergenceSummary {
    fn from_closure(d: &DivergenceClosure) -> Self {
        Self {
            total: d.len(),
            clean_core: d.is_clean_core(),
            externally_coupled: d.has_externally_coupled(),
            latent_bugs: d.latent_bug_count(),
        }
    }
}

/// The full badge report. The proof-depth meter ([`Self::proof_depth`]) and the
/// inference meter ([`Self::inference`]) are SEPARATE fields — never one fused
/// score (rail 2).
///
/// `#[non_exhaustive]`: more report fields may be added.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct BadgeReport {
    /// The assigned trust label.
    pub label: Label,
    /// The proof-depth meter (proved, modulo named models/axioms).
    pub proof_depth: Option<ProofDepthSummary>,
    /// The inference meter (validated, disclosed — never fused with proof depth).
    pub inference: InferenceSummary,
    /// The temporal scope the claim is allowed to make.
    pub phase: Phase,
    /// The refinement-divergence disclosure.
    pub divergence: DivergenceSummary,
}

/// Compute the trust badge for a formalization.
///
/// # The `RustCertifiedToBinary` gate (ALL required)
///
/// * `goodness.is_some()` — `None` => fail-closed, NOT certified (rail 7).
/// * `floor == FloorLevel::Foundational`.
/// * `domain_axioms.is_empty()`.
/// * `trust_markers.is_empty()`.
/// * `phase == Phase::StaticUniversal`.
/// * `models` are exactly `{isa, runtime, semantic_reflection} = true`, nothing extra.
/// * `divergence.is_clean_core()`.
///
/// # Cardinal-error rule (design section 6, honesty rail 2)
///
/// The **inference meter is NOT in the gate**. It is reported in
/// [`BadgeReport::inference`]. A NON-EMPTY inference meter does **not** by itself
/// deny `RustCertifiedToBinary`. (A Python-rooted formalization tops out not
/// because of its inference count, but because its faithfulness stage forces
/// `phase = RuntimeInstance`, so the PHASE gate denies it — never the inference
/// count.) Fusing the two meters into one gate is the cardinal error this
/// function is built to avoid.
///
/// # The §5b FLAW rail
///
/// A **FLAW** — a [`crate::divergence::RefinementDivergenceKind::LatentBugExposed`]
/// divergence, i.e. a proven counterexample (rail 4) — FORBIDS any
/// certified/proven label on the affected path. When
/// `divergence.latent_bug_count() > 0`, this function returns
/// [`Label::FlawWitnessed`] and NEVER [`Label::RustCertifiedToBinary`],
/// [`Label::CertifiedToSpecModuloInferred`], or [`Label::SmtBackedToSpec`]. The
/// certified and SMT branches each independently re-assert `latent_bug_count() == 0`.
#[must_use]
pub fn compute_badge(
    goodness: Option<&Goodness>,
    phase: Phase,
    models: &TrustedModels,
    inference: &InferenceMeter,
    divergence: &DivergenceClosure,
) -> BadgeReport {
    let proof_depth = goodness.map(ProofDepthSummary::from_goodness);
    let inference_summary = InferenceSummary::from_meter(inference);
    let divergence_summary = DivergenceSummary::from_closure(divergence);

    // §5b rail: a FLAW (a proven counterexample, i.e. a `LatentBugExposed`
    // divergence) FORBIDS any certified/proven label on the affected path. It is
    // checked FIRST so a witnessed bug can never fall through into a certified or
    // SMT-backed branch — those branches additionally re-assert `latent_bug_count
    // == 0` as belt-and-braces.
    let latent_bugs = divergence.latent_bug_count();

    // The certified gate: proof-depth + phase + models + divergence ONLY.
    // The inference meter is deliberately absent from this predicate.
    // `is_clean_core()` already implies no latent bug, but the explicit
    // `latent_bugs == 0` makes the §5b rail load-bearing in this branch too.
    let certified_to_binary = latent_bugs == 0
        && goodness.is_some_and(|g| {
            g.floor == FloorLevel::Foundational
                && g.domain_axioms.is_empty()
                && g.trust_markers.is_empty()
        })
        && phase.is_static_universal()
        && models.is_exactly_three()
        && divergence.is_clean_core();

    let label = if latent_bugs > 0 {
        // §5b rail: a witnessed FLAW denies every certified-flavored label.
        Label::FlawWitnessed {
            counterexamples: latent_bugs,
        }
    } else if certified_to_binary {
        Label::RustCertifiedToBinary
    } else if latent_bugs == 0
        && goodness.is_some_and(Goodness::is_foundational)
        && !divergence.has_externally_coupled()
    {
        // Foundational proof depth but blocked from binary certification (phase,
        // models, axioms, or disclosed divergences): certified to spec modulo
        // the disclosed inferred facts / divergences. §5b rail: only when no
        // latent bug is witnessed.
        Label::CertifiedToSpecModuloInferred {
            inferred_facts: inference.count(),
            divergences: divergence.len(),
        }
    } else if latent_bugs == 0 && goodness.is_some() && !divergence.has_externally_coupled() {
        // §5b rail: SMT-backed is a proven-flavored label; deny it under a FLAW.
        Label::SmtBackedToSpec
    } else {
        Label::IntentValidatedOnly
    };

    BadgeReport {
        label,
        proof_depth,
        inference: inference_summary,
        phase,
        divergence: divergence_summary,
    }
}
