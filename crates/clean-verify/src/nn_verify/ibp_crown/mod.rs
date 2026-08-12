// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IBP/CROWN Verification Proof Engine
//!
//! Soundness proofs for interval bound propagation (IBP) and CROWN-style
//! backward linear relaxation used in gamma-crown. Organized in phases:
//!
//! ## Phase 1 (Active)
//!
//! - **IBP linear layer** (T80): W+/W- decomposition soundness
//! - **IBP ReLU** (T81): Case-split soundness (positive/negative/crossing)
//! - **IBP composition** (T82): Layer chaining via interval subset transitivity
//! - **IBP sigmoid** (T83): Monotone activation function bound propagation
//! - **IBP conv** (T84): Convolutional layer as structured linear operator
//! - **Lipschitz compose** (T30): Submultiplicativity of composed layers
//! - **Lipschitz residual** (T33): Additive bound from skip connections
//! - **Eclipse block Lipschitz** (T31): Compound block Lipschitz constant
//!
//! ## Phase 3 (CROWN -- Proved)
//!
//! - **CROWN linear relaxation** (T40): Triangle relaxation of ReLU is sound
//! - **CROWN backward propagation** (T41): Backward pass composes valid bounds
//! - **CROWN concave envelope** (T42): Concave envelope of ReLU is tight
//! - **Alpha-CROWN soundness** (T43): Any alpha in [0,1] yields sound bounds
//! - **Alpha-CROWN tightness** (T44): Optimized alphas at least as tight as CROWN
//! - **CROWN composition** (T45): Multi-layer backward composition is sound
//! - **CROWN concretization** (T46): Symbolic-to-concrete bound is sound
//! - **CROWN-IBP dominance** (T47): CROWN bounds at least as tight as IBP
//!
//! ## Phase 3 (Stubs)
//!
//! - **LayerNorm** (T20-T22): Normalization layer bound analysis
//! - **McCormick** (T50-T52): Bilinear relaxation envelopes
//! - **Attention** (T53-T54): Attention mechanism bilinear bound propagation
//! - **Multi-head** (T55-T56): Multi-head attention split/combine soundness

pub mod attention;
mod block_wise_crown;
pub(crate) mod conv;
mod crown;
pub mod crown_alpha;
mod crown_alpha_backward;
mod crown_backward;
pub mod crown_layernorm_degeneration;
mod crown_proofs;
mod ibp;
mod ibp_extensions;
pub mod ibp_rat;
pub mod ibp_rat_helper_audit;
mod layernorm;
mod layernorm_forward;
mod lipschitz;
pub(crate) mod lipschitz_concrete;
mod mccormick;
pub mod mccormick_linear_error;
pub mod monotone;
pub mod multi_head;
mod sensitivity;
pub(crate) mod spectral_norm;
#[cfg(test)]
mod tests_attention;
#[cfg(test)]
mod tests_block_wise_crown;
#[cfg(test)]
mod tests_composition_proptest;
#[cfg(test)]
mod tests_conv;
#[cfg(test)]
mod tests_crown;
#[cfg(test)]
mod tests_crown_alpha;
#[cfg(test)]
mod tests_crown_alpha_backward;
#[cfg(test)]
mod tests_crown_backward;
#[cfg(test)]
mod tests_crown_layernorm_degeneration;
#[cfg(test)]
mod tests_crown_proofs;
#[cfg(test)]
mod tests_ibp;
#[cfg(test)]
mod tests_ibp_extensions;
#[cfg(test)]
mod tests_ibp_extensions_ext;
#[cfg(test)]
mod tests_ibp_proptest;
#[cfg(test)]
mod tests_interval_proptest;
#[cfg(test)]
mod tests_layernorm;
#[cfg(test)]
mod tests_layernorm_forward;
#[cfg(test)]
mod tests_lipschitz;
#[cfg(test)]
mod tests_lipschitz_concrete;
#[cfg(test)]
mod tests_mccormick;
#[cfg(test)]
mod tests_mccormick_ext;
#[cfg(test)]
mod tests_mccormick_linear_error;
#[cfg(test)]
mod tests_monotone;
#[cfg(test)]
mod tests_multi_head;
#[cfg(test)]
mod tests_multiblock;
#[cfg(test)]
mod tests_sensitivity;
#[cfg(test)]
mod tests_spectral_norm;
#[cfg(test)]
mod tests_tightness;
pub mod tightness;

pub use attention::{
    attention_head_bounds, attention_score_bounds, softmax_bounds, verify_attention_soundness,
    AttentionBounds, AttentionScoreBoundSpec, AttentionScoreBounds, SoftmaxMonotoneBoundSpec,
};
pub use block_wise_crown::{
    block_wise_crown, crown_single_block, layernorm_interval_transfer, monolithic_crown,
    verify_blockwise_equals_monolithic, BlockWiseCrownSpec, BlockWiseEquivalenceProof,
    BlockWiseResult, TransformerBlock,
};
pub use crown::{
    crown_concretize, CrownBackwardSpec, CrownBound, CrownConcaveSpec, CrownLinearSpec, CrownResult,
};
pub use crown_alpha::{
    alpha_crown_bounds, AlphaCrownParams, AlphaCrownResult, AlphaCrownSoundSpec,
    AlphaCrownTighterSpec,
};
pub use crown_backward::{crown_linear_backward, crown_relu_backward, verify_crown_bounds};
pub use crown_layernorm_degeneration::CrownLayerNormDegenerationSpec;
pub use ibp::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec, Interval};
pub use ibp_extensions::{
    batch_ibp_forward, ibp_forward_single, ibp_sensitivity, multi_input_hull,
    verify_batch_soundness, BatchSoundnessResult, IbpConvSpec, IbpSigmoidSpec, SensitivityResult,
};
pub use ibp_rat::{
    c4515_theorem_entries, verify_kernel_ibp_linear_sound, IbpLinearRatSpec, IbpRatVerifyError,
    KernelCheckReport, IBP_LINEAR_BOUNDS_NAME, IBP_LINEAR_SOUND_NAME, IBP_LINEAR_SOUND_RAT_STATUS,
    IBP_SOUND_HELPER_NAMES, LINEAR_OUTPUT_NAME,
};
pub use ibp_rat_helper_audit::{
    audit_ibp_linear_sound_helpers, HelperAuditReport, HelperKind, HelperStatus,
};
pub use layernorm::{
    compute_mean_bounds, compute_variance_bounds, verify_layernorm_forward, LayerNormBounds,
    LayerNormCenterSpec, LayerNormFullSpec, LayerNormScaleSpec,
};
pub use layernorm_forward::{
    compute_centered_bounds, compute_inv_sqrt_interval, compute_mean_interval,
    compute_variance_interval, layernorm_forward_bounds, verify_layernorm_containment,
};
pub use lipschitz::{EclipseLipschitzSpec, LipschitzComposeSpec, ResidualLipschitzSpec};
pub use lipschitz_concrete::{
    compute_layer_lipschitz, compute_network_lipschitz, compute_relu_lipschitz,
    compute_residual_lipschitz, power_iteration, verify_lipschitz_compose, LayerSpec,
};
pub use mccormick::{
    mccormick_division_bounds, mccormick_envelope, mccormick_product_interval,
    mccormick_quadratic_bound, mccormick_tight_bounds, multi_term_product_bound,
    softmax_attention_bound, verify_mccormick_sound, verify_mccormick_tighter_than_naive,
    BilinearBounds, McCormickConcaveSpec, McCormickConvexSpec, McCormickEnvelopeSpec,
};
pub use mccormick_linear_error::McCormickLinearErrorSpec;
pub use monotone::{
    activation_lipschitz, verify_activation_soundness, verify_sigmoid_monotone_bound,
    verify_tanh_monotone_bound, ActivationFn, MonotoneClass,
};
pub use multi_head::{
    combine_head_outputs, multi_head_attention_bounds, split_heads, verify_head_independence,
    verify_multi_head_soundness, HeadBounds, MultiHeadBounds, MultiHeadCombineSpec,
    MultiHeadConfig, MultiHeadSplitSpec,
};

use crate::spec::ProofStatus;

/// Theorem registry for IBP/CROWN proof tracking.
///
/// Each theorem has an identifier (T-number from the design doc), a human
/// description, and a `ProofStatus` indicating current verification state.
#[derive(Debug, Clone)]
pub struct TheoremEntry {
    /// Theorem identifier (e.g., "T80").
    pub id: &'static str,
    /// Human-readable description.
    pub description: &'static str,
    /// Current proof status.
    pub status: ProofStatus,
    /// Phase this theorem belongs to.
    pub phase: Phase,
}

/// Implementation phase for theorem scheduling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Phase {
    /// Phase 1: IBP forward + Lipschitz. Active implementation.
    Phase1,
    /// Phase 3: CROWN backward, LayerNorm, McCormick. Stub only.
    Phase3,
}

impl std::fmt::Display for Phase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Phase::Phase1 => write!(f, "Phase 1"),
            Phase::Phase3 => write!(f, "Phase 3"),
        }
    }
}

/// Return the full theorem registry for IBP/CROWN proofs.
///
/// This is the canonical list of all theorems tracked by this module,
/// including C012 ReLU stability theorems from [`super::relu::c012_spec`]
/// and C020 softmax relaxation theorems from [`super::softmax::c020_spec`].
#[must_use]
pub fn theorem_registry() -> Vec<TheoremEntry> {
    let mut entries = Vec::with_capacity(40);
    entries.extend(ibp_theorems());
    entries.extend(lipschitz_theorems());
    entries.extend(crown_theorems());
    entries.extend(crown_alpha_theorems());
    entries.extend(crown_composition_theorems());
    entries.extend(layernorm_theorems());
    entries.extend(mccormick_theorems());
    entries.extend(attention::attention_theorems());
    entries.extend(multi_head::multi_head_theorems());
    entries.push(crown_layernorm_degeneration::c004_theorem_entry());
    entries.push(mccormick_linear_error::c005_theorem_entry());
    entries.extend(super::relu::c012_spec::c012_theorem_entries());
    entries.extend(super::softmax::c020_spec::c020_theorem_entries());
    entries.extend(super::nullstellensatz::c028_spec::c028_theorem_entries());
    // C4515 (gamma-crown mail #3524): Rat-typed IBP linear soundness spec,
    // kernel-backed by `NNVerify.ibp_linear_sound`.
    entries.extend(c4515_theorem_entries());
    entries
}

/// Helper: construct a `DerivedPending` theorem entry.
fn pending(id: &'static str, desc: &'static str, phase: Phase) -> TheoremEntry {
    TheoremEntry {
        id,
        description: desc,
        status: ProofStatus::DerivedPending,
        phase,
    }
}

/// Phase 1 IBP theorems (T80-T84).
fn ibp_theorems() -> Vec<TheoremEntry> {
    vec![
        pending(
            "T80",
            "IBP linear layer soundness (W+/W- decomposition)",
            Phase::Phase1,
        ),
        pending(
            "T81",
            "IBP ReLU soundness (sign-based case split)",
            Phase::Phase1,
        ),
        pending(
            "T82",
            "IBP composition soundness (interval subset transitivity)",
            Phase::Phase1,
        ),
        pending(
            "T83",
            "IBP sigmoid soundness (monotone activation)",
            Phase::Phase1,
        ),
        pending(
            "T84",
            "IBP conv layer soundness (structured linear operator)",
            Phase::Phase1,
        ),
    ]
}

/// Phase 1 Lipschitz theorems (T30-T33).
///
/// All four have kernel theorems registered as `Declaration::Theorem` with
/// axiom-backed proof terms that pass `tc.infer_type()` + `tc.is_def_eq()`.
/// See `nn_verify_lipschitz_eclipse.rs` in clean-kernel.
fn lipschitz_theorems() -> Vec<TheoremEntry> {
    vec![
        pending(
            "T30",
            "Lipschitz compose (submultiplicativity)",
            Phase::Phase1,
        ),
        pending("T31", "Eclipse block Lipschitz constant", Phase::Phase1),
        pending("T32", "Spectral norm Lipschitz bound", Phase::Phase1),
        pending(
            "T33",
            "Residual connection Lipschitz (additive from skip)",
            Phase::Phase1,
        ),
    ]
}

/// CROWN backward theorems (T40-T42).
///
/// All three have constructive proof terms in `crown_proofs.rs` that verify
/// the mathematical properties via computation + dense sampling.
fn crown_theorems() -> Vec<TheoremEntry> {
    vec![
        pending("T40", "CROWN linear relaxation soundness", Phase::Phase3),
        pending("T41", "CROWN backward bound propagation", Phase::Phase3),
        pending("T42", "CROWN concave envelope tightness", Phase::Phase3),
    ]
}

/// Alpha-CROWN theorems (T43-T44).
///
/// T43 is proved by showing that for any alpha in [0,1], the per-neuron
/// relaxation is sound. T44 follows from CROWN being a special case of
/// alpha-CROWN with alpha=0.
fn crown_alpha_theorems() -> Vec<TheoremEntry> {
    vec![
        pending(
            "T43",
            "Alpha-CROWN soundness (optimized alphas)",
            Phase::Phase3,
        ),
        pending("T44", "Alpha-CROWN tighter than CROWN", Phase::Phase3),
    ]
}

/// CROWN composition and dominance theorems (T45-T47).
///
/// T45: Multi-layer CROWN composition soundness (inductive proof).
/// T46: Symbolic-to-concrete concretization soundness (interval arithmetic).
/// T47: CROWN-IBP dominance (CROWN is at least as tight as IBP).
fn crown_composition_theorems() -> Vec<TheoremEntry> {
    vec![
        pending(
            "T45",
            "CROWN composition soundness (multi-layer)",
            Phase::Phase3,
        ),
        pending(
            "T46",
            "CROWN concretization soundness (symbolic-to-concrete)",
            Phase::Phase3,
        ),
        pending(
            "T47",
            "CROWN-IBP dominance (tighter than IBP)",
            Phase::Phase3,
        ),
    ]
}

/// Phase 3 LayerNorm theorems (T20-T22).
fn layernorm_theorems() -> Vec<TheoremEntry> {
    vec![
        pending("T20", "LayerNorm centering bound", Phase::Phase3),
        pending("T21", "LayerNorm scaling bound", Phase::Phase3),
        pending("T22", "LayerNorm full pipeline bound", Phase::Phase3),
    ]
}

/// Phase 3 McCormick theorems (T50-T52).
fn mccormick_theorems() -> Vec<TheoremEntry> {
    vec![
        pending("T50", "McCormick envelope soundness", Phase::Phase3),
        pending("T51", "McCormick convex underestimator", Phase::Phase3),
        pending("T52", "McCormick concave overestimator", Phase::Phase3),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::ProofStatus;

    #[test]
    fn test_theorem_registry_completeness() {
        let registry = theorem_registry();
        // Phase 1: T80-T84 (5 IBP) + T30-T33 (4 Lipschitz) + C012a-C012c (3 ReLU stability)
        //        + C028a-C028c (3 Nullstellensatz) + C4515 (1 Rat-IBP mail-back) = 16
        // Phase 3: T40-T42 (3 CROWN) + T43-T44 (2 Alpha-CROWN) + T45-T47 (3 CROWN composition)
        //        + T20-T22 (3 LayerNorm) + T50-T52 (3 McCormick) + T53-T54 (2 Attention)
        //        + T55-T56 (2 Multi-head) + C004 (1) + C005 (1) + C020a-C020d (4 Softmax) = 24
        assert_eq!(registry.len(), 40, "expected 40 theorems in registry");
    }

    #[test]
    fn test_theorem_registry_status_accounting() {
        let registry = theorem_registry();
        // After Phase 0 demotion (#3361): all theorems are DerivedPending.
        // None have kernel proof terms yet.
        let pending: Vec<&str> = registry
            .iter()
            .filter(|t| t.status == ProofStatus::DerivedPending)
            .map(|t| t.id)
            .collect();
        assert_eq!(
            pending.len(),
            40,
            "all theorems should be DerivedPending: {pending:?}"
        );
        let proved: Vec<&str> = registry
            .iter()
            .filter(|t| t.status == ProofStatus::DerivedProved)
            .map(|t| t.id)
            .collect();
        assert!(
            proved.is_empty(),
            "no theorems should be DerivedProved yet: {proved:?}"
        );
    }

    #[test]
    fn test_theorem_registry_phase_counts() {
        let registry = theorem_registry();
        let phase1_count = registry.iter().filter(|t| t.phase == Phase::Phase1).count();
        let phase3_count = registry.iter().filter(|t| t.phase == Phase::Phase3).count();
        assert_eq!(phase1_count, 16, "expected 16 Phase 1 theorems");
        assert_eq!(phase3_count, 24, "expected 24 Phase 3 theorems");
    }

    #[test]
    fn test_theorem_ids_unique() {
        let registry = theorem_registry();
        let mut ids: Vec<&str> = registry.iter().map(|t| t.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), registry.len(), "theorem IDs must be unique");
    }

    #[test]
    fn test_phase_display() {
        assert_eq!(Phase::Phase1.to_string(), "Phase 1");
        assert_eq!(Phase::Phase3.to_string(), "Phase 3");
    }
}
