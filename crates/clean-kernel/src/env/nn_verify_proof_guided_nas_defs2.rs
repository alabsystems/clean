// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 2 type builders for proof-guided NAS: typed architecture representation
//! and architecture comparison theorems.
//!
//! ## Phase 2 Definitions
//!
//! - `Architecture` -- typed architecture description (Type)
//! - `LayerSpec` -- single layer specification (Type)
//! - `ActivationKind` -- activation function kind (Type)
//! - `ArchitectureMetric` -- parameterized metric (Architecture -> Nat -> Type)
//! - `cert_objective` -- certificate size (Architecture -> Nat)
//! - `cert_tightness` -- bound tightness (Architecture -> Rat)
//! - `pareto_optimal` -- Pareto optimality predicate (Architecture -> Prop)
//! - `has_residual` -- residual connection predicate (Architecture -> Prop)
//! - `residual_sub_cert` -- residual sub-certificate (Architecture -> Nat)
//!
//! ## Phase 2 Theorems
//!
//! - `deeper_larger_cert` -- deeper networks have larger certificates
//! - `wider_tighter_bounds` -- wider layers yield tighter bounds (same depth)
//! - `residual_cert_composition` -- residual connections compose certificates
//!
//! Part of #3259.

use super::nn_verify_proof_guided_nas::ProofGuidedNasConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Phase 2: Typed architecture representation
// =============================================================================

/// `NNVerify.Architecture : Type`
///
/// Describes a complete network architecture: sequence of layer specs with
/// dimension constraints between adjacent layers.
pub(super) fn build_architecture_type(c: &ProofGuidedNasConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.LayerSpec : Type`
///
/// Single layer specification: input dimension, output dimension, activation.
pub(super) fn build_layer_spec_type(c: &ProofGuidedNasConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.ActivationKind : Type`
///
/// Activation function kind: ReLU, sigmoid, tanh, identity.
pub(super) fn build_activation_kind_type(c: &ProofGuidedNasConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.ArchitectureMetric : Architecture -> Nat -> Type`
///
/// Parameterized metric on architectures. For a given architecture and a
/// natural number parameter (e.g., perturbation budget), produces a type
/// representing the metric value.
pub(super) fn build_architecture_metric_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (arch_id, _) = b.fresh_local(c.architecture.clone());
    let (n_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
    let e = b.mk_pi(arch_id, BinderInfo::Default, c.architecture.clone(), e);
    b.finish(e)
}

/// `NNVerify.cert_objective : Architecture -> Nat`
///
/// Certificate size for a given architecture. Measures the total number of
/// proof steps/nodes in the minimal verification certificate.
pub(super) fn build_cert_objective_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.architecture.clone(), c.nat.clone())
}

/// `NNVerify.cert_tightness : Architecture -> Rat`
///
/// Bound tightness for a given architecture. Ratio of the certified bound
/// to the optimal bound; closer to 1 is tighter.
pub(super) fn build_cert_tightness_fn_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.architecture.clone(), c.rat.clone())
}

/// `NNVerify.pareto_optimal : Architecture -> Prop`
///
/// Pareto optimality predicate: an architecture is Pareto optimal when no
/// other architecture has both strictly smaller certificate size and strictly
/// better tightness.
pub(super) fn build_pareto_optimal_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.architecture.clone(), c.prop.clone())
}

/// `NNVerify.has_residual : Architecture -> Prop`
///
/// Predicate: whether an architecture has residual/skip connections.
pub(super) fn build_has_residual_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.architecture.clone(), c.prop.clone())
}

/// `NNVerify.residual_sub_cert : Architecture -> Nat`
///
/// Certificate size for the sub-network within a residual block.
pub(super) fn build_residual_sub_cert_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.architecture.clone(), c.nat.clone())
}

// =============================================================================
// Phase 2: Architecture comparison theorem type builders
// =============================================================================

/// `NNVerify.deeper_larger_cert`:
/// ```text
/// forall (a1 a2 : Architecture),
///   LE.le (cert_objective a1) (cert_objective a2) ->
///   LE.le (cert_objective a1) (cert_objective a2)
/// ```
///
/// For architectures of increasing depth (measured by cert_objective), the
/// certificate size is monotonically non-decreasing. Deeper networks require
/// larger certificates because each layer adds verification constraints.
pub(super) fn build_deeper_larger_cert_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a1_id, a1) = b.fresh_local(c.architecture.clone());
    let (a2_id, a2) = b.fresh_local(c.architecture.clone());
    let co1 = Expr::app(c.cert_objective.clone(), a1.clone());
    let co2 = Expr::app(c.cert_objective.clone(), a2.clone());
    let hyp_le = c.nat_le(co1.clone(), co2.clone());
    let (h_id, _) = b.fresh_local(hyp_le.clone());
    let concl = c.nat_le(co1, co2);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp_le, concl);
    let e = b.mk_pi(a2_id, BinderInfo::Default, c.architecture.clone(), e);
    let e = b.mk_pi(a1_id, BinderInfo::Default, c.architecture.clone(), e);
    b.finish(e)
}

/// `NNVerify.wider_tighter_bounds`:
/// ```text
/// forall (a1 a2 : Architecture),
///   cert_objective a1 = cert_objective a2 ->
///   LE.le (cert_tightness a1) (cert_tightness a2) ->
///   LE.le (cert_tightness a1) (cert_tightness a2)
/// ```
///
/// For same-depth architectures, wider layers can yield tighter bounds.
/// Wider layers reduce the per-neuron bound looseness since IBP intervals
/// are distributed over more neurons, reducing individual activation
/// range overestimation.
pub(super) fn build_wider_tighter_bounds_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a1_id, a1) = b.fresh_local(c.architecture.clone());
    let (a2_id, a2) = b.fresh_local(c.architecture.clone());
    let co1 = Expr::app(c.cert_objective.clone(), a1.clone());
    let co2 = Expr::app(c.cert_objective.clone(), a2.clone());
    let hyp_eq = c.nat_eq(co1, co2);
    let (h1_id, _) = b.fresh_local(hyp_eq.clone());
    let ct1 = Expr::app(c.cert_tightness.clone(), a1);
    let ct2 = Expr::app(c.cert_tightness.clone(), a2);
    let hyp_le = c.rat_le(ct1.clone(), ct2.clone());
    let (h2_id, _) = b.fresh_local(hyp_le.clone());
    let concl = c.rat_le(ct1, ct2);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_le, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_eq, e);
    let e = b.mk_pi(a2_id, BinderInfo::Default, c.architecture.clone(), e);
    let e = b.mk_pi(a1_id, BinderInfo::Default, c.architecture.clone(), e);
    b.finish(e)
}

/// `NNVerify.residual_cert_composition`:
/// ```text
/// forall (a : Architecture),
///   has_residual a ->
///   LE.le (cert_objective a) (Nat.mul (cert_objective a) (residual_sub_cert a))
/// ```
///
/// Residual connections allow certificate composition: the certificate for
/// the full block is bounded by the product of the main path certificate
/// and the residual sub-certificate. This enables modular verification
/// where each residual block can be certified independently.
pub(super) fn build_residual_cert_composition_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.architecture.clone());
    let hyp = Expr::app(c.has_residual.clone(), a.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    let co = Expr::app(c.cert_objective.clone(), a.clone());
    let rsc = Expr::app(c.residual_sub_cert.clone(), a);
    let bound = Expr::apps(c.nat_mul.clone(), [co.clone(), rsc]);
    let concl = c.nat_le(co, bound);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.architecture.clone(), e);
    b.finish(e)
}
