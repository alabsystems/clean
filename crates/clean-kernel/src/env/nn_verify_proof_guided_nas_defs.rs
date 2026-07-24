// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1 type builders for proof-guided neural architecture search (NAS).
//!
//! ## Phase 1 Definitions
//!
//! - `architecture_space` -- space of network architectures (depth, width, activation)
//! - `verifiability_score` -- how easy a network is to verify (cert size / precision)
//! - `pareto_front` -- Pareto-optimal set of (accuracy, verifiability) architectures
//! - `architecture_transform` -- architecture modification operation
//! - `verified_accuracy` -- accuracy under verified robustness constraint
//!
//! ## Phase 1 Theorems
//!
//! 1. `wider_more_verifiable` -- wider networks admit tighter IBP bounds
//! 2. `depth_verifiability_tradeoff` -- deeper networks have looser bounds
//! 3. `pareto_dominance_sound` -- Pareto dominance implies better accuracy AND verifiability
//! 4. `nas_search_monotone` -- proof-guided search converges to Pareto front
//! 5. `skip_connections_improve_verifiability` -- residual connections tighten bounds
//! 6. `certified_accuracy_bound` -- verified_accuracy <= standard accuracy (soundness)
//!
//! Phase 2 type builders are in `nn_verify_proof_guided_nas_defs2.rs`.
//!
//! Part of #3259.

use super::nn_verify_proof_guided_nas::ProofGuidedNasConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Phase 1: Definition type builders
// =============================================================================

/// `NNVerify.architecture_space : Type`
pub(super) fn build_architecture_space_type(c: &ProofGuidedNasConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.verifiability_score : architecture_space -> Rat`
pub(super) fn build_verifiability_score_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.rat.clone())
}

/// `NNVerify.pareto_front : (architecture_space -> Rat) -> (architecture_space -> Rat) -> architecture_space -> Prop`
pub(super) fn build_pareto_front_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let fn_ty = Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.rat.clone());
    let (acc_id, _) = b.fresh_local(fn_ty.clone());
    let (ver_id, _) = b.fresh_local(fn_ty.clone());
    let (arch_id, _) = b.fresh_local(c.arch_space.clone());
    let e = b.mk_pi(
        arch_id,
        BinderInfo::Default,
        c.arch_space.clone(),
        c.prop.clone(),
    );
    let e = b.mk_pi(ver_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(acc_id, BinderInfo::Default, fn_ty, e);
    b.finish(e)
}

/// `NNVerify.architecture_transform : Type`
pub(super) fn build_architecture_transform_type(c: &ProofGuidedNasConsts) -> Expr {
    c.type0.clone()
}

/// `NNVerify.apply_transform : architecture_transform -> architecture_space -> architecture_space`
pub(super) fn build_apply_transform_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (t_id, _) = b.fresh_local(c.arch_transform.clone());
    let (a_id, _) = b.fresh_local(c.arch_space.clone());
    let e = b.mk_pi(
        a_id,
        BinderInfo::Default,
        c.arch_space.clone(),
        c.arch_space.clone(),
    );
    let e = b.mk_pi(t_id, BinderInfo::Default, c.arch_transform.clone(), e);
    b.finish(e)
}

/// `NNVerify.verified_accuracy : architecture_space -> Rat -> Rat`
pub(super) fn build_verified_accuracy_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (arch_id, _) = b.fresh_local(c.arch_space.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(arch_id, BinderInfo::Default, c.arch_space.clone(), e);
    b.finish(e)
}

/// `NNVerify.arch_depth : architecture_space -> Nat`
pub(super) fn build_arch_depth_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.nat.clone())
}

/// `NNVerify.arch_width : architecture_space -> Nat`
pub(super) fn build_arch_width_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.nat.clone())
}

/// `NNVerify.standard_accuracy : architecture_space -> Rat`
pub(super) fn build_standard_accuracy_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.rat.clone())
}

/// `NNVerify.has_skip_connections : architecture_space -> Prop`
pub(super) fn build_has_skip_connections_type(c: &ProofGuidedNasConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.prop.clone())
}

// =============================================================================
// Phase 1: Theorem type builders
// =============================================================================

/// `NNVerify.wider_more_verifiable`:
/// ```text
/// forall (a1 a2 : architecture_space),
///   arch_depth a1 = arch_depth a2 ->
///   LE.le (arch_width a1) (arch_width a2) ->
///   LE.le (verifiability_score a1) (verifiability_score a2)
/// ```
pub(super) fn build_wider_more_verifiable_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a1_id, a1) = b.fresh_local(c.arch_space.clone());
    let (a2_id, a2) = b.fresh_local(c.arch_space.clone());
    let depth1 = Expr::app(c.arch_depth.clone(), a1.clone());
    let depth2 = Expr::app(c.arch_depth.clone(), a2.clone());
    let hyp_eq = c.nat_eq(depth1, depth2);
    let (h1_id, _) = b.fresh_local(hyp_eq.clone());
    let width1 = Expr::app(c.arch_width.clone(), a1.clone());
    let width2 = Expr::app(c.arch_width.clone(), a2.clone());
    let hyp_le = c.nat_le(width1, width2);
    let (h2_id, _) = b.fresh_local(hyp_le.clone());
    let vs1 = Expr::app(c.verifiability_score.clone(), a1);
    let vs2 = Expr::app(c.verifiability_score.clone(), a2);
    let concl = c.rat_le(vs1, vs2);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_le, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_eq, e);
    let e = b.mk_pi(a2_id, BinderInfo::Default, c.arch_space.clone(), e);
    let e = b.mk_pi(a1_id, BinderInfo::Default, c.arch_space.clone(), e);
    b.finish(e)
}

/// `NNVerify.depth_verifiability_tradeoff`:
/// ```text
/// forall (a1 a2 : architecture_space),
///   arch_width a1 = arch_width a2 ->
///   LE.le (arch_depth a1) (arch_depth a2) ->
///   LE.le (verifiability_score a2) (verifiability_score a1)
/// ```
pub(super) fn build_depth_verifiability_tradeoff_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a1_id, a1) = b.fresh_local(c.arch_space.clone());
    let (a2_id, a2) = b.fresh_local(c.arch_space.clone());
    let width1 = Expr::app(c.arch_width.clone(), a1.clone());
    let width2 = Expr::app(c.arch_width.clone(), a2.clone());
    let hyp_eq = c.nat_eq(width1, width2);
    let (h1_id, _) = b.fresh_local(hyp_eq.clone());
    let depth1 = Expr::app(c.arch_depth.clone(), a1.clone());
    let depth2 = Expr::app(c.arch_depth.clone(), a2.clone());
    let hyp_le = c.nat_le(depth1, depth2);
    let (h2_id, _) = b.fresh_local(hyp_le.clone());
    let vs1 = Expr::app(c.verifiability_score.clone(), a1);
    let vs2 = Expr::app(c.verifiability_score.clone(), a2);
    let concl = c.rat_le(vs2, vs1);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_le, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_eq, e);
    let e = b.mk_pi(a2_id, BinderInfo::Default, c.arch_space.clone(), e);
    let e = b.mk_pi(a1_id, BinderInfo::Default, c.arch_space.clone(), e);
    b.finish(e)
}

/// `NNVerify.pareto_dominance_sound`:
/// ```text
/// forall (acc_fn ver_fn : architecture_space -> Rat) (a b : arch_space),
///   LT.lt (acc_fn a) (acc_fn b) ->
///   LT.lt (ver_fn a) (ver_fn b) ->
///   pareto_front acc_fn ver_fn a ->
///   False
/// ```
pub(super) fn build_pareto_dominance_sound_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let fn_ty = Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.rat.clone());
    let (acc_id, acc) = b.fresh_local(fn_ty.clone());
    let (ver_id, ver) = b.fresh_local(fn_ty.clone());
    let (a_id, a) = b.fresh_local(c.arch_space.clone());
    let (b_id, b_arch) = b.fresh_local(c.arch_space.clone());
    let acc_a = Expr::app(acc.clone(), a.clone());
    let acc_b = Expr::app(acc.clone(), b_arch.clone());
    let hyp_acc = c.rat_lt(acc_a, acc_b);
    let (h1_id, _) = b.fresh_local(hyp_acc.clone());
    let ver_a = Expr::app(ver.clone(), a.clone());
    let ver_b = Expr::app(ver.clone(), b_arch);
    let hyp_ver = c.rat_lt(ver_a, ver_b);
    let (h2_id, _) = b.fresh_local(hyp_ver.clone());
    let pf = Expr::apps(c.pareto_front.clone(), [acc.clone(), ver.clone(), a]);
    let (h3_id, _) = b.fresh_local(pf.clone());
    let e = b.mk_pi(h3_id, BinderInfo::Default, pf, c.false_.clone());
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_ver, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_acc, e);
    let e = b.mk_pi(b_id, BinderInfo::Default, c.arch_space.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.arch_space.clone(), e);
    let e = b.mk_pi(ver_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(acc_id, BinderInfo::Default, fn_ty, e);
    b.finish(e)
}

/// `NNVerify.nas_search_monotone`:
/// ```text
/// forall (t : architecture_transform) (acc_fn ver_fn : arch_space -> Rat) (a : arch_space),
///   LE.le (ver_fn a) (ver_fn (apply_transform t a)) ->
///   LE.le (acc_fn a) (acc_fn (apply_transform t a)) ->
///   pareto_front acc_fn ver_fn a ->
///   pareto_front acc_fn ver_fn (apply_transform t a)
/// ```
pub(super) fn build_nas_search_monotone_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (t_id, t) = b.fresh_local(c.arch_transform.clone());
    let fn_ty = Expr::pi(BinderInfo::Default, c.arch_space.clone(), c.rat.clone());
    let (acc_id, acc) = b.fresh_local(fn_ty.clone());
    let (ver_id, ver) = b.fresh_local(fn_ty.clone());
    let (a_id, a) = b.fresh_local(c.arch_space.clone());
    let ta = Expr::apps(c.apply_transform.clone(), [t, a.clone()]);
    let ver_a = Expr::app(ver.clone(), a.clone());
    let ver_ta = Expr::app(ver.clone(), ta.clone());
    let hyp_ver = c.rat_le(ver_a, ver_ta);
    let (h1_id, _) = b.fresh_local(hyp_ver.clone());
    let acc_a = Expr::app(acc.clone(), a.clone());
    let acc_ta = Expr::app(acc.clone(), ta.clone());
    let hyp_acc = c.rat_le(acc_a, acc_ta);
    let (h2_id, _) = b.fresh_local(hyp_acc.clone());
    let pf_a = Expr::apps(c.pareto_front.clone(), [acc.clone(), ver.clone(), a]);
    let (h3_id, _) = b.fresh_local(pf_a.clone());
    let pf_ta = Expr::apps(c.pareto_front.clone(), [acc, ver, ta]);
    let e = b.mk_pi(h3_id, BinderInfo::Default, pf_a, pf_ta);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_acc, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_ver, e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.arch_space.clone(), e);
    let e = b.mk_pi(ver_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(acc_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_pi(t_id, BinderInfo::Default, c.arch_transform.clone(), e);
    b.finish(e)
}

/// `NNVerify.skip_connections_improve_verifiability`:
/// ```text
/// forall (a : architecture_space),
///   has_skip_connections a ->
///   LE.le (verifiability_score (without_skip a)) (verifiability_score a)
/// ```
pub(super) fn build_skip_connections_improve_verifiability_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.arch_space.clone());
    let hyp = Expr::app(c.has_skip_connections.clone(), a.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    let ws_a = Expr::app(c.without_skip.clone(), a.clone());
    let vs_ws = Expr::app(c.verifiability_score.clone(), ws_a);
    let vs_a = Expr::app(c.verifiability_score.clone(), a);
    let concl = c.rat_le(vs_ws, vs_a);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.arch_space.clone(), e);
    b.finish(e)
}

/// `NNVerify.certified_accuracy_bound`:
/// ```text
/// forall (a : architecture_space) (epsilon : Rat),
///   0 < epsilon ->
///   LE.le (verified_accuracy a epsilon) (standard_accuracy a)
/// ```
pub(super) fn build_certified_accuracy_bound_type(c: &ProofGuidedNasConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.arch_space.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hyp_pos = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h_id, _) = b.fresh_local(hyp_pos.clone());
    let va = Expr::apps(c.verified_accuracy.clone(), [a.clone(), eps]);
    let sa = Expr::app(c.standard_accuracy.clone(), a);
    let concl = c.rat_le(va, sa);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp_pos, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.arch_space.clone(), e);
    b.finish(e)
}
