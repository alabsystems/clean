// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for abstract interpretation framework: zonotope domain,
//! transfer functions, and domain/transfer soundness theorems.
//!
//! Split from `abstract_interpretation_framework_defs.rs` for the 500-line
//! limit. The base file holds lattice ops, Galois connection, interval domain,
//! and core lattice/Galois theorems.
//!
//! ## Definitions
//!
//! - `zonotope_*` - zonotope-domain lattice operators
//! - `linear_transfer` - linear-layer abstract transformer
//! - `relu_transfer` - ReLU abstract transformer
//! - `layer_compose_transfer` - composition of abstract layer transformers
//!
//! ## Theorems
//!
//! - `interval_is_abstract_domain` - intervals satisfy the domain laws
//! - `zonotope_is_abstract_domain` - zonotopes satisfy the domain laws
//! - `zonotope_refines_interval_galois` - zonotopes refine intervals
//! - `linear_transfer_sound` - linear transfer preserves containment
//! - `relu_transfer_sound` - ReLU transfer preserves containment
//!
//! Part of #3189.

use super::abstract_interpretation::AbstractInterpConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Zonotope domain definition type builders
// =============================================================================

/// `AbstractInterp.Framework.zonotope_join :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Zonotope-domain join operation. Computes the least upper bound of two
/// zonotope abstract states.
pub(super) fn build_zonotope_join_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.zonotope_meet :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Zonotope-domain meet operation. Computes the greatest lower bound of two
/// zonotope abstract states.
pub(super) fn build_zonotope_meet_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.zonotope_bot : AbstractState`
///
/// Bottom element for the zonotope abstract domain.
pub(super) fn build_zonotope_bot_type(c: &AbstractInterpConsts) -> Expr {
    c.abstract_state.clone()
}

/// `AbstractInterp.Framework.zonotope_top : AbstractState`
///
/// Top element for the zonotope abstract domain.
pub(super) fn build_zonotope_top_type(c: &AbstractInterpConsts) -> Expr {
    c.abstract_state.clone()
}

/// `AbstractInterp.Framework.zonotope_widening :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Zonotope-domain widening operator. Accelerates fixpoint computation by
/// extrapolating ascending chains in the zonotope lattice.
pub(super) fn build_zonotope_widening_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

// =============================================================================
// Transfer function definition type builders
// =============================================================================

/// `AbstractInterp.Framework.linear_transfer :
///    (AbstractState -> AbstractState) ->
///    AbstractState ->
///    AbstractState ->
///    AbstractState`
///
/// Abstract transfer function for affine layers. Takes a weight transform, a
/// bias abstract state, and an input abstract state, then returns the output
/// abstract state after linear propagation.
pub(super) fn build_linear_transfer_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let weight_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (weight_id, _) = b.fresh_local(weight_ty.clone());
    let (bias_id, _) = b.fresh_local(c.abstract_state.clone());
    let (input_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        input_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(bias_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(weight_id, BinderInfo::Default, weight_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.relu_transfer :
///    AbstractState -> AbstractState`
///
/// Abstract transfer function for ReLU activation. Maps input bounds to the
/// abstract state describing the ReLU output bounds.
pub(super) fn build_relu_transfer_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (input_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        input_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    b.finish(e)
}

/// `AbstractInterp.Framework.layer_compose_transfer :
///    (AbstractState -> AbstractState) ->
///    (AbstractState -> AbstractState) ->
///    AbstractState ->
///    AbstractState`
///
/// Composition operator for abstract layer transformers. Given two unary
/// transfer functions and an input abstract state, returns the abstract state
/// obtained by applying the two transfers in sequence.
pub(super) fn build_layer_compose_transfer_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let transfer_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (f_id, _) = b.fresh_local(transfer_ty.clone());
    let (g_id, _) = b.fresh_local(transfer_ty.clone());
    let (input_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        input_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(g_id, BinderInfo::Default, transfer_ty.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, transfer_ty, e);
    b.finish(e)
}

// =============================================================================
// Domain witness and transfer soundness theorem type builders
// =============================================================================

/// `AbstractInterp.Framework.interval_is_abstract_domain`:
/// Simplified abstract-domain witness for intervals.
pub(super) fn build_interval_is_abstract_domain_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let binop_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (join_id, join) = b.fresh_local(binop_ty.clone());
    let (meet_id, meet) = b.fresh_local(binop_ty.clone());
    let (widen_id, widen) = b.fresh_local(binop_ty.clone());
    let (bot_id, bot) = b.fresh_local(c.abstract_state.clone());
    let (top_id, top) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, bv) = b.fresh_local(c.abstract_state.clone());
    let join_a_b = Expr::app(Expr::app(join, a.clone()), bv.clone());
    let hyp_join = c.state_le(a.clone(), join_a_b);
    let (hj_id, _) = b.fresh_local(hyp_join.clone());
    let meet_a_b = Expr::app(Expr::app(meet, a.clone()), bv.clone());
    let hyp_meet = c.state_le(meet_a_b, a.clone());
    let (hm_id, _) = b.fresh_local(hyp_meet.clone());
    let hyp_bot = c.state_le(bot.clone(), a.clone());
    let (hb_id, _) = b.fresh_local(hyp_bot.clone());
    let hyp_top = c.state_le(a.clone(), top.clone());
    let (ht_id, _) = b.fresh_local(hyp_top.clone());
    let widen_a_b = Expr::app(Expr::app(widen, a.clone()), bv);
    let hyp_widen = c.state_le(a, widen_a_b);
    let (hw_id, _) = b.fresh_local(hyp_widen.clone());
    let concl = c.state_le(bot, top);
    let e = b.mk_pi(hw_id, BinderInfo::Default, hyp_widen, concl);
    let e = b.mk_pi(ht_id, BinderInfo::Default, hyp_top, e);
    let e = b.mk_pi(hb_id, BinderInfo::Default, hyp_bot, e);
    let e = b.mk_pi(hm_id, BinderInfo::Default, hyp_meet, e);
    let e = b.mk_pi(hj_id, BinderInfo::Default, hyp_join, e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(top_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(bot_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(widen_id, BinderInfo::Default, binop_ty.clone(), e);
    let e = b.mk_pi(meet_id, BinderInfo::Default, binop_ty.clone(), e);
    let e = b.mk_pi(join_id, BinderInfo::Default, binop_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.zonotope_is_abstract_domain`:
/// Simplified abstract-domain witness for zonotopes.
pub(super) fn build_zonotope_is_abstract_domain_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let binop_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (join_id, join) = b.fresh_local(binop_ty.clone());
    let (meet_id, meet) = b.fresh_local(binop_ty.clone());
    let (widen_id, widen) = b.fresh_local(binop_ty.clone());
    let (bot_id, bot) = b.fresh_local(c.abstract_state.clone());
    let (top_id, top) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, bv) = b.fresh_local(c.abstract_state.clone());
    let join_a_b = Expr::app(Expr::app(join, a.clone()), bv.clone());
    let hyp_join = c.state_le(a.clone(), join_a_b);
    let (hj_id, _) = b.fresh_local(hyp_join.clone());
    let meet_a_b = Expr::app(Expr::app(meet, a.clone()), bv.clone());
    let hyp_meet = c.state_le(meet_a_b, a.clone());
    let (hm_id, _) = b.fresh_local(hyp_meet.clone());
    let hyp_bot = c.state_le(bot.clone(), a.clone());
    let (hb_id, _) = b.fresh_local(hyp_bot.clone());
    let hyp_top = c.state_le(a.clone(), top.clone());
    let (ht_id, _) = b.fresh_local(hyp_top.clone());
    let widen_a_b = Expr::app(Expr::app(widen, a.clone()), bv);
    let hyp_widen = c.state_le(a, widen_a_b);
    let (hw_id, _) = b.fresh_local(hyp_widen.clone());
    let concl = c.state_le(bot, top);
    let e = b.mk_pi(hw_id, BinderInfo::Default, hyp_widen, concl);
    let e = b.mk_pi(ht_id, BinderInfo::Default, hyp_top, e);
    let e = b.mk_pi(hb_id, BinderInfo::Default, hyp_bot, e);
    let e = b.mk_pi(hm_id, BinderInfo::Default, hyp_meet, e);
    let e = b.mk_pi(hj_id, BinderInfo::Default, hyp_join, e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(top_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(bot_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(widen_id, BinderInfo::Default, binop_ty.clone(), e);
    let e = b.mk_pi(meet_id, BinderInfo::Default, binop_ty.clone(), e);
    let e = b.mk_pi(join_id, BinderInfo::Default, binop_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.zonotope_refines_interval_galois`:
/// Full refinement interface for the interval/zonotope Galois connection.
pub(super) fn build_zonotope_refines_interval_galois_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let map_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (alpha_id, alpha) = b.fresh_local(map_ty.clone());
    let (gamma_id, gamma) = b.fresh_local(map_ty.clone());
    let (cv_id, cv) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let gamma_a = Expr::app(gamma, a.clone());
    let hyp = c.state_le(cv.clone(), gamma_a);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let alpha_c = Expr::app(alpha, cv);
    let concl = c.state_le(alpha_c, a);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, map_ty.clone(), e);
    let e = b.mk_pi(alpha_id, BinderInfo::Default, map_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.linear_transfer_sound`:
/// Soundness interface for affine transfer.
pub(super) fn build_linear_transfer_sound_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let map_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let linear_transfer_ty = Expr::pi(
        BinderInfo::Default,
        map_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            Expr::pi(
                BinderInfo::Default,
                c.abstract_state.clone(),
                c.abstract_state.clone(),
            ),
        ),
    );
    let (transfer_id, transfer) = b.fresh_local(linear_transfer_ty.clone());
    let (weight_id, weight) = b.fresh_local(map_ty.clone());
    let (bias_id, bias) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, bv) = b.fresh_local(c.abstract_state.clone());
    let hyp = c.state_le(a.clone(), bv.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    let lhs = Expr::apps(transfer.clone(), [weight.clone(), bias.clone(), a]);
    let rhs = Expr::apps(transfer, [weight, bias, bv]);
    let concl = c.state_le(lhs, rhs);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(weight_id, BinderInfo::Default, map_ty, e);
    let e = b.mk_pi(transfer_id, BinderInfo::Default, linear_transfer_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.relu_transfer_sound`:
/// Soundness interface for the ReLU transfer function.
pub(super) fn build_relu_transfer_sound_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let relu_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (relu_id, relu) = b.fresh_local(relu_ty.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, bv) = b.fresh_local(c.abstract_state.clone());
    let hyp = c.state_le(a.clone(), bv.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    let lhs = Expr::app(relu.clone(), a);
    let rhs = Expr::app(relu, bv);
    let concl = c.state_le(lhs, rhs);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(relu_id, BinderInfo::Default, relu_ty, e);
    b.finish(e)
}
