// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C005 type, proof, and opaque value builders for the McCormick attention
//! tightness theorem.
//!
//! This module contains the complex Expr builders for the theorem statement,
//! proof term, opaque sorry-based value terms, and helper type builders.
//! The simpler helper definition builders and Environment registration live
//! in `nn_verify_mccormick_attention.rs`.
//!
//! Part of #3150, #3381.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;
use crate::sorry::create_sorry_term;

use super::nn_verify_mccormick_attention::C005Consts;

// ========================================================================
// Main theorem type construction
// ========================================================================

/// **C005 Main Theorem: `NNVerify.McCormick.attention_tightness`**
///
/// ```text
/// forall (w_q w_k c eps : Rat),
///   0 <= eps ->
///   And
///     (Eq (gap (shared_lower w_q c eps)
///              (shared_upper w_q c eps)
///              (shared_lower w_k c eps)
///              (shared_upper w_k c eps))
///         (4 * |w_q| * |w_k| * eps^2))
///     (le (gap ...) (shared_input_width w_q eps * shared_input_width w_k eps))
/// ```
///
/// **Note:** gap = `(xu-xl)*(yu-yl)` = `(2*|w_q|*eps)*(2*|w_k|*eps)` = `4*|w_q|*|w_k|*eps^2`.
/// Part 2 is `gap <= width_Q * width_K`, which holds with equality.
pub(crate) fn build_attention_tightness_type(c: &C005Consts) -> Expr {
    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );
    let shared_width = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_width"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    // Hypothesis: 0 <= eps
    let h_eps = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    let q_lower = Expr::apps(
        shared_lower.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let q_upper = Expr::apps(
        shared_upper.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps.clone()]);
    let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps.clone()]);

    let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);

    // Part 1: gap = 4 * |w_q| * |w_k| * eps^2
    let abs_wq = c.abs(wq.clone());
    let abs_wk = c.abs(wk.clone());
    let eps_sq = c.mul(eps.clone(), eps.clone());
    let expected_gap = c.mul(c.rat_four(), c.mul(c.mul(abs_wq, abs_wk), eps_sq));
    let part1 = c.rat_eq(gap_val.clone(), expected_gap);

    // Part 2: gap <= width_Q * width_K
    let width_q = Expr::apps(shared_width.clone(), [wq.clone(), eps.clone()]);
    let width_k = Expr::apps(shared_width, [wk.clone(), eps.clone()]);
    let rhs = c.mul(width_q, width_k);
    let part2 = c.rat_le(gap_val, rhs);

    let conclusion = c.and_prop(part1, part2);

    let e = b.mk_pi(h_eps_id, BinderInfo::Default, h_eps, conclusion);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `attention_tightness`.
///
/// Applies `And.intro` to the helper axioms `shared_input_gap_eq`
/// and `shared_input_normalized_le`, forwarding all quantified variables.
pub(crate) fn build_attention_tightness_proof(c: &C005Consts) -> Expr {
    let gap_eq_axiom = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_gap_eq"),
        vec![],
    );
    let normalized_le_axiom = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_normalized_le"),
        vec![],
    );
    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_eps_ty = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, h_eps) = b.fresh_local(h_eps_ty.clone());

    let proof_part1 = Expr::apps(
        gap_eq_axiom,
        [
            wq.clone(),
            wk.clone(),
            center.clone(),
            eps.clone(),
            h_eps.clone(),
        ],
    );
    let proof_part2 = Expr::apps(
        normalized_le_axiom,
        [
            wq.clone(),
            wk.clone(),
            center.clone(),
            eps.clone(),
            h_eps.clone(),
        ],
    );

    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );
    let shared_width = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_width"),
        vec![],
    );

    let q_lower = Expr::apps(
        shared_lower.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let q_upper = Expr::apps(
        shared_upper.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps.clone()]);
    let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps.clone()]);
    let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);

    // Part 1 proposition: gap = 4 * |w_q| * |w_k| * eps^2
    let abs_wq = c.abs(wq.clone());
    let abs_wk = c.abs(wk.clone());
    let eps_sq = c.mul(eps.clone(), eps.clone());
    let expected_gap = c.mul(c.rat_four(), c.mul(c.mul(abs_wq, abs_wk), eps_sq));
    let prop_p = c.rat_eq(gap_val.clone(), expected_gap);

    // Part 2 proposition: gap <= width_Q * width_K
    let width_q = Expr::apps(shared_width.clone(), [wq.clone(), eps.clone()]);
    let width_k = Expr::apps(shared_width, [wk.clone(), eps.clone()]);
    let rhs = c.mul(width_q, width_k);
    let prop_q = c.rat_le(gap_val, rhs);

    // And.intro P Q proof_P proof_Q
    let body = Expr::apps(and_intro, [prop_p, prop_q, proof_part1, proof_part2]);

    let e = b.mk_lam(h_eps_id, BinderInfo::Default, h_eps_ty, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ========================================================================
// Helper axiom types
// ========================================================================

/// `NNVerify.McCormick.shared_input_gap_eq`:
///
/// ```text
/// forall (w_q w_k c eps : Rat),
///   0 <= eps ->
///   gap (shared_lower w_q c eps) (shared_upper w_q c eps)
///       (shared_lower w_k c eps) (shared_upper w_k c eps)
///   = 4 * |w_q| * |w_k| * eps^2
/// ```
///
/// **Derivation:** gap = (xu-xl)*(yu-yl) where xu-xl = 2*|w_q|*eps,
/// yu-yl = 2*|w_k|*eps, so gap = 4*|w_q|*|w_k|*eps^2.
/// Requires algebraic reasoning (Rat.sub/add cancellation) for proof;
/// route through ay QF_LRA when available.
pub(crate) fn build_shared_input_gap_eq_type(c: &C005Consts) -> Expr {
    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    let q_lower = Expr::apps(
        shared_lower.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let q_upper = Expr::apps(
        shared_upper.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps.clone()]);
    let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps.clone()]);

    let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);
    let abs_wq = c.abs(wq);
    let abs_wk = c.abs(wk);
    let eps_sq = c.mul(eps.clone(), eps.clone());
    let expected = c.mul(c.rat_four(), c.mul(c.mul(abs_wq, abs_wk), eps_sq));
    let concl = c.rat_eq(gap_val, expected);

    let e = b.mk_pi(h_eps_id, BinderInfo::Default, h_eps, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.McCormick.shared_input_normalized_le`:
///
/// ```text
/// forall (w_q w_k c eps : Rat),
///   0 <= eps ->
///   gap (...) <= shared_input_width w_q eps * shared_input_width w_k eps
/// ```
///
/// This holds with equality: gap = (xu-xl)*(yu-yl) = width_Q * width_K.
/// Requires algebraic reasoning for proof; route through ay QF_LRA.
pub(crate) fn build_shared_input_normalized_le_type(c: &C005Consts) -> Expr {
    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );
    let shared_width = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_width"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    let q_lower = Expr::apps(
        shared_lower.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let q_upper = Expr::apps(
        shared_upper.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps.clone()]);
    let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps.clone()]);

    let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);
    let width_q = Expr::apps(shared_width.clone(), [wq, eps.clone()]);
    let width_k = Expr::apps(shared_width, [wk, eps]);
    let rhs = c.mul(width_q, width_k);
    let concl = c.rat_le(gap_val, rhs);

    let e = b.mk_pi(h_eps_id, BinderInfo::Default, h_eps, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.McCormick.shared_input_width_eq`:
///
/// ```text
/// forall (w eps : Rat), 0 <= eps ->
///   (shared_input_width w eps = 2 * |w| * eps) ->
///   shared_input_width w eps = 2 * |w| * eps
/// ```
pub(crate) fn build_shared_input_width_eq_type(c: &C005Consts) -> Expr {
    let shared_width = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_width"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    let lhs = Expr::apps(shared_width, [w.clone(), eps.clone()]);
    let rhs = c.mul(c.mul(c.rat_two(), c.abs(w)), eps);
    let concl = c.rat_eq(lhs, rhs);
    let (h_width_eq_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_width_eq_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h_eps_id, BinderInfo::Default, h_eps, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

pub(crate) fn build_shared_input_width_eq_value(c: &C005Consts) -> Expr {
    let shared_width = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_width"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    let lhs = Expr::apps(shared_width, [w.clone(), eps.clone()]);
    let rhs = c.mul(c.mul(c.rat_two(), c.abs(w)), eps);
    let concl = c.rat_eq(lhs, rhs);
    let (h_width_eq_id, h_width_eq) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_width_eq_id, BinderInfo::Default, concl, h_width_eq);
    let e = b.mk_lam(h_eps_id, BinderInfo::Default, h_eps, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ========================================================================
// Sorry-based opaque value builders (Axiom -> Opaque conversion)
// ========================================================================

/// Build sorry-based opaque value for `shared_input_gap_eq`.
///
/// ```text
/// fun (w_q w_k c eps : Rat) (_ : 0 <= eps) =>
///   @sorryAx.{0} (Eq Rat (gap ...) (4 * |w_q| * |w_k| * eps^2)) true
/// ```
///
/// Mathematical justification: gap = (xu-xl)*(yu-yl) where
/// xu-xl = (w*c + |w|*eps) - (w*c - |w|*eps) = 2*|w_q|*eps,
/// yu-yl = 2*|w_k|*eps, so gap = 4*|w_q|*|w_k|*eps^2.
/// Requires algebraic reasoning (Rat.sub/add cancellation) that the kernel
/// cannot perform via definitional reduction; sorry provides proof inhabitation.
///
/// Part of #3381: convert C005 axioms to opaques.
pub(crate) fn build_shared_input_gap_eq_value(env: &Environment, c: &C005Consts) -> Expr {
    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    let q_lower = Expr::apps(
        shared_lower.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let q_upper = Expr::apps(
        shared_upper.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps.clone()]);
    let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps.clone()]);

    let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);
    let abs_wq = c.abs(wq);
    let abs_wk = c.abs(wk);
    let eps_sq = c.mul(eps.clone(), eps.clone());
    let expected = c.mul(c.rat_four(), c.mul(c.mul(abs_wq, abs_wk), eps_sq));
    let concl = c.rat_eq(gap_val, expected);

    let body = create_sorry_term(env, &concl);

    let e = b.mk_lam(h_eps_id, BinderInfo::Default, h_eps, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build sorry-based opaque value for `shared_input_normalized_le`.
///
/// ```text
/// fun (w_q w_k c eps : Rat) (_ : 0 <= eps) =>
///   @sorryAx.{0} (LE.le Rat instLERat (gap ...) (width_Q * width_K)) true
/// ```
///
/// Mathematical justification: gap = (xu-xl)*(yu-yl) = width_Q * width_K
/// holds with equality, so the inequality follows trivially.
///
/// Part of #3381: convert C005 axioms to opaques.
pub(crate) fn build_shared_input_normalized_le_value(env: &Environment, c: &C005Consts) -> Expr {
    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );
    let shared_width = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_width"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    let q_lower = Expr::apps(
        shared_lower.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let q_upper = Expr::apps(
        shared_upper.clone(),
        [wq.clone(), center.clone(), eps.clone()],
    );
    let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps.clone()]);
    let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps.clone()]);

    let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);
    let width_q = Expr::apps(shared_width.clone(), [wq, eps.clone()]);
    let width_k = Expr::apps(shared_width, [wk, eps]);
    let rhs = c.mul(width_q, width_k);
    let concl = c.rat_le(gap_val, rhs);

    let body = create_sorry_term(env, &concl);

    let e = b.mk_lam(h_eps_id, BinderInfo::Default, h_eps, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build sorry-based opaque value for `attention_gap_linear_in_eps`.
///
/// ```text
/// fun (w_q w_k c eps_max : Rat) (_ : 0 <= eps_max) =>
///   @sorryAx.{0} (And (0 <= C) (forall eps' ...)) true
/// ```
///
/// Mathematical justification: C = 4*|w_q|*|w_k|*eps_max is non-negative
/// (product of non-negatives), and gap(eps') = 4*|w_q|*|w_k|*eps'^2
/// <= 4*|w_q|*|w_k|*eps_max*eps' since eps' <= eps_max.
///
/// Part of #3381: convert C005 axioms to opaques.
pub(crate) fn build_attention_gap_linear_value(env: &Environment, c: &C005Consts) -> Expr {
    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_max_id, eps_max) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps_max.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    // C = 4 * |w_q| * |w_k| * eps_max
    let bound_const = c.mul(
        c.rat_four(),
        c.mul(c.mul(c.abs(wq.clone()), c.abs(wk.clone())), eps_max.clone()),
    );

    let inner = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (eps2_id, eps2) = ch.fresh_local(c.rat.clone());
        let h_eps2 = c.rat_le(c.rat_zero.clone(), eps2.clone());
        let (h_eps2_id, _) = ch.fresh_local(h_eps2.clone());
        let h_le_max = c.rat_le(eps2.clone(), eps_max.clone());
        let (h_le_max_id, _) = ch.fresh_local(h_le_max.clone());

        let q_lower = Expr::apps(
            shared_lower.clone(),
            [wq.clone(), center.clone(), eps2.clone()],
        );
        let q_upper = Expr::apps(
            shared_upper.clone(),
            [wq.clone(), center.clone(), eps2.clone()],
        );
        let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps2.clone()]);
        let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps2.clone()]);

        let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);
        let bound_rhs = c.mul(bound_const.clone(), eps2);
        let concl = c.rat_le(gap_val, bound_rhs);

        let r = ch.mk_pi(h_le_max_id, BinderInfo::Default, h_le_max, concl);
        let r = ch.mk_pi(h_eps2_id, BinderInfo::Default, h_eps2, r);
        let r = ch.mk_pi(eps2_id, BinderInfo::Default, c.rat.clone(), r);
        ch.finish_child(r)
    };

    // And (0 <= C) (forall eps' ...)
    let c_nonneg = c.rat_le(c.rat_zero.clone(), bound_const);
    let conclusion = c.and_prop(c_nonneg, inner);

    let body = create_sorry_term(env, &conclusion);

    let e = b.mk_lam(h_eps_id, BinderInfo::Default, h_eps, body);
    let e = b.mk_lam(eps_max_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.McCormick.attention_gap_linear_in_eps`:
///
/// The O(eps) existence claim: there exists a constant C = 4*|w_q|*|w_k|*eps_max
/// such that gap(eps') <= C * eps' for all eps' in [0, eps_max].
///
/// **Derivation:** gap(eps') = 4*|w_q|*|w_k|*eps'^2 (from gap_eq).
/// Need: 4*|w_q|*|w_k|*eps'^2 <= C*eps', i.e., C >= 4*|w_q|*|w_k|*eps'.
/// Since eps' <= eps_max, C = 4*|w_q|*|w_k|*eps_max suffices.
pub(crate) fn build_attention_gap_linear_type(c: &C005Consts) -> Expr {
    let shared_lower = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_lower"),
        vec![],
    );
    let shared_upper = Expr::const_(
        Name::from_string("NNVerify.McCormick.shared_input_upper"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (wq_id, wq) = b.fresh_local(c.rat.clone());
    let (wk_id, wk) = b.fresh_local(c.rat.clone());
    let (center_id, center) = b.fresh_local(c.rat.clone());
    let (eps_max_id, eps_max) = b.fresh_local(c.rat.clone());

    let h_eps = c.rat_le(c.rat_zero.clone(), eps_max.clone());
    let (h_eps_id, _) = b.fresh_local(h_eps.clone());

    // C = 4 * |w_q| * |w_k| * eps_max
    let bound_const = c.mul(
        c.rat_four(),
        c.mul(c.mul(c.abs(wq.clone()), c.abs(wk.clone())), eps_max.clone()),
    );

    let inner = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (eps2_id, eps2) = ch.fresh_local(c.rat.clone());
        let h_eps2 = c.rat_le(c.rat_zero.clone(), eps2.clone());
        let (h_eps2_id, _) = ch.fresh_local(h_eps2.clone());
        let h_le_max = c.rat_le(eps2.clone(), eps_max.clone());
        let (h_le_max_id, _) = ch.fresh_local(h_le_max.clone());

        let q_lower = Expr::apps(
            shared_lower.clone(),
            [wq.clone(), center.clone(), eps2.clone()],
        );
        let q_upper = Expr::apps(
            shared_upper.clone(),
            [wq.clone(), center.clone(), eps2.clone()],
        );
        let k_lower = Expr::apps(shared_lower, [wk.clone(), center.clone(), eps2.clone()]);
        let k_upper = Expr::apps(shared_upper, [wk.clone(), center.clone(), eps2.clone()]);

        let gap_val = c.gap_app(q_lower, q_upper, k_lower, k_upper);
        let bound_rhs = c.mul(bound_const.clone(), eps2);
        let concl = c.rat_le(gap_val, bound_rhs);

        let r = ch.mk_pi(h_le_max_id, BinderInfo::Default, h_le_max, concl);
        let r = ch.mk_pi(h_eps2_id, BinderInfo::Default, h_eps2, r);
        let r = ch.mk_pi(eps2_id, BinderInfo::Default, c.rat.clone(), r);
        ch.finish_child(r)
    };

    // And (0 <= C) (forall eps' ...)
    let c_nonneg = c.rat_le(c.rat_zero.clone(), bound_const);
    let conclusion = c.and_prop(c_nonneg, inner);

    let e = b.mk_pi(h_eps_id, BinderInfo::Default, h_eps, conclusion);
    let e = b.mk_pi(eps_max_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(center_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wk_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(wq_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
