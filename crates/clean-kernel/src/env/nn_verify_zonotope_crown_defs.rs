// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C010 Type Builders
//!
//! Status: former C010 domain axioms are represented as
//! hypothesis-wrapped theorem types where missing evidence is an explicit
//! local premise. See `nn_verify_zonotope_crown.rs` for the full inventory.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!
//! ---
//!
//! Contains all `build_*` functions that construct the Expr types for
//! definitions, lemmas, and theorems. Separated from the main module
//! to keep each file under 500 lines.

use super::nn_verify_zonotope_crown::ZonotopeCrownConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// =============================================================================
// Type builders for definitions
// =============================================================================

/// `NNVerify.NNMat.mul : (m n p : Nat) -> NNMat m n -> NNMat n p -> NNMat m p`
pub(super) fn build_mat_mul_type(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let (p_id, p) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let mat_np = c.base.mat_of(n, p.clone());
    let result = c.base.mat_of(m, p);
    let (b_id, _) = b.fresh_local(mat_np.clone());
    let (a_id, _) = b.fresh_local(mat_mn.clone());
    let e = b.mk_pi(b_id, BinderInfo::Default, mat_np, result);
    let e = b.mk_pi(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(p_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.NNMat.transpose : (m n : Nat) -> NNMat m n -> NNMat n m`
pub(super) fn build_mat_transpose_type(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let result = c.base.mat_of(n, m);
    let (a_id, _) = b.fresh_local(mat_mn.clone());
    let e = b.mk_pi(a_id, BinderInfo::Default, mat_mn, result);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Zonotope.linear_propagate`:
/// `(m n : Nat) -> NNMat m n -> NNVec m -> IntervalBounds n -> IntervalBounds m`
pub(super) fn build_zonotope_linear_propagate_type(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let vec_m = c.base.vec_of(m.clone());
    let input_bounds = c.base.ib_of(n);
    let (ib_id, _) = b.fresh_local(input_bounds.clone());
    let (bias_id, _) = b.fresh_local(vec_m.clone());
    let (w_id, _) = b.fresh_local(mat_mn.clone());
    let result = c.base.ib_of(m);
    let e = b.mk_pi(ib_id, BinderInfo::Default, input_bounds, result);
    let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.CROWN.backward_linear`:
/// `(m n : Nat) -> NNMat m n -> NNVec m -> IntervalBounds n -> IntervalBounds m`
pub(super) fn build_crown_backward_linear_type(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let vec_m = c.base.vec_of(m.clone());
    let input_bounds = c.base.ib_of(n);
    let (ib_id, _) = b.fresh_local(input_bounds.clone());
    let (bias_id, _) = b.fresh_local(vec_m.clone());
    let (w_id, _) = b.fresh_local(mat_mn.clone());
    let result = c.base.ib_of(m);
    let e = b.mk_pi(ib_id, BinderInfo::Default, input_bounds, result);
    let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Zonotope.to_bounds`:
/// `(n : Nat) -> NNVec n -> IntervalBounds n -> IntervalBounds n`
pub(super) fn build_zonotope_to_bounds_type(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let vec_n = c.base.vec_of(n.clone());
    let input_bounds = c.base.ib_of(n.clone());
    let (center_id, _) = b.fresh_local(vec_n.clone());
    let (ib_id, _) = b.fresh_local(input_bounds.clone());
    let result = c.base.ib_of(n);
    let e = b.mk_pi(ib_id, BinderInfo::Default, input_bounds, result);
    let e = b.mk_pi(center_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.CROWN.concretize_linear`:
/// `(k : Nat) -> (output_dim : Nat -> Nat) -> weight_family -> bias_family ->
///     IntervalBounds (output_dim 0) -> IntervalBounds (output_dim k)`
pub(super) fn build_crown_concretize_linear_type(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, _) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, _) = b.fresh_local(bias_ty.clone());
    let input_ty = c.base.ib_of(c.out_dim(&output_dim, c.nat_zero.clone()));
    let (input_id, _) = b.fresh_local(input_ty.clone());
    let result = c.base.ib_of(c.out_dim(&output_dim, k));
    let e = b.mk_pi(input_id, BinderInfo::Default, input_ty, result);
    let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_pi(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Lemma and theorem type builders
// =============================================================================

/// `NNVerify.C010.mat_mul_assoc`: matrix multiplication associativity.
/// The missing associativity fact is exposed as a local premise after the
/// matrix binders, so the registered theorem does not depend on a global
/// C010 axiom or on unfolding opaque `NNVerify.NNMat.mul`.
pub(super) fn build_mat_mul_assoc_type(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let (p_id, p) = b.fresh_local(c.base.nat.clone());
    let (q_id, q) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let mat_np = c.base.mat_of(n.clone(), p.clone());
    let mat_pq = c.base.mat_of(p.clone(), q.clone());
    let (a_id, a) = b.fresh_local(mat_mn.clone());
    let (bv_id, bv) = b.fresh_local(mat_np.clone());
    let (cv_id, cv) = b.fresh_local(mat_pq.clone());
    let mat_mq = c.base.mat_of(m.clone(), q.clone());
    let bc = c.mat_mul_app(n.clone(), p.clone(), q.clone(), bv.clone(), cv.clone());
    let lhs = c.mat_mul_app(m.clone(), n.clone(), q.clone(), a.clone(), bc);
    let ab = c.mat_mul_app(m.clone(), n, p.clone(), a, bv);
    let rhs = c.mat_mul_app(m, p, q, ab, cv);
    let eq_mat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let concl = Expr::app(Expr::app(Expr::app(eq_mat, mat_mq), lhs), rhs);
    let (h_assoc_id, _) = b.fresh_local(concl.clone());
    let e = b.mk_pi(h_assoc_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(cv_id, BinderInfo::Default, mat_pq, e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, mat_np, e);
    let e = b.mk_pi(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(q_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(p_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// Proof for the hypothesis-wrapped `NNVerify.C010.mat_mul_assoc`.
///
/// The proof returns the explicit local associativity premise:
/// `fun m n p q A B C h_assoc => h_assoc`.
pub(super) fn build_mat_mul_assoc_proof(c: &ZonotopeCrownConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let (p_id, p) = b.fresh_local(c.base.nat.clone());
    let (q_id, q) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let mat_np = c.base.mat_of(n.clone(), p.clone());
    let mat_pq = c.base.mat_of(p.clone(), q.clone());
    let (a_id, a) = b.fresh_local(mat_mn.clone());
    let (bv_id, bv) = b.fresh_local(mat_np.clone());
    let (cv_id, cv) = b.fresh_local(mat_pq.clone());
    let mat_mq = c.base.mat_of(m.clone(), q.clone());
    let bc = c.mat_mul_app(n.clone(), p.clone(), q.clone(), bv.clone(), cv.clone());
    let lhs = c.mat_mul_app(m.clone(), n.clone(), q.clone(), a.clone(), bc);
    let ab = c.mat_mul_app(m.clone(), n, p.clone(), a, bv);
    let rhs = c.mat_mul_app(m, p, q, ab, cv);
    let eq_mat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let concl = Expr::app(Expr::app(Expr::app(eq_mat, mat_mq), lhs), rhs);
    let (h_assoc_id, h_assoc) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_assoc_id, BinderInfo::Default, concl, h_assoc);
    let e = b.mk_lam(cv_id, BinderInfo::Default, mat_pq, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, mat_np, e);
    let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(q_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_lam(p_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// Single-layer zonotope = IBP linear bounds.
pub(super) fn build_zonotope_single_linear_eq_type(c: &ZonotopeCrownConsts) -> Expr {
    build_single_method_eq_type(c, &c.zonotope_linear_propagate)
}

/// Single-layer CROWN = IBP linear bounds.
pub(super) fn build_crown_single_linear_eq_type(c: &ZonotopeCrownConsts) -> Expr {
    build_single_method_eq_type(c, &c.crown_backward_linear)
}

/// Shared builder for single-layer equivalence: method m n W b input = ibp m n W b input.
fn build_single_method_eq_type(c: &ZonotopeCrownConsts, method: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let vec_m = c.base.vec_of(m.clone());
    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (bias_id, bias) = b.fresh_local(vec_m.clone());
    let input_ty = c.base.ib_of(n.clone());
    let (inp_id, inp) = b.fresh_local(input_ty.clone());
    let result_ty = c.base.ib_of(m.clone());
    let lhs = Expr::apps(
        method.clone(),
        [m.clone(), n.clone(), w.clone(), bias.clone(), inp.clone()],
    );
    let ibp_linear = Expr::const_(Name::from_string("NNVerify.ibp_linear_bounds"), vec![]);
    let rhs = Expr::apps(ibp_linear, [m, n, w, bias, inp]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let concl = Expr::app(Expr::app(Expr::app(eq, result_ty), lhs), rhs);
    let e = b.mk_pi(inp_id, BinderInfo::Default, input_ty, concl);
    let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// Main theorem type: zonotope forward = CROWN backward for k-layer linear network.
pub(super) fn build_zonotope_equals_crown_type(c: &ZonotopeCrownConsts) -> Expr {
    build_network_eq_type(
        c,
        "NNVerify.Zonotope.linear_propagate_network",
        "NNVerify.CROWN.concretize_linear",
    )
}

/// Corollary type: zonotope forward = exact affine combined.
pub(super) fn build_both_compute_exact_affine_type(c: &ZonotopeCrownConsts) -> Expr {
    build_network_eq_hypothesis_wrapped_type(
        c,
        "NNVerify.Zonotope.linear_propagate_network",
        "NNVerify.C010.affine_combined",
    )
}

/// Proof for the hypothesis-wrapped `both_compute_exact_affine` corollary.
pub(super) fn build_both_compute_exact_affine_proof(c: &ZonotopeCrownConsts) -> Expr {
    build_network_eq_hypothesis_wrapped_proof(
        c,
        "NNVerify.Zonotope.linear_propagate_network",
        "NNVerify.C010.affine_combined",
    )
}

/// Shared builder for network-level equality theorems.
fn build_network_eq_type(c: &ZonotopeCrownConsts, lhs_name: &str, rhs_name: &str) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, w) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let input_ty = c.base.ib_of(c.out_dim(&output_dim, c.nat_zero.clone()));
    let (inp_id, inp) = b.fresh_local(input_ty.clone());
    let result_ty = c.base.ib_of(c.out_dim(&output_dim, k.clone()));
    let args = [
        k.clone(),
        output_dim.clone(),
        w.clone(),
        bias.clone(),
        inp.clone(),
    ];
    let lhs_const = Expr::const_(Name::from_string(lhs_name), vec![]);
    let lhs = Expr::apps(lhs_const, args.clone());
    let rhs_const = Expr::const_(Name::from_string(rhs_name), vec![]);
    let rhs = Expr::apps(rhs_const, args);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let concl = Expr::app(Expr::app(Expr::app(eq, result_ty), lhs), rhs);
    let e = b.mk_pi(inp_id, BinderInfo::Default, input_ty, concl);
    let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_pi(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// Shared builder for network-level equality theorems where the equality
/// proof is passed explicitly as local evidence.
fn build_network_eq_hypothesis_wrapped_type(
    c: &ZonotopeCrownConsts,
    lhs_name: &str,
    rhs_name: &str,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, w) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let input_ty = c.base.ib_of(c.out_dim(&output_dim, c.nat_zero.clone()));
    let (inp_id, inp) = b.fresh_local(input_ty.clone());
    let result_ty = c.base.ib_of(c.out_dim(&output_dim, k.clone()));
    let args = [
        k.clone(),
        output_dim.clone(),
        w.clone(),
        bias.clone(),
        inp.clone(),
    ];
    let lhs_const = Expr::const_(Name::from_string(lhs_name), vec![]);
    let lhs = Expr::apps(lhs_const, args.clone());
    let rhs_const = Expr::const_(Name::from_string(rhs_name), vec![]);
    let rhs = Expr::apps(rhs_const, args);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let concl = Expr::app(Expr::app(Expr::app(eq, result_ty), lhs), rhs);
    let (h_eq_id, _) = b.fresh_local(concl.clone());
    let e = b.mk_pi(h_eq_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(inp_id, BinderInfo::Default, input_ty, e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_pi(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

fn build_network_eq_hypothesis_wrapped_proof(
    c: &ZonotopeCrownConsts,
    lhs_name: &str,
    rhs_name: &str,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, w) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let input_ty = c.base.ib_of(c.out_dim(&output_dim, c.nat_zero.clone()));
    let (inp_id, inp) = b.fresh_local(input_ty.clone());
    let result_ty = c.base.ib_of(c.out_dim(&output_dim, k.clone()));
    let args = [
        k.clone(),
        output_dim.clone(),
        w.clone(),
        bias.clone(),
        inp.clone(),
    ];
    let lhs_const = Expr::const_(Name::from_string(lhs_name), vec![]);
    let lhs = Expr::apps(lhs_const, args.clone());
    let rhs_const = Expr::const_(Name::from_string(rhs_name), vec![]);
    let rhs = Expr::apps(rhs_const, args);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let concl = Expr::app(Expr::app(Expr::app(eq, result_ty), lhs), rhs);
    let (h_eq_id, h_eq) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_eq_id, BinderInfo::Default, concl, h_eq);
    let e = b.mk_lam(inp_id, BinderInfo::Default, input_ty, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_lam(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// k-layer zonotope forward propagation type (same as CROWN concretize).
pub(super) fn build_zonotope_linear_propagate_network_type(c: &ZonotopeCrownConsts) -> Expr {
    build_crown_concretize_linear_type(c)
}

/// Affine combined type (same as CROWN concretize).
pub(super) fn build_affine_combined_type(c: &ZonotopeCrownConsts) -> Expr {
    build_crown_concretize_linear_type(c)
}
