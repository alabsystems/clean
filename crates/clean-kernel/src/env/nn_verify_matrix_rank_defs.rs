// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # Matrix Rank Type/Value Builders — STATED CONJECTURES (NOT PROVED)
//!
//! **Status: The "theorem type builders" in this file construct type
//! signatures (statement types) for declarations that are registered as
//! `Declaration::Axiom` — they have NO proof terms. These conjectures are
//! formally stated but not formally proved in the clean kernel.**
//!
//! To make these genuine proofs, the corresponding axiom registrations in
//! `nn_verify_matrix_rank.rs` must be replaced with `Declaration::Theorem`
//! entries containing constructive proof terms.
//!
//! ---
//!
//! Type and value builders for `nn_verify_matrix_rank` declarations.
//!
//! Separated from the main module to stay within the 500-line file limit.
//! All `build_*` functions accept a `MatrixRankConsts` reference and return
//! well-formed `Expr` types/values for kernel declaration registration.
//!
//! Part of #3207.

use super::nn_verify_matrix_rank::MatrixRankConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// =============================================================================
// Definition type/value builders
// =============================================================================

/// `ones_matrix (n : Nat) : NNMat n n`
pub(super) fn build_ones_matrix_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let result = c.mat_of(n.clone(), n);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), result);
    b.finish(e)
}

/// `ones_matrix n := fun (i : Fin n) (j : Fin n) => Rat.one`
pub(super) fn build_ones_matrix_value(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), n.clone());
    let (i_id, _i) = b.fresh_local(fin_n.clone());
    let (j_id, _j) = b.fresh_local(fin_n.clone());
    let body = c.rat_one.clone();
    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), body);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `mean_projection (n : Nat) : NNMat n n`
pub(super) fn build_mean_projection_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let result = c.mat_of(n.clone(), n);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), result);
    b.finish(e)
}

pub(super) fn build_identity_matrix_value(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    let eq_cond = Expr::app(
        Expr::app(Expr::app(c.eq_u1.clone(), fin_n.clone()), i.clone()),
        j.clone(),
    );
    let dec_inst = Expr::app(
        Expr::app(Expr::app(c.inst_dec_eq_fin.clone(), n.clone()), i),
        j,
    );
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(c.ite.clone(), c.rat.clone()), eq_cond),
                dec_inst,
            ),
            c.rat_one.clone(),
        ),
        c.rat_zero.clone(),
    );

    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), body);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

pub(super) fn build_matrix_sub_value(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let (a_id, a) = b.fresh_local(mat_mn.clone());
    let (b2_id, b2) = b.fresh_local(mat_mn.clone());

    let fin_m = Expr::app(c.fin.clone(), m);
    let fin_n = Expr::app(c.fin.clone(), n);
    let (i_id, i) = b.fresh_local(fin_m.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    let a_ij = Expr::app(Expr::app(a, i.clone()), j.clone());
    let b_ij = Expr::app(Expr::app(b2, i), j);
    let body = Expr::app(Expr::app(c.rat_sub.clone(), a_ij), b_ij);

    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n, body);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_m, e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, mat_mn.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

pub(super) fn build_mean_projection_value(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::app(c.ones_matrix.clone(), n);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(e)
}

// =============================================================================
// Helper axiom type builders
// =============================================================================

/// `matrix_rank (m n : Nat) (M : NNMat m n) : Nat`
pub(super) fn build_matrix_rank_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m, n);
    let (w_id, _) = b.fresh_local(mat_mn.clone());
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, c.nat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `matrix_mul (m n p : Nat) (A : NNMat m n) (B : NNMat n p) : NNMat m p`
pub(super) fn build_matrix_mul_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (p_id, p) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let mat_np = c.mat_of(n, p.clone());
    let result = c.mat_of(m, p);
    let (b_id, _) = b.fresh_local(mat_np.clone());
    let (a_id, _) = b.fresh_local(mat_mn.clone());
    let e = b.mk_pi(b_id, BinderInfo::Default, mat_np, result);
    let e = b.mk_pi(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(p_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `matrix_sub (m n : Nat) (A B : NNMat m n) : NNMat m n`
pub(super) fn build_matrix_sub_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let result = c.mat_of(m, n);
    let (b2_id, _) = b.fresh_local(mat_mn.clone());
    let (a_id, _) = b.fresh_local(mat_mn.clone());
    let e = b.mk_pi(b2_id, BinderInfo::Default, mat_mn.clone(), result);
    let e = b.mk_pi(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `identity_matrix (n : Nat) : NNMat n n`
pub(super) fn build_identity_matrix_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let result = c.mat_of(n.clone(), n);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), result);
    b.finish(e)
}

/// `interval_hull_width (n : Nat) (B : IntervalBounds n) : Rat`
pub(super) fn build_interval_hull_width_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = Expr::app(c.ib.clone(), n);
    let (bnd_id, _) = b.fresh_local(ib_n.clone());
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, c.rat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `linear_image_zonotope (n m : Nat) (L : NNMat m n) (Z : IntervalBounds n) : IntervalBounds m`
pub(super) fn build_linear_image_zonotope_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let ib_n = Expr::app(c.ib.clone(), n);
    let ib_m = Expr::app(c.ib.clone(), m);
    let (z_id, _) = b.fresh_local(ib_n.clone());
    let (l_id, _) = b.fresh_local(mat_mn.clone());
    let e = b.mk_pi(z_id, BinderInfo::Default, ib_n, ib_m);
    let e = b.mk_pi(l_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `fresh_zonotope_from_hull (n : Nat) (B : IntervalBounds n) : IntervalBounds n`
pub(super) fn build_fresh_zonotope_from_hull_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = Expr::app(c.ib.clone(), n);
    let (b_id, _) = b.fresh_local(ib_n.clone());
    let e = b.mk_pi(b_id, BinderInfo::Default, ib_n.clone(), ib_n);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Conjecture type builders (axiom-backed, no proof terms)
// =============================================================================

/// `ones_matrix_rank_one : forall (n : Nat), 1 <= n -> rank(ones_matrix n) = 1`
pub(super) fn build_ones_matrix_rank_one_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hyp = c.nat_le(c.nat_one.clone(), n.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    let ones_n = Expr::app(c.ones_matrix.clone(), n.clone());
    let rank_ones = c.rank_app(&n, ones_n);
    let conclusion = c.nat_eq(rank_ones, c.nat_one.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, conclusion);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `mean_projection_idempotent : forall (n : Nat), 1 <= n ->
///   matrix_mul n n n (mean_projection n) (mean_projection n) = mean_projection n`
pub(super) fn build_mean_projection_idempotent_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hyp = c.nat_le(c.nat_one.clone(), n.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    let mp_n = Expr::app(c.mean_projection.clone(), n.clone());
    let mp_sq = c.mat_mul_app(&n, mp_n.clone(), mp_n.clone());
    let conclusion = c.mat_eq(&n, mp_sq, mp_n);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, conclusion);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `identity_minus_projection_rank : forall (n : Nat), 1 <= n ->
///   rank(identity_matrix n - mean_projection n) = n - 1`
pub(super) fn build_identity_minus_projection_rank_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hyp = c.nat_le(c.nat_one.clone(), n.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    let id_n = Expr::app(c.identity_matrix.clone(), n.clone());
    let mp_n = Expr::app(c.mean_projection.clone(), n.clone());
    let diff = c.mat_sub_app(&n, id_n, mp_n);
    let rank_diff = c.rank_app(&n, diff);
    let n_minus_1 = c.nat_sub_app(n.clone(), c.nat_one.clone());
    let conclusion = c.nat_eq(rank_diff, n_minus_1);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, conclusion);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `zonotope_rankdef_width_eq : forall (n m : Nat) (L : NNMat m n)
///   (Z : IntervalBounds n),
///   rank(L) < n ->
///   interval_hull_width m (linear_image_zonotope n m L Z) =
///   interval_hull_width m (fresh_zonotope_from_hull m (linear_image_zonotope n m L Z))`
pub(super) fn build_zonotope_rankdef_width_eq_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let (l_id, l) = b.fresh_local(mat_mn.clone());
    let ib_n = Expr::app(c.ib.clone(), n.clone());
    let (z_id, _z) = b.fresh_local(ib_n.clone());
    // hypothesis: rank(L) < n  encoded as  LE.le (Nat.succ (rank L)) n
    // i.e. rank(L) + 1 <= n
    // L : NNMat m n is rectangular, so its rank is matrix_rank m n L
    // (the square helper c.rank_app would build matrix_rank n n L, which
    // demands L : NNMat n n and is the wrong dimension wiring here).
    let rank_l = Expr::apps(c.matrix_rank.clone(), [m.clone(), n.clone(), l.clone()]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_rank = Expr::app(nat_succ, rank_l);
    let hyp = c.nat_le(succ_rank, n.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    // LHS: interval_hull_width m (linear_image_zonotope n m L Z)
    let liz = Expr::apps(
        c.linear_image_zonotope.clone(),
        [n.clone(), m.clone(), l.clone(), _z.clone()],
    );
    let lhs = Expr::apps(c.interval_hull_width.clone(), [m.clone(), liz.clone()]);
    // RHS: interval_hull_width m (fresh_zonotope_from_hull m (...))
    let fresh = Expr::apps(c.fresh_zonotope_from_hull.clone(), [m.clone(), liz]);
    let rhs = Expr::apps(c.interval_hull_width.clone(), [m.clone(), fresh]);
    // Conclusion: Eq @Rat lhs rhs
    let rat_eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let conclusion = Expr::app(Expr::app(Expr::app(rat_eq, c.rat.clone()), lhs), rhs);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, conclusion);
    let e = b.mk_pi(z_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(l_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Supporting axiom type builders for C002 constructive proofs
// Part of #3307.
// =============================================================================

/// `scalar_mat_rank_le : forall (n : Nat) (s : Rat) (M : NNMat n n),
///   LE.le @Nat instLENat (matrix_rank n n (scalar_mat_mul n n s M)) (matrix_rank n n M)`
///
/// Scalar multiplication does not increase matrix rank.
pub(super) fn build_scalar_mat_rank_le_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (s_id, s) = b.fresh_local(c.rat.clone());
    let mat_nn = c.mat_of(n.clone(), n.clone());
    let (m_id, m) = b.fresh_local(mat_nn.clone());

    let scalar_mat_mul = Expr::const_(Name::from_string("NNVerify.scalar_mat_mul"), vec![]);
    let scaled = Expr::apps(scalar_mat_mul, [n.clone(), n.clone(), s, m.clone()]);
    let rank_scaled = c.rank_app(&n, scaled);
    let rank_m = c.rank_app(&n, m);
    let conclusion = c.nat_le(rank_scaled, rank_m);

    let e = b.mk_pi(m_id, BinderInfo::Default, mat_nn, conclusion);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `nat_eq_pred_succ_le : forall (a n : Nat),
///   Eq Nat a (Nat.sub n (Nat.succ Nat.zero)) -> LE.le @Nat instLENat (Nat.succ Nat.zero) n ->
///   LE.le @Nat instLENat (Nat.succ a) n`
///
/// If a = n - 1 and 1 <= n, then a + 1 <= n.
pub(super) fn build_nat_eq_pred_succ_le_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());

    let n_minus_1 = c.nat_sub_app(n.clone(), c.nat_one.clone());
    let h_eq = c.nat_eq(a.clone(), n_minus_1);
    let (heq_id, _) = b.fresh_local(h_eq.clone());

    let h_ge = c.nat_le(c.nat_one.clone(), n.clone());
    let (hge_id, _) = b.fresh_local(h_ge.clone());

    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_a = Expr::app(nat_succ, a);
    let conclusion = c.nat_le(succ_a, n);

    let e = b.mk_pi(hge_id, BinderInfo::Default, h_ge, conclusion);
    let e = b.mk_pi(heq_id, BinderInfo::Default, h_eq, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `le_trans_nat : forall (a b c : Nat),
///   LE.le @Nat instLENat a b -> LE.le @Nat instLENat b c ->
///   LE.le @Nat instLENat a c`
///
/// Transitivity of Nat ordering.
pub(super) fn build_le_trans_nat_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (b2_id, b2) = b.fresh_local(c.nat.clone());
    let (c_id, c_var) = b.fresh_local(c.nat.clone());

    let h_ab = c.nat_le(a.clone(), b2.clone());
    let (hab_id, _) = b.fresh_local(h_ab.clone());
    let h_bc = c.nat_le(b2, c_var.clone());
    let (hbc_id, _) = b.fresh_local(h_bc.clone());

    let conclusion = c.nat_le(a, c_var);

    let e = b.mk_pi(hbc_id, BinderInfo::Default, h_bc, conclusion);
    let e = b.mk_pi(hab_id, BinderInfo::Default, h_ab, e);
    let e = b.mk_pi(c_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(b2_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `nat_succ_le_succ : forall (a b : Nat),
///   LE.le @Nat instLENat a b ->
///   LE.le @Nat instLENat (Nat.succ a) (Nat.succ b)`
///
/// Monotonicity of Nat.succ w.r.t. LE.
pub(super) fn build_nat_succ_le_succ_type(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (b2_id, b2) = b.fresh_local(c.nat.clone());

    let h_le = c.nat_le(a.clone(), b2.clone());
    let (h_id, _) = b.fresh_local(h_le.clone());

    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_a = Expr::app(nat_succ.clone(), a);
    let succ_b = Expr::app(nat_succ, b2);
    let conclusion = c.nat_le(succ_a, succ_b);

    let e = b.mk_pi(h_id, BinderInfo::Default, h_le, conclusion);
    let e = b.mk_pi(b2_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Value builders for constructive definitions (#3372)
// =============================================================================

/// Build constructive value for `NNVerify.scalar_mat_mul` (Definition).
///
/// ```text
/// fun (m n : Nat) (s : Rat) (A : NNMat m n) =>
///   fun (i : Fin m) (j : Fin n) => Rat.mul s (A i j)
/// ```
///
/// Scalar-matrix multiplication: multiply each entry by the scalar.
/// NNMat m n = Fin m -> Fin n -> Rat, so the result is a function that
/// applies Rat.mul to each element.
///
/// Part of #3372: upgraded from Axiom to Definition.
pub(super) fn build_scalar_mat_mul_value(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let (s_id, s) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(mat_mn.clone());

    let fin_m = Expr::app(c.fin.clone(), m.clone());
    let fin_n = Expr::app(c.fin.clone(), n.clone());
    let (i_id, i) = b.fresh_local(fin_m.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    // A i j
    let a_ij = Expr::app(Expr::app(a, i), j);
    // Rat.mul s (A i j)
    let body = Expr::app(Expr::app(rat_mul, s), a_ij);

    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n, body);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_m, e);
    let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build constructive value for `NNVerify.fresh_zonotope_from_hull` (Definition).
///
/// ```text
/// fun (n : Nat) (B : IntervalBounds n) => B
/// ```
///
/// The identity function on `IntervalBounds n`. "Freshening" a zonotope
/// from its interval hull discards cross-term correlations, but at the
/// level of `IntervalBounds` (axis-aligned boxes), there are no
/// cross-term correlations to discard — the bounds already represent
/// an independent per-dimension range.
///
/// Part of #3371: upgraded from Axiom to Definition. Makes
/// `interval_hull_width n (fresh_zonotope_from_hull n B)` definitionally
/// equal to `interval_hull_width n B`, enabling Eq.refl proofs.
pub(super) fn build_fresh_zonotope_from_hull_value(c: &MatrixRankConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = Expr::app(c.ib.clone(), n);
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, bnd);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// Note: build_layernorm_ibp_bridge_type was moved to nn_verification_c002_defs.rs
// because it references C002-specific names (NNVerify.C002.layernorm_zonotope)
// that are only available after C002 init. Part of #3307.
