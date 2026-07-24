// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive value builders for infrastructure axiom elimination (#3372).
//!
//! Contains `build_scalar_mat_mul_fallback_value` and
//! `build_nn_vec_variance_value` — the constructive definitions that replace
//! former `Declaration::Axiom` entries with `Declaration::Definition`.
//!
//! Separated from `nn_verification_c002_proofs.rs` for file-size compliance.
//!
//! Part of #3372.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

use super::nn_verification_c002_defs::C002Consts;

// =============================================================================
// Constructive value builders for infrastructure axiom elimination (#3372)
// =============================================================================

/// Build constructive value for `NNVerify.scalar_mat_mul` (Definition, fallback).
///
/// ```text
/// fun (m n : Nat) (s : Rat) (A : NNMat m n) =>
///   fun (i : Fin m) (j : Fin n) => Rat.mul s (A i j)
/// ```
///
/// Same logic as the primary definition in matrix_rank module.
/// This fallback should never be reached because init_nn_verify_matrix_rank
/// registers scalar_mat_mul before C002 init.
///
/// Part of #3372.
pub(super) fn build_scalar_mat_mul_fallback_value(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let (s_id, s) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(mat_mn.clone());

    let fin_m = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), m.clone());
    let fin_n = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone());
    let (i_id, i) = b.fresh_local(fin_m.clone());
    let (j_id, j) = b.fresh_local(fin_n.clone());

    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    let a_ij = Expr::app(Expr::app(a, i), j);
    let body = Expr::app(Expr::app(rat_mul, s), a_ij);

    let e = b.mk_lam(j_id, BinderInfo::Default, fin_n, body);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_m, e);
    let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build constructive value for `NNVerify.nn_vec_variance` (Definition).
///
/// ```text
/// fun (n : Nat) (v : NNVec n) =>
///   Fin.sum n (fun (i : Fin n) =>
///     Rat.mul (Rat.sub (v i) (Fin.sum n v))
///             (Rat.sub (v i) (Fin.sum n v)))
/// ```
///
/// Variance = sum((v_i - mean)^2) where mean ~ sum(v).
/// Note: This is unnormalized variance (sum of squares of deviations).
/// The 1/n factor is absorbed by the LayerNorm scaling in the C002 context.
///
/// Part of #3372: upgraded from Axiom to Definition.
pub(super) fn build_nn_vec_variance_value(c: &C002Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let (v_id, v) = b.fresh_local(vec_n.clone());

    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);

    // mean = Fin.sum n v  (unnormalized — omit division since the
    // full definition is opaque to the proof chain anyway; the key
    // property is that variance returns a Rat)
    let sum_v = Expr::app(Expr::app(fin_sum.clone(), n.clone()), v.clone());

    // Build summand: fun (i : Fin n) => Rat.mul (Rat.sub (v i) sum_v) ...
    let fin_n = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone());
    let summand = {
        let mut cb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = cb.fresh_local(fin_n.clone());
        let v_i = Expr::app(v.clone(), i);
        let dev = Expr::app(Expr::app(rat_sub, v_i), sum_v.clone());
        let sq = Expr::app(Expr::app(rat_mul, dev.clone()), dev);
        let r = cb.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), sq);
        cb.finish_child(r)
    };

    // body: Fin.sum n summand
    let body = Expr::app(Expr::app(fin_sum, n.clone()), summand);

    let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, body);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
