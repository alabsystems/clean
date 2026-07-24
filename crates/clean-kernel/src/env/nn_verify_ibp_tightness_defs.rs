// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008 definition value builders, eps_ball opaque value, and main theorem.
//!
//! Contains `Nat.rec` value terms for 4 definitions (infinity_norm,
//! ibp_width, norm_product, ibp_propagate), eps_ball opaque value, and
//! the main theorem (`ibp_tightness_bound`) type and proof.
//!
//! Induction proof builders live in `nn_verify_ibp_tightness_proofs`.
//! Part of #3374.

use super::nn_verify_ibp_tightness::IbpTightnessConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Well-typed placeholder value for the `NNVerify.eps_ball` opaque definition.
/// Returns zero IntervalBounds; opaque prevents reduction. Category A fix.
pub(super) fn build_eps_ball_value(c: &IbpTightnessConsts) -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let rat_zero = c.base.rat_zero.clone();
    let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin = c.base.fin.clone();

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let vec_n = c.base.vec_of(n.clone());
    let (center_id, _center) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.base.rat.clone());

    let fin_n = Expr::app(fin.clone(), n.clone());

    // zero_vec : NNVec n = fun (i : Fin n) => Rat.zero
    let zero_vec = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, _) = ch.fresh_local(fin_n.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), rat_zero.clone());
        ch.finish_child(r)
    };

    // valid : forall (i : Fin n), Rat.le Rat.zero Rat.zero
    // = fun (i : Fin n) => Rat.le_refl Rat.zero
    let valid = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, _) = ch.fresh_local(fin_n.clone());
        let proof = Expr::app(le_refl, rat_zero);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, proof);
        ch.finish_child(r)
    };

    // IntervalBounds.mk n zero_vec zero_vec valid
    let body = Expr::apps(ib_mk, [n.clone(), zero_vec.clone(), zero_vec, valid]);

    let e = b.mk_lam(eps_id, BinderInfo::Default, c.base.rat.clone(), body);
    let e = b.mk_lam(center_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Definition value builders
// =============================================================================

/// Succ case for `infinity_norm` Nat.rec: max of prefix norm and last row sum.
fn infinity_norm_succ_case(c: &IbpTightnessConsts, b: &EnvDeclBuilder, n: &Expr) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (rows_id, rows) = ch.fresh_local(c.base.nat.clone());
    let ih_ty = Expr::pi(
        BinderInfo::Default,
        c.base.mat_of(rows.clone(), n.clone()),
        c.base.rat.clone(),
    );
    let (ih_id, ih) = ch.fresh_local(ih_ty.clone());
    let rows_succ = Expr::app(c.nat_succ.clone(), rows.clone());
    let mat_succ_n = c.base.mat_of(rows_succ.clone(), n.clone());
    let (ws_id, ws) = ch.fresh_local(mat_succ_n.clone());

    let prefix_w = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let fin_rows = Expr::app(c.base.fin.clone(), rows.clone());
        let fin_n = Expr::app(c.base.fin.clone(), n.clone());
        let (i_id, i) = ch2.fresh_local(fin_rows.clone());
        let inner = {
            let mut ch3 = EnvDeclBuilder::child_of(&ch2);
            let (j_id, j) = ch3.fresh_local(fin_n.clone());
            let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), rows.clone()), i.clone());
            let body = Expr::app(Expr::app(ws.clone(), cast_i), j);
            let r = ch3.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), body);
            ch3.finish_child(r)
        };
        let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_rows, inner);
        ch2.finish_child(r)
    };

    let last_row_abs = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let fin_n = Expr::app(c.base.fin.clone(), n.clone());
        let (j_id, j) = ch2.fresh_local(fin_n.clone());
        let last_i = Expr::app(c.fin_last.clone(), rows.clone());
        let w_last_j = Expr::app(Expr::app(ws.clone(), last_i), j);
        let body = Expr::app(c.rat_abs.clone(), w_last_j);
        let r = ch2.mk_lam(j_id, BinderInfo::Default, fin_n, body);
        ch2.finish_child(r)
    };

    let prefix_norm = Expr::app(ih, prefix_w);
    let row_sum = c.base.sum(n.clone(), last_row_abs);
    let body = Expr::app(Expr::app(c.rat_max.clone(), prefix_norm), row_sum);

    let r = ch.mk_lam(ws_id, BinderInfo::Default, mat_succ_n, body);
    let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
    let r = ch.mk_lam(rows_id, BinderInfo::Default, c.base.nat.clone(), r);
    ch.finish_child(r)
}

pub(super) fn build_infinity_norm_value(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.base.nat.clone());
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let mat_mn = c.base.mat_of(m.clone(), n.clone());
    let (w_id, w) = b.fresh_local(mat_mn.clone());

    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (rows_id, rows) = ch.fresh_local(c.base.nat.clone());
        let body = Expr::pi(
            BinderInfo::Default,
            c.base.mat_of(rows.clone(), n.clone()),
            c.base.rat.clone(),
        );
        let r = ch.mk_lam(rows_id, BinderInfo::Default, c.base.nat.clone(), body);
        ch.finish_child(r)
    };

    let zero_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (w0_id, _) = ch.fresh_local(c.base.mat_of(c.nat_zero.clone(), n.clone()));
        let r = ch.mk_lam(
            w0_id,
            BinderInfo::Default,
            c.base.mat_of(c.nat_zero.clone(), n.clone()),
            c.base.rat_zero.clone(),
        );
        ch.finish_child(r)
    };

    let succ_case = infinity_norm_succ_case(c, &b, &n);

    let rec_result = Expr::apps(
        c.nat_rec_type0.clone(),
        [motive, zero_case, succ_case, m.clone()],
    );
    let body = Expr::app(rec_result, w);

    let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, body);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// Succ case for `ibp_width` Nat.rec: max of prefix width and last coord width.
fn ibp_width_succ_case(c: &IbpTightnessConsts, b: &EnvDeclBuilder) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (d_id, d) = ch.fresh_local(c.base.nat.clone());
    let ih_ty = Expr::pi(
        BinderInfo::Default,
        c.base.ib_of(d.clone()),
        c.base.rat.clone(),
    );
    let (ih_id, ih) = ch.fresh_local(ih_ty.clone());
    let d_succ = Expr::app(c.nat_succ.clone(), d.clone());
    let ib_succ = c.base.ib_of(d_succ.clone());
    let (bs_id, bs) = ch.fresh_local(ib_succ.clone());

    let lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bs.clone());
    let upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bs.clone());
    let valid = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 2, bs.clone());

    let lower_prefix = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let fin_d = Expr::app(c.base.fin.clone(), d.clone());
        let (i_id, i) = ch2.fresh_local(fin_d.clone());
        let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), d.clone()), i.clone());
        let body = Expr::app(lower.clone(), cast_i);
        let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_d, body);
        ch2.finish_child(r)
    };

    let upper_prefix = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let fin_d = Expr::app(c.base.fin.clone(), d.clone());
        let (i_id, i) = ch2.fresh_local(fin_d.clone());
        let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), d.clone()), i.clone());
        let body = Expr::app(upper.clone(), cast_i);
        let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_d, body);
        ch2.finish_child(r)
    };

    let valid_prefix = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let fin_d = Expr::app(c.base.fin.clone(), d.clone());
        let (i_id, i) = ch2.fresh_local(fin_d.clone());
        let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), d.clone()), i.clone());
        let body = Expr::app(valid.clone(), cast_i);
        let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_d, body);
        ch2.finish_child(r)
    };

    let prefix_bounds = Expr::apps(
        c.ib_mk.clone(),
        [d.clone(), lower_prefix, upper_prefix, valid_prefix],
    );
    let prefix_width = Expr::app(ih, prefix_bounds);

    let last_i = Expr::app(c.fin_last.clone(), d.clone());
    let last_width = Expr::app(
        Expr::app(c.rat_sub.clone(), Expr::app(upper, last_i.clone())),
        Expr::app(lower, last_i),
    );
    let body = Expr::app(Expr::app(c.rat_max.clone(), prefix_width), last_width);

    let r = ch.mk_lam(bs_id, BinderInfo::Default, ib_succ, body);
    let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
    let r = ch.mk_lam(d_id, BinderInfo::Default, c.base.nat.clone(), r);
    ch.finish_child(r)
}

pub(super) fn build_ibp_width_value(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let ib_n = c.base.ib_of(n.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (d_id, d) = ch.fresh_local(c.base.nat.clone());
        let body = Expr::pi(
            BinderInfo::Default,
            c.base.ib_of(d.clone()),
            c.base.rat.clone(),
        );
        let r = ch.mk_lam(d_id, BinderInfo::Default, c.base.nat.clone(), body);
        ch.finish_child(r)
    };

    let zero_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (b0_id, _) = ch.fresh_local(c.base.ib_of(c.nat_zero.clone()));
        let r = ch.mk_lam(
            b0_id,
            BinderInfo::Default,
            c.base.ib_of(c.nat_zero.clone()),
            c.base.rat_zero.clone(),
        );
        ch.finish_child(r)
    };

    let succ_case = ibp_width_succ_case(c, &b);

    let rec_result = Expr::apps(
        c.nat_rec_type0.clone(),
        [motive, zero_case, succ_case, n.clone()],
    );
    let body = Expr::app(rec_result, bnd);

    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, body);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

pub(super) fn build_norm_product_value(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let fin_k = Expr::app(c.base.fin.clone(), k.clone());
    let norms_ty = Expr::pi(BinderInfo::Default, fin_k.clone(), c.base.rat.clone());
    let (norms_id, norms) = b.fresh_local(norms_ty.clone());

    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (d_id, d) = ch.fresh_local(c.base.nat.clone());
        let fin_d = Expr::app(c.base.fin.clone(), d.clone());
        let body = Expr::pi(BinderInfo::Default, fin_d, c.base.rat.clone());
        let body = Expr::pi(BinderInfo::Default, body, c.base.rat.clone());
        let r = ch.mk_lam(d_id, BinderInfo::Default, c.base.nat.clone(), body);
        ch.finish_child(r)
    };

    let zero_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_zero = Expr::app(c.base.fin.clone(), c.nat_zero.clone());
        let norms_zero_ty = Expr::pi(BinderInfo::Default, fin_zero, c.base.rat.clone());
        let (f_id, _) = ch.fresh_local(norms_zero_ty.clone());
        let r = ch.mk_lam(f_id, BinderInfo::Default, norms_zero_ty, c.rat_one.clone());
        ch.finish_child(r)
    };

    let succ_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (d_id, d) = ch.fresh_local(c.base.nat.clone());
        let fin_d = Expr::app(c.base.fin.clone(), d.clone());
        let prefix_ty = Expr::pi(BinderInfo::Default, fin_d.clone(), c.base.rat.clone());
        let ih_ty = Expr::pi(BinderInfo::Default, prefix_ty.clone(), c.base.rat.clone());
        let (ih_id, ih) = ch.fresh_local(ih_ty.clone());
        let d_succ = Expr::app(c.nat_succ.clone(), d.clone());
        let fin_succ = Expr::app(c.base.fin.clone(), d_succ.clone());
        let succ_ty = Expr::pi(BinderInfo::Default, fin_succ.clone(), c.base.rat.clone());
        let (f_id, f) = ch.fresh_local(succ_ty.clone());

        let prefix_f = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (i_id, i) = ch2.fresh_local(fin_d.clone());
            let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), d.clone()), i.clone());
            let body = Expr::app(f.clone(), cast_i);
            let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_d, body);
            ch2.finish_child(r)
        };

        let last_norm = Expr::app(f.clone(), Expr::app(c.fin_last.clone(), d.clone()));
        let prefix_prod = Expr::app(ih, prefix_f);
        let body = c.base.mul(last_norm, prefix_prod);

        let r = ch.mk_lam(f_id, BinderInfo::Default, succ_ty, body);
        let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
        let r = ch.mk_lam(d_id, BinderInfo::Default, c.base.nat.clone(), r);
        ch.finish_child(r)
    };

    let rec_result = Expr::apps(
        c.nat_rec_type0.clone(),
        [motive, zero_case, succ_case, k.clone()],
    );
    let body = Expr::app(rec_result, norms);

    let e = b.mk_lam(norms_id, BinderInfo::Default, norms_ty, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

pub(super) fn build_ibp_propagate_value(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let input_ty = c.input_bounds_ty(&output_dim);
    let (input_id, input_bounds) = b.fresh_local(input_ty.clone());

    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (d_id, d) = ch.fresh_local(c.base.nat.clone());
        let body = Expr::pi(
            BinderInfo::Default,
            c.input_bounds_ty(&output_dim),
            c.base.ib_of(c.out_dim(&output_dim, d.clone())),
        );
        let r = ch.mk_lam(d_id, BinderInfo::Default, c.base.nat.clone(), body);
        ch.finish_child(r)
    };

    let zero_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let input_ty0 = c.input_bounds_ty(&output_dim);
        let (b0_id, b0) = ch.fresh_local(input_ty0.clone());
        let r = ch.mk_lam(b0_id, BinderInfo::Default, input_ty0, b0);
        ch.finish_child(r)
    };

    let succ_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (d_id, d) = ch.fresh_local(c.base.nat.clone());
        let ih_ty = Expr::pi(
            BinderInfo::Default,
            c.input_bounds_ty(&output_dim),
            c.base.ib_of(c.out_dim(&output_dim, d.clone())),
        );
        let (ih_id, ih) = ch.fresh_local(ih_ty.clone());
        let input_ty0 = c.input_bounds_ty(&output_dim);
        let (b0_id, b0) = ch.fresh_local(input_ty0.clone());

        let d_succ = Expr::app(c.nat_succ.clone(), d.clone());
        let out_d = c.out_dim(&output_dim, d.clone());
        let out_succ_d = c.out_dim(&output_dim, d_succ.clone());
        let w_d = Expr::app(weight.clone(), d.clone());
        let bias_d = Expr::app(bias.clone(), d);
        let prev = Expr::app(ih, b0.clone());
        let linear = c.linear_bounds_app(out_succ_d.clone(), out_d, w_d, bias_d, prev);
        let body = c.relu_bounds_app(out_succ_d, linear);

        let r = ch.mk_lam(b0_id, BinderInfo::Default, input_ty0, body);
        let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
        let r = ch.mk_lam(d_id, BinderInfo::Default, c.base.nat.clone(), r);
        ch.finish_child(r)
    };

    let rec_result = Expr::apps(
        c.nat_rec_type0.clone(),
        [motive, zero_case, succ_case, k.clone()],
    );
    let body = Expr::app(rec_result, input_bounds);

    let e = b.mk_lam(input_id, BinderInfo::Default, input_ty, body);
    let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_lam(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

// === Main theorem type ======================================================

/// Type for `ibp_tightness_bound` / `ibp_tightness_bound_inductive`.
/// Carries `Rat.le Rat.zero eps` per designs/2026-04-18-c008-statement-redesign.md.
pub(super) fn build_ibp_tightness_bound_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let center_ty = c.center_ty(&output_dim);
    let (center_id, center) = b.fresh_local(center_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
    let nonneg_ty = c.base.rat_le(c.base.rat_zero.clone(), eps.clone());
    let (h_nonneg_id, _h_nonneg) = b.fresh_local(nonneg_ty.clone());

    let input_bounds = c.eps_ball_app(
        c.out_dim(&output_dim, c.nat_zero.clone()),
        center,
        eps.clone(),
    );
    let propagated = c.ibp_propagate_app(
        k.clone(),
        output_dim.clone(),
        weight.clone(),
        bias,
        input_bounds,
    );
    let lhs = c.ibp_width_app(c.out_dim(&output_dim, k.clone()), propagated);
    let norms = c.norm_lambda(&b, &k, &output_dim, &weight);
    let rhs = c
        .base
        .mul(c.base.mul(c.two(), eps), c.norm_product_app(k, norms));
    let concl = c.base.rat_le(lhs, rhs);

    let e = b.mk_pi(h_nonneg_id, BinderInfo::Default, nonneg_ty, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.base.rat.clone(), e);
    let e = b.mk_pi(center_id, BinderInfo::Default, center_ty, e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_pi(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

/// Proof term for `ibp_tightness_bound` — delegates to the inductive helper,
/// threading the new `h_nonneg` hypothesis through as an extra argument.
pub(super) fn build_ibp_tightness_bound_proof(c: &IbpTightnessConsts) -> Expr {
    let helper = Expr::const_(
        Name::from_string("NNVerify.ibp_tightness_bound_inductive"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let center_ty = c.center_ty(&output_dim);
    let (center_id, center) = b.fresh_local(center_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
    let nonneg_ty = c.base.rat_le(c.base.rat_zero.clone(), eps.clone());
    let (h_nonneg_id, h_nonneg) = b.fresh_local(nonneg_ty.clone());

    let body = Expr::apps(
        helper,
        [
            k.clone(),
            output_dim.clone(),
            weight,
            bias,
            center,
            eps,
            h_nonneg,
        ],
    );

    let e = b.mk_lam(h_nonneg_id, BinderInfo::Default, nonneg_ty, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.base.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, center_ty, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_lam(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}
