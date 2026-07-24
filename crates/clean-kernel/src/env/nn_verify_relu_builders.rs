// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof term builders for T81 (IBP ReLU soundness).
//!
//! Each `build_*` function returns `(type, value)` pairs or raw `Expr` values
//! that the registration methods in `nn_verify_relu` wrap in `Declaration`s.
//!
//! ## Proof Architecture
//!
//! - `relu_nonneg`: `Or.rec` on `Rat.le_total(0, x)` + `Eq.subst` transport
//! - `relu_monotone`: nested `Or.rec` (3-case split) + `Eq.subst` transport
//! - `ibp_relu_bounds`: element-wise relu Definition using `relu_monotone`
//! - `ibp_relu_soundness` (T81): per-coordinate `relu_monotone` (mirrors T70)
//!
//! Part of #3220, #3254.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_relu_proofs::T81Consts;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build relu_nonneg proof: `forall x, 0 <= relu(x)`.
pub(super) fn build_relu_nonneg_proof(c: &T81Consts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.rat.clone());
        let body = c.le(c.rat_zero.clone(), c.relu_app(x));
        let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), body);
        b.finish(e)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.rat.clone());
        let relu_x = c.relu_app(x.clone());
        let goal = c.le(c.rat_zero.clone(), relu_x.clone());
        let a_prop = c.le(c.rat_zero.clone(), x.clone());
        let b_prop = c.le(x.clone(), c.rat_zero.clone());
        let motive = c.const_motive(&b, &a_prop, &b_prop, &goal);
        let major = c.le_total_app(c.rat_zero.clone(), x.clone());
        let case_inl = build_nonneg_case_inl(c, &b, &x, &relu_x, &a_prop);
        let case_inr = build_nonneg_case_inr(c, &b, &x, &relu_x, &b_prop);
        let body = c.or_rec_app(a_prop, b_prop, motive, case_inl, case_inr, major);
        let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        b.finish(e)
    };
    (ty, value)
}

fn build_nonneg_case_inl(
    c: &T81Consts,
    b: &EnvDeclBuilder,
    x: &Expr,
    relu_x: &Expr,
    a_prop: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (h_id, h) = ch.fresh_local(a_prop.clone());
    let eq_proof = Expr::app(Expr::app(c.relu_of_nonneg_c.clone(), x.clone()), h.clone());
    let sym = c.symm(relu_x.clone(), x.clone(), eq_proof);
    let motive_fn = build_le_zero_motive(c, &ch);
    let result = c.subst(motive_fn, x.clone(), relu_x.clone(), sym, h);
    let r = ch.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), result);
    ch.finish_child(r)
}

fn build_nonneg_case_inr(
    c: &T81Consts,
    b: &EnvDeclBuilder,
    x: &Expr,
    relu_x: &Expr,
    b_prop: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (h_id, h) = ch.fresh_local(b_prop.clone());
    let eq_proof = Expr::app(Expr::app(c.relu_of_nonpos_c.clone(), x.clone()), h);
    let sym = c.symm(relu_x.clone(), c.rat_zero.clone(), eq_proof);
    let motive_fn = build_le_zero_motive(c, &ch);
    let le_refl_0 = c.le_refl_app(c.rat_zero.clone());
    let result = c.subst(
        motive_fn,
        c.rat_zero.clone(),
        relu_x.clone(),
        sym,
        le_refl_0,
    );
    let r = ch.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), result);
    ch.finish_child(r)
}

/// Motive: `fun z => 0 <= z`
fn build_le_zero_motive(c: &T81Consts, outer: &EnvDeclBuilder) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (z_id, z) = ch.fresh_local(c.rat.clone());
    let body = c.le(c.rat_zero.clone(), z);
    let r = ch.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body);
    ch.finish_child(r)
}

/// Build relu_monotone proof: `forall x y, x <= y -> relu x <= relu y`.
pub(super) fn build_relu_monotone_proof(c: &T81Consts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.rat.clone());
        let (y_id, y) = b.fresh_local(c.rat.clone());
        let le_xy = c.le(x.clone(), y.clone());
        let (h_id, _) = b.fresh_local(le_xy.clone());
        let le_relu = c.le(c.relu_app(x), c.relu_app(y));
        let e = b.mk_pi(h_id, BinderInfo::Default, le_xy, le_relu);
        let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c.rat.clone());
        let (y_id, y) = b.fresh_local(c.rat.clone());
        let le_xy = c.le(x.clone(), y.clone());
        let (hxy_id, h_xy) = b.fresh_local(le_xy.clone());
        let relu_x = c.relu_app(x.clone());
        let relu_y = c.relu_app(y.clone());
        let goal = c.le(relu_x.clone(), relu_y.clone());
        let a1 = c.le(c.rat_zero.clone(), x.clone());
        let b1 = c.le(x.clone(), c.rat_zero.clone());
        let motive1 = c.const_motive(&b, &a1, &b1, &goal);
        let major1 = c.le_total_app(c.rat_zero.clone(), x.clone());
        let case1 = build_monotone_case1(c, &b, &x, &y, &h_xy, &relu_x, &relu_y, &a1);
        let case2_3 = build_monotone_case2_3(c, &b, &x, &y, &h_xy, &relu_x, &relu_y, &b1, &goal);
        let body = c.or_rec_app(a1, b1, motive1, case1, case2_3, major1);
        let e = b.mk_lam(hxy_id, BinderInfo::Default, le_xy, body);
        let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };
    (ty, value)
}

/// Case 1: 0 <= x (both nonneg)
fn build_monotone_case1(
    c: &T81Consts,
    b: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    h_xy: &Expr,
    relu_x: &Expr,
    relu_y: &Expr,
    a1: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (h0x_id, h_0_le_x) = ch.fresh_local(a1.clone());
    let h_0_le_y = c.le_trans_app(
        c.rat_zero.clone(),
        x.clone(),
        y.clone(),
        h_0_le_x.clone(),
        h_xy.clone(),
    );
    let eq_x = Expr::app(Expr::app(c.relu_of_nonneg_c.clone(), x.clone()), h_0_le_x);
    let eq_y = Expr::app(Expr::app(c.relu_of_nonneg_c.clone(), y.clone()), h_0_le_y);
    let result = c.transport_le(&ch, relu_x, relu_y, x, y, eq_x, eq_y, h_xy.clone());
    let r = ch.mk_lam(h0x_id, BinderInfo::Default, a1.clone(), result);
    ch.finish_child(r)
}

/// Case 2+3: x <= 0, inner split on le_total(y, 0)
fn build_monotone_case2_3(
    c: &T81Consts,
    b: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    _h_xy: &Expr,
    relu_x: &Expr,
    relu_y: &Expr,
    b1: &Expr,
    goal: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (hx0_id, h_x_le_0) = ch.fresh_local(b1.clone());
    let a2 = c.le(y.clone(), c.rat_zero.clone());
    let b2 = c.le(c.rat_zero.clone(), y.clone());
    let motive2 = c.const_motive(&ch, &a2, &b2, goal);
    let major2 = c.le_total_app(y.clone(), c.rat_zero.clone());
    let case2 = build_monotone_case2(c, &ch, x, y, &h_x_le_0, relu_x, relu_y, &a2);
    let case3 = build_monotone_case3(c, &ch, x, y, &h_x_le_0, relu_x, relu_y, &b2);
    let inner = c.or_rec_app(a2, b2, motive2, case2, case3, major2);
    let r = ch.mk_lam(hx0_id, BinderInfo::Default, b1.clone(), inner);
    ch.finish_child(r)
}

/// Case 2: x <= 0 AND y <= 0 (both nonpos)
fn build_monotone_case2(
    c: &T81Consts,
    ch: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    h_x_le_0: &Expr,
    relu_x: &Expr,
    relu_y: &Expr,
    a2: &Expr,
) -> Expr {
    let mut ch2 = EnvDeclBuilder::child_of(ch);
    let (hy0_id, h_y_le_0) = ch2.fresh_local(a2.clone());
    let eq_x = Expr::app(
        Expr::app(c.relu_of_nonpos_c.clone(), x.clone()),
        h_x_le_0.clone(),
    );
    let eq_y = Expr::app(Expr::app(c.relu_of_nonpos_c.clone(), y.clone()), h_y_le_0);
    let le_refl_0 = c.le_refl_app(c.rat_zero.clone());
    let result = c.transport_le(
        &ch2,
        relu_x,
        relu_y,
        &c.rat_zero,
        &c.rat_zero,
        eq_x,
        eq_y,
        le_refl_0,
    );
    let r = ch2.mk_lam(hy0_id, BinderInfo::Default, a2.clone(), result);
    ch2.finish_child(r)
}

/// Case 3: x <= 0 AND 0 <= y (mixed)
fn build_monotone_case3(
    c: &T81Consts,
    ch: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    h_x_le_0: &Expr,
    relu_x: &Expr,
    relu_y: &Expr,
    b2: &Expr,
) -> Expr {
    let mut ch2 = EnvDeclBuilder::child_of(ch);
    let (h0y_id, h_0_le_y) = ch2.fresh_local(b2.clone());
    let eq_x = Expr::app(
        Expr::app(c.relu_of_nonpos_c.clone(), x.clone()),
        h_x_le_0.clone(),
    );
    let eq_y = Expr::app(
        Expr::app(c.relu_of_nonneg_c.clone(), y.clone()),
        h_0_le_y.clone(),
    );
    let result = c.transport_le(&ch2, relu_x, relu_y, &c.rat_zero, y, eq_x, eq_y, h_0_le_y);
    let r = ch2.mk_lam(h0y_id, BinderInfo::Default, b2.clone(), result);
    ch2.finish_child(r)
}

/// Build ibp_relu_bounds definition value.
pub(super) fn build_ibp_relu_bounds_value(c: &T81Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = Expr::app(c.ib.clone(), d.clone());
    let (bv_id, bv) = b.fresh_local(ib_d.clone());
    let b_lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bv.clone());
    let b_upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bv.clone());
    let b_valid = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 2, bv);
    let fin_d = Expr::app(c.fin.clone(), d.clone());
    let lower_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let body = c.relu_app(Expr::app(b_lower.clone(), i));
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };
    let upper_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let body = c.relu_app(Expr::app(b_upper.clone(), i));
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };
    let valid_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let lo_i = Expr::app(b_lower, i.clone());
        let hi_i = Expr::app(b_upper, i.clone());
        let v_i = Expr::app(b_valid, i);
        let body = Expr::app(
            Expr::app(Expr::app(c.relu_monotone_c.clone(), lo_i), hi_i),
            v_i,
        );
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, body);
        ch.finish_child(r)
    };
    let body = Expr::app(
        Expr::app(Expr::app(Expr::app(c.ib_mk.clone(), d), lower_fn), upper_fn),
        valid_fn,
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, ib_d, body);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build T81 soundness proof value.
pub(super) fn build_t81_proof(c: &T81Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = Expr::app(c.ib.clone(), d.clone());
    let nn_vec_d = Expr::app(c.nn_vec.clone(), d.clone());
    let (bv_id, bv) = b.fresh_local(ib_d.clone());
    let (x_id, x) = b.fresh_local(nn_vec_d.clone());
    let contains_b_x = Expr::app(
        Expr::app(Expr::app(c.contains.clone(), d.clone()), bv.clone()),
        x.clone(),
    );
    let (h_id, h) = b.fresh_local(contains_b_x.clone());
    let b_lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bv.clone());
    let b_upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bv);
    let fin_d = Expr::app(c.fin.clone(), d.clone());
    let inner = build_t81_per_index(c, &b, &fin_d, &x, &h, &b_lower, &b_upper);
    let e = b.mk_lam(h_id, BinderInfo::Default, contains_b_x, inner);
    let e = b.mk_lam(x_id, BinderInfo::Default, nn_vec_d, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn build_t81_per_index(
    c: &T81Consts,
    b: &EnvDeclBuilder,
    fin_d: &Expr,
    x: &Expr,
    h: &Expr,
    b_lower: &Expr,
    b_upper: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (i_id, i) = ch.fresh_local(fin_d.clone());
    let lo_i = Expr::app(b_lower.clone(), i.clone());
    let hi_i = Expr::app(b_upper.clone(), i.clone());
    let x_i = Expr::app(x.clone(), i.clone());
    let h_i = Expr::app(h.clone(), i.clone());
    let lo_le_xi = c.le(lo_i.clone(), x_i.clone());
    let xi_le_hi = c.le(x_i.clone(), hi_i.clone());
    let h_lo = c.and_left_app(lo_le_xi.clone(), xi_le_hi.clone(), h_i.clone());
    let h_hi = c.and_right_app(lo_le_xi, xi_le_hi, h_i);
    let mono_lo = Expr::app(
        Expr::app(Expr::app(c.relu_monotone_c.clone(), lo_i), x_i.clone()),
        h_lo,
    );
    let mono_hi = Expr::app(
        Expr::app(Expr::app(c.relu_monotone_c.clone(), x_i), hi_i),
        h_hi,
    );
    let relu_lo_i = c.relu_app(Expr::app(b_lower.clone(), i.clone()));
    let relu_x_i = c.relu_app(Expr::app(x.clone(), i.clone()));
    let relu_hi_i = c.relu_app(Expr::app(b_upper.clone(), i));
    let goal_left = c.le(relu_lo_i, relu_x_i.clone());
    let goal_right = c.le(relu_x_i, relu_hi_i);
    let proof = c.and_intro_app(goal_left, goal_right, mono_lo, mono_hi);
    let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), proof);
    ch.finish_child(r)
}
