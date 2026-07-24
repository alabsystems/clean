// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B1 order toolkit — proof-term builders.
//!
//! Split from `boolean_analysis_order_toolkit.rs` to keep each file under the
//! 500-line limit (mirrors the `nn_verify_rat_ordering` /
//! `nn_verify_rat_ordering_proofs` split). The registration entry points and
//! the `OrderConsts` plumbing live in the parent module; this file holds the
//! pure proof-term construction the registrars consume.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Proof-term builders
// ---------------------------------------------------------------------------

/// Build the proof term for `Rat.neg_neg`.
pub(super) fn build_neg_neg_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());

    let neg_a = c.neg(a.clone());
    let neg_neg_a = c.neg(neg_a.clone());

    let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
    let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
    let add_right_cancel = Expr::const_(Name::from_string("Rat.add_right_cancel"), vec![]);

    // h1 : (-a) + (-(-a)) = 0   [add_neg_self (-a)]
    let h1 = Expr::app(add_neg_self.clone(), neg_a.clone());
    // h_comm : (-a) + (-(-a)) = (-(-a)) + (-a)   [add_comm (-a) (-(-a))]
    let h_comm = Expr::apps(add_comm, [neg_a.clone(), neg_neg_a.clone()]);
    // h2 : (-(-a)) + (-a) = 0   [symm h_comm ∘ h1]
    let lhs1 = c.add(neg_a.clone(), neg_neg_a.clone()); // (-a)+(-(-a))
    let rhs1 = c.add(neg_neg_a.clone(), neg_a.clone()); // (-(-a))+(-a)
    let h_comm_symm = c.symm(lhs1.clone(), rhs1.clone(), h_comm);
    let h2 = c.trans(
        rhs1.clone(),
        lhs1.clone(),
        c.rat_zero.clone(),
        h_comm_symm,
        h1,
    );
    // h3 : a + (-a) = 0   [add_neg_self a]
    let h3 = Expr::app(add_neg_self, a.clone());
    // h4 : (-(-a)) + (-a) = a + (-a)   [trans h2 (symm h3)]
    let a_plus_nega = c.add(a.clone(), neg_a.clone());
    let h3_symm = c.symm(a_plus_nega.clone(), c.rat_zero.clone(), h3);
    let h4 = c.trans(
        rhs1.clone(),
        c.rat_zero.clone(),
        a_plus_nega.clone(),
        h2,
        h3_symm,
    );
    // Rat.add_right_cancel (-(-a)) (-a) a h4 : -(-a) = a
    let body = Expr::apps(add_right_cancel, [neg_neg_a, neg_a, a.clone(), h4]);

    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), body);
    b.finish(e)
}

/// Build the proof term for `Rat.neg_mul_neg`.
pub(super) fn build_neg_mul_neg_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());

    let mul_neg = Expr::const_(Name::from_string("Rat.mul_neg"), vec![]);
    let mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);
    let neg_neg = Expr::const_(Name::from_string("Rat.neg_neg"), vec![]);

    // Goal: (-a)·(-b) = a·b.
    //
    // step_outer : (-a)·(-b) = -((-a)·b)   [mul_neg (-a) b]
    let lhs = c.mul(neg_a.clone(), neg_b.clone());
    let nega_b = c.mul(neg_a.clone(), bv.clone()); // (-a)·b
    let neg_nega_b = c.neg(nega_b.clone());
    let step_outer = Expr::apps(mul_neg.clone(), [neg_a.clone(), bv.clone()]);

    // inner : (-a)·b = -(a·b)
    //   (-a)·b = b·(-a)     [mul_comm (-a) b]
    //   b·(-a) = -(b·a)     [mul_neg b a]
    //   b·a    = a·b        [mul_comm b a]  ⇒ -(b·a) = -(a·b) via congrArg neg
    let b_nega = c.mul(bv.clone(), neg_a.clone()); // b·(-a)
    let ba = c.mul(bv.clone(), a.clone()); // b·a
    let ab = c.mul(a.clone(), bv.clone()); // a·b
    let neg_ba = c.neg(ba.clone());
    let neg_ab = c.neg(ab.clone());

    // i1 : (-a)·b = b·(-a)
    let i1 = Expr::apps(mul_comm.clone(), [neg_a.clone(), bv.clone()]);
    // i2 : b·(-a) = -(b·a)
    let i2 = Expr::apps(mul_neg.clone(), [bv.clone(), a.clone()]);
    // i_left : (-a)·b = -(b·a)   [trans i1 i2]
    let i_left = c.trans(nega_b.clone(), b_nega.clone(), neg_ba.clone(), i1, i2);
    // h_ba_ab : b·a = a·b   [mul_comm b a]
    let h_ba_ab = Expr::apps(mul_comm.clone(), [bv.clone(), a.clone()]);
    // congr_neg : -(b·a) = -(a·b)   [congrArg Rat.neg h_ba_ab]
    let congr_neg = congr_arg_neg(c, ba.clone(), ab.clone(), h_ba_ab);
    // inner : (-a)·b = -(a·b)   [trans i_left congr_neg]
    let inner = c.trans(
        nega_b.clone(),
        neg_ba.clone(),
        neg_ab.clone(),
        i_left,
        congr_neg,
    );

    // congr_outer : -((-a)·b) = -(-(a·b))   [congrArg Rat.neg inner]
    let neg_neg_ab = c.neg(neg_ab.clone());
    let congr_outer = congr_arg_neg(c, nega_b.clone(), neg_ab.clone(), inner);
    // dn : -(-(a·b)) = a·b   [neg_neg (a·b)]
    let dn = Expr::app(neg_neg, ab.clone());
    // right : -((-a)·b) = a·b   [trans congr_outer dn]
    let right = c.trans(
        neg_nega_b.clone(),
        neg_neg_ab.clone(),
        ab.clone(),
        congr_outer,
        dn,
    );

    // body : (-a)·(-b) = a·b   [trans step_outer right]
    let body = c.trans(
        lhs.clone(),
        neg_nega_b.clone(),
        ab.clone(),
        step_outer,
        right,
    );

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `congrArg.{1,1} @Rat @Rat Rat.neg @x @y h : Rat.neg x = Rat.neg y`.
fn congr_arg_neg(c: &OrderConsts, x: Expr, y: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]);
    Expr::apps(
        congr_arg,
        [c.rat.clone(), c.rat.clone(), x, y, c.rat_neg.clone(), h],
    )
}

/// Type of `Rat.mul_le_mul_of_nonneg_left`:
/// `∀ a b c, Rat.le b c → Rat.le 0 a → Rat.le (a·b) (a·c)`.
pub(super) fn mul_le_mul_left_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_bc_ty = c.rat_le(bv.clone(), cv.clone());
    let h_a_ty = c.rat_le(c.rat_zero.clone(), a.clone());
    let concl = c.rat_le(c.mul(a.clone(), bv.clone()), c.mul(a.clone(), cv.clone()));
    let (ha_id, _) = b.fresh_local(h_a_ty.clone());
    let (hbc_id, _) = b.fresh_local(h_bc_ty.clone());
    let e = b.mk_pi(ha_id, BinderInfo::Default, h_a_ty, concl);
    let e = b.mk_pi(hbc_id, BinderInfo::Default, h_bc_ty, e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Type of `Rat.mul_le_mul_of_nonneg_right`:
/// `∀ a b c, Rat.le b c → Rat.le 0 a → Rat.le (b·a) (c·a)`.
pub(super) fn mul_le_mul_right_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_bc_ty = c.rat_le(bv.clone(), cv.clone());
    let h_a_ty = c.rat_le(c.rat_zero.clone(), a.clone());
    let concl = c.rat_le(c.mul(bv.clone(), a.clone()), c.mul(cv.clone(), a.clone()));
    let (ha_id, _) = b.fresh_local(h_a_ty.clone());
    let (hbc_id, _) = b.fresh_local(h_bc_ty.clone());
    let e = b.mk_pi(ha_id, BinderInfo::Default, h_a_ty, concl);
    let e = b.mk_pi(hbc_id, BinderInfo::Default, h_bc_ty, e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.mul_le_mul_of_nonneg_left`.
pub(super) fn build_mul_le_mul_of_nonneg_left_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_bc_ty = c.rat_le(bv.clone(), cv.clone());
    let h_a_ty = c.rat_le(c.rat_zero.clone(), a.clone());
    let (hbc_id, h_bc) = b.fresh_local(h_bc_ty.clone());
    let (ha_id, h_a) = b.fresh_local(h_a_ty.clone());

    let c_sub_b = c.sub(cv.clone(), bv.clone());
    let a_csb = c.mul(a.clone(), c_sub_b.clone());
    let ac = c.mul(a.clone(), cv.clone());
    let ab = c.mul(a.clone(), bv.clone());
    let ac_sub_ab = c.sub(ac.clone(), ab.clone());

    // 1. h_cb_nn : 0 ≤ c - b   [sub_nonneg_of_le b c h_bc]
    let sub_nonneg_of_le = Expr::const_(Name::from_string("Rat.sub_nonneg_of_le"), vec![]);
    let h_cb_nn = Expr::apps(sub_nonneg_of_le, [bv.clone(), cv.clone(), h_bc]);
    // 2. h_prod_nn : 0 ≤ a·(c-b)   [mul_nonneg a (c-b) h_a h_cb_nn]
    let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
    let h_prod_nn = Expr::apps(mul_nonneg, [a.clone(), c_sub_b.clone(), h_a, h_cb_nn]);
    // 3. h_dist : a·(c-b) = a·c - a·b   [mul_sub a c b]
    let mul_sub = Expr::const_(Name::from_string("Rat.mul_sub"), vec![]);
    let h_dist = Expr::apps(mul_sub, [a.clone(), cv.clone(), bv.clone()]);
    // 4. motive : fun x => Rat.le 0 x ; subst transports h_prod_nn along h_dist
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(c.rat_zero.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let h_acab_nn = c.subst(motive, a_csb, ac_sub_ab, h_dist, h_prod_nn);
    // 5. le_of_sub_nonneg (a·b)(a·c) h_acab_nn : a·b ≤ a·c
    let le_of_sub_nonneg = Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]);
    let body = Expr::apps(le_of_sub_nonneg, [ab, ac, h_acab_nn]);

    let e = b.mk_lam(ha_id, BinderInfo::Default, h_a_ty, body);
    let e = b.mk_lam(hbc_id, BinderInfo::Default, h_bc_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.mul_le_mul_of_nonneg_right`.
///
/// Reuses `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_a : a·b ≤ a·c`, then
/// rewrites both endpoints via `Rat.mul_comm` (`a·b = b·a`, `a·c = c·a`).
pub(super) fn build_mul_le_mul_of_nonneg_right_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_bc_ty = c.rat_le(bv.clone(), cv.clone());
    let h_a_ty = c.rat_le(c.rat_zero.clone(), a.clone());
    let (hbc_id, h_bc) = b.fresh_local(h_bc_ty.clone());
    let (ha_id, h_a) = b.fresh_local(h_a_ty.clone());

    let ab = c.mul(a.clone(), bv.clone());
    let ac = c.mul(a.clone(), cv.clone());
    let ba = c.mul(bv.clone(), a.clone());
    let ca = c.mul(cv.clone(), a.clone());

    // base : a·b ≤ a·c
    let left = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]);
    let base = Expr::apps(left, [a.clone(), bv.clone(), cv.clone(), h_bc, h_a]);

    let mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);
    // h_ab : a·b = b·a ; h_ac : a·c = c·a
    let h_ab = Expr::apps(mul_comm.clone(), [a.clone(), bv.clone()]);
    let h_ac = Expr::apps(mul_comm, [a.clone(), cv.clone()]);

    // step1 : b·a ≤ a·c   [subst (fun x => x ≤ a·c) along h_ab]
    let motive1 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(x, ac.clone());
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let step1 = c.subst(motive1, ab.clone(), ba.clone(), h_ab, base);
    // step2 : b·a ≤ c·a   [subst (fun x => b·a ≤ x) along h_ac]
    let motive2 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(ba.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let body = c.subst(motive2, ac.clone(), ca.clone(), h_ac, step1);

    let e = b.mk_lam(ha_id, BinderInfo::Default, h_a_ty, body);
    let e = b.mk_lam(hbc_id, BinderInfo::Default, h_bc_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.sq_nonneg`.
pub(super) fn build_sq_nonneg_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());

    let aa = c.mul(a.clone(), a.clone());
    let goal = c.rat_le(c.rat_zero.clone(), aa.clone());

    // le_total 0 a : Or (0 ≤ a) (a ≤ 0)
    let le_total = Expr::const_(Name::from_string("Rat.le_total"), vec![]);
    let h_total = Expr::apps(le_total, [c.rat_zero.clone(), a.clone()]);

    let le_0a = c.rat_le(c.rat_zero.clone(), a.clone());
    let le_a0 = c.rat_le(a.clone(), c.rat_zero.clone());

    // Branch 1: 0 ≤ a  ⇒  mul_nonneg a a h h : 0 ≤ a·a
    let branch_pos = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h_id, h) = ch.fresh_local(le_0a.clone());
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        let body = Expr::apps(mul_nonneg, [a.clone(), a.clone(), h.clone(), h]);
        let lam = ch.mk_lam(h_id, BinderInfo::Default, le_0a.clone(), body);
        ch.finish_child(lam)
    };

    // Branch 2: a ≤ 0  ⇒  0 ≤ a·a
    let branch_neg = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h_id, h) = ch.fresh_local(le_a0.clone());
        let neg_a = c.neg(a.clone());

        // h_sub : 0 ≤ 0 - a   [sub_nonneg_of_le a 0 h]
        let sub_nonneg_of_le = Expr::const_(Name::from_string("Rat.sub_nonneg_of_le"), vec![]);
        let h_sub = Expr::apps(sub_nonneg_of_le, [a.clone(), c.rat_zero.clone(), h]);
        // 0 - a is definitionally 0 + (-a); zero_add (-a) : 0 + (-a) = -a.
        // We transport h_sub : 0 ≤ (0 - a) to 0 ≤ (-a). Since `Rat.sub 0 a`
        // delta-reduces to `Rat.add 0 (-a)`, subst along zero_add is valid.
        let zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
        let h_za = Expr::app(zero_add, neg_a.clone()); // 0 + (-a) = -a
        let zero_sub_a = c.sub(c.rat_zero.clone(), a.clone()); // 0 - a
        let motive_nega = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(c.rat_zero.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        // h_nega_nn : 0 ≤ -a
        let h_nega_nn = c.subst(motive_nega, zero_sub_a, neg_a.clone(), h_za, h_sub);

        // h_prod : 0 ≤ (-a)·(-a)   [mul_nonneg (-a) (-a) h_nega_nn h_nega_nn]
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        let h_prod = Expr::apps(
            mul_nonneg,
            [neg_a.clone(), neg_a.clone(), h_nega_nn.clone(), h_nega_nn],
        );
        // h_eq : (-a)·(-a) = a·a   [neg_mul_neg a a]
        let neg_mul_neg = Expr::const_(Name::from_string("Rat.neg_mul_neg"), vec![]);
        let h_eq = Expr::apps(neg_mul_neg, [a.clone(), a.clone()]);
        let nega_nega = c.mul(neg_a.clone(), neg_a.clone());
        // motive2 : fun x => 0 ≤ x ; subst h_prod along h_eq → 0 ≤ a·a
        let motive2 = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(c.rat_zero.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let body = c.subst(motive2, nega_nega, aa.clone(), h_eq, h_prod);
        let lam = ch.mk_lam(h_id, BinderInfo::Default, le_a0.clone(), body);
        ch.finish_child(lam)
    };

    // Or.elim h_total branch_pos branch_neg : goal
    let body = or_elim(&b, le_0a, le_a0, goal, h_total, branch_pos, branch_neg);

    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), body);
    b.finish(e)
}

/// Case-split on `h_or : Or p q` into a (non-dependent) `goal`, via
/// `@Or.rec p q motive h_left h_right h_or` where `motive := fun _ => goal`.
///
/// The codebase eliminates `Or` of Props into a Prop goal through `Or.rec`
/// (carrying no level params); `Or.elim` is not registered. `h_left` /
/// `h_right` must be functions `p → goal` / `q → goal`. `parent` is the
/// builder whose fvar scope `goal`/`h_*` live in (so the motive binder is
/// allocated as a child of it).
fn or_elim(
    parent: &EnvDeclBuilder,
    p: Expr,
    q: Expr,
    goal: Expr,
    h_or: Expr,
    h_left: Expr,
    h_right: Expr,
) -> Expr {
    let or_c = Expr::const_(Name::from_string("Or"), vec![]);
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    // motive := fun (_ : Or p q) => goal
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let or_ty = Expr::apps(or_c, [p.clone(), q.clone()]);
        let (h_id, _) = m.fresh_local(or_ty.clone());
        let lam = m.mk_lam(h_id, BinderInfo::Default, or_ty, goal);
        m.finish_child(lam)
    };
    Expr::apps(or_rec, [p, q, motive, h_left, h_right, h_or])
}

/// Type of `Rat.sq_le_one_of_abs_le_one`:
/// `∀ a, Rat.le (-1) a → Rat.le a 1 → Rat.le (a·a) 1`.
pub(super) fn sq_le_one_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let neg_one = c.neg(c.rat_one.clone());
    let h_lo_ty = c.rat_le(neg_one, a.clone());
    let h_hi_ty = c.rat_le(a.clone(), c.rat_one.clone());
    let concl = c.rat_le(c.mul(a.clone(), a.clone()), c.rat_one.clone());
    let (hhi_id, _) = b.fresh_local(h_hi_ty.clone());
    let (hlo_id, _) = b.fresh_local(h_lo_ty.clone());
    let e = b.mk_pi(hhi_id, BinderInfo::Default, h_hi_ty, concl);
    let e = b.mk_pi(hlo_id, BinderInfo::Default, h_lo_ty, e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.sq_le_one_of_abs_le_one`.
pub(super) fn build_sq_le_one_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let neg_one = c.neg(c.rat_one.clone());
    let h_lo_ty = c.rat_le(neg_one.clone(), a.clone());
    let h_hi_ty = c.rat_le(a.clone(), c.rat_one.clone());
    let (hlo_id, h_lo) = b.fresh_local(h_lo_ty.clone());
    let (hhi_id, h_hi) = b.fresh_local(h_hi_ty.clone());

    let aa = c.mul(a.clone(), a.clone());
    let goal = c.rat_le(aa.clone(), c.rat_one.clone());

    let le_total = Expr::const_(Name::from_string("Rat.le_total"), vec![]);
    let h_total = Expr::apps(le_total, [c.rat_zero.clone(), a.clone()]);
    let le_0a = c.rat_le(c.rat_zero.clone(), a.clone());
    let le_a0 = c.rat_le(a.clone(), c.rat_zero.clone());

    let mul_le_right = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]);
    let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
    let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);

    // Branch 1: 0 ≤ a.
    //   mul_le_mul_of_nonneg_right a a 1 h_hi h0 : a·a ≤ 1·a
    //   one_mul a : 1·a = a ; subst → a·a ≤ a ; le_trans with h_hi : a·a ≤ 1
    let branch_pos = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h0_id, h0) = ch.fresh_local(le_0a.clone());
        // base : a·a ≤ 1·a
        let base = Expr::apps(
            mul_le_right.clone(),
            [a.clone(), a.clone(), c.rat_one.clone(), h_hi.clone(), h0],
        );
        let one_a = c.mul(c.rat_one.clone(), a.clone());
        // h_om : 1·a = a
        let h_om = Expr::app(one_mul.clone(), a.clone());
        // motive : fun x => a·a ≤ x ; subst base along h_om → a·a ≤ a
        let motive = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(aa.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let h_aa_le_a = c.subst(motive, one_a, a.clone(), h_om, base);
        // le_trans (a·a) a 1 h_aa_le_a h_hi : a·a ≤ 1
        let body = Expr::apps(
            le_trans.clone(),
            [
                aa.clone(),
                a.clone(),
                c.rat_one.clone(),
                h_aa_le_a,
                h_hi.clone(),
            ],
        );
        let lam = ch.mk_lam(h0_id, BinderInfo::Default, le_0a.clone(), body);
        ch.finish_child(lam)
    };

    // Branch 2: a ≤ 0.
    //   Let n = -a. From h_lo : -1 ≤ a, neg_le_neg gives -a ≤ -(-1) = 1
    //   (after neg_neg on 1). From a ≤ 0, sub_nonneg gives 0 ≤ -a.
    //   mul_le_mul_of_nonneg_right n n 1 h_n_le1 h_n_nn : n·n ≤ 1·n
    //   neg_mul_neg a a : n·n = a·a ; one_mul n : 1·n = n
    //   ⇒ a·a ≤ n = -a ; and -a ≤ 1 (h_n_le1); le_trans ⇒ a·a ≤ 1.
    let branch_neg = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h0_id, h_a0) = ch.fresh_local(le_a0.clone());
        let n = c.neg(a.clone()); // -a

        // h_n_nn : 0 ≤ -a   [sub_nonneg_of_le a 0 h_a0 then zero_add]
        let sub_nonneg_of_le = Expr::const_(Name::from_string("Rat.sub_nonneg_of_le"), vec![]);
        let h_sub = Expr::apps(sub_nonneg_of_le, [a.clone(), c.rat_zero.clone(), h_a0]);
        let zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
        let h_za = Expr::app(zero_add, n.clone());
        let zero_sub_a = c.sub(c.rat_zero.clone(), a.clone());
        let motive_nn = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(c.rat_zero.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let h_n_nn = c.subst(motive_nn, zero_sub_a, n.clone(), h_za, h_sub);

        // h_n_le1 : -a ≤ 1.
        //   neg_le_neg (-1) a h_lo : -a ≤ -(-1)   [neg_le_neg flips -1 ≤ a]
        //   neg_neg 1 : -(-1) = 1 ; subst → -a ≤ 1
        let neg_le_neg = Expr::const_(Name::from_string("Rat.neg_le_neg"), vec![]);
        // neg_le_neg : ∀ a b, a ≤ b → -b ≤ -a  (so a:=-1, b:=a → -a ≤ -(-1))
        let h_nln = Expr::apps(neg_le_neg, [neg_one.clone(), a.clone(), h_lo]);
        let neg_neg = Expr::const_(Name::from_string("Rat.neg_neg"), vec![]);
        let h_nn1 = Expr::app(neg_neg, c.rat_one.clone()); // -(-1) = 1
        let neg_neg_one = c.neg(neg_one.clone()); // -(-1)
        let motive_le1 = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(n.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let h_n_le1 = c.subst(motive_le1, neg_neg_one, c.rat_one.clone(), h_nn1, h_nln);

        // base : n·n ≤ 1·n   [mul_le_mul_of_nonneg_right n n 1 h_n_le1 h_n_nn]
        let base = Expr::apps(
            mul_le_right.clone(),
            [
                n.clone(),
                n.clone(),
                c.rat_one.clone(),
                h_n_le1.clone(),
                h_n_nn,
            ],
        );
        // rewrite LHS n·n → a·a via neg_mul_neg a a
        let nn = c.mul(n.clone(), n.clone());
        let neg_mul_neg = Expr::const_(Name::from_string("Rat.neg_mul_neg"), vec![]);
        let h_nn_eq = Expr::apps(neg_mul_neg, [a.clone(), a.clone()]); // n·n = a·a
        let one_n = c.mul(c.rat_one.clone(), n.clone());
        let motive_lhs = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(x, one_n.clone());
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let step1 = c.subst(motive_lhs, nn, aa.clone(), h_nn_eq, base); // a·a ≤ 1·n
                                                                        // rewrite RHS 1·n → n via one_mul n
        let h_omn = Expr::app(one_mul.clone(), n.clone()); // 1·n = n
        let motive_rhs = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = ch2.fresh_local(c.rat.clone());
            let body = c.rat_le(aa.clone(), x);
            let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
            ch2.finish_child(r)
        };
        let step2 = c.subst(motive_rhs, one_n, n.clone(), h_omn, step1); // a·a ≤ n
                                                                         // le_trans (a·a) n 1 step2 h_n_le1 : a·a ≤ 1
        let body = Expr::apps(
            le_trans.clone(),
            [aa.clone(), n.clone(), c.rat_one.clone(), step2, h_n_le1],
        );
        let lam = ch.mk_lam(h0_id, BinderInfo::Default, le_a0.clone(), body);
        ch.finish_child(lam)
    };

    let body = or_elim(&b, le_0a, le_a0, goal, h_total, branch_pos, branch_neg);

    let e = b.mk_lam(hhi_id, BinderInfo::Default, h_hi_ty, body);
    let e = b.mk_lam(hlo_id, BinderInfo::Default, h_lo_ty, e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
