// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T80 unlock (#3490 follow-up): constructive proof term for
//! `NNVerify.ibp_linear_per_component`.
//!
//! Now that `NNVerify.ibp_linear_bounds` is a faithful reducible
//! `Declaration::Definition` returning `IntervalBounds.mk m lo' hi' valid`, the
//! `IntervalBounds` projections in the per-component statement proj-reduce:
//! ```text
//! (ibp_linear_bounds m n W b B).lower j ≡ Σ_i (w_pos j i · lo i + w_neg j i · hi i) + b j
//! (ibp_linear_bounds m n W b B).upper j ≡ Σ_i (w_neg j i · lo i + w_pos j i · hi i) + b j
//! (linear_output m n W b x) j           ≡ Σ_i (W j i · x i) + b j
//! ```
//! so the goal at output index `j` is the pair
//! ```text
//! lo' j ≤ Σ_i (W j i · x i) + b j   ∧   Σ_i (W j i · x i) + b j ≤ hi' j
//! ```
//! both proved per-summand:
//!   - `w_pos ≥ 0` (`w_pos_nonneg`) + `lo ≤ x` (`And.left (hx i)`) gives
//!     `w_pos·lo ≤ w_pos·x` (`mul_nonneg_le_left`);
//!   - `w_neg ≤ 0` (`w_neg_nonpos`) + `x ≤ hi` (`And.right (hx i)`) gives
//!     `w_neg·hi ≤ w_neg·x` (`mul_nonpos_le_left`);
//!   - `add_le_add` joins them to `(w_pos·lo + w_neg·hi) ≤ (w_pos·x + w_neg·x)`;
//!   - recombination `w_pos·x + w_neg·x = W·x` via `w_decompose`
//!     (`W = w_pos + w_neg`) lifted through `congrArg (· * x)` and closed with
//!     `Rat.right_distrib`;
//!   - `Fin.sum_le` lifts the pointwise inequality to the sums;
//!   - `add_le_add` with `Rat.le_refl (b j)` adds the shared bias.
//!
//! The upper bound is dual (with one `Rat.add_comm` to match the `hi'`
//! summand order). Zero `sorry`; closure is a subset of the W+/W-
//! decomposition Theorems (`w_decompose`, `w_pos_nonneg`, `w_neg_nonpos`),
//! `mul_nonneg_le_left`, `mul_nonpos_le_left`, `add_le_add`, `le_of_eq_of_le`,
//! `le_of_le_of_eq`, `Fin.sum_le`, `Rat.right_distrib`, `Rat.add_comm`,
//! `Rat.le_refl`, `Eq.trans`, `Eq.symm`, `congrArg`, `And.left`, `And.right`,
//! and `And.intro`.

use super::nn_verify_ibp_linear::IbpLinearConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Constants for the `ibp_linear_per_component` proof construction (on top of
/// the shared `IbpLinearConsts`).
struct PerCompConsts {
    w_pos: Expr,
    w_neg: Expr,
    w_pos_nonneg: Expr,
    w_neg_nonpos: Expr,
    w_decompose: Expr,
    mul_nonneg_le_left: Expr,
    mul_nonpos_le_left: Expr,
    add_le_add: Expr,
    le_of_eq_of_le: Expr,
    le_of_le_of_eq: Expr,
    fin_sum_le: Expr,
    right_distrib: Expr,
    add_comm: Expr,
    le_refl: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    ib_contains: Expr,
}

impl PerCompConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            w_pos: Expr::const_(Name::from_string("NNVerify.w_pos"), vec![]),
            w_neg: Expr::const_(Name::from_string("NNVerify.w_neg"), vec![]),
            w_pos_nonneg: Expr::const_(Name::from_string("NNVerify.w_pos_nonneg"), vec![]),
            w_neg_nonpos: Expr::const_(Name::from_string("NNVerify.w_neg_nonpos"), vec![]),
            w_decompose: Expr::const_(Name::from_string("NNVerify.w_decompose"), vec![]),
            mul_nonneg_le_left: Expr::const_(
                Name::from_string("NNVerify.mul_nonneg_le_left"),
                vec![],
            ),
            mul_nonpos_le_left: Expr::const_(
                Name::from_string("NNVerify.mul_nonpos_le_left"),
                vec![],
            ),
            add_le_add: Expr::const_(Name::from_string("NNVerify.add_le_add"), vec![]),
            le_of_eq_of_le: Expr::const_(Name::from_string("NNVerify.le_of_eq_of_le"), vec![]),
            le_of_le_of_eq: Expr::const_(Name::from_string("NNVerify.le_of_le_of_eq"), vec![]),
            fin_sum_le: Expr::const_(Name::from_string("Fin.sum_le"), vec![]),
            right_distrib: Expr::const_(Name::from_string("Rat.right_distrib"), vec![]),
            add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
            le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
        }
    }

    /// `(w_pos m n W) j i : Rat`.
    fn w_pos_entry(&self, m: &Expr, n: &Expr, w: &Expr, j: &Expr, i: &Expr) -> Expr {
        let mat = Expr::apps(self.w_pos.clone(), [m.clone(), n.clone(), w.clone()]);
        Expr::app(Expr::app(mat, j.clone()), i.clone())
    }

    /// `(w_neg m n W) j i : Rat`.
    fn w_neg_entry(&self, m: &Expr, n: &Expr, w: &Expr, j: &Expr, i: &Expr) -> Expr {
        let mat = Expr::apps(self.w_neg.clone(), [m.clone(), n.clone(), w.clone()]);
        Expr::app(Expr::app(mat, j.clone()), i.clone())
    }

    /// `Eq.trans.{1} @Rat @a @b @c h1 h2`.
    fn trans(&self, c: &IbpLinearConsts, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [c.rat.clone(), a, b, d, h1, h2])
    }

    /// `Eq.symm.{1} @Rat @a @b h`.
    fn symm(&self, c: &IbpLinearConsts, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [c.rat.clone(), a, b, h])
    }

    /// `@congrArg.{1,1} Rat Rat a b f h : Eq Rat (f a) (f b)`.
    fn congr(&self, c: &IbpLinearConsts, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [c.rat.clone(), c.rat.clone(), a, b, f, h],
        )
    }
}

/// Build the constructive proof term for `NNVerify.ibp_linear_per_component`:
/// ```text
/// fun (m n : Nat) (W : NNMat m n) (b : NNVec m) (B : IntervalBounds n)
///     (x : NNVec n) (hx : contains B x) (j : Fin m) =>
///   And.intro (lo' j ≤ out j) (out j ≤ hi' j) <lower> <upper>
/// ```
pub(super) fn build_ibp_linear_per_component_proof(c: &IbpLinearConsts) -> Expr {
    let d = PerCompConsts::new();

    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (bias_id, bias) = b.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());

    // hx : contains B x ≡ ∀ i, (B.lower i ≤ x i) ∧ (x i ≤ B.upper i).
    let contains_input = Expr::apps(d.ib_contains.clone(), [n.clone(), bnd.clone(), x.clone()]);
    let (hx_id, hx) = b.fresh_local(contains_input.clone());

    let fin_m = Expr::app(c.fin.clone(), m.clone());
    let fin_n = Expr::app(c.fin.clone(), n.clone());

    // B.lower / B.upper : Fin n -> Rat.
    let proj_lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone());
    let proj_upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd.clone());

    // Per-output index body: And.intro of the two sum-level inequalities.
    let body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = ch.fresh_local(fin_m.clone());

        let bias_j = Expr::app(bias.clone(), j.clone());

        // Summand lambdas (must be β-identical to the define's lo'/hi'/out
        // summands so the proj-reduced goal matches).
        // lo_summand i := w_pos j i * lo i + w_neg j i * hi i.
        let lo_summand = {
            let mut ci = EnvDeclBuilder::child_of(&ch);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let p = d.w_pos_entry(&m, &n, &w, &j, &i);
            let q = d.w_neg_entry(&m, &n, &w, &j, &i);
            let lo_i = Expr::app(proj_lower.clone(), i.clone());
            let hi_i = Expr::app(proj_upper.clone(), i.clone());
            let s = c.add(c.mul(p, lo_i), c.mul(q, hi_i));
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), s))
        };
        // hi_summand i := w_neg j i * lo i + w_pos j i * hi i.
        let hi_summand = {
            let mut ci = EnvDeclBuilder::child_of(&ch);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let p = d.w_pos_entry(&m, &n, &w, &j, &i);
            let q = d.w_neg_entry(&m, &n, &w, &j, &i);
            let lo_i = Expr::app(proj_lower.clone(), i.clone());
            let hi_i = Expr::app(proj_upper.clone(), i.clone());
            let s = c.add(c.mul(q, lo_i), c.mul(p, hi_i));
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), s))
        };
        // out_summand i := W j i * x i.
        let out_summand = {
            let mut ci = EnvDeclBuilder::child_of(&ch);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let w_ji = Expr::app(Expr::app(w.clone(), j.clone()), i.clone());
            let x_i = Expr::app(x.clone(), i.clone());
            let s = c.mul(w_ji, x_i);
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), s))
        };

        let sum_lo = c.sum(n.clone(), lo_summand.clone());
        let sum_hi = c.sum(n.clone(), hi_summand.clone());
        let sum_out = c.sum(n.clone(), out_summand.clone());

        // h_bias : b j ≤ b j  via Rat.le_refl (b j).
        let h_bias = Expr::app(d.le_refl.clone(), bias_j.clone());

        // -------- pointwise lower : ∀ i, lo_summand i ≤ out_summand i ----------
        let pointwise_lo = {
            let mut ci = EnvDeclBuilder::child_of(&ch);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let p = d.w_pos_entry(&m, &n, &w, &j, &i);
            let q = d.w_neg_entry(&m, &n, &w, &j, &i);
            let w_ji = Expr::app(Expr::app(w.clone(), j.clone()), i.clone());
            let lo_i = Expr::app(proj_lower.clone(), i.clone());
            let hi_i = Expr::app(proj_upper.clone(), i.clone());
            let x_i = Expr::app(x.clone(), i.clone());

            // hx i : (lo i ≤ x i) ∧ (x i ≤ hi i).
            let hx_i = Expr::app(hx.clone(), i.clone());
            let le_lo_x = c.rat_le(lo_i.clone(), x_i.clone());
            let le_x_hi = c.rat_le(x_i.clone(), hi_i.clone());
            let h_lo_x = Expr::apps(
                d.and_left.clone(),
                [le_lo_x.clone(), le_x_hi.clone(), hx_i.clone()],
            );
            let h_x_hi = Expr::apps(d.and_right.clone(), [le_lo_x, le_x_hi, hx_i]);

            // h_pos : 0 ≤ w_pos j i ; h_neg : w_neg j i ≤ 0.
            let h_pos = Expr::apps(
                d.w_pos_nonneg.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );
            let h_neg = Expr::apps(
                d.w_neg_nonpos.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );

            // h1 : p*lo ≤ p*x  via mul_nonneg_le_left p lo x h_pos h_lo_x.
            let h1 = Expr::apps(
                d.mul_nonneg_le_left.clone(),
                [p.clone(), lo_i.clone(), x_i.clone(), h_pos, h_lo_x],
            );
            // h2 : q*hi ≤ q*x  via mul_nonpos_le_left q x hi h_neg h_x_hi.
            //   (mul_nonpos_le_left w a b : w≤0 → a≤b → w*b ≤ w*a; a=x, b=hi)
            let h2 = Expr::apps(
                d.mul_nonpos_le_left.clone(),
                [q.clone(), x_i.clone(), hi_i.clone(), h_neg, h_x_hi],
            );

            let p_lo = c.mul(p.clone(), lo_i.clone());
            let p_x = c.mul(p.clone(), x_i.clone());
            let q_hi = c.mul(q.clone(), hi_i.clone());
            let q_x = c.mul(q.clone(), x_i.clone());

            // h12 : (p*lo + q*hi) ≤ (p*x + q*x)  via add_le_add.
            let h12 = Expr::apps(
                d.add_le_add.clone(),
                [p_lo.clone(), p_x.clone(), q_hi.clone(), q_x.clone(), h1, h2],
            );

            // Recombination: (p*x + q*x) = W j i * x i.
            //   wd : W j i = p + q  via w_decompose m n W j i.
            let wd = Expr::apps(
                d.w_decompose.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );
            //   f := fun t : Rat => t * x i.
            let mul_by_x = {
                let mut cf = EnvDeclBuilder::child_of(&ci);
                let (t_id, t) = cf.fresh_local(c.rat.clone());
                let bodyf = c.mul(t, x_i.clone());
                cf.finish_child(cf.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), bodyf))
            };
            //   eq_wx : W j i * x i = (p + q) * x i  via congrArg.
            let p_plus_q = c.add(p.clone(), q.clone());
            let eq_wx = d.congr(c, w_ji.clone(), p_plus_q.clone(), mul_by_x, wd);
            //   eq_dist : (p + q) * x i = p*x + q*x  via Rat.right_distrib p q (x i).
            let eq_dist = Expr::apps(d.right_distrib.clone(), [p.clone(), q.clone(), x_i.clone()]);
            let w_x = c.mul(w_ji.clone(), x_i.clone());
            let pq_x = c.mul(p_plus_q.clone(), x_i.clone());
            let px_plus_qx = c.add(p_x.clone(), q_x.clone());
            //   eq_full : W j i * x i = p*x + q*x  via Eq.trans.
            let eq_full = d.trans(c, w_x.clone(), pq_x, px_plus_qx.clone(), eq_wx, eq_dist);
            //   eq_sym : (p*x + q*x) = W j i * x i  via Eq.symm.
            let eq_sym = d.symm(c, w_x.clone(), px_plus_qx.clone(), eq_full);

            // result : (p*lo + q*hi) ≤ W j i * x i
            //   via le_of_le_of_eq (p*lo+q*hi) (p*x+q*x) (W j i * x i) h12 eq_sym.
            let lo_sum_i = c.add(p_lo, q_hi);
            let per = Expr::apps(
                d.le_of_le_of_eq.clone(),
                [lo_sum_i, px_plus_qx, w_x, h12, eq_sym],
            );
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), per))
        };

        // h_sum_lo : sum_lo ≤ sum_out  via Fin.sum_le n lo_summand out_summand pointwise_lo.
        let h_sum_lo = Expr::apps(
            d.fin_sum_le.clone(),
            [
                n.clone(),
                lo_summand.clone(),
                out_summand.clone(),
                pointwise_lo,
            ],
        );
        // lower : (sum_lo + b j) ≤ (sum_out + b j)  via add_le_add.
        let lower_proof = Expr::apps(
            d.add_le_add.clone(),
            [
                sum_lo.clone(),
                sum_out.clone(),
                bias_j.clone(),
                bias_j.clone(),
                h_sum_lo,
                h_bias.clone(),
            ],
        );

        // -------- pointwise upper : ∀ i, out_summand i ≤ hi_summand i ----------
        let pointwise_hi = {
            let mut ci = EnvDeclBuilder::child_of(&ch);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let p = d.w_pos_entry(&m, &n, &w, &j, &i);
            let q = d.w_neg_entry(&m, &n, &w, &j, &i);
            let w_ji = Expr::app(Expr::app(w.clone(), j.clone()), i.clone());
            let lo_i = Expr::app(proj_lower.clone(), i.clone());
            let hi_i = Expr::app(proj_upper.clone(), i.clone());
            let x_i = Expr::app(x.clone(), i.clone());

            // hx i : (lo i ≤ x i) ∧ (x i ≤ hi i).
            let hx_i = Expr::app(hx.clone(), i.clone());
            let le_lo_x = c.rat_le(lo_i.clone(), x_i.clone());
            let le_x_hi = c.rat_le(x_i.clone(), hi_i.clone());
            let h_lo_x = Expr::apps(
                d.and_left.clone(),
                [le_lo_x.clone(), le_x_hi.clone(), hx_i.clone()],
            );
            let h_x_hi = Expr::apps(d.and_right.clone(), [le_lo_x, le_x_hi, hx_i]);

            let h_pos = Expr::apps(
                d.w_pos_nonneg.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );
            let h_neg = Expr::apps(
                d.w_neg_nonpos.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );

            // h1 : p*x ≤ p*hi  via mul_nonneg_le_left p x hi h_pos h_x_hi.
            let h1 = Expr::apps(
                d.mul_nonneg_le_left.clone(),
                [p.clone(), x_i.clone(), hi_i.clone(), h_pos, h_x_hi],
            );
            // h2 : q*x ≤ q*lo  via mul_nonpos_le_left q lo x h_neg h_lo_x.
            //   (mul_nonpos_le_left w a b : w≤0 → a≤b → w*b ≤ w*a; a=lo, b=x)
            let h2 = Expr::apps(
                d.mul_nonpos_le_left.clone(),
                [q.clone(), lo_i.clone(), x_i.clone(), h_neg, h_lo_x],
            );

            let p_x = c.mul(p.clone(), x_i.clone());
            let p_hi = c.mul(p.clone(), hi_i.clone());
            let q_x = c.mul(q.clone(), x_i.clone());
            let q_lo = c.mul(q.clone(), lo_i.clone());

            // h12 : (p*x + q*x) ≤ (p*hi + q*lo)  via add_le_add.
            let h12 = Expr::apps(
                d.add_le_add.clone(),
                [p_x.clone(), p_hi.clone(), q_x.clone(), q_lo.clone(), h1, h2],
            );

            // Recombination: W j i * x i = p*x + q*x  (same eq_full as the lower side).
            let wd = Expr::apps(
                d.w_decompose.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );
            let mul_by_x = {
                let mut cf = EnvDeclBuilder::child_of(&ci);
                let (t_id, t) = cf.fresh_local(c.rat.clone());
                let bodyf = c.mul(t, x_i.clone());
                cf.finish_child(cf.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), bodyf))
            };
            let p_plus_q = c.add(p.clone(), q.clone());
            let eq_wx = d.congr(c, w_ji.clone(), p_plus_q.clone(), mul_by_x, wd);
            let eq_dist = Expr::apps(d.right_distrib.clone(), [p.clone(), q.clone(), x_i.clone()]);
            let w_x = c.mul(w_ji.clone(), x_i.clone());
            let pq_x = c.mul(p_plus_q.clone(), x_i.clone());
            let px_plus_qx = c.add(p_x.clone(), q_x.clone());
            //   eq_full : W j i * x i = p*x + q*x.
            let eq_full = d.trans(c, w_x.clone(), pq_x, px_plus_qx.clone(), eq_wx, eq_dist);

            // h_eq_le : W j i * x i ≤ (p*hi + q*lo)
            //   via le_of_eq_of_le (W j i*x i) (p*x+q*x) (p*hi+q*lo) eq_full h12.
            let p_hi_plus_q_lo = c.add(p_hi.clone(), q_lo.clone());
            let h_eq_le = Expr::apps(
                d.le_of_eq_of_le.clone(),
                [
                    w_x.clone(),
                    px_plus_qx,
                    p_hi_plus_q_lo.clone(),
                    eq_full,
                    h12,
                ],
            );

            // Reorder to the hi' summand order: hi_summand i = q*lo + p*hi.
            //   comm : (p*hi + q*lo) = (q*lo + p*hi)  via Rat.add_comm (p*hi) (q*lo).
            let comm = Expr::apps(d.add_comm.clone(), [p_hi.clone(), q_lo.clone()]);
            let q_lo_plus_p_hi = c.add(q_lo, p_hi);
            // result : W j i * x i ≤ (q*lo + p*hi)
            //   via le_of_le_of_eq (W j i*x i) (p*hi+q*lo) (q*lo+p*hi) h_eq_le comm.
            let per = Expr::apps(
                d.le_of_le_of_eq.clone(),
                [w_x, p_hi_plus_q_lo, q_lo_plus_p_hi, h_eq_le, comm],
            );
            ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), per))
        };

        // h_sum_hi : sum_out ≤ sum_hi  via Fin.sum_le n out_summand hi_summand pointwise_hi.
        let h_sum_hi = Expr::apps(
            d.fin_sum_le.clone(),
            [
                n.clone(),
                out_summand.clone(),
                hi_summand.clone(),
                pointwise_hi,
            ],
        );
        // upper : (sum_out + b j) ≤ (sum_hi + b j)  via add_le_add.
        let upper_proof = Expr::apps(
            d.add_le_add.clone(),
            [
                sum_out.clone(),
                sum_hi.clone(),
                bias_j.clone(),
                bias_j.clone(),
                h_sum_hi,
                h_bias,
            ],
        );

        // The two conjunct Props (must equal the stated goal after reduction).
        let out_j = c.add(sum_out.clone(), bias_j.clone());
        let lo_j = c.add(sum_lo, bias_j.clone());
        let hi_j = c.add(sum_hi, bias_j);
        let prop_lo = c.rat_le(lo_j, out_j.clone());
        let prop_hi = c.rat_le(out_j, hi_j);

        // And.intro prop_lo prop_hi lower upper.
        let conj = Expr::apps(
            d.and_intro.clone(),
            [prop_lo, prop_hi, lower_proof, upper_proof],
        );
        ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), conj))
    };

    let e = b.mk_lam(hx_id, BinderInfo::Default, contains_input, body);
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
