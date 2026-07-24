// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T80 follow-up (#3490): `NNVerify.ibp_linear_bounds` as a faithful reducible
//! `Declaration::Definition` (was an uninterpreted `Declaration::Axiom`).
//!
//! For a linear layer `y = W·x + b` with the W+/W- decomposition
//! `W = w_pos W + w_neg W` (positive / negative parts), the sound IBP output
//! interval is
//! ```text
//! lo' j = Σ_i (w_pos j i · B.lower i + w_neg j i · B.upper i) + b j
//! hi' j = Σ_i (w_neg j i · B.lower i + w_pos j i · B.upper i) + b j
//! ```
//! The result is `IntervalBounds.mk m lo' hi' valid`, with `valid : ∀ j,
//! lo' j ≤ hi' j` proved CONSTRUCTIVELY (no `sorry`) from per-summand
//! monotonicity:
//!   - `w_pos ≥ 0` (`w_pos_nonneg`) and `B.lower ≤ B.upper` (`B.valid`) give
//!     `w_pos·lo ≤ w_pos·hi` (`mul_nonneg_le_left`);
//!   - `w_neg ≤ 0` (`w_neg_nonpos`) gives `w_neg·hi ≤ w_neg·lo`
//!     (`mul_nonpos_le_left`);
//!   - `add_le_add` then `le_of_le_of_eq` (with `Rat.add_comm`) lift the pair to
//!     `(w_pos·lo + w_neg·hi) ≤ (w_neg·lo + w_pos·hi)` per index;
//!   - `Fin.sum_le` lifts the pointwise inequality to the sums;
//!   - `add_le_add` with `Rat.le_refl (b j)` adds the shared bias.
//!
//! Closure ⊆ the W+/W- decomposition lemmas (`w_pos_nonneg`, `w_neg_nonpos`,
//! constructive Theorems) ∪ `mul_nonneg_le_left` / `mul_nonpos_le_left` /
//! `add_le_add` / `le_of_le_of_eq` (constructive Theorems) ∪ `Fin.sum_le`
//! (the per-summand→sum monotonicity lemma) ∪ `Rat.add_comm` / `Rat.le_refl`.

use super::nn_verify_ibp_linear::IbpLinearConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Constants for the `ibp_linear_bounds` body construction (on top of the
/// shared `IbpLinearConsts`).
struct DefineConsts {
    ib_mk: Expr,
    w_pos: Expr,
    w_neg: Expr,
    w_pos_nonneg: Expr,
    w_neg_nonpos: Expr,
    mul_nonneg_le_left: Expr,
    mul_nonpos_le_left: Expr,
    add_le_add: Expr,
    le_of_le_of_eq: Expr,
    fin_sum_le: Expr,
    rat_add_comm: Expr,
    rat_le_refl: Expr,
}

impl DefineConsts {
    fn new() -> Self {
        Self {
            ib_mk: Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
            w_pos: Expr::const_(Name::from_string("NNVerify.w_pos"), vec![]),
            w_neg: Expr::const_(Name::from_string("NNVerify.w_neg"), vec![]),
            w_pos_nonneg: Expr::const_(Name::from_string("NNVerify.w_pos_nonneg"), vec![]),
            w_neg_nonpos: Expr::const_(Name::from_string("NNVerify.w_neg_nonpos"), vec![]),
            mul_nonneg_le_left: Expr::const_(
                Name::from_string("NNVerify.mul_nonneg_le_left"),
                vec![],
            ),
            mul_nonpos_le_left: Expr::const_(
                Name::from_string("NNVerify.mul_nonpos_le_left"),
                vec![],
            ),
            add_le_add: Expr::const_(Name::from_string("NNVerify.add_le_add"), vec![]),
            le_of_le_of_eq: Expr::const_(Name::from_string("NNVerify.le_of_le_of_eq"), vec![]),
            fin_sum_le: Expr::const_(Name::from_string("Fin.sum_le"), vec![]),
            rat_add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
            rat_le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        }
    }

    /// `(w_pos m n W) j i : Rat` — the positive-part entry at output `j`, input `i`.
    fn w_pos_entry(&self, m: &Expr, n: &Expr, w: &Expr, j: &Expr, i: &Expr) -> Expr {
        let mat = Expr::apps(self.w_pos.clone(), [m.clone(), n.clone(), w.clone()]);
        Expr::app(Expr::app(mat, j.clone()), i.clone())
    }

    /// `(w_neg m n W) j i : Rat` — the negative-part entry at output `j`, input `i`.
    fn w_neg_entry(&self, m: &Expr, n: &Expr, w: &Expr, j: &Expr, i: &Expr) -> Expr {
        let mat = Expr::apps(self.w_neg.clone(), [m.clone(), n.clone(), w.clone()]);
        Expr::app(Expr::app(mat, j.clone()), i.clone())
    }
}

/// Build the value term for the `NNVerify.ibp_linear_bounds` Definition:
/// `fun (m n : Nat) (W : NNMat m n) (b : NNVec m) (B : IntervalBounds n) =>
///    IntervalBounds.mk m lo' hi' valid`.
pub(super) fn build_ibp_linear_bounds_value(c: &IbpLinearConsts) -> Expr {
    let d = DefineConsts::new();

    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let ib_n = c.ib_of(n.clone());
    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (bias_id, bias) = b.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    let fin_m = Expr::app(c.fin.clone(), m.clone());
    let fin_n = Expr::app(c.fin.clone(), n.clone());

    // B.lower : Fin n -> Rat, B.upper : Fin n -> Rat, B.valid : ∀ i, lower i ≤ upper i.
    let lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone());
    let upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd.clone());
    let valid = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 2, bnd.clone());

    // Per-output-index `j` summand builders (lambdas of `i : Fin n`).
    // lo summand i := w_pos j i * lower i + w_neg j i * upper i
    let lo_summand = |bb: &EnvDeclBuilder, j: &Expr| -> Expr {
        let mut ch = EnvDeclBuilder::child_of(bb);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let p = d.w_pos_entry(&m, &n, &w, j, &i);
        let q = d.w_neg_entry(&m, &n, &w, j, &i);
        let lo_i = Expr::app(lower.clone(), i.clone());
        let hi_i = Expr::app(upper.clone(), i.clone());
        let body = c.add(c.mul(p, lo_i), c.mul(q, hi_i));
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body);
        ch.finish_child(r)
    };
    // hi summand i := w_neg j i * lower i + w_pos j i * upper i
    let hi_summand = |bb: &EnvDeclBuilder, j: &Expr| -> Expr {
        let mut ch = EnvDeclBuilder::child_of(bb);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let p = d.w_pos_entry(&m, &n, &w, j, &i);
        let q = d.w_neg_entry(&m, &n, &w, j, &i);
        let lo_i = Expr::app(lower.clone(), i.clone());
        let hi_i = Expr::app(upper.clone(), i.clone());
        let body = c.add(c.mul(q, lo_i), c.mul(p, hi_i));
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body);
        ch.finish_child(r)
    };

    // lo' : NNVec m := fun j => Fin.sum n (lo_summand j) + b j
    let lo_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = ch.fresh_local(fin_m.clone());
        let s = c.sum(n.clone(), lo_summand(&ch, &j));
        let body = c.add(s, Expr::app(bias.clone(), j.clone()));
        let r = ch.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body);
        ch.finish_child(r)
    };
    // hi' : NNVec m := fun j => Fin.sum n (hi_summand j) + b j
    let hi_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = ch.fresh_local(fin_m.clone());
        let s = c.sum(n.clone(), hi_summand(&ch, &j));
        let body = c.add(s, Expr::app(bias.clone(), j.clone()));
        let r = ch.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body);
        ch.finish_child(r)
    };

    // valid : ∀ (j : Fin m), lo' j ≤ hi' j.
    let valid_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = ch.fresh_local(fin_m.clone());

        let f_lo = lo_summand(&ch, &j);
        let f_hi = hi_summand(&ch, &j);
        let sum_lo = c.sum(n.clone(), f_lo.clone());
        let sum_hi = c.sum(n.clone(), f_hi.clone());
        let bias_j = Expr::app(bias.clone(), j.clone());

        // Pointwise: ∀ i, lo_summand j i ≤ hi_summand j i.
        let pointwise = {
            let mut ci = EnvDeclBuilder::child_of(&ch);
            let (i_id, i) = ci.fresh_local(fin_n.clone());
            let p = d.w_pos_entry(&m, &n, &w, &j, &i);
            let q = d.w_neg_entry(&m, &n, &w, &j, &i);
            let lo_i = Expr::app(lower.clone(), i.clone());
            let hi_i = Expr::app(upper.clone(), i.clone());

            // h_valid_i : lower i ≤ upper i.
            let h_valid_i = Expr::app(valid.clone(), i.clone());
            // h_pos : 0 ≤ w_pos j i ; h_neg : w_neg j i ≤ 0.
            let h_pos = Expr::apps(
                d.w_pos_nonneg.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );
            let h_neg = Expr::apps(
                d.w_neg_nonpos.clone(),
                [m.clone(), n.clone(), w.clone(), j.clone(), i.clone()],
            );

            // h1 : p*lo ≤ p*hi   via mul_nonneg_le_left p lo hi h_pos h_valid_i.
            let h1 = Expr::apps(
                d.mul_nonneg_le_left.clone(),
                [
                    p.clone(),
                    lo_i.clone(),
                    hi_i.clone(),
                    h_pos,
                    h_valid_i.clone(),
                ],
            );
            // h2 : q*hi ≤ q*lo   via mul_nonpos_le_left q lo hi h_neg h_valid_i.
            let h2 = Expr::apps(
                d.mul_nonpos_le_left.clone(),
                [q.clone(), lo_i.clone(), hi_i.clone(), h_neg, h_valid_i],
            );

            let p_lo = c.mul(p.clone(), lo_i.clone());
            let p_hi = c.mul(p.clone(), hi_i.clone());
            let q_lo = c.mul(q.clone(), lo_i.clone());
            let q_hi = c.mul(q.clone(), hi_i.clone());

            // h12 : (p*lo + q*hi) ≤ (p*hi + q*lo)  via add_le_add.
            let h12 = Expr::apps(
                d.add_le_add.clone(),
                [
                    p_lo.clone(),
                    p_hi.clone(),
                    q_hi.clone(),
                    q_lo.clone(),
                    h1,
                    h2,
                ],
            );
            // h_comm : (p*hi + q*lo) = (q*lo + p*hi)  via Rat.add_comm.
            let h_comm = Expr::apps(d.rat_add_comm.clone(), [p_hi.clone(), q_lo.clone()]);
            // le_of_le_of_eq (p*lo+q*hi) (p*hi+q*lo) (q*lo+p*hi) h12 h_comm
            //   : (p*lo + q*hi) ≤ (q*lo + p*hi).
            let lhs_sum = c.add(p_lo, q_hi);
            let mid_sum = c.add(p_hi.clone(), q_lo.clone());
            let rhs_sum = c.add(q_lo, p_hi);
            let per = Expr::apps(
                d.le_of_le_of_eq.clone(),
                [lhs_sum, mid_sum, rhs_sum, h12, h_comm],
            );
            let r = ci.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), per);
            ci.finish_child(r)
        };

        // h_sum : sum_lo ≤ sum_hi  via Fin.sum_le n f_lo f_hi pointwise.
        let h_sum = Expr::apps(d.fin_sum_le.clone(), [n.clone(), f_lo, f_hi, pointwise]);

        // le_refl (b j) : b j ≤ b j.
        let h_bias = Expr::app(d.rat_le_refl.clone(), bias_j.clone());

        // add_le_add sum_lo sum_hi (b j) (b j) h_sum h_bias
        //   : (sum_lo + b j) ≤ (sum_hi + b j).
        let body = Expr::apps(
            d.add_le_add.clone(),
            [sum_lo, sum_hi, bias_j.clone(), bias_j, h_sum, h_bias],
        );
        let r = ch.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body);
        ch.finish_child(r)
    };

    // IntervalBounds.mk m lo' hi' valid.
    let result = Expr::apps(d.ib_mk.clone(), [m.clone(), lo_fn, hi_fn, valid_fn]);

    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, result);
    let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
