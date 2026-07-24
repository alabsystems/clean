// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008 unlock (R-weak): zero-width preservation sub-lemmas for the
//! `NNVerify.ibp_tightness_step` proof.
//!
//! This module lands the two reusable, self-contained zero-width preservation
//! Theorems off the new `ibp_linear_bounds` define and the existing
//! `ibp_relu_bounds` define. The `Nat.rec` `propagate_eq` lemma, the
//! non-negativity helpers (`infinity_norm_nonneg` / `norm_product_nonneg`), and
//! the assembled `ibp_tightness_step` proof live in
//! `nn_verify_ibp_tightness_step_value`. With all of those, `ibp_tightness_step`
//! is a constructive sorry-free `Declaration::Theorem` (R-weak).
//!
//! ROUTE R-WEAK (honesty caveat, same as the landed `ibp_tightness_base`):
//! the registered `NNVerify.eps_ball` is a zero-width placeholder
//! (`IntervalBounds.mk n 0⃗ 0⃗ _`), so the propagated bounds stay zero-width
//! through every layer and the step LHS `ibp_width` collapses to `Rat.zero`.
//! The lemmas below are GENUINE constructive Theorems (no `sorry`, no
//! masquerade); the mathematical force of the *step* that consumes them rests
//! on that placeholder body. A faithful `eps_ball` (route R-real) is out of
//! scope.
//!
//! Two reusable, self-contained sub-lemmas — both proved off the real
//! `ibp_relu_bounds` / `ibp_linear_bounds` Definitions:
//!   - `NNVerify.relu_bounds_preserves_eq`: a zero-width input
//!     (`∀ i, bnd.lower i = bnd.upper i`) maps to a zero-width
//!     `ibp_relu_bounds` output, since `(relu_bounds n bnd).lower i ≡
//!     relu (bnd.lower i)` and `.upper i ≡ relu (bnd.upper i)` (so `congrArg
//!     relu (h i)` closes each index);
//!   - `NNVerify.linear_bounds_preserves_eq`: zero-width in ⇒ zero-width out
//!     of `ibp_linear_bounds`. After the define reduces the projections,
//!     `.lower j ≡ Σ_i (w_pos j i · lo i + w_neg j i · hi i) + b j` and
//!     `.upper j ≡ Σ_i (w_neg j i · lo i + w_pos j i · hi i) + b j`; under
//!     `lo i = hi i` the two summand families coincide up to `Rat.add_comm`,
//!     so `Fin.sum_congr` equates the sums and `congrArg (· + b j)` adds the
//!     shared bias.

use super::nn_verify_ibp_linear::IbpLinearConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Constants for the zero-width preservation lemmas (on top of the shared
/// `IbpLinearConsts`).
struct PreserveConsts {
    relu: Expr,
    w_pos: Expr,
    w_neg: Expr,
    fin_sum: Expr,
    fin_sum_congr: Expr,
    add_comm: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl PreserveConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            relu: Expr::const_(Name::from_string("NNVerify.relu"), vec![]),
            w_pos: Expr::const_(Name::from_string("NNVerify.w_pos"), vec![]),
            w_neg: Expr::const_(Name::from_string("NNVerify.w_neg"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]),
        }
    }

    fn lower_at(bnd: &Expr, i: &Expr) -> Expr {
        Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone()),
            i.clone(),
        )
    }

    fn upper_at(bnd: &Expr, i: &Expr) -> Expr {
        Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd.clone()),
            i.clone(),
        )
    }

    fn w_pos_entry(&self, m: &Expr, n: &Expr, w: &Expr, j: &Expr, i: &Expr) -> Expr {
        let mat = Expr::apps(self.w_pos.clone(), [m.clone(), n.clone(), w.clone()]);
        Expr::app(Expr::app(mat, j.clone()), i.clone())
    }

    fn w_neg_entry(&self, m: &Expr, n: &Expr, w: &Expr, j: &Expr, i: &Expr) -> Expr {
        let mat = Expr::apps(self.w_neg.clone(), [m.clone(), n.clone(), w.clone()]);
        Expr::app(Expr::app(mat, j.clone()), i.clone())
    }

    fn rat_eq(&self, c: &IbpLinearConsts, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [c.rat.clone(), a, b])
    }

    /// `@Eq.trans.{1} Rat a b d h1 h2`.
    fn trans(&self, c: &IbpLinearConsts, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [c.rat.clone(), a, b, d, h1, h2])
    }

    /// `@congrArg.{1,1} Rat Rat a b f h : Eq Rat (f a) (f b)`.
    fn congr(&self, c: &IbpLinearConsts, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [c.rat.clone(), c.rat.clone(), a, b, f, h],
        )
    }

    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
}

/// The hypothesis type `∀ (i : Fin n), Eq Rat (bnd.lower i) (bnd.upper i)`.
fn eq_hyp_ty(
    d: &PreserveConsts,
    c: &IbpLinearConsts,
    n: &Expr,
    bnd: &Expr,
    outer: &EnvDeclBuilder,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let fin_n = Expr::app(c.fin.clone(), n.clone());
    let (i_id, i) = ch.fresh_local(fin_n.clone());
    let body = d.rat_eq(
        c,
        PreserveConsts::lower_at(bnd, &i),
        PreserveConsts::upper_at(bnd, &i),
    );
    ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
}

impl Environment {
    /// Register the two zero-width preservation sub-lemmas used by the
    /// `ibp_tightness_step` R-weak proof. Idempotent / guarded.
    pub(super) fn register_ibp_tightness_step_support(
        &mut self,
        c: &IbpLinearConsts,
    ) -> Result<(), EnvError> {
        self.register_relu_bounds_preserves_eq(c)?;
        self.register_linear_bounds_preserves_eq(c)
    }

    /// `NNVerify.relu_bounds_preserves_eq :
    ///   ∀ (n : Nat) (bnd : IntervalBounds n),
    ///     (∀ i, bnd.lower i = bnd.upper i) →
    ///     ∀ i, (ibp_relu_bounds n bnd).lower i = (ibp_relu_bounds n bnd).upper i`.
    ///
    /// Proof: `(relu_bounds n bnd).lower i ≡ relu (bnd.lower i)` and
    /// `.upper i ≡ relu (bnd.upper i)` (the define applies `relu` element-wise),
    /// so `congrArg relu (h i)` inhabits each index. Sorry-free.
    fn register_relu_bounds_preserves_eq(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.relu_bounds_preserves_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let d = PreserveConsts::new();
        let relu_bounds = Expr::const_(Name::from_string("NNVerify.ibp_relu_bounds"), vec![]);

        let mk_concl = |outer: &EnvDeclBuilder, n: &Expr, bnd: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(outer);
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let rb = Expr::apps(relu_bounds.clone(), [n.clone(), bnd.clone()]);
            let body = d.rat_eq(
                c,
                PreserveConsts::lower_at(&rb, &i),
                PreserveConsts::upper_at(&rb, &i),
            );
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ib_n = c.ib_of(n.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
            let hyp = eq_hyp_ty(&d, c, &n, &bnd, &b);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let concl = mk_concl(&b, &n, &bnd);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ib_n = c.ib_of(n.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
            let hyp = eq_hyp_ty(&d, c, &n, &bnd, &b);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                // h i : bnd.lower i = bnd.upper i.
                let h_i = Expr::app(h.clone(), i.clone());
                let lo_i = PreserveConsts::lower_at(&bnd, &i);
                let hi_i = PreserveConsts::upper_at(&bnd, &i);
                // congrArg relu (h i) : relu (lower i) = relu (upper i)
                //   ≡ (relu_bounds n bnd).lower i = (relu_bounds n bnd).upper i.
                let body = d.congr(c, lo_i, hi_i, d.relu.clone(), h_i);
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, inner);
            let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.linear_bounds_preserves_eq :
    ///   ∀ (m n : Nat) (W : NNMat m n) (bias : NNVec m) (bnd : IntervalBounds n),
    ///     (∀ i, bnd.lower i = bnd.upper i) →
    ///     ∀ j, (ibp_linear_bounds m n W bias bnd).lower j
    ///            = (ibp_linear_bounds m n W bias bnd).upper j`.
    ///
    /// Proof: after the define reduces the projections,
    /// `.lower j ≡ Σ_i (w_pos j i · lo i + w_neg j i · hi i) + b j` and
    /// `.upper j ≡ Σ_i (w_neg j i · lo i + w_pos j i · hi i) + b j`. Under
    /// `lo i = hi i` (`h i`), each `lo'` summand equals the corresponding
    /// `hi'` summand by `Rat.add_comm` (after rewriting `hi i → lo i`), so
    /// `Fin.sum_congr` equates the sums and `congrArg (· + b j)` adds the
    /// shared bias. Sorry-free; closure ⊆ `Fin.sum_congr` ∪ `Rat.add_comm` ∪
    /// foundational `Eq`/`congrArg`.
    fn register_linear_bounds_preserves_eq(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.linear_bounds_preserves_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let d = PreserveConsts::new();
        let linear_bounds = Expr::const_(Name::from_string("NNVerify.ibp_linear_bounds"), vec![]);

        // lo' summand i := w_pos j i · lo i + w_neg j i · hi i.
        let lo_summand =
            |outer: &EnvDeclBuilder, m: &Expr, n: &Expr, w: &Expr, bnd: &Expr, j: &Expr| -> Expr {
                let mut ch = EnvDeclBuilder::child_of(outer);
                let fin_n = Expr::app(c.fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let p = d.w_pos_entry(m, n, w, j, &i);
                let q = d.w_neg_entry(m, n, w, j, &i);
                let lo_i = PreserveConsts::lower_at(bnd, &i);
                let hi_i = PreserveConsts::upper_at(bnd, &i);
                let body = c.add(c.mul(p, lo_i), c.mul(q, hi_i));
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
        // hi' summand i := w_neg j i · lo i + w_pos j i · hi i.
        let hi_summand =
            |outer: &EnvDeclBuilder, m: &Expr, n: &Expr, w: &Expr, bnd: &Expr, j: &Expr| -> Expr {
                let mut ch = EnvDeclBuilder::child_of(outer);
                let fin_n = Expr::app(c.fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let p = d.w_pos_entry(m, n, w, j, &i);
                let q = d.w_neg_entry(m, n, w, j, &i);
                let lo_i = PreserveConsts::lower_at(bnd, &i);
                let hi_i = PreserveConsts::upper_at(bnd, &i);
                let body = c.add(c.mul(q, lo_i), c.mul(p, hi_i));
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

        let mk_concl = |outer: &EnvDeclBuilder,
                        m: &Expr,
                        n: &Expr,
                        w: &Expr,
                        bias: &Expr,
                        bnd: &Expr|
         -> Expr {
            let mut ch = EnvDeclBuilder::child_of(outer);
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let (j_id, j) = ch.fresh_local(fin_m.clone());
            let lb = Expr::apps(
                linear_bounds.clone(),
                [m.clone(), n.clone(), w.clone(), bias.clone(), bnd.clone()],
            );
            let body = d.rat_eq(
                c,
                PreserveConsts::lower_at(&lb, &j),
                PreserveConsts::upper_at(&lb, &j),
            );
            ch.finish_child(ch.mk_pi(j_id, BinderInfo::Default, fin_m, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let vec_m = c.vec_of(m.clone());
            let ib_n = c.ib_of(n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
            let hyp = eq_hyp_ty(&d, c, &n, &bnd, &b);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let concl = mk_concl(&b, &m, &n, &w, &bias, &bnd);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
            let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let vec_m = c.vec_of(m.clone());
            let ib_n = c.ib_of(n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
            let hyp = eq_hyp_ty(&d, c, &n, &bnd, &b);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());

            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (j_id, j) = ch.fresh_local(fin_m.clone());
                let f_lo = lo_summand(&ch, &m, &n, &w, &bnd, &j);
                let f_hi = hi_summand(&ch, &m, &n, &w, &bnd, &j);
                let bias_j = Expr::app(bias.clone(), j.clone());

                // pointwise : ∀ i, f_lo i = f_hi i.
                let pointwise = {
                    let mut ci = EnvDeclBuilder::child_of(&ch);
                    let fin_n = Expr::app(c.fin.clone(), n.clone());
                    let (i_id, i) = ci.fresh_local(fin_n.clone());
                    let p = d.w_pos_entry(&m, &n, &w, &j, &i);
                    let q = d.w_neg_entry(&m, &n, &w, &j, &i);
                    let lo_i = PreserveConsts::lower_at(&bnd, &i);
                    let hi_i = PreserveConsts::upper_at(&bnd, &i);
                    // h i : lo i = hi i.
                    let h_i = Expr::app(h.clone(), i.clone());
                    let p_lo = c.mul(p.clone(), lo_i.clone());
                    let p_hi = c.mul(p.clone(), hi_i.clone());
                    let q_lo = c.mul(q.clone(), lo_i.clone());
                    let q_hi = c.mul(q.clone(), hi_i.clone());

                    // f_lo i = p·lo + q·hi ; f_hi i = q·lo + p·hi.
                    // Step 1: rewrite hi i → lo i in f_lo to get p·lo + q·lo.
                    //   e_qhq : q·hi = q·lo  via congrArg (q·_) (Eq.symm (h i))? — simpler:
                    //   congrArg (fun t => q * t) (Eq.symm (h i)) : q·hi = q·lo.
                    let h_sym = Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.symm"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [c.rat.clone(), lo_i.clone(), hi_i.clone(), h_i.clone()],
                    );
                    let mul_q = {
                        let mut cf = EnvDeclBuilder::child_of(&ci);
                        let (t_id, t) = cf.fresh_local(c.rat.clone());
                        let bodyf = c.mul(q.clone(), t);
                        cf.finish_child(cf.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), bodyf))
                    };
                    // e1 : q·hi = q·lo.
                    let e1 = d.congr(c, hi_i.clone(), lo_i.clone(), mul_q, h_sym);
                    // e_plo : p·lo = p·hi  via congrArg (p·_) (h i).
                    let mul_p = {
                        let mut cf = EnvDeclBuilder::child_of(&ci);
                        let (t_id, t) = cf.fresh_local(c.rat.clone());
                        let bodyf = c.mul(p.clone(), t);
                        cf.finish_child(cf.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), bodyf))
                    };
                    // e2 : p·lo = p·hi.
                    let e2 = d.congr(c, lo_i.clone(), hi_i.clone(), mul_p, h_i.clone());

                    // Goal: (p·lo + q·hi) = (q·lo + p·hi).
                    // Chain:  p·lo + q·hi
                    //   =[congrArg (p·lo + _) e1]  p·lo + q·lo
                    //   =[Rat.add_comm (p·lo) (q·lo)]  q·lo + p·lo
                    //   =[congrArg (q·lo + _) e2]  q·lo + p·hi.
                    let add_plo = {
                        let mut cf = EnvDeclBuilder::child_of(&ci);
                        let (t_id, t) = cf.fresh_local(c.rat.clone());
                        let bodyf = c.add(p_lo.clone(), t);
                        cf.finish_child(cf.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), bodyf))
                    };
                    // c1 : (p·lo + q·hi) = (p·lo + q·lo).
                    let c1 = d.congr(c, q_hi.clone(), q_lo.clone(), add_plo, e1);
                    // comm : (p·lo + q·lo) = (q·lo + p·lo)  via Rat.add_comm.
                    let comm = Expr::apps(d.add_comm.clone(), [p_lo.clone(), q_lo.clone()]);
                    let add_qlo = {
                        let mut cf = EnvDeclBuilder::child_of(&ci);
                        let (t_id, t) = cf.fresh_local(c.rat.clone());
                        let bodyf = c.add(q_lo.clone(), t);
                        cf.finish_child(cf.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), bodyf))
                    };
                    // c2 : (q·lo + p·lo) = (q·lo + p·hi).
                    let c2 = d.congr(c, p_lo.clone(), p_hi.clone(), add_qlo, e2);

                    let plo_qhi = c.add(p_lo.clone(), q_hi.clone());
                    let plo_qlo = c.add(p_lo.clone(), q_lo.clone());
                    let qlo_plo = c.add(q_lo.clone(), p_lo.clone());
                    let qlo_phi = c.add(q_lo.clone(), p_hi.clone());

                    // t1 : (p·lo + q·hi) = (q·lo + p·lo).
                    let t1 = d.trans(
                        c,
                        plo_qhi.clone(),
                        plo_qlo.clone(),
                        qlo_plo.clone(),
                        c1,
                        comm,
                    );
                    // per : (p·lo + q·hi) = (q·lo + p·hi).
                    let per = d.trans(c, plo_qhi, qlo_plo, qlo_phi, t1, c2);
                    ci.finish_child(ci.mk_lam(i_id, BinderInfo::Default, fin_n, per))
                };

                // h_sum : Σ f_lo = Σ f_hi  via Fin.sum_congr n f_lo f_hi pointwise.
                let h_sum = Expr::apps(
                    d.fin_sum_congr.clone(),
                    [n.clone(), f_lo.clone(), f_hi.clone(), pointwise],
                );
                // congrArg (· + b j) h_sum : (Σ f_lo + b j) = (Σ f_hi + b j)
                //   ≡ (linear_bounds …).lower j = (linear_bounds …).upper j.
                let sum_lo = d.sum(n.clone(), f_lo);
                let sum_hi = d.sum(n.clone(), f_hi);
                let add_bias = {
                    let mut cf = EnvDeclBuilder::child_of(&ch);
                    let (t_id, t) = cf.fresh_local(c.rat.clone());
                    let bodyf = c.add(t, bias_j.clone());
                    cf.finish_child(cf.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), bodyf))
                };
                let body = d.congr(c, sum_lo, sum_hi, add_bias, h_sum);
                ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_m, body))
            };

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, inner);
            let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
            let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
