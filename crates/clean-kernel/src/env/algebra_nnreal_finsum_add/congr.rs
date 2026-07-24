// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `NNReal.finSum_congr` — the pointwise-rewrite-under-the-sum lemma, the NNReal
//! dual of the landed Rat `Fin.sum_congr`. `Nat.rec.{0}` induction; step closes
//! by `congr (congrArg NNReal.add (ih …)) (h (last k))`.

use super::FinSumStructConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `NNReal.finSum_congr : ∀ n f g, (∀ i, f i = g i) → finSum n f = finSum n g`.
    pub(crate) fn register_nnreal_finsum_congr(
        &mut self,
        c: &FinSumStructConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.finSum_congr");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_congr_type(c);
        let value = build_congr_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

fn build_congr_type(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let ft = c.fin_to_nn(&n);
    let (f_id, f) = b.fresh_local(ft.clone());
    let (g_id, g) = b.fresh_local(ft.clone());
    let h = c.hyp_ty(&b, &n, &f, &g);
    let (h_id, _h) = b.fresh_local(h.clone());
    let concl = c.eq_nn(&c.sum(&n, &f), &c.sum(&n, &g));
    let r = b.mk_pi(h_id, BinderInfo::Default, h, concl);
    let r = b.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
    let r = b.mk_pi(f_id, BinderInfo::Default, ft, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), r);
    b.finish(r)
}

fn build_motive(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let inner = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ft = c.fin_to_nn(&k);
        let (f_id, f) = d.fresh_local(ft.clone());
        let (g_id, g) = d.fresh_local(ft.clone());
        let h = c.hyp_ty(&d, &k, &f, &g);
        let (h_id, _h) = d.fresh_local(h.clone());
        let concl = c.eq_nn(&c.sum(&k, &f), &c.sum(&k, &g));
        let r = d.mk_pi(h_id, BinderInfo::Default, h, concl);
        let r = d.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
        let r = d.mk_pi(f_id, BinderInfo::Default, ft, r);
        d.finish_child(r)
    };
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), inner))
}

/// Base `motive 0`: `fun f g h => Eq.refl NNReal NNReal.zero`
/// (`finSum 0 _ ≡ NNReal.zero` both sides).
fn build_base(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let ft = c.fin_to_nn(&c.nat_zero);
    let (f_id, f) = b.fresh_local(ft.clone());
    let (g_id, g) = b.fresh_local(ft.clone());
    let h = c.hyp_ty(&b, &c.nat_zero, &f, &g);
    let (h_id, _h) = b.fresh_local(h.clone());
    let refl = Expr::apps(c.eq_refl1.clone(), [c.nn(), c.base.nnreal_zero.clone()]);
    let r = b.mk_lam(h_id, BinderInfo::Default, h, refl);
    let r = b.mk_lam(g_id, BinderInfo::Default, ft.clone(), r);
    let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
    b.finish(r)
}

/// Step `motive k → motive (k+1)`.
fn build_step(c: &FinSumStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());

    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ft = c.fin_to_nn(&k);
        let (f_id, f) = d.fresh_local(ft.clone());
        let (g_id, g) = d.fresh_local(ft.clone());
        let h = c.hyp_ty(&d, &k, &f, &g);
        let (h_id, _h) = d.fresh_local(h.clone());
        let concl = c.eq_nn(&c.sum(&k, &f), &c.sum(&k, &g));
        let r = d.mk_pi(h_id, BinderInfo::Default, h, concl);
        let r = d.mk_pi(g_id, BinderInfo::Default, ft.clone(), r);
        let r = d.mk_pi(f_id, BinderInfo::Default, ft, r);
        d.finish_child(r)
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let ft_sk = c.fin_to_nn(&succ_k);
    let (f_id, f) = b.fresh_local(ft_sk.clone());
    let (g_id, g) = b.fresh_local(ft_sk.clone());
    let h_outer = c.hyp_ty(&b, &succ_k, &f, &g);
    let (h_id, h) = b.fresh_local(h_outer.clone());

    let f_cs = c.cast_fn(&b, &k, &f);
    let g_cs = c.cast_fn(&b, &k, &g);

    // h_cs : fun i => h (castSucc k i) : (f∘cs) i = (g∘cs) i.
    let h_cs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(c.fin_n(&k));
        let cast_i = Expr::apps(c.fin_cast_succ.clone(), [k.clone(), i]);
        let body = Expr::app(h.clone(), cast_i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_n(&k), body))
    };
    let ih_app = Expr::apps(ih.clone(), [f_cs.clone(), g_cs.clone(), h_cs]);

    let last_k = Expr::app(c.fin_last.clone(), k.clone());
    let h_last = Expr::app(h.clone(), last_k.clone());

    // congrArg NNReal.add ih_app : NNReal.add (sum f∘cs) = NNReal.add (sum g∘cs).
    let nn_to_nn = Expr::pi(BinderInfo::Default, c.nn(), c.nn());
    let sum_f = c.sum(&k, &f_cs);
    let sum_g = c.sum(&k, &g_cs);
    let congr_add = Expr::apps(
        c.congr_arg11.clone(),
        [
            c.nn(),
            nn_to_nn.clone(),
            sum_f.clone(),
            sum_g.clone(),
            c.nnreal_add.clone(),
            ih_app,
        ],
    );

    // congr (congr_add) (h_last) : add (sum f∘cs)(f last) = add (sum g∘cs)(g last).
    let add_sum_f = Expr::app(c.nnreal_add.clone(), sum_f);
    let add_sum_g = Expr::app(c.nnreal_add.clone(), sum_g);
    let f_last = Expr::app(f.clone(), last_k.clone());
    let g_last = Expr::app(g.clone(), last_k);
    let result = Expr::apps(
        c.congr11.clone(),
        [
            c.nn(),
            c.nn(),
            add_sum_f,
            add_sum_g,
            f_last,
            g_last,
            congr_add,
            h_last,
        ],
    );

    let r = b.mk_lam(h_id, BinderInfo::Default, h_outer, result);
    let r = b.mk_lam(g_id, BinderInfo::Default, ft_sk.clone(), r);
    let r = b.mk_lam(f_id, BinderInfo::Default, ft_sk, r);
    let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
    let r = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), r);
    b.finish(r)
}

fn build_congr_value(c: &FinSumStructConsts) -> Expr {
    let motive = build_motive(c);
    let base = build_base(c);
    let step = build_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let ft = c.fin_to_nn(&n);
    let (f_id, f) = b.fresh_local(ft.clone());
    let (g_id, g) = b.fresh_local(ft.clone());
    let h = c.hyp_ty(&b, &n, &f, &g);
    let (h_id, hh) = b.fresh_local(h.clone());
    let rec_app = Expr::apps(
        c.nat_rec0.clone(),
        [motive, base, step, n.clone(), f.clone(), g.clone(), hh],
    );
    let r = b.mk_lam(h_id, BinderInfo::Default, h, rec_app);
    let r = b.mk_lam(g_id, BinderInfo::Default, ft.clone(), r);
    let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
    let r = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), r);
    b.finish(r)
}
