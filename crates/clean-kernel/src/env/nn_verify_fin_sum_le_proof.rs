// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.sum_le`.
//!
//! The proof is induction over the faithful `Fin.sum` carrier. The zero case
//! closes with `Rat.le_refl Rat.zero`. The successor case applies the
//! induction hypothesis to the cast-prefix functions and combines the prefix
//! and last-index inequalities with the standard Rat addition monotonicity
//! chain built from `Rat.add_le_add_left`, `Rat.add_comm`, `Rat.le_trans`,
//! and `Eq.subst`.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FinSumLeConsts {
    base: FinSumConsts,
    nat_zero: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec: Expr,
    eq_subst: Expr,
    rat_le_refl: Expr,
    rat_le_trans: Expr,
    rat_add_comm: Expr,
    rat_add_le_add_left: Expr,
}

impl FinSumLeConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            base: FinSumConsts::new(),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
            rat_le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            rat_le_trans: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            rat_add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
            rat_add_le_add_left: Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]),
        }
    }

    fn add_rat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.base.rat_add.clone(), lhs), rhs)
    }

    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::app(Expr::app(self.base.fin_sum.clone(), n), f)
    }

    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.base.rat_le(lhs, rhs)
    }

    fn fin_to_rat(&self, n: Expr) -> Expr {
        self.base.fin_to_rat(n)
    }
}

fn cast_succ_fn(c: &FinSumLeConsts, parent: &EnvDeclBuilder, k: Expr, f: Expr) -> Expr {
    let fin_k = Expr::app(c.base.fin.clone(), k.clone());
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_k.clone());
    let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), k), i);
    let body = Expr::app(f, cast_i);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_k, body);
    b.finish_child(lam)
}

fn pointwise_le_type(
    c: &FinSumLeConsts,
    parent: &EnvDeclBuilder,
    n: Expr,
    f: Expr,
    g: Expr,
) -> Expr {
    let fin_n = Expr::app(c.base.fin.clone(), n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.rat_le(Expr::app(f, i.clone()), Expr::app(g, i));
    let pi = b.mk_pi(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(pi)
}

fn eq_subst_rat(
    c: &FinSumLeConsts,
    motive: Expr,
    a: Expr,
    b: Expr,
    h_eq: Expr,
    h_motive_a: Expr,
) -> Expr {
    Expr::apps(
        c.eq_subst.clone(),
        [c.base.rat.clone(), motive, a, b, h_eq, h_motive_a],
    )
}

fn build_add_le_add(
    c: &FinSumLeConsts,
    parent: &EnvDeclBuilder,
    a1: Expr,
    b1: Expr,
    a2: Expr,
    b2: Expr,
    h1: Expr,
    h2: Expr,
) -> Expr {
    let a2_plus_a1 = c.add_rat(a2.clone(), a1.clone());
    let a1_plus_a2 = c.add_rat(a1.clone(), a2.clone());
    let a2_plus_b1 = c.add_rat(a2.clone(), b1.clone());
    let b1_plus_a2 = c.add_rat(b1.clone(), a2.clone());
    let b1_plus_b2 = c.add_rat(b1.clone(), b2.clone());

    let step_a = Expr::apps(
        c.rat_add_le_add_left.clone(),
        [a1.clone(), b1.clone(), h1, a2.clone()],
    );
    let comm1 = Expr::apps(c.rat_add_comm.clone(), [a2.clone(), a1.clone()]);
    let motive1 = {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = b.fresh_local(c.base.rat.clone());
        let body = c.rat_le(x, a2_plus_b1.clone());
        let lam = b.mk_lam(x_id, BinderInfo::Default, c.base.rat.clone(), body);
        b.finish_child(lam)
    };
    let step_b = eq_subst_rat(c, motive1, a2_plus_a1, a1_plus_a2.clone(), comm1, step_a);

    let comm2 = Expr::apps(c.rat_add_comm.clone(), [a2.clone(), b1.clone()]);
    let motive2 = {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = b.fresh_local(c.base.rat.clone());
        let body = c.rat_le(a1_plus_a2.clone(), x);
        let lam = b.mk_lam(x_id, BinderInfo::Default, c.base.rat.clone(), body);
        b.finish_child(lam)
    };
    let step_c = eq_subst_rat(c, motive2, a2_plus_b1, b1_plus_a2.clone(), comm2, step_b);

    let step_d = Expr::apps(c.rat_add_le_add_left.clone(), [a2.clone(), b2, h2, b1]);
    Expr::apps(
        c.rat_le_trans.clone(),
        [a1_plus_a2, b1_plus_a2, b1_plus_b2, step_c, step_d],
    )
}

fn build_type(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let hyp = pointwise_le_type(c, &b, n.clone(), f.clone(), g.clone());
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let concl = c.rat_le(c.sum(n.clone(), f), c.sum(n, g));
    let ty = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let ty = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), ty);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_type, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), ty);
    b.finish(ty)
}

fn build_motive(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(k.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let hyp = pointwise_le_type(c, &b, k.clone(), f.clone(), g.clone());
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let concl = c.rat_le(c.sum(k.clone(), f), c.sum(k, g));
    let pi_h = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let pi_g = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), pi_h);
    let pi_f = b.mk_pi(f_id, BinderInfo::Default, f_type, pi_g);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), pi_f);
    b.finish(lam)
}

fn build_base(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let f_type = c.fin_to_rat(c.nat_zero.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let hyp = pointwise_le_type(c, &b, c.nat_zero.clone(), f, g);
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let proof = Expr::app(c.rat_le_refl.clone(), c.base.rat_zero.clone());
    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, f_type.clone(), val);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type, val);
    b.finish(val)
}

fn build_step(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let f_type_k = c.fin_to_rat(k.clone());
    let (ih_f_id, ih_f) = b.fresh_local(f_type_k.clone());
    let (ih_g_id, ih_g) = b.fresh_local(f_type_k.clone());
    let ih_hyp = pointwise_le_type(c, &b, k.clone(), ih_f.clone(), ih_g.clone());
    let (ih_h_id, _ih_h) = b.fresh_local(ih_hyp.clone());
    let ih_concl = c.rat_le(c.sum(k.clone(), ih_f), c.sum(k.clone(), ih_g));
    let ih_type = b.mk_pi(ih_h_id, BinderInfo::Default, ih_hyp, ih_concl);
    let ih_type = b.mk_pi(ih_g_id, BinderInfo::Default, f_type_k.clone(), ih_type);
    let ih_type = b.mk_pi(ih_f_id, BinderInfo::Default, f_type_k, ih_type);
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let f_type_succ = c.fin_to_rat(succ_k.clone());
    let (f_id, f) = b.fresh_local(f_type_succ.clone());
    let (g_id, g) = b.fresh_local(f_type_succ.clone());
    let hyp = pointwise_le_type(c, &b, succ_k, f.clone(), g.clone());
    let (h_id, h) = b.fresh_local(hyp.clone());

    let f_cast = cast_succ_fn(c, &b, k.clone(), f.clone());
    let g_cast = cast_succ_fn(c, &b, k.clone(), g.clone());
    let h_cast = {
        let fin_k = Expr::app(c.base.fin.clone(), k.clone());
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = hb.fresh_local(fin_k.clone());
        let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), k.clone()), i);
        let body = Expr::app(h.clone(), cast_i);
        let lam = hb.mk_lam(i_id, BinderInfo::Default, fin_k, body);
        hb.finish_child(lam)
    };
    let prefix_le = Expr::app(
        Expr::app(Expr::app(ih, f_cast.clone()), g_cast.clone()),
        h_cast,
    );

    let f_last = Expr::app(f, Expr::app(c.fin_last.clone(), k.clone()));
    let g_last = Expr::app(g, Expr::app(c.fin_last.clone(), k.clone()));
    let last_le = Expr::app(h, Expr::app(c.fin_last.clone(), k.clone()));

    let proof = build_add_le_add(
        c,
        &b,
        c.sum(k.clone(), f_cast),
        c.sum(k, g_cast),
        f_last,
        g_last,
        prefix_le,
        last_le,
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, f_type_succ.clone(), val);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type_succ, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), val);
    b.finish(val)
}

fn build_value(c: &FinSumLeConsts) -> Expr {
    let motive = build_motive(c);
    let base = build_base(c);
    let step = build_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), body);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.sum_le` as a kernel-checked theorem.
    pub(crate) fn register_fin_sum_le_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.init_rat_field_inst()?;
        self.init_rat_linear_order()?;
        self.init_rat_ordered_field_axioms()?;

        let c = FinSumLeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}
