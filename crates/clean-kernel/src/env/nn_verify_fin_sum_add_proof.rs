// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.sum_add`.
//!
//! The proof is induction over the faithful `Fin.sum` carrier. The base case
//! closes by `Rat.add_zero 0`; the step case consumes the induction
//! hypothesis and reassociates/reorders four Rat additions with checked
//! `Rat.add_assoc` and `Rat.add_comm`.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FinSumAddConsts {
    base: FinSumConsts,
    nat_zero: Expr,
    nat_succ: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    rat_add_zero: Expr,
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
}

impl FinSumAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            base: FinSumConsts::new(),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            rat_add_zero: Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            rat_add_assoc: Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
            rat_add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
        }
    }

    fn add_rat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.base.rat_add.clone(), lhs), rhs)
    }

    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::app(Expr::app(self.base.fin_sum.clone(), n), f)
    }

    fn eq_rat(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.base.rat_eq(lhs, rhs)
    }

    fn fin_to_rat(&self, n: Expr) -> Expr {
        self.base.fin_to_rat(n)
    }
}

fn pointwise_add(c: &FinSumAddConsts, parent: &EnvDeclBuilder, n: Expr, f: Expr, g: Expr) -> Expr {
    let fin_n = Expr::app(c.base.fin.clone(), n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.add_rat(Expr::app(f, i.clone()), Expr::app(g, i));
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

fn cast_succ_fn(c: &FinSumAddConsts, parent: &EnvDeclBuilder, k: Expr, f: Expr) -> Expr {
    let fin_k = Expr::app(c.base.fin.clone(), k.clone());
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_k.clone());
    let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), k), i);
    let body = Expr::app(f, cast_i);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_k, body);
    b.finish_child(lam)
}

fn add_right_fn(c: &FinSumAddConsts, parent: &EnvDeclBuilder, right: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.base.rat.clone());
    let body = c.add_rat(x, right);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.base.rat.clone(), body);
    b.finish_child(lam)
}

fn add_outer_right_fn(c: &FinSumAddConsts, parent: &EnvDeclBuilder, d: Expr) -> Expr {
    add_right_fn(c, parent, d)
}

fn add_left_then_outer_right_fn(
    c: &FinSumAddConsts,
    parent: &EnvDeclBuilder,
    left: Expr,
    right: Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.base.rat.clone());
    let body = c.add_rat(c.add_rat(left, x), right);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.base.rat.clone(), body);
    b.finish_child(lam)
}

fn build_type(c: &FinSumAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let lhs = c.sum(
        n.clone(),
        pointwise_add(c, &b, n.clone(), f.clone(), g.clone()),
    );
    let rhs = c.add_rat(c.sum(n.clone(), f), c.sum(n, g));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_type, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), ty);
    b.finish(ty)
}

fn build_motive(c: &FinSumAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(k.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let lhs = c.sum(
        k.clone(),
        pointwise_add(c, &b, k.clone(), f.clone(), g.clone()),
    );
    let rhs = c.add_rat(c.sum(k.clone(), f), c.sum(k, g));
    let body = c.eq_rat(lhs, rhs);
    let pi_g = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), body);
    let pi_f = b.mk_pi(f_id, BinderInfo::Default, f_type, pi_g);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), pi_f);
    b.finish(lam)
}

fn build_base(c: &FinSumAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let f_type = c.fin_to_rat(c.nat_zero.clone());
    let (f_id, _f) = b.fresh_local(f_type.clone());
    let (g_id, _g) = b.fresh_local(f_type.clone());
    let add_zero_zero = c.add_rat(c.base.rat_zero.clone(), c.base.rat_zero.clone());
    let h = Expr::app(c.rat_add_zero.clone(), c.base.rat_zero.clone());
    let proof = Expr::apps(
        c.eq_symm.clone(),
        [
            c.base.rat.clone(),
            add_zero_zero,
            c.base.rat_zero.clone(),
            h,
        ],
    );
    let val = b.mk_lam(g_id, BinderInfo::Default, f_type.clone(), proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type, val);
    b.finish(val)
}

fn congr_rat(c: &FinSumAddConsts, alpha: Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
    Expr::apps(c.congr_arg.clone(), [alpha, c.base.rat.clone(), a, b, f, h])
}

fn eq_trans(c: &FinSumAddConsts, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(c.eq_trans.clone(), [c.base.rat.clone(), a, b, d, h1, h2])
}

fn eq_symm(c: &FinSumAddConsts, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c.eq_symm.clone(), [c.base.rat.clone(), a, b, h])
}

fn build_four_add_rearrange(
    c: &FinSumAddConsts,
    parent: &EnvDeclBuilder,
    a: Expr,
    b: Expr,
    x: Expr,
    d: Expr,
) -> Expr {
    let ab = c.add_rat(a.clone(), b.clone());
    let xd = c.add_rat(x.clone(), d.clone());
    let ax = c.add_rat(a.clone(), x.clone());
    let bx = c.add_rat(b.clone(), x.clone());
    let xb = c.add_rat(x.clone(), b.clone());
    let mid0 = c.add_rat(ab.clone(), xd.clone());
    let mid1 = c.add_rat(c.add_rat(ab.clone(), x.clone()), d.clone());
    let mid2 = c.add_rat(c.add_rat(a.clone(), bx.clone()), d.clone());
    let mid3 = c.add_rat(c.add_rat(a.clone(), xb.clone()), d.clone());
    let mid4 = c.add_rat(c.add_rat(ax.clone(), b.clone()), d.clone());
    let target = c.add_rat(ax.clone(), c.add_rat(b.clone(), d.clone()));

    let assoc_ab_x_d = Expr::apps(c.rat_add_assoc.clone(), [ab.clone(), x.clone(), d.clone()]);
    let step1 = eq_symm(c, mid1.clone(), mid0.clone(), assoc_ab_x_d);

    let assoc_a_b_x = Expr::apps(c.rat_add_assoc.clone(), [a.clone(), b.clone(), x.clone()]);
    let step2_fn = add_outer_right_fn(c, parent, d.clone());
    let step2 = congr_rat(
        c,
        c.base.rat.clone(),
        c.add_rat(ab, x.clone()),
        c.add_rat(a.clone(), bx),
        step2_fn,
        assoc_a_b_x,
    );

    let comm_b_x = Expr::apps(c.rat_add_comm.clone(), [b.clone(), x.clone()]);
    let step3_fn = add_left_then_outer_right_fn(c, parent, a.clone(), d.clone());
    let step3 = congr_rat(
        c,
        c.base.rat.clone(),
        c.add_rat(b.clone(), x.clone()),
        xb.clone(),
        step3_fn,
        comm_b_x,
    );

    let assoc_a_x_b = Expr::apps(c.rat_add_assoc.clone(), [a.clone(), x.clone(), b.clone()]);
    let assoc_a_x_b_rev = eq_symm(
        c,
        c.add_rat(ax.clone(), b.clone()),
        c.add_rat(a.clone(), xb.clone()),
        assoc_a_x_b,
    );
    let step4_fn = add_outer_right_fn(c, parent, d.clone());
    let step4 = congr_rat(
        c,
        c.base.rat.clone(),
        c.add_rat(a.clone(), xb),
        c.add_rat(ax.clone(), b.clone()),
        step4_fn,
        assoc_a_x_b_rev,
    );

    let step5 = Expr::apps(c.rat_add_assoc.clone(), [ax, b, d]);

    let chain12 = eq_trans(c, mid0.clone(), mid1.clone(), mid2.clone(), step1, step2);
    let chain123 = eq_trans(c, mid0.clone(), mid2.clone(), mid3.clone(), chain12, step3);
    let chain1234 = eq_trans(c, mid0.clone(), mid3, mid4.clone(), chain123, step4);
    eq_trans(c, mid0, mid4, target, chain1234, step5)
}

fn build_step(c: &FinSumAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let f_type_k = c.fin_to_rat(k.clone());
    let (ih_f_id, ih_f) = b.fresh_local(f_type_k.clone());
    let (ih_g_id, ih_g) = b.fresh_local(f_type_k.clone());
    let ih_lhs = c.sum(
        k.clone(),
        pointwise_add(c, &b, k.clone(), ih_f.clone(), ih_g.clone()),
    );
    let ih_rhs = c.add_rat(c.sum(k.clone(), ih_f), c.sum(k.clone(), ih_g));
    let ih_body = c.eq_rat(ih_lhs, ih_rhs);
    let ih_type = b.mk_pi(ih_g_id, BinderInfo::Default, f_type_k.clone(), ih_body);
    let ih_type = b.mk_pi(ih_f_id, BinderInfo::Default, f_type_k, ih_type);
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_k = Expr::app(c.nat_succ.clone(), k.clone());
    let f_type_succ = c.fin_to_rat(succ_k.clone());
    let (f_id, f) = b.fresh_local(f_type_succ.clone());
    let (g_id, g) = b.fresh_local(f_type_succ.clone());
    let f_cast = cast_succ_fn(c, &b, k.clone(), f.clone());
    let g_cast = cast_succ_fn(c, &b, k.clone(), g.clone());
    let fg_cast = pointwise_add(c, &b, k.clone(), f_cast.clone(), g_cast.clone());
    let sum_fg = c.sum(k.clone(), fg_cast);
    let sum_f = c.sum(k.clone(), f_cast.clone());
    let sum_g = c.sum(k.clone(), g_cast.clone());
    let f_last = Expr::app(f.clone(), Expr::app(c.fin_last.clone(), k.clone()));
    let g_last = Expr::app(g.clone(), Expr::app(c.fin_last.clone(), k));
    let last_sum = c.add_rat(f_last.clone(), g_last.clone());

    let lhs = c.add_rat(sum_fg.clone(), last_sum.clone());
    let mid0 = c.add_rat(c.add_rat(sum_f.clone(), sum_g.clone()), last_sum);
    let rhs = c.add_rat(
        c.add_rat(sum_f.clone(), f_last.clone()),
        c.add_rat(sum_g.clone(), g_last.clone()),
    );

    let ih_app = Expr::app(Expr::app(ih, f_cast), g_cast);
    let step1_fn = add_right_fn(c, &b, c.add_rat(f_last.clone(), g_last.clone()));
    let step1 = congr_rat(
        c,
        c.base.rat.clone(),
        sum_fg,
        c.add_rat(sum_f.clone(), sum_g.clone()),
        step1_fn,
        ih_app,
    );
    let step2 = build_four_add_rearrange(c, &b, sum_f, sum_g, f_last, g_last);
    let proof = eq_trans(c, lhs, mid0, rhs, step1, step2);

    let val = b.mk_lam(g_id, BinderInfo::Default, f_type_succ.clone(), proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type_succ, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), val);
    b.finish(val)
}

fn build_value(c: &FinSumAddConsts) -> Expr {
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
    /// Register `Fin.sum_add` as a kernel-checked theorem.
    pub(crate) fn register_fin_sum_add_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.init_rat_field_inst()?;

        let c = FinSumAddConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}
