// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Fin.sum_nonneg`.
//!
//! The proof reuses the checked `Fin.sum_le` theorem with the zero function,
//! then rewrites `Fin.sum n (fun _ => Rat.zero)` to `Rat.zero` via the checked
//! `Fin.sum_zero_fn` theorem.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FinSumNonnegConsts {
    base: FinSumConsts,
    eq_subst: Expr,
    fin_sum_le: Expr,
    fin_sum_zero_fn: Expr,
}

impl FinSumNonnegConsts {
    fn new() -> Self {
        Self {
            base: FinSumConsts::new(),
            eq_subst: Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
            fin_sum_le: Expr::const_(Name::from_string("Fin.sum_le"), vec![]),
            fin_sum_zero_fn: Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]),
        }
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

fn zero_fn_of(c: &FinSumNonnegConsts, parent: &EnvDeclBuilder, n: Expr) -> Expr {
    let fin_n = Expr::app(c.base.fin.clone(), n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, _i) = b.fresh_local(fin_n.clone());
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, c.base.rat_zero.clone());
    b.finish_child(lam)
}

fn pointwise_nonneg_type(
    c: &FinSumNonnegConsts,
    parent: &EnvDeclBuilder,
    n: Expr,
    f: Expr,
) -> Expr {
    let fin_n = Expr::app(c.base.fin.clone(), n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.rat_le(c.base.rat_zero.clone(), Expr::app(f, i));
    let pi = b.mk_pi(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(pi)
}

fn le_motive(c: &FinSumNonnegConsts, parent: &EnvDeclBuilder, rhs: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.base.rat.clone());
    let body = c.rat_le(x, rhs);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.base.rat.clone(), body);
    b.finish_child(lam)
}

fn eq_subst_rat(
    c: &FinSumNonnegConsts,
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

fn build_type(c: &FinSumNonnegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let hyp = pointwise_nonneg_type(c, &b, n.clone(), f.clone());
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let concl = c.rat_le(c.base.rat_zero.clone(), c.sum(n, f));
    let ty = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let ty = b.mk_pi(f_id, BinderInfo::Default, f_type, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), ty);
    b.finish(ty)
}

fn build_value(c: &FinSumNonnegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let f_type = c.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let hyp = pointwise_nonneg_type(c, &b, n.clone(), f.clone());
    let (h_id, h) = b.fresh_local(hyp.clone());

    let zero_fn = zero_fn_of(c, &b, n.clone());
    let sum_zero = c.sum(n.clone(), zero_fn.clone());
    let sum_f = c.sum(n.clone(), f.clone());
    let sum_zero_le_sum_f = Expr::apps(c.fin_sum_le.clone(), [n.clone(), zero_fn, f, h]);
    let sum_zero_eq_zero = Expr::app(c.fin_sum_zero_fn.clone(), n);
    let motive = le_motive(c, &b, sum_f);
    let proof = eq_subst_rat(
        c,
        motive,
        sum_zero,
        c.base.rat_zero.clone(),
        sum_zero_eq_zero,
        sum_zero_le_sum_f,
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.sum_nonneg` as a kernel-checked theorem.
    pub(super) fn register_fin_sum_nonneg_theorem(
        &mut self,
        c: &FinSumConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.init_rat_field_inst()?;
        self.init_rat_linear_order()?;
        self.init_rat_ordered_field_axioms()?;
        self.register_fin_sum_le_theorem()?;
        if self
            .get_const(&Name::from_string("Fin.sum_zero_fn"))
            .is_none()
        {
            self.register_fin_sum_zero_fn(c)?;
        }

        let c = FinSumNonnegConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }
}
