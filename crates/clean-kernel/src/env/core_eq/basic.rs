// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic Eq lemmas: rfl, Eq.symm, Eq.trans.

use super::context::EqCtx;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::decl_emit;
use crate::env::{EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) fn register(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    register_rfl(env, ctx)?;
    register_symm(env, ctx)?;
    register_trans(env, ctx)?;
    Ok(())
}

/// rfl : ∀ {α : Sort u} {a : α}, Eq a a
fn register_rfl(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let rfl_type = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a_var) = b.fresh_local(ctx.sort_u.clone());
        let (x_id, x_var) = b.fresh_local(a_var.clone());
        let r = ctx.eq(&a_var, x_var.clone(), x_var);
        let r = b.mk_pi(x_id, BinderInfo::Implicit, a_var.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };
    let rfl_value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a_var) = b.fresh_local(ctx.sort_u.clone());
        let (x_id, x_var) = b.fresh_local(a_var.clone());
        let r = ctx.refl(&a_var, x_var);
        let r = b.mk_lam(x_id, BinderInfo::Implicit, a_var.clone(), r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };
    decl_emit::add_decl(
        env,
        decl_emit::reducible_def("rfl", vec![ctx.u.clone()], rfl_type, rfl_value),
    )
}

/// Eq.symm : ∀ {α : Sort u} {a b : α}, Eq a b → Eq b a
fn register_symm(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let eq_rec_const = Expr::const_(
        Name::from_string("Eq.rec"),
        vec![Level::zero(), Level::param(ctx.u.clone())],
    );

    let symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let r = ctx.eq(&alpha, bb_var, a_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let symm_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        // motive = λ (x : α) (_ : Eq a x), Eq x a
        let motive = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (x_id, x_var) = c.fresh_local(alpha.clone());
            let eq_a_x = ctx.eq(&alpha, a_var.clone(), x_var.clone());
            let (hp_id, _) = c.fresh_local(eq_a_x.clone());
            let r = ctx.eq(&alpha, x_var, a_var.clone());
            let r = c.mk_lam(hp_id, BinderInfo::Default, eq_a_x, r);
            let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
            c.finish_child(r)
        };
        let base = ctx.refl(&alpha, a_var.clone());
        // Eq.rec {α} {a} {motive} base {b} h
        let r = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(eq_rec_const.clone(), alpha.clone()), a_var),
                        motive,
                    ),
                    base,
                ),
                bb_var,
            ),
            h_var,
        );
        let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_lam(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::theorem("Eq.symm", vec![ctx.u.clone()], symm_type, symm_value),
    )
}

/// Eq.trans : ∀ {α : Sort u} {a b c : α}, Eq a b → Eq b c → Eq a c
fn register_trans(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let eq_rec_const = Expr::const_(
        Name::from_string("Eq.rec"),
        vec![Level::zero(), Level::param(ctx.u.clone())],
    );

    let trans_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let (c_id, c_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h1_id, _) = b.fresh_local(eq_a_b.clone());
        let eq_b_c = ctx.eq(&alpha, bb_var, c_var.clone());
        let (h2_id, _) = b.fresh_local(eq_b_c.clone());
        let r = ctx.eq(&alpha, a_var, c_var);
        let r = b.mk_pi(h2_id, BinderInfo::Default, eq_b_c, r);
        let r = b.mk_pi(h1_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let trans_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let (c_id, c_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h1_id, h1_var) = b.fresh_local(eq_a_b.clone());
        let eq_b_c = ctx.eq(&alpha, bb_var.clone(), c_var.clone());
        let (h2_id, h2_var) = b.fresh_local(eq_b_c.clone());
        // motive = λ (x : α) (_ : Eq b x), Eq a x
        let motive = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (x_id, x_var) = c.fresh_local(alpha.clone());
            let eq_b_x = ctx.eq(&alpha, bb_var.clone(), x_var.clone());
            let (hp_id, _) = c.fresh_local(eq_b_x.clone());
            let r = ctx.eq(&alpha, a_var.clone(), x_var);
            let r = c.mk_lam(hp_id, BinderInfo::Default, eq_b_x, r);
            let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
            c.finish_child(r)
        };
        // Eq.rec {α} {b} {motive} h1 {c} h2
        let r = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(eq_rec_const, alpha.clone()), bb_var),
                        motive,
                    ),
                    h1_var,
                ),
                c_var,
            ),
            h2_var,
        );
        let r = b.mk_lam(h2_id, BinderInfo::Default, eq_b_c, r);
        let r = b.mk_lam(h1_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_lam(c_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::theorem("Eq.trans", vec![ctx.u.clone()], trans_type, trans_value),
    )
}
