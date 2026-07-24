// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Eq transport declarations: Eq.ndrec, Eq.ndrecOn, Eq.subst, cast, Eq.mp, Eq.mpr.

use super::context::EqCtx;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::decl_emit;
use crate::env::decl_emit::mk_apps;
use crate::env::{EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

pub(crate) fn register(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    register_ndrec(env, ctx)?;
    register_ndrec_on(env, ctx)?;
    register_subst(env, ctx)?;
    register_cast(env, ctx)?;
    register_mp(env, ctx)?;
    register_mpr(env, ctx)?;
    Ok(())
}

/// Eq.ndrec : {α : Sort u} → {a : α} → {motive : α → Sort v} → motive a → {b : α} → Eq a b → motive b
fn register_ndrec(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let v = Name::from_string("v");
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let eq_rec_const = Expr::const_(
        Name::from_string("Eq.rec"),
        vec![Level::param(v.clone()), Level::param(ctx.u.clone())],
    );

    let ndrec_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = nondep_motive_type(&b, &alpha, &sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let minor_ty = Expr::app(mot_var.clone(), a_var.clone());
        let (m_id, _) = b.fresh_local(minor_ty.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let r = Expr::app(mot_var, bb_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(m_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let ndrec_value = ndrec_value_expr(ctx, &sort_v, &eq_rec_const);

    decl_emit::add_decl(
        env,
        decl_emit::reducible_def("Eq.ndrec", vec![v, ctx.u.clone()], ndrec_type, ndrec_value),
    )
}

fn ndrec_value_expr(ctx: &EqCtx, sort_v: &Expr, eq_rec_const: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    let motive_ty = nondep_motive_type(&b, &alpha, sort_v);
    let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
    let minor_ty = Expr::app(mot_var.clone(), a_var.clone());
    let (m_id, m_var) = b.fresh_local(minor_ty.clone());
    let (bb_id, bb_var) = b.fresh_local(alpha.clone());
    let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
    let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
    // wrapped_motive = λ (x : α) (_ : Eq a x), motive x
    let wrapped_motive = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (x_id, x_var) = c.fresh_local(alpha.clone());
        let eq_a_x = ctx.eq(&alpha, a_var.clone(), x_var.clone());
        let (hp_id, _) = c.fresh_local(eq_a_x.clone());
        let r = Expr::app(mot_var.clone(), x_var);
        let r = c.mk_lam(hp_id, BinderInfo::Default, eq_a_x, r);
        let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
        c.finish_child(r)
    };
    let r = mk_apps(
        eq_rec_const.clone(),
        vec![alpha.clone(), a_var, wrapped_motive, m_var, bb_var, h_var],
    );
    let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
    let r = b.mk_lam(bb_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(m_id, BinderInfo::Default, minor_ty, r);
    let r = b.mk_lam(mot_id, BinderInfo::Implicit, motive_ty, r);
    let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

/// Eq.ndrecOn : {α : Sort u} → {a : α} → {motive : α → Sort v} → {b : α} → Eq a b → motive a → motive b
fn register_ndrec_on(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let v = Name::from_string("v");
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let eq_ndrec_const = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![Level::param(v.clone()), Level::param(ctx.u.clone())],
    );

    let ndrec_on_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = nondep_motive_type(&b, &alpha, &sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let minor_ty = Expr::app(mot_var.clone(), a_var.clone());
        let (m_id, _) = b.fresh_local(minor_ty.clone());
        let r = Expr::app(mot_var, bb_var);
        let r = b.mk_pi(m_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let ndrec_on_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = nondep_motive_type(&b, &alpha, &sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        let minor_ty = Expr::app(mot_var.clone(), a_var.clone());
        let (m_id, m_var) = b.fresh_local(minor_ty.clone());
        let r = mk_apps(
            eq_ndrec_const,
            vec![alpha.clone(), a_var, mot_var, m_var, bb_var, h_var],
        );
        let r = b.mk_lam(m_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_lam(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(mot_id, BinderInfo::Implicit, motive_ty, r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::reducible_def(
            "Eq.ndrecOn",
            vec![v, ctx.u.clone()],
            ndrec_on_type,
            ndrec_on_value,
        ),
    )
}

/// Eq.subst : {α : Sort u} → {motive : α → Prop} → {a b : α} → Eq a b → motive a → motive b
fn register_subst(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let eq_subst_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let motive_ty = nondep_motive_type(&b, &alpha, &ctx.prop);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let minor_ty = Expr::app(mot_var.clone(), a_var.clone());
        let (m_id, _) = b.fresh_local(minor_ty.clone());
        let r = Expr::app(mot_var, bb_var);
        let r = b.mk_pi(m_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let eq_subst_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let motive_ty = nondep_motive_type(&b, &alpha, &ctx.prop);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        let minor_ty = Expr::app(mot_var.clone(), a_var.clone());
        let (m_id, m_var) = b.fresh_local(minor_ty.clone());
        let eq_ndrec_subst = Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![Level::zero(), Level::param(ctx.u.clone())],
        );
        let r = mk_apps(
            eq_ndrec_subst,
            vec![alpha.clone(), a_var, mot_var, m_var, bb_var, h_var],
        );
        let r = b.mk_lam(m_id, BinderInfo::Default, minor_ty, r);
        let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_lam(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(mot_id, BinderInfo::Implicit, motive_ty, r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::theorem(
            "Eq.subst",
            vec![ctx.u.clone()],
            eq_subst_type,
            eq_subst_value,
        ),
    )
}

/// cast : {α β : Sort u} → Eq α β → α → β
fn register_cast(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let eq_succ_u_const = Expr::const_(
        Name::from_string("Eq"),
        vec![Level::succ(Level::param(ctx.u.clone()))],
    );
    let eq_ndrec_succ_const = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![
            Level::param(ctx.u.clone()),
            Level::succ(Level::param(ctx.u.clone())),
        ],
    );

    let cast_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let eq_a_b = mk_apps(
            eq_succ_u_const.clone(),
            vec![ctx.sort_u.clone(), alpha.clone(), beta.clone()],
        );
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let (a_id, _) = b.fresh_local(alpha.clone());
        let r = beta;
        let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let cast_value = cast_value_expr(ctx, &eq_succ_u_const, &eq_ndrec_succ_const);

    decl_emit::add_decl(
        env,
        decl_emit::reducible_def("cast", vec![ctx.u.clone()], cast_type, cast_value),
    )
}

fn cast_value_expr(ctx: &EqCtx, eq_succ_u_const: &Expr, eq_ndrec_succ_const: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
    let eq_a_b = mk_apps(
        eq_succ_u_const.clone(),
        vec![ctx.sort_u.clone(), alpha.clone(), beta.clone()],
    );
    let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    // motive = λ (γ : Sort u), γ
    let motive = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (g_id, g_var) = c.fresh_local(ctx.sort_u.clone());
        let r = c.mk_lam(g_id, BinderInfo::Default, ctx.sort_u.clone(), g_var);
        c.finish_child(r)
    };
    let r = mk_apps(
        eq_ndrec_succ_const.clone(),
        vec![
            ctx.sort_u.clone(),
            alpha.clone(),
            motive,
            a_var,
            beta,
            h_var,
        ],
    );
    let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
    let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
    let r = b.mk_lam(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

/// Eq.mp : {α β : Sort u} → Eq α β → α → β
fn register_mp(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let eq_succ_u_const = Expr::const_(
        Name::from_string("Eq"),
        vec![Level::succ(Level::param(ctx.u.clone()))],
    );
    let cast_const = Expr::const_(Name::from_string("cast"), vec![Level::param(ctx.u.clone())]);

    let eq_mp_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let eq_a_b = mk_apps(
            eq_succ_u_const.clone(),
            vec![ctx.sort_u.clone(), alpha.clone(), beta.clone()],
        );
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let (aa_id, _) = b.fresh_local(alpha.clone());
        let r = beta;
        let r = b.mk_pi(aa_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let eq_mp_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let eq_a_b = mk_apps(
            eq_succ_u_const,
            vec![ctx.sort_u.clone(), alpha.clone(), beta.clone()],
        );
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        let (aa_id, aa_var) = b.fresh_local(alpha.clone());
        let r = mk_apps(cast_const, vec![alpha.clone(), beta, h_var, aa_var]);
        let r = b.mk_lam(aa_id, BinderInfo::Default, alpha, r);
        let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::reducible_def("Eq.mp", vec![ctx.u.clone()], eq_mp_type, eq_mp_value),
    )
}

/// Eq.mpr : {α β : Sort u} → Eq α β → β → α
fn register_mpr(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let eq_succ_u_const = Expr::const_(
        Name::from_string("Eq"),
        vec![Level::succ(Level::param(ctx.u.clone()))],
    );
    let cast_const = Expr::const_(Name::from_string("cast"), vec![Level::param(ctx.u.clone())]);
    let eq_symm_const = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::param(ctx.u.clone()))],
    );

    let eq_mpr_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let eq_a_b = mk_apps(
            eq_succ_u_const.clone(),
            vec![ctx.sort_u.clone(), alpha.clone(), beta.clone()],
        );
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let (bb_id, _) = b.fresh_local(beta.clone());
        let r = alpha.clone();
        let r = b.mk_pi(bb_id, BinderInfo::Default, beta.clone(), r);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let eq_mpr_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let eq_a_b = mk_apps(
            eq_succ_u_const,
            vec![ctx.sort_u.clone(), alpha.clone(), beta.clone()],
        );
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        let (bb_id, bb_var) = b.fresh_local(beta.clone());
        // Eq.symm {Sort u} {α} {β} h
        let symm_h = mk_apps(
            eq_symm_const,
            vec![ctx.sort_u.clone(), alpha.clone(), beta.clone(), h_var],
        );
        let beta_ty = beta.clone();
        let r = mk_apps(cast_const, vec![beta, alpha, symm_h, bb_var]);
        let r = b.mk_lam(bb_id, BinderInfo::Default, beta_ty, r);
        let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::reducible_def("Eq.mpr", vec![ctx.u.clone()], eq_mpr_type, eq_mpr_value),
    )
}

/// Build the non-dependent motive type: α → result_sort
fn nondep_motive_type(b: &EnvDeclBuilder, alpha: &Expr, result_sort: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (x_id, _) = c.fresh_local(alpha.clone());
    let r = c.mk_pi(
        x_id,
        BinderInfo::Default,
        alpha.clone(),
        result_sort.clone(),
    );
    c.finish_child(r)
}
