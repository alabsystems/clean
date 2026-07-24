// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Congruence lemmas: congrArg, congrFun, congrFun'.
//! (congr is in its own submodule.)

use super::context::EqCtx;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::decl_emit;
use crate::env::decl_emit::mk_apps;
use crate::env::{EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

pub(crate) fn register(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    register_congr_arg(env, ctx)?;
    register_congr_fun(env, ctx)?;
    register_congr_fun_prime(env, ctx)?;
    super::congr::register(env, ctx)?;
    Ok(())
}

/// congrArg : {α : Sort u} → {β : Sort v} → {a₁ a₂ : α} → (f : α → β) → Eq a₁ a₂ → Eq (f a₁) (f a₂)
fn register_congr_arg(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let v = Name::from_string("v");
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let eq_v_const = Expr::const_(Name::from_string("Eq"), vec![Level::param(v.clone())]);

    let congr_arg_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (beta_id, beta) = b.fresh_local(sort_v.clone());
        let (a1_id, a1_var) = b.fresh_local(alpha.clone());
        let (a2_id, a2_var) = b.fresh_local(alpha.clone());
        let f_ty = simple_arrow(&b, &alpha, &beta);
        let (f_id, f_var) = b.fresh_local(f_ty.clone());
        let eq_a1_a2 = ctx.eq(&alpha, a1_var.clone(), a2_var.clone());
        let (h_id, _) = b.fresh_local(eq_a1_a2.clone());
        let r = mk_apps(
            eq_v_const.clone(),
            vec![
                beta.clone(),
                Expr::app(f_var.clone(), a1_var.clone()),
                Expr::app(f_var.clone(), a2_var.clone()),
            ],
        );
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a1_a2, r);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty.clone(), r);
        let r = b.mk_pi(a2_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(a1_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let congr_arg_value = congr_arg_value_expr(ctx, &sort_v, &eq_v_const);

    decl_emit::add_decl(
        env,
        decl_emit::theorem(
            "congrArg",
            vec![ctx.u.clone(), v],
            congr_arg_type,
            congr_arg_value,
        ),
    )
}

fn congr_arg_value_expr(ctx: &EqCtx, sort_v: &Expr, eq_v_const: &Expr) -> Expr {
    let v = Name::from_string("v");
    let eq_refl_v_const = Expr::const_(Name::from_string("Eq.refl"), vec![Level::param(v)]);
    let eq_ndrec_uv_const = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![Level::zero(), Level::param(ctx.u.clone())],
    );

    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (beta_id, beta) = b.fresh_local(sort_v.clone());
    let (a1_id, a1_var) = b.fresh_local(alpha.clone());
    let (a2_id, a2_var) = b.fresh_local(alpha.clone());
    let f_ty = simple_arrow(&b, &alpha, &beta);
    let (f_id, f_var) = b.fresh_local(f_ty.clone());
    let eq_a1_a2 = ctx.eq(&alpha, a1_var.clone(), a2_var.clone());
    let (h_id, h_var) = b.fresh_local(eq_a1_a2.clone());
    // motive = λ (x : α), Eq.{v} β (f a₁) (f x)
    let motive = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (x_id, x_var) = c.fresh_local(alpha.clone());
        let r = mk_apps(
            eq_v_const.clone(),
            vec![
                beta.clone(),
                Expr::app(f_var.clone(), a1_var.clone()),
                Expr::app(f_var.clone(), x_var),
            ],
        );
        let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
        c.finish_child(r)
    };
    let base = Expr::app(
        Expr::app(eq_refl_v_const, beta.clone()),
        Expr::app(f_var.clone(), a1_var.clone()),
    );
    let r = mk_apps(
        eq_ndrec_uv_const,
        vec![alpha.clone(), a1_var, motive, base, a2_var, h_var],
    );
    let r = b.mk_lam(h_id, BinderInfo::Default, eq_a1_a2, r);
    let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, r);
    let r = b.mk_lam(a2_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(a1_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

/// congrFun : {α : Sort u} → {β : α → Sort v} → {f g : (x : α) → β x} → Eq f g → (a : α) → Eq (f a) (g a)
fn register_congr_fun(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let v = Name::from_string("v");
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let eq_v_const = Expr::const_(Name::from_string("Eq"), vec![Level::param(v.clone())]);
    let eq_func_const = Expr::const_(
        Name::from_string("Eq"),
        vec![Level::imax(
            Level::param(ctx.u.clone()),
            Level::param(v.clone()),
        )],
    );

    let congr_fun_type = congr_fun_type_expr(ctx, &sort_v, &eq_v_const, &eq_func_const);
    let congr_fun_value = congr_fun_value_expr(ctx, &sort_v, &eq_v_const, &eq_func_const);

    decl_emit::add_decl(
        env,
        decl_emit::theorem(
            "congrFun",
            vec![ctx.u.clone(), v],
            congr_fun_type,
            congr_fun_value,
        ),
    )
}

fn congr_fun_type_expr(
    ctx: &EqCtx,
    sort_v: &Expr,
    eq_v_const: &Expr,
    eq_func_const: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let beta_ty = dep_type_family(&b, &alpha, sort_v);
    let (beta_id, beta) = b.fresh_local(beta_ty.clone());
    let dep_func_ty = dep_func_type(&b, &alpha, &beta);
    let (f_id, f_var) = b.fresh_local(dep_func_ty.clone());
    let (g_id, g_var) = b.fresh_local(dep_func_ty.clone());
    let eq_f_g = mk_apps(
        eq_func_const.clone(),
        vec![dep_func_ty.clone(), f_var.clone(), g_var.clone()],
    );
    let (h_id, _) = b.fresh_local(eq_f_g.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    let r = mk_apps(
        eq_v_const.clone(),
        vec![
            Expr::app(beta.clone(), a_var.clone()),
            Expr::app(f_var.clone(), a_var.clone()),
            Expr::app(g_var.clone(), a_var.clone()),
        ],
    );
    let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
    let r = b.mk_pi(h_id, BinderInfo::Default, eq_f_g, r);
    let r = b.mk_pi(g_id, BinderInfo::Implicit, dep_func_ty.clone(), r);
    let r = b.mk_pi(f_id, BinderInfo::Implicit, dep_func_ty, r);
    let r = b.mk_pi(beta_id, BinderInfo::Implicit, beta_ty, r);
    let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

fn congr_fun_value_expr(
    ctx: &EqCtx,
    sort_v: &Expr,
    eq_v_const: &Expr,
    eq_func_const: &Expr,
) -> Expr {
    let v = Name::from_string("v");
    let eq_refl_v_const = Expr::const_(Name::from_string("Eq.refl"), vec![Level::param(v.clone())]);
    let eq_ndrec_func_const = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![
            Level::zero(),
            Level::imax(Level::param(ctx.u.clone()), Level::param(v)),
        ],
    );

    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let beta_ty = dep_type_family(&b, &alpha, sort_v);
    let (beta_id, beta) = b.fresh_local(beta_ty.clone());
    let dep_func_ty = dep_func_type(&b, &alpha, &beta);
    let (f_id, f_var) = b.fresh_local(dep_func_ty.clone());
    let (g_id, g_var) = b.fresh_local(dep_func_ty.clone());
    let eq_f_g = mk_apps(
        eq_func_const.clone(),
        vec![dep_func_ty.clone(), f_var.clone(), g_var.clone()],
    );
    let (h_id, h_var) = b.fresh_local(eq_f_g.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    // motive = λ (k : (x:α) → β x), @Eq.{v} (β a) (f a) (k a)
    let motive = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (k_id, k_var) = c.fresh_local(dep_func_ty.clone());
        let r = mk_apps(
            eq_v_const.clone(),
            vec![
                Expr::app(beta.clone(), a_var.clone()),
                Expr::app(f_var.clone(), a_var.clone()),
                Expr::app(k_var, a_var.clone()),
            ],
        );
        let r = c.mk_lam(k_id, BinderInfo::Default, dep_func_ty.clone(), r);
        c.finish_child(r)
    };
    let base = Expr::app(
        Expr::app(eq_refl_v_const, Expr::app(beta.clone(), a_var.clone())),
        Expr::app(f_var.clone(), a_var.clone()),
    );
    let r = mk_apps(
        eq_ndrec_func_const,
        vec![dep_func_ty.clone(), f_var, motive, base, g_var, h_var],
    );
    let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
    let r = b.mk_lam(h_id, BinderInfo::Default, eq_f_g, r);
    let r = b.mk_lam(g_id, BinderInfo::Implicit, dep_func_ty.clone(), r);
    let r = b.mk_lam(f_id, BinderInfo::Implicit, dep_func_ty, r);
    let r = b.mk_lam(beta_id, BinderInfo::Implicit, beta_ty, r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

/// congrFun' : {α : Sort u} → {β : Sort v} → {f g : α → β} → Eq f g → (a : α) → Eq (f a) (g a)
fn register_congr_fun_prime(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
    let v = Name::from_string("v");
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let eq_v_const = Expr::const_(Name::from_string("Eq"), vec![Level::param(v.clone())]);
    let eq_func_const = Expr::const_(
        Name::from_string("Eq"),
        vec![Level::imax(
            Level::param(ctx.u.clone()),
            Level::param(v.clone()),
        )],
    );

    let congr_fun_prime_type = congr_fun_prime_type_expr(ctx, &sort_v, &eq_v_const, &eq_func_const);
    let congr_fun_prime_value = congr_fun_prime_value_expr(ctx, &sort_v, &eq_func_const);

    decl_emit::add_decl(
        env,
        decl_emit::theorem(
            "congrFun'",
            vec![ctx.u.clone(), v],
            congr_fun_prime_type,
            congr_fun_prime_value,
        ),
    )
}

fn congr_fun_prime_type_expr(
    ctx: &EqCtx,
    sort_v: &Expr,
    eq_v_const: &Expr,
    eq_func_const: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (beta_id, beta) = b.fresh_local(sort_v.clone());
    let func_ty = simple_arrow(&b, &alpha, &beta);
    let (f_id, f_var) = b.fresh_local(func_ty.clone());
    let (g_id, g_var) = b.fresh_local(func_ty.clone());
    let eq_f_g = mk_apps(
        eq_func_const.clone(),
        vec![func_ty.clone(), f_var.clone(), g_var.clone()],
    );
    let (h_id, _) = b.fresh_local(eq_f_g.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    let r = mk_apps(
        eq_v_const.clone(),
        vec![
            beta.clone(),
            Expr::app(f_var.clone(), a_var.clone()),
            Expr::app(g_var.clone(), a_var.clone()),
        ],
    );
    let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
    let r = b.mk_pi(h_id, BinderInfo::Default, eq_f_g, r);
    let r = b.mk_pi(g_id, BinderInfo::Implicit, func_ty.clone(), r);
    let r = b.mk_pi(f_id, BinderInfo::Implicit, func_ty, r);
    let r = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
    let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

fn congr_fun_prime_value_expr(ctx: &EqCtx, sort_v: &Expr, eq_func_const: &Expr) -> Expr {
    let v = Name::from_string("v");
    let congr_fun_dep_const = Expr::const_(
        Name::from_string("congrFun"),
        vec![Level::param(ctx.u.clone()), Level::param(v)],
    );

    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (beta_id, beta) = b.fresh_local(sort_v.clone());
    let func_ty = simple_arrow(&b, &alpha, &beta);
    let (f_id, f_var) = b.fresh_local(func_ty.clone());
    let (g_id, g_var) = b.fresh_local(func_ty.clone());
    let eq_f_g = mk_apps(
        eq_func_const.clone(),
        vec![func_ty.clone(), f_var.clone(), g_var.clone()],
    );
    let (h_id, h_var) = b.fresh_local(eq_f_g.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    // β as constant type family: λ (_ : α), β
    let const_beta = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (x_id, _) = c.fresh_local(alpha.clone());
        let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), beta.clone());
        c.finish_child(r)
    };
    let r = mk_apps(
        congr_fun_dep_const,
        vec![alpha.clone(), const_beta, f_var, g_var, h_var, a_var],
    );
    let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
    let r = b.mk_lam(h_id, BinderInfo::Default, eq_f_g, r);
    let r = b.mk_lam(g_id, BinderInfo::Implicit, func_ty.clone(), r);
    let r = b.mk_lam(f_id, BinderInfo::Implicit, func_ty, r);
    let r = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

/// Build simple arrow type: α → β
pub(super) fn simple_arrow(b: &EnvDeclBuilder, alpha: &Expr, beta: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (x_id, _) = c.fresh_local(alpha.clone());
    let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), beta.clone());
    c.finish_child(r)
}

/// Build dependent type family: α → Sort v
pub(super) fn dep_type_family(b: &EnvDeclBuilder, alpha: &Expr, sort_v: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (x_id, _) = c.fresh_local(alpha.clone());
    let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), sort_v.clone());
    c.finish_child(r)
}

/// Build dependent function type: (x : α) → β x
pub(super) fn dep_func_type(b: &EnvDeclBuilder, alpha: &Expr, beta: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (x_id, x_var) = c.fresh_local(alpha.clone());
    let r = Expr::app(beta.clone(), x_var);
    let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
    c.finish_child(r)
}
