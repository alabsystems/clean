// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `congr` lemma (full congruence for non-dependent function application).

use super::congruence::simple_arrow;
use super::context::EqCtx;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::decl_emit;
use crate::env::decl_emit::mk_apps;
use crate::env::{EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// congr : {α : Sort u} → {β : Sort v} → {f₁ f₂ : α → β} → {a₁ a₂ : α}
///       → Eq f₁ f₂ → Eq a₁ a₂ → Eq (f₁ a₁) (f₂ a₂)
pub(crate) fn register(env: &mut Environment, ctx: &EqCtx) -> Result<(), EnvError> {
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

    let congr_type = congr_type_expr(ctx, &sort_v, &eq_v_const, &eq_func_const);
    let congr_value = congr_value_expr(ctx, &sort_v, &eq_func_const);

    decl_emit::add_decl(
        env,
        decl_emit::theorem("congr", vec![ctx.u.clone(), v], congr_type, congr_value),
    )
}

fn congr_type_expr(ctx: &EqCtx, sort_v: &Expr, eq_v_const: &Expr, eq_func_const: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (beta_id, beta) = b.fresh_local(sort_v.clone());
    let func_ty = simple_arrow(&b, &alpha, &beta);
    let (f1_id, f1_var) = b.fresh_local(func_ty.clone());
    let (f2_id, f2_var) = b.fresh_local(func_ty.clone());
    let (a1_id, a1_var) = b.fresh_local(alpha.clone());
    let (a2_id, a2_var) = b.fresh_local(alpha.clone());
    let eq_f1_f2 = mk_apps(
        eq_func_const.clone(),
        vec![func_ty.clone(), f1_var.clone(), f2_var.clone()],
    );
    let (h1_id, _) = b.fresh_local(eq_f1_f2.clone());
    let eq_a1_a2 = ctx.eq(&alpha, a1_var.clone(), a2_var.clone());
    let (h2_id, _) = b.fresh_local(eq_a1_a2.clone());
    let r = mk_apps(
        eq_v_const.clone(),
        vec![
            beta.clone(),
            Expr::app(f1_var.clone(), a1_var.clone()),
            Expr::app(f2_var.clone(), a2_var.clone()),
        ],
    );
    let r = b.mk_pi(h2_id, BinderInfo::Default, eq_a1_a2, r);
    let r = b.mk_pi(h1_id, BinderInfo::Default, eq_f1_f2, r);
    let r = b.mk_pi(a2_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_pi(a1_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_pi(f2_id, BinderInfo::Implicit, func_ty.clone(), r);
    let r = b.mk_pi(f1_id, BinderInfo::Implicit, func_ty, r);
    let r = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
    let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

fn congr_value_expr(ctx: &EqCtx, sort_v: &Expr, eq_func_const: &Expr) -> Expr {
    let v = Name::from_string("v");
    let congr_fun_const = Expr::const_(
        Name::from_string("congrFun"),
        vec![Level::param(ctx.u.clone()), Level::param(v.clone())],
    );
    let congr_arg_const = Expr::const_(
        Name::from_string("congrArg"),
        vec![Level::param(ctx.u.clone()), Level::param(v.clone())],
    );
    let eq_trans_const = Expr::const_(Name::from_string("Eq.trans"), vec![Level::param(v.clone())]);

    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (beta_id, beta) = b.fresh_local(sort_v.clone());
    let func_ty = simple_arrow(&b, &alpha, &beta);
    let (f1_id, f1_var) = b.fresh_local(func_ty.clone());
    let (f2_id, f2_var) = b.fresh_local(func_ty.clone());
    let (a1_id, a1_var) = b.fresh_local(alpha.clone());
    let (a2_id, a2_var) = b.fresh_local(alpha.clone());
    let eq_f1_f2 = mk_apps(
        eq_func_const.clone(),
        vec![func_ty.clone(), f1_var.clone(), f2_var.clone()],
    );
    let (h1_id, h1_var) = b.fresh_local(eq_f1_f2.clone());
    let eq_a1_a2 = ctx.eq(&alpha, a1_var.clone(), a2_var.clone());
    let (h2_id, h2_var) = b.fresh_local(eq_a1_a2.clone());
    // const_beta = λ (_ : α), β
    let const_beta = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (x_id, _) = c.fresh_local(alpha.clone());
        let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), beta.clone());
        c.finish_child(r)
    };
    // left: congrFun {α} {λ _, β} {f₁} {f₂} h₁ a₁
    let left = mk_apps(
        congr_fun_const,
        vec![
            alpha.clone(),
            const_beta,
            f1_var.clone(),
            f2_var.clone(),
            h1_var,
            a1_var.clone(),
        ],
    );
    // right: congrArg {α} {β} {a₁} {a₂} f₂ h₂
    let right = mk_apps(
        congr_arg_const,
        vec![
            alpha.clone(),
            beta.clone(),
            a1_var.clone(),
            a2_var.clone(),
            f2_var.clone(),
            h2_var,
        ],
    );
    // Eq.trans {β} {f₁ a₁} {f₂ a₁} {f₂ a₂} left right
    let r = mk_apps(
        eq_trans_const,
        vec![
            beta.clone(),
            Expr::app(f1_var.clone(), a1_var.clone()),
            Expr::app(f2_var.clone(), a1_var),
            Expr::app(f2_var, a2_var),
            left,
            right,
        ],
    );
    let r = b.mk_lam(h2_id, BinderInfo::Default, eq_a1_a2, r);
    let r = b.mk_lam(h1_id, BinderInfo::Default, eq_f1_f2, r);
    let r = b.mk_lam(a2_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(a1_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(f2_id, BinderInfo::Implicit, func_ty.clone(), r);
    let r = b.mk_lam(f1_id, BinderInfo::Implicit, func_ty, r);
    let r = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}
