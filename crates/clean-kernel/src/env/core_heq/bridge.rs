// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HEq inductive declaration and Eq/HEq bridge lemmas: HEq.rfl, heq_of_eq, eq_of_heq.

use super::context::HeqCtx;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::decl_emit;
use crate::env::decl_emit::mk_apps;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

pub(crate) fn register(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    register_inductive(env, ctx)?;
    register_rfl(env, ctx)?;
    register_heq_of_eq(env, ctx)?;
    register_eq_of_heq(env, ctx)?;
    Ok(())
}

fn register_inductive(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    // HEq type: {α : Sort u} → α → {β : Sort u} → β → Prop
    let heq_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, _) = b.fresh_local(alpha.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let (b_id, _) = b.fresh_local(beta.clone());
        let r = ctx.prop.clone();
        let r = b.mk_pi(b_id, BinderInfo::Default, beta.clone(), r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    // HEq.refl : {α : Sort u} → (a : α) → HEq α a α a
    let refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let r = ctx.heq(&alpha, a_var.clone(), &alpha, a_var);
        let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let heq_decl = InductiveDecl {
        level_params: vec![ctx.u.clone()],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("HEq"),
            type_: heq_type,
            constructors: vec![Constructor {
                name: Name::from_string("HEq.refl"),
                type_: refl_type,
            }],
        }],
    };

    env.add_inductive(heq_decl)?;

    // Validate metadata consistency (#1394)
    #[cfg(debug_assertions)]
    for name in &["HEq.rec", "HEq.casesOn", "HEq.recOn"] {
        let rec_name = Name::from_string(name);
        debug_assert!(
            env.validate_recursor_metadata(&rec_name).is_ok(),
            "init_heq metadata inconsistency for {name}: {:?}",
            env.validate_recursor_metadata(&rec_name).unwrap_err()
        );
    }
    Ok(())
}

/// HEq.rfl : {α : Sort u} → {a : α} → HEq α a α a
fn register_rfl(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    let rfl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let r = ctx.heq(&alpha, a_var.clone(), &alpha, a_var);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };
    let rfl_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let r = Expr::app(Expr::app(ctx.heq_refl_const.clone(), alpha.clone()), a_var);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };
    // Restored to checked add_decl now that whnf_core_cache prevents
    // exponential blowup (#1768).
    env.add_decl(Declaration::Definition {
        name: Name::from_string("HEq.rfl"),
        level_params: vec![ctx.u.clone()],
        type_: rfl_type,
        value: rfl_value,
        is_reducible: true,
    })
}

/// heq_of_eq : {α : Sort u} → {a b : α} → Eq a b → HEq a b
fn register_heq_of_eq(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    let eq_rec_const = Expr::const_(
        Name::from_string("Eq.rec"),
        vec![Level::zero(), Level::param(ctx.u.clone())],
    );

    let heq_of_eq_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, _) = b.fresh_local(eq_a_b.clone());
        let r = ctx.heq(&alpha, a_var, &alpha, bb_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let heq_of_eq_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (bb_id, bb_var) = b.fresh_local(alpha.clone());
        let eq_a_b = ctx.eq(&alpha, a_var.clone(), bb_var.clone());
        let (h_id, h_var) = b.fresh_local(eq_a_b.clone());
        // motive = λ (x : α) (_ : Eq a x), HEq α a α x
        let motive = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (x_id, x_var) = c.fresh_local(alpha.clone());
            let eq_a_x = ctx.eq(&alpha, a_var.clone(), x_var.clone());
            let (p_id, _) = c.fresh_local(eq_a_x.clone());
            let r = ctx.heq(&alpha, a_var.clone(), &alpha, x_var);
            let r = c.mk_lam(p_id, BinderInfo::Default, eq_a_x, r);
            let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
            c.finish_child(r)
        };
        let base = Expr::app(
            Expr::app(ctx.heq_refl_const.clone(), alpha.clone()),
            a_var.clone(),
        );
        let r = mk_apps(
            eq_rec_const,
            vec![alpha.clone(), a_var, motive, base, bb_var, h_var],
        );
        let r = b.mk_lam(h_id, BinderInfo::Default, eq_a_b, r);
        let r = b.mk_lam(bb_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::theorem(
            "heq_of_eq",
            vec![ctx.u.clone()],
            heq_of_eq_type,
            heq_of_eq_value,
        ),
    )
}

/// eq_of_heq : {α : Sort u} → {a a' : α} → HEq a a' → Eq a a'
fn register_eq_of_heq(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    let eq_of_heq_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (ap_id, ap_var) = b.fresh_local(alpha.clone());
        let heq_a_ap = ctx.heq(&alpha, a_var.clone(), &alpha, ap_var.clone());
        let (h_id, _) = b.fresh_local(heq_a_ap.clone());
        let r = ctx.eq(&alpha, a_var, ap_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, heq_a_ap, r);
        let r = b.mk_pi(ap_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let eq_of_heq_value = eq_of_heq_value_expr(ctx);

    decl_emit::add_decl(
        env,
        decl_emit::theorem(
            "eq_of_heq",
            vec![ctx.u.clone()],
            eq_of_heq_type,
            eq_of_heq_value,
        ),
    )
}

/// Build the motive for eq_of_heq:
/// λ {γ : Sort u} (x : γ) (_ : HEq α a γ x), (h_eq : @Eq (Sort u) α γ) → @Eq γ (cast h_eq a) x
fn eq_of_heq_motive(
    ctx: &HeqCtx,
    b: &EnvDeclBuilder,
    alpha: &Expr,
    a_var: &Expr,
    eq_type_const: Expr,
    cast_const: Expr,
) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (gamma_id, gamma) = c.fresh_local(ctx.sort_u.clone());
    let (x_id, x_var) = c.fresh_local(gamma.clone());
    let heq_a_x = ctx.heq(alpha, a_var.clone(), &gamma, x_var.clone());
    let (p_id, _) = c.fresh_local(heq_a_x.clone());
    let eq_alpha_gamma = mk_apps(
        eq_type_const,
        vec![ctx.sort_u.clone(), alpha.clone(), gamma.clone()],
    );
    let mut d = EnvDeclBuilder::child_of(&c);
    let (heq_id, heq_var) = d.fresh_local(eq_alpha_gamma.clone());
    let cast_expr = mk_apps(
        cast_const,
        vec![alpha.clone(), gamma.clone(), heq_var, a_var.clone()],
    );
    let eq_cast_x = ctx.eq(&gamma, cast_expr, x_var);
    let r = d.mk_pi(heq_id, BinderInfo::Default, eq_alpha_gamma, eq_cast_x);
    let r = d.finish_child(r);
    let r = c.mk_lam(p_id, BinderInfo::Default, heq_a_x, r);
    let r = c.mk_lam(x_id, BinderInfo::Default, gamma.clone(), r);
    let r = c.mk_lam(gamma_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    c.finish_child(r)
}

fn eq_of_heq_value_expr(ctx: &HeqCtx) -> Expr {
    let succ_u = Level::succ(Level::param(ctx.u.clone()));
    let heq_rec_const = Expr::const_(
        Name::from_string("HEq.rec"),
        vec![Level::zero(), Level::param(ctx.u.clone())],
    );
    let eq_refl_const = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::param(ctx.u.clone())],
    );
    let eq_refl_type_const = Expr::const_(Name::from_string("Eq.refl"), vec![succ_u.clone()]);
    let cast_const = Expr::const_(Name::from_string("cast"), vec![Level::param(ctx.u.clone())]);
    let eq_type_const = Expr::const_(Name::from_string("Eq"), vec![succ_u]);

    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    let (ap_id, ap_var) = b.fresh_local(alpha.clone());
    let heq_a_ap = ctx.heq(&alpha, a_var.clone(), &alpha, ap_var.clone());
    let (h_id, h_var) = b.fresh_local(heq_a_ap.clone());

    let motive = eq_of_heq_motive(ctx, &b, &alpha, &a_var, eq_type_const.clone(), cast_const);

    // base = λ (_ : @Eq (Sort u) α α), @Eq.refl α a
    let base = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let eq_alpha_alpha = mk_apps(
            eq_type_const,
            vec![ctx.sort_u.clone(), alpha.clone(), alpha.clone()],
        );
        let (p_id, _) = c.fresh_local(eq_alpha_alpha.clone());
        let refl_a = Expr::app(Expr::app(eq_refl_const, alpha.clone()), a_var.clone());
        let r = c.mk_lam(p_id, BinderInfo::Default, eq_alpha_alpha, refl_a);
        c.finish_child(r)
    };

    let heq_rec_app = mk_apps(
        heq_rec_const,
        vec![
            alpha.clone(),
            a_var.clone(),
            motive,
            base,
            alpha.clone(),
            ap_var,
            h_var,
        ],
    );

    let type_refl = Expr::app(
        Expr::app(eq_refl_type_const, ctx.sort_u.clone()),
        alpha.clone(),
    );
    let body = Expr::app(heq_rec_app, type_refl);

    let r = b.mk_lam(h_id, BinderInfo::Default, heq_a_ap, body);
    let r = b.mk_lam(ap_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}
