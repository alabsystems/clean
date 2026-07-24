// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HEq transport declarations: HEq.ndrec, HEq.ndrecOn, HEq.symm, HEq.trans.

use super::context::HeqCtx;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::decl_emit;
use crate::env::decl_emit::mk_apps;
use crate::env::{EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

pub(crate) fn register(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    register_ndrec(env, ctx)?;
    register_ndrec_on(env, ctx)?;
    register_symm(env, ctx)?;
    register_trans(env, ctx)?;
    Ok(())
}

/// Build the HEq motive type: {β : Sort u} → β → Sort v
fn heq_motive_type(b: &EnvDeclBuilder, sort_u: &Expr, sort_v: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (beta_id, beta) = c.fresh_local(sort_u.clone());
    let (x_id, _) = c.fresh_local(beta.clone());
    let r = c.mk_pi(x_id, BinderInfo::Default, beta.clone(), sort_v.clone());
    let r = c.mk_pi(beta_id, BinderInfo::Implicit, sort_u.clone(), r);
    c.finish_child(r)
}

/// HEq.ndrec : {α : Sort u} → {a : α} → {motive : {β : Sort u} → β → Sort v}
///          → motive a → {β : Sort u} → {b : β} → HEq a b → motive b
fn register_ndrec(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    let v = Name::from_string("v");
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let heq_rec_const = Expr::const_(
        Name::from_string("HEq.rec"),
        vec![Level::param(v.clone()), Level::param(ctx.u.clone())],
    );

    let ndrec_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = heq_motive_type(&b, &ctx.sort_u, &sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let mot_a = Expr::app(Expr::app(mot_var.clone(), alpha.clone()), a_var.clone());
        let (m_id, _) = b.fresh_local(mot_a.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let (bb_id, bb_var) = b.fresh_local(beta.clone());
        let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
        let (h_id, _) = b.fresh_local(heq_a_b.clone());
        let r = Expr::app(Expr::app(mot_var, beta.clone()), bb_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, heq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, beta.clone(), r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_pi(m_id, BinderInfo::Default, mot_a, r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty, r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let ndrec_value = ndrec_value_expr(ctx, &sort_v, &heq_rec_const);

    decl_emit::add_decl(
        env,
        // Level-param order is MOTIVE-first (`{u_1 motive, u_2 α}`) to match
        // genuine Lean v4.30 `HEq.ndrec.{u_1, u_2}`. Olean values instantiate
        // these positionally (`HEq.ndrec.{0, u}` for a Prop motive), so the
        // α-first order rejected every such import (HEq.subst, HEq.comm, …).
        decl_emit::reducible_def("HEq.ndrec", vec![v, ctx.u.clone()], ndrec_type, ndrec_value),
    )
}

fn ndrec_value_expr(ctx: &HeqCtx, sort_v: &Expr, heq_rec_const: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    let motive_ty = heq_motive_type(&b, &ctx.sort_u, sort_v);
    let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
    let mot_a = Expr::app(Expr::app(mot_var.clone(), alpha.clone()), a_var.clone());
    let (m_id, m_var) = b.fresh_local(mot_a.clone());
    let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
    let (bb_id, bb_var) = b.fresh_local(beta.clone());
    let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
    let (h_id, h_var) = b.fresh_local(heq_a_b.clone());
    // wrapped_motive = λ {γ} (x : γ) (_ : HEq α a γ x), motive γ x
    let wrapped_motive = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (gamma_id, gamma) = c.fresh_local(ctx.sort_u.clone());
        let (x_id, x_var) = c.fresh_local(gamma.clone());
        let heq_a_gx = ctx.heq(&alpha, a_var.clone(), &gamma, x_var.clone());
        let (p_id, _) = c.fresh_local(heq_a_gx.clone());
        let r = Expr::app(Expr::app(mot_var.clone(), gamma.clone()), x_var);
        let r = c.mk_lam(p_id, BinderInfo::Default, heq_a_gx, r);
        let r = c.mk_lam(x_id, BinderInfo::Default, gamma.clone(), r);
        let r = c.mk_lam(gamma_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        c.finish_child(r)
    };
    let r = mk_apps(
        heq_rec_const.clone(),
        vec![
            alpha.clone(),
            a_var,
            wrapped_motive,
            m_var,
            beta.clone(),
            bb_var,
            h_var,
        ],
    );
    let r = b.mk_lam(h_id, BinderInfo::Default, heq_a_b, r);
    let r = b.mk_lam(bb_id, BinderInfo::Implicit, beta.clone(), r);
    let r = b.mk_lam(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    let r = b.mk_lam(m_id, BinderInfo::Default, mot_a, r);
    let r = b.mk_lam(mot_id, BinderInfo::Implicit, motive_ty, r);
    let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

/// HEq.ndrecOn : flip-argument wrapper around HEq.ndrec
fn register_ndrec_on(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    let v = Name::from_string("v");
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    // HEq.ndrec now declares motive-first levels (Lean v4.30 order), so
    // instantiate `{motive := v, α := u}` positionally.
    let heq_ndrec_const = Expr::const_(
        Name::from_string("HEq.ndrec"),
        vec![Level::param(v.clone()), Level::param(ctx.u.clone())],
    );

    let ndrec_on_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = heq_motive_type(&b, &ctx.sort_u, &sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let (bb_id, bb_var) = b.fresh_local(beta.clone());
        let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
        let (h_id, _) = b.fresh_local(heq_a_b.clone());
        let mot_a = Expr::app(Expr::app(mot_var.clone(), alpha.clone()), a_var.clone());
        let (m_id, _) = b.fresh_local(mot_a.clone());
        let mot_b = Expr::app(Expr::app(mot_var, beta.clone()), bb_var);
        let r = b.mk_pi(m_id, BinderInfo::Default, mot_a, mot_b);
        let r = b.mk_pi(h_id, BinderInfo::Default, heq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, beta.clone(), r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_pi(mot_id, BinderInfo::Implicit, motive_ty.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let ndrec_on_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let motive_ty = heq_motive_type(&b, &ctx.sort_u, &sort_v);
        let (mot_id, mot_var) = b.fresh_local(motive_ty.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let (bb_id, bb_var) = b.fresh_local(beta.clone());
        let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
        let (h_id, h_var) = b.fresh_local(heq_a_b.clone());
        let mot_a = Expr::app(Expr::app(mot_var.clone(), alpha.clone()), a_var.clone());
        let (m_id, m_var) = b.fresh_local(mot_a.clone());
        let r = mk_apps(
            heq_ndrec_const,
            vec![
                alpha.clone(),
                a_var,
                mot_var,
                m_var,
                beta.clone(),
                bb_var,
                h_var,
            ],
        );
        let r = b.mk_lam(m_id, BinderInfo::Default, mot_a, r);
        let r = b.mk_lam(h_id, BinderInfo::Default, heq_a_b, r);
        let r = b.mk_lam(bb_id, BinderInfo::Implicit, beta.clone(), r);
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_lam(mot_id, BinderInfo::Implicit, motive_ty, r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        // Motive-first level order, matching genuine `HEq.ndrecOn.{u_1, u_2}`
        // (see HEq.ndrec above).
        decl_emit::reducible_def(
            "HEq.ndrecOn",
            vec![v, ctx.u.clone()],
            ndrec_on_type,
            ndrec_on_value,
        ),
    )
}

/// HEq.symm : {α β : Sort u} → {a : α} → {b : β} → HEq a b → HEq b a
///
/// FIDELITY (residual-to-zero campaign, 2026-07-03): binder order matches
/// Lean 4.8's genuine theorem (`#print HEq.symm`: types grouped FIRST,
/// `{α β}{a}{b}`). The previous stub interleaved `{α}{a}{β}{b}`, so the
/// shadowed import made every positional Mathlib application
/// (`@HEq.symm T₁ T₂ r s h` in `RelIso.cast_symm`/`cast_trans`) bind the
/// wrong binders and fail with `expected <relation>, got Sort u+1`.
fn register_symm(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    let heq_rec_const = Expr::const_(
        Name::from_string("HEq.rec"),
        vec![Level::zero(), Level::param(ctx.u.clone())],
    );

    let symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let (bb_id, bb_var) = b.fresh_local(beta.clone());
        let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
        let (h_id, _) = b.fresh_local(heq_a_b.clone());
        let r = ctx.heq(&beta, bb_var, &alpha, a_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, heq_a_b, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, beta.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    let symm_value = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
        let (a_id, a_var) = b.fresh_local(alpha.clone());
        let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
        let (bb_id, bb_var) = b.fresh_local(beta.clone());
        let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
        let (h_id, h_var) = b.fresh_local(heq_a_b.clone());
        // motive = λ {γ} (x : γ) (_ : HEq α a γ x), HEq γ x α a
        let motive = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (gamma_id, gamma) = c.fresh_local(ctx.sort_u.clone());
            let (x_id, x_var) = c.fresh_local(gamma.clone());
            let heq_a_gx = ctx.heq(&alpha, a_var.clone(), &gamma, x_var.clone());
            let (p_id, _) = c.fresh_local(heq_a_gx.clone());
            let r = ctx.heq(&gamma, x_var, &alpha, a_var.clone());
            let r = c.mk_lam(p_id, BinderInfo::Default, heq_a_gx, r);
            let r = c.mk_lam(x_id, BinderInfo::Default, gamma.clone(), r);
            let r = c.mk_lam(gamma_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
            c.finish_child(r)
        };
        let base = Expr::app(
            Expr::app(ctx.heq_refl_const.clone(), alpha.clone()),
            a_var.clone(),
        );
        let r = mk_apps(
            heq_rec_const.clone(),
            vec![
                alpha.clone(),
                a_var,
                motive,
                base,
                beta.clone(),
                bb_var,
                h_var,
            ],
        );
        let r = b.mk_lam(h_id, BinderInfo::Default, heq_a_b, r);
        let r = b.mk_lam(bb_id, BinderInfo::Implicit, beta.clone(), r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        b.finish(r)
    };

    decl_emit::add_decl(
        env,
        decl_emit::theorem("HEq.symm", vec![ctx.u.clone()], symm_type, symm_value),
    )
}

/// HEq.trans : {α β γ : Sort u} → {a : α} → {b : β} → {c : γ}
///          → HEq a b → HEq b c → HEq a c
///
/// FIDELITY (residual-to-zero campaign, 2026-07-03): binder order matches
/// Lean 4.8's genuine theorem (`#print HEq.trans`: `{α β φ}{a}{b}{c}`); the
/// previous stub interleaved `{α}{a}{β}{b}{γ}{c}` and shadowed the genuine
/// olean theorem, breaking every positional application (same class as
/// HEq.symm above).
fn register_trans(env: &mut Environment, ctx: &HeqCtx) -> Result<(), EnvError> {
    let trans_type = trans_type_expr(ctx);
    let trans_value = trans_value_expr(ctx);
    decl_emit::add_decl(
        env,
        decl_emit::theorem("HEq.trans", vec![ctx.u.clone()], trans_type, trans_value),
    )
}

fn trans_type_expr(ctx: &HeqCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
    let (bb_id, bb_var) = b.fresh_local(beta.clone());
    let (gamma_id, gamma) = b.fresh_local(ctx.sort_u.clone());
    let (c_id, c_var) = b.fresh_local(gamma.clone());
    let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
    let (h1_id, _) = b.fresh_local(heq_a_b.clone());
    let heq_b_c = ctx.heq(&beta, bb_var, &gamma, c_var.clone());
    let (h2_id, _) = b.fresh_local(heq_b_c.clone());
    let r = ctx.heq(&alpha, a_var, &gamma, c_var);
    let r = b.mk_pi(h2_id, BinderInfo::Default, heq_b_c, r);
    let r = b.mk_pi(h1_id, BinderInfo::Default, heq_a_b, r);
    let r = b.mk_pi(c_id, BinderInfo::Implicit, gamma.clone(), r);
    let r = b.mk_pi(bb_id, BinderInfo::Implicit, beta.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_pi(gamma_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    let r = b.mk_pi(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    let r = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

fn trans_value_expr(ctx: &HeqCtx) -> Expr {
    let heq_rec_const = Expr::const_(
        Name::from_string("HEq.rec"),
        vec![Level::zero(), Level::param(ctx.u.clone())],
    );
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.sort_u.clone());
    let (a_id, a_var) = b.fresh_local(alpha.clone());
    let (beta_id, beta) = b.fresh_local(ctx.sort_u.clone());
    let (bb_id, bb_var) = b.fresh_local(beta.clone());
    let (gamma_id, gamma) = b.fresh_local(ctx.sort_u.clone());
    let (c_id, c_var) = b.fresh_local(gamma.clone());
    let heq_a_b = ctx.heq(&alpha, a_var.clone(), &beta, bb_var.clone());
    let (h1_id, h1_var) = b.fresh_local(heq_a_b.clone());
    let heq_b_c = ctx.heq(&beta, bb_var.clone(), &gamma, c_var.clone());
    let (h2_id, h2_var) = b.fresh_local(heq_b_c.clone());
    // motive = λ {δ} (x : δ) (_ : HEq β b δ x), HEq α a δ x
    let motive = {
        let mut c = EnvDeclBuilder::child_of(&b);
        let (delta_id, delta) = c.fresh_local(ctx.sort_u.clone());
        let (x_id, x_var) = c.fresh_local(delta.clone());
        let heq_b_dx = ctx.heq(&beta, bb_var.clone(), &delta, x_var.clone());
        let (p_id, _) = c.fresh_local(heq_b_dx.clone());
        let r = ctx.heq(&alpha, a_var.clone(), &delta, x_var);
        let r = c.mk_lam(p_id, BinderInfo::Default, heq_b_dx, r);
        let r = c.mk_lam(x_id, BinderInfo::Default, delta.clone(), r);
        let r = c.mk_lam(delta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
        c.finish_child(r)
    };
    let r = mk_apps(
        heq_rec_const,
        vec![
            beta.clone(),
            bb_var,
            motive,
            h1_var,
            gamma.clone(),
            c_var,
            h2_var,
        ],
    );
    let r = b.mk_lam(h2_id, BinderInfo::Default, heq_b_c, r);
    let r = b.mk_lam(h1_id, BinderInfo::Default, heq_a_b, r);
    let r = b.mk_lam(c_id, BinderInfo::Implicit, gamma.clone(), r);
    let r = b.mk_lam(bb_id, BinderInfo::Implicit, beta.clone(), r);
    let r = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), r);
    let r = b.mk_lam(gamma_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    let r = b.mk_lam(beta_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, ctx.sort_u.clone(), r);
    b.finish(r)
}

#[cfg(test)]
mod heq_binder_order_tests {
    use crate::env::Environment;
    use crate::expr::Expr;
    use crate::level::Level;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    /// FIDELITY + ADVERSARIAL pins for the `HEq.symm`/`HEq.trans` binder-order
    /// correction (residual-to-zero campaign, 2026-07-03).
    ///
    /// Lean 4.8 ground truth (`#print`): both group the TYPE binders first —
    /// `HEq.symm : {α β}{a}{b} → HEq a b → HEq b a`,
    /// `HEq.trans : {α β φ}{a}{b}{c} → HEq a b → HEq b c → HEq a c`.
    /// The previous stubs interleaved `{α}{a}{β}{b}…`, so positional Mathlib
    /// applications (`@HEq.symm T₁ T₂ r s h` inside `RelIso.cast_symm`) bound
    /// the wrong binders. Pins BOTH directions: Lean-order applications check;
    /// the old interleaved-order application is rejected.
    #[test]
    fn test_heq_symm_trans_lean_binder_order() {
        let mut env = Environment::new();
        env.init_nat().expect("nat");
        env.init_heq().expect("heq");
        let tc = TypeChecker::new(&env);

        let nat = Expr::const_(n("Nat"), vec![]);
        let zero = Expr::const_(n("Nat.zero"), vec![]);
        // h : HEq Nat 0 Nat 0
        let h = Expr::apps(
            Expr::const_(n("HEq.refl"), vec![Level::succ(Level::zero())]),
            [nat.clone(), zero.clone()],
        );

        // Lean order: @HEq.symm Nat Nat 0 0 h — types first.
        let symm_good = Expr::apps(
            Expr::const_(n("HEq.symm"), vec![Level::succ(Level::zero())]),
            [
                nat.clone(),
                nat.clone(),
                zero.clone(),
                zero.clone(),
                h.clone(),
            ],
        );
        let _ = tc
            .infer_type_full(&symm_good)
            .expect("Lean-binder-order HEq.symm application must type-check");

        // Old interleaved order: @HEq.symm Nat 0 Nat 0 h — the second
        // position (a type slot under the corrected signature) receives 0.
        let tc2 = TypeChecker::new(&env);
        let symm_old = Expr::apps(
            Expr::const_(n("HEq.symm"), vec![Level::succ(Level::zero())]),
            [
                nat.clone(),
                zero.clone(),
                nat.clone(),
                zero.clone(),
                h.clone(),
            ],
        );
        assert!(
            tc2.infer_type_full(&symm_old).is_err(),
            "old interleaved-order HEq.symm application must be rejected"
        );

        // Lean order: @HEq.trans Nat Nat Nat 0 0 0 h h — types first.
        let tc3 = TypeChecker::new(&env);
        let trans_good = Expr::apps(
            Expr::const_(n("HEq.trans"), vec![Level::succ(Level::zero())]),
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                zero.clone(),
                zero.clone(),
                zero.clone(),
                h.clone(),
                h.clone(),
            ],
        );
        let _ = tc3
            .infer_type_full(&trans_good)
            .expect("Lean-binder-order HEq.trans application must type-check");

        // Old interleaved order: @HEq.trans Nat 0 Nat 0 Nat 0 h h.
        let tc4 = TypeChecker::new(&env);
        let trans_old = Expr::apps(
            Expr::const_(n("HEq.trans"), vec![Level::succ(Level::zero())]),
            [
                nat.clone(),
                zero.clone(),
                nat.clone(),
                zero.clone(),
                nat.clone(),
                zero.clone(),
                h.clone(),
                h.clone(),
            ],
        );
        assert!(
            tc4.infer_type_full(&trans_old).is_err(),
            "old interleaved-order HEq.trans application must be rejected"
        );
    }
}
