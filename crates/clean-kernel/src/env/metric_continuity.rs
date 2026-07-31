// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metric continuity initialization functions for Environment
//!
//! This module contains metric topology and continuity-related init_* and has_*
//! functions: metric balls and epsilon-delta continuity.
//!
//! Lipschitz and uniform continuity are in `metric_continuity_advanced.rs`.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Initialize Metric.ball/closedBall helper definitions for metric spaces
    ///
    /// Adds:
    /// - `Metric.ball : {α : Type u} → [MetricSpace α] → α → Rat → α → Prop`
    ///     Open ball `{x | dist x center < radius}`
    /// - `Metric.closedBall : {α : Type u} → [MetricSpace α] → α → Rat → α → Prop`
    ///     Closed ball `{x | dist x center ≤ radius}`
    /// - `Metric.mem_ball_self` and `Metric.mem_closedBall_self` axioms
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.metric_ball_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_metric_ball(&mut self) -> Result<(), EnvError> {
        if self.metric_ball_init {
            return Ok(());
        }

        // Dependencies: MetricSpace typeclass and Rat ordering
        self.init_metric_space()?;
        self.init_rat_ord()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

        let metric_space = |lvl: Level| Expr::const_(Name::from_string("MetricSpace"), vec![lvl]);
        let metric_dist =
            Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);

        // Helper: build MetricSpace.dist α inst x y
        let ms_dist = |alpha: &Expr, inst: &Expr, x: &Expr, y: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(metric_dist.clone(), alpha.clone()), inst.clone()),
                    x.clone(),
                ),
                y.clone(),
            )
        };

        // ================================================================
        // Metric.ball : {α : Type u} → [MetricSpace α] → α → Rat → α → Prop
        // Metric.ball {α} [inst] center r x := Rat.lt (MetricSpace.dist x center) r
        // ================================================================
        let ball_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(ms_alpha.clone());
            let (center_id, _center) = b.fresh_local(alpha.clone());
            let (r_id, _r) = b.fresh_local(rat_const.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop);
            let e = b.mk_pi(r_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(center_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let ball_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (center_id, center) = b.fresh_local(alpha.clone());
            let (r_id, r) = b.fresh_local(rat_const.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            // Rat.lt (MetricSpace.dist x center) r
            let body = Expr::app(
                Expr::app(rat_lt.clone(), ms_dist(&alpha, &inst, &x, &center)),
                r,
            );
            let e = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(r_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_lam(center_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Metric.ball"),
            level_params: vec![u.clone()],
            type_: ball_type,
            value: ball_value,
            is_reducible: true,
        })?;

        // ================================================================
        // Metric.closedBall : {α : Type u} → [MetricSpace α] → α → Rat → α → Prop
        // Metric.closedBall {α} [inst] center r x := Rat.le (MetricSpace.dist x center) r
        // ================================================================
        let closed_ball_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(ms_alpha.clone());
            let (center_id, _center) = b.fresh_local(alpha.clone());
            let (r_id, _r) = b.fresh_local(rat_const.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop);
            let e = b.mk_pi(r_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(center_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let closed_ball_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (center_id, center) = b.fresh_local(alpha.clone());
            let (r_id, r) = b.fresh_local(rat_const.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            // Rat.le (MetricSpace.dist x center) r
            let body = Expr::app(
                Expr::app(rat_le.clone(), ms_dist(&alpha, &inst, &x, &center)),
                r,
            );
            let e = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(r_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_lam(center_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Metric.closedBall"),
            level_params: vec![u.clone()],
            type_: closed_ball_type,
            value: closed_ball_value,
            is_reducible: true,
        })?;

        // ================================================================
        // Metric.mem_ball_self : {α} → [MetricSpace α] → ∀ x r, 0 < r → Metric.ball x r x
        // ================================================================
        let mem_ball_self_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (r_id, r) = b.fresh_local(rat_const.clone());
            let lt_zero_r = Expr::app(Expr::app(rat_lt.clone(), rat_zero.clone()), r.clone());
            let (h_id, _h) = b.fresh_local(lt_zero_r.clone());
            let ball_const = Expr::const_(Name::from_string("Metric.ball"), vec![u_level.clone()]);
            let conclusion = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(ball_const, alpha.clone()), inst),
                        x.clone(),
                    ),
                    r,
                ),
                x.clone(),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, lt_zero_r, conclusion);
            let e = b.mk_pi(r_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.mem_ball_self"),
            level_params: vec![u.clone()],
            type_: mem_ball_self_type,
        })?;

        // ================================================================
        // Metric.mem_closedBall_self
        // ================================================================
        let mem_closed_ball_self_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (r_id, r) = b.fresh_local(rat_const.clone());
            let le_zero_r = Expr::app(Expr::app(rat_le.clone(), rat_zero.clone()), r.clone());
            let (h_id, _h) = b.fresh_local(le_zero_r.clone());
            let closed_ball_const = Expr::const_(
                Name::from_string("Metric.closedBall"),
                vec![u_level.clone()],
            );
            let conclusion = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(closed_ball_const, alpha.clone()), inst),
                        x.clone(),
                    ),
                    r,
                ),
                x.clone(),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, le_zero_r, conclusion);
            let e = b.mk_pi(r_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.mem_closedBall_self"),
            level_params: vec![u],
            type_: mem_closed_ball_self_type,
        })?;

        self.metric_ball_init = true;
        Ok(())
    }

    /// Check if Metric.ball/closedBall have been initialized
    #[cfg(test)]
    pub(crate) fn has_metric_ball(&self) -> bool {
        self.metric_ball_init
    }

    /// Initialize Metric.Continuous for metric spaces
    ///
    /// Adds:
    /// - Metric.Continuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] → (α → β) → Prop
    ///   (the epsilon-delta definition of continuity)
    /// - Metric.continuous_id, Metric.continuous_const, Metric.continuous_comp
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.metric_continuous_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_metric_continuous(&mut self) -> Result<(), EnvError> {
        if self.metric_continuous_init {
            return Ok(());
        }

        // Dependencies
        self.init_metric_space()?;
        self.init_rat_ord()?;
        self.init_exists()?;
        self.init_and()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let exists_const = |lvl: Level| Expr::const_(Name::from_string("Exists"), vec![lvl]);

        let metric_space = |lvl: Level| Expr::const_(Name::from_string("MetricSpace"), vec![lvl]);
        let metric_dist =
            Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);

        // ================================================================
        // Metric.Continuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] → (α → β) → Prop
        //
        // Definition: ∀ x ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ y, dist y x < δ → dist (f y) (f x) < ε
        // ================================================================
        let continuous_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let (inst_a_id, _inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, _inst_b) = b.fresh_local(ms_beta.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, prop.clone());
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let continuous_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let (inst_a_id, inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, inst_b) = b.fresh_local(ms_beta.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (eps_id, eps) = b.fresh_local(rat_const.clone());

            let mk_dist_fvar = |ty: &Expr, inst: &Expr, a: &Expr, b_: &Expr| {
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(metric_dist.clone(), ty.clone()), inst.clone()),
                        a.clone(),
                    ),
                    b_.clone(),
                )
            };

            let zero_lt_eps = Expr::app(Expr::app(rat_lt.clone(), rat_zero.clone()), eps.clone());
            let (h_eps_id, _h_eps) = b.fresh_local(zero_lt_eps.clone());

            let (delta_id, delta) = b.fresh_local(rat_const.clone());
            let zero_lt_delta =
                Expr::app(Expr::app(rat_lt.clone(), rat_zero.clone()), delta.clone());

            let (y_id, y) = b.fresh_local(alpha.clone());
            let dist_y_x = mk_dist_fvar(&alpha, &inst_a, &y, &x);
            let dist_y_x_lt_delta = Expr::app(Expr::app(rat_lt.clone(), dist_y_x), delta.clone());
            let f_y = Expr::app(f.clone(), y.clone());
            let f_x = Expr::app(f.clone(), x.clone());
            let dist_fy_fx = mk_dist_fvar(&beta, &inst_b, &f_y, &f_x);
            let dist_fy_fx_lt_eps = Expr::app(Expr::app(rat_lt.clone(), dist_fy_fx), eps.clone());

            let forall_y_body = Expr::arrow(dist_y_x_lt_delta, dist_fy_fx_lt_eps);
            let forall_y = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), forall_y_body);

            let and_body = Expr::app(Expr::app(and_const.clone(), zero_lt_delta), forall_y);

            let exists_pred = b.mk_lam(delta_id, BinderInfo::Default, rat_const.clone(), and_body);

            let exists_delta = Expr::app(
                Expr::app(exists_const(Level::succ(Level::zero())), rat_const.clone()),
                exists_pred,
            );

            let impl_body = b.mk_pi(h_eps_id, BinderInfo::Default, zero_lt_eps, exists_delta);
            let forall_eps = b.mk_pi(eps_id, BinderInfo::Default, rat_const.clone(), impl_body);
            let forall_x = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), forall_eps);

            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, forall_x);
            let e = b.mk_lam(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_lam(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Metric.Continuous"),
            level_params: vec![u.clone()],
            type_: continuous_type,
            value: continuous_value,
            is_reducible: true,
        })?;

        let continuous_const_name = Expr::const_(
            Name::from_string("Metric.Continuous"),
            vec![u_level.clone()],
        );

        let mk_continuous = |alpha: &Expr, beta: &Expr, inst_a: &Expr, inst_b: &Expr, f: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(continuous_const_name.clone(), alpha.clone()),
                            beta.clone(),
                        ),
                        inst_a.clone(),
                    ),
                    inst_b.clone(),
                ),
                f.clone(),
            )
        };

        // ================================================================
        // Metric.continuous_id
        // ================================================================
        let continuous_id_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let id_fun = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), x);
            let conclusion = mk_continuous(&alpha, &alpha, &inst, &inst, &id_fun);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha, conclusion);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.continuous_id"),
            level_params: vec![u.clone()],
            type_: continuous_id_type,
        })?;

        // ================================================================
        // Metric.continuous_const
        // ================================================================
        let continuous_const_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let (inst_a_id, inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, inst_b) = b.fresh_local(ms_beta.clone());
            let (c_id, c) = b.fresh_local(beta.clone());
            let (dummy_id, _dummy) = b.fresh_local(alpha.clone());
            let const_fun = b.mk_lam(dummy_id, BinderInfo::Default, alpha.clone(), c);
            let conclusion = mk_continuous(&alpha, &beta, &inst_a, &inst_b, &const_fun);
            let e = b.mk_pi(c_id, BinderInfo::Default, beta.clone(), conclusion);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.continuous_const"),
            level_params: vec![u.clone()],
            type_: continuous_const_type,
        })?;

        // ================================================================
        // Metric.continuous_comp
        // ================================================================
        let continuous_comp_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let ms_gamma = Expr::app(metric_space(u_level.clone()), gamma.clone());
            let (inst_a_id, inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, inst_b) = b.fresh_local(ms_beta.clone());
            let (inst_g_id, inst_g) = b.fresh_local(ms_gamma.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let g_ty = Expr::arrow(beta.clone(), gamma.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let hf_ty = mk_continuous(&alpha, &beta, &inst_a, &inst_b, &f);
            let (hf_id, _hf) = b.fresh_local(hf_ty.clone());
            let hg_ty = mk_continuous(&beta, &gamma, &inst_b, &inst_g, &g);
            let (hg_id, _hg) = b.fresh_local(hg_ty.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let comp_fun = b.mk_lam(
                x_id,
                BinderInfo::Default,
                alpha.clone(),
                Expr::app(g.clone(), Expr::app(f.clone(), x)),
            );
            let conclusion = mk_continuous(&alpha, &gamma, &inst_a, &inst_g, &comp_fun);
            let e = b.mk_pi(hg_id, BinderInfo::Default, hg_ty, conclusion);
            let e = b.mk_pi(hf_id, BinderInfo::Default, hf_ty, e);
            let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(inst_g_id, BinderInfo::InstImplicit, ms_gamma, e);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.continuous_comp"),
            level_params: vec![u],
            type_: continuous_comp_type,
        })?;

        self.metric_continuous_init = true;
        Ok(())
    }

    /// Check if Metric.Continuous has been initialized
    #[cfg(test)]
    pub(crate) fn has_metric_continuous(&self) -> bool {
        self.metric_continuous_init
    }
}
