// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lipschitz continuity initialization for metric spaces.
//!
//! Extracted from `metric_continuity.rs` for maintainability.
//! Contains `init_metric_lipschitz` and `has_metric_lipschitz`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Metric.Lipschitz for Lipschitz continuous functions
    ///
    /// Adds:
    /// - Metric.Lipschitz : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    ///                      Rat → (α → β) → Prop
    ///   (f is K-Lipschitz if ∀ x y, dist (f x) (f y) ≤ K * dist x y)
    /// - Metric.lipschitz_continuous : Lipschitz → Continuous
    /// - Metric.lipschitz_id : identity is 1-Lipschitz
    /// - Metric.lipschitz_const : constant functions are 0-Lipschitz
    /// - Metric.lipschitz_comp : composition preserves Lipschitz with bound K₂ * K₁
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.metric_lipschitz_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_metric_lipschitz(&mut self) -> Result<(), EnvError> {
        if self.metric_lipschitz_init {
            return Ok(());
        }

        // Dependencies
        self.init_metric_space()?;
        self.init_metric_continuous()?;
        self.init_rat_ord()?;
        self.init_rat()?; // For Rat.mul, Rat.one, Rat.zero

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);

        let metric_space = |lvl: Level| Expr::const_(Name::from_string("MetricSpace"), vec![lvl]);
        let metric_dist =
            Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);

        // ================================================================
        // Metric.Lipschitz : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
        //                    Rat → (α → β) → Prop
        //
        // Definition: ∀ x y, dist (f x) (f y) ≤ K * dist x y
        // ================================================================
        let lipschitz_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let (inst_a_id, _inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, _inst_b) = b.fresh_local(ms_beta.clone());
            let (k_id, _k) = b.fresh_local(rat_const.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, prop.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Body: λ {α β} [instα] [instβ] K f =>
        //   ∀ x y, dist (f x) (f y) ≤ K * dist x y
        let lipschitz_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let (inst_a_id, inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, inst_b) = b.fresh_local(ms_beta.clone());
            let (k_id, k) = b.fresh_local(rat_const.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());

            // Helper: dist using FVars
            let mk_dist_fvar = |ty: &Expr, inst: &Expr, a: &Expr, b_: &Expr| {
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(metric_dist.clone(), ty.clone()), inst.clone()),
                        a.clone(),
                    ),
                    b_.clone(),
                )
            };

            // dist (f x) (f y) using β's metric
            let f_x = Expr::app(f.clone(), x.clone());
            let f_y = Expr::app(f.clone(), y.clone());
            let dist_fx_fy = mk_dist_fvar(&beta, &inst_b, &f_x, &f_y);
            // dist x y using α's metric
            let dist_x_y = mk_dist_fvar(&alpha, &inst_a, &x, &y);
            // K * dist x y
            let k_times_dist = Expr::app(Expr::app(rat_mul.clone(), k), dist_x_y);
            // dist (f x) (f y) ≤ K * dist x y
            let le_constraint = Expr::app(Expr::app(rat_le.clone(), dist_fx_fy), k_times_dist);

            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), le_constraint);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_lam(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_lam(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Metric.Lipschitz"),
            level_params: vec![u.clone()],
            type_: lipschitz_type,
            value: lipschitz_value,
            is_reducible: true,
        })?;

        let lipschitz_const_name =
            Expr::const_(Name::from_string("Metric.Lipschitz"), vec![u_level.clone()]);
        let continuous_const_name2 = Expr::const_(
            Name::from_string("Metric.Continuous"),
            vec![u_level.clone()],
        );

        // Helper: Metric.Lipschitz {α} {β} [instα] [instβ] K f
        let mk_lipschitz =
            |alpha: &Expr, beta: &Expr, inst_a: &Expr, inst_b: &Expr, k: &Expr, f: &Expr| {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(lipschitz_const_name.clone(), alpha.clone()),
                                    beta.clone(),
                                ),
                                inst_a.clone(),
                            ),
                            inst_b.clone(),
                        ),
                        k.clone(),
                    ),
                    f.clone(),
                )
            };

        // Helper: Metric.Continuous {α} {β} [instα] [instβ] f
        let mk_continuous2 = |alpha: &Expr, beta: &Expr, inst_a: &Expr, inst_b: &Expr, f: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(continuous_const_name2.clone(), alpha.clone()),
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
        // Metric.lipschitz_continuous
        // ================================================================
        let lipschitz_continuous_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let (inst_a_id, inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, inst_b) = b.fresh_local(ms_beta.clone());
            let (k_id, k) = b.fresh_local(rat_const.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let zero_le_k = Expr::app(Expr::app(rat_le.clone(), rat_zero.clone()), k.clone());
            let (hk_id, _hk) = b.fresh_local(zero_le_k.clone());
            let lip_kf = mk_lipschitz(&alpha, &beta, &inst_a, &inst_b, &k, &f);
            let (hl_id, _hl) = b.fresh_local(lip_kf.clone());
            let conclusion = mk_continuous2(&alpha, &beta, &inst_a, &inst_b, &f);
            let e = b.mk_pi(hl_id, BinderInfo::Default, lip_kf, conclusion);
            let e = b.mk_pi(hk_id, BinderInfo::Default, zero_le_k, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(k_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.lipschitz_continuous"),
            level_params: vec![u.clone()],
            type_: lipschitz_continuous_type,
        })?;

        // ================================================================
        // Metric.lipschitz_id
        // ================================================================
        let lipschitz_id_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let id_fun = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), x);
            let conclusion = mk_lipschitz(&alpha, &alpha, &inst, &inst, &rat_one, &id_fun);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha, conclusion);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.lipschitz_id"),
            level_params: vec![u.clone()],
            type_: lipschitz_id_type,
        })?;

        // ================================================================
        // Metric.lipschitz_const
        // ================================================================
        let lipschitz_const_decl_type = {
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
            let conclusion = mk_lipschitz(&alpha, &beta, &inst_a, &inst_b, &rat_zero, &const_fun);
            let e = b.mk_pi(c_id, BinderInfo::Default, beta.clone(), conclusion);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.lipschitz_const"),
            level_params: vec![u.clone()],
            type_: lipschitz_const_decl_type,
        })?;

        // ================================================================
        // Metric.lipschitz_comp
        // ================================================================
        let lipschitz_comp_type = {
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
            let (k1_id, k1) = b.fresh_local(rat_const.clone());
            let (k2_id, k2) = b.fresh_local(rat_const.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let g_ty = Expr::arrow(beta.clone(), gamma.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let lip_k1_f = mk_lipschitz(&alpha, &beta, &inst_a, &inst_b, &k1, &f);
            let (hf_id, _hf) = b.fresh_local(lip_k1_f.clone());
            let lip_k2_g = mk_lipschitz(&beta, &gamma, &inst_b, &inst_g, &k2, &g);
            let (hg_id, _hg) = b.fresh_local(lip_k2_g.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let comp_fun = b.mk_lam(
                x_id,
                BinderInfo::Default,
                alpha.clone(),
                Expr::app(g, Expr::app(f, x)),
            );
            let k2_times_k1 = Expr::app(Expr::app(rat_mul.clone(), k2), k1);
            let conclusion =
                mk_lipschitz(&alpha, &gamma, &inst_a, &inst_g, &k2_times_k1, &comp_fun);
            let e = b.mk_pi(hg_id, BinderInfo::Default, lip_k2_g, conclusion);
            let e = b.mk_pi(hf_id, BinderInfo::Default, lip_k1_f, e);
            let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(k2_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(k1_id, BinderInfo::Default, rat_const.clone(), e);
            let e = b.mk_pi(inst_g_id, BinderInfo::InstImplicit, ms_gamma, e);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.lipschitz_comp"),
            level_params: vec![u],
            type_: lipschitz_comp_type,
        })?;

        self.metric_lipschitz_init = true;
        Ok(())
    }

    /// Check if Metric.Lipschitz has been initialized
    pub(crate) fn has_metric_lipschitz(&self) -> bool {
        self.metric_lipschitz_init
    }
}
