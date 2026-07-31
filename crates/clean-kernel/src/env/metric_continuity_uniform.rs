// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Uniform continuity initialization for metric spaces.
//!
//! Extracted from `metric_continuity.rs` for maintainability.
//! Contains `init_metric_uniform_continuous` and `has_metric_uniform_continuous`.

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
    /// Initialize uniformly continuous functions for metric spaces.
    ///
    /// Adds Metric.UniformContinuous and related axioms:
    /// - uniform_continuous_continuous, lipschitz_uniform_continuous
    /// - uniform_continuous_id, uniform_continuous_const, uniform_continuous_comp
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.metric_uniform_continuous_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_metric_uniform_continuous(&mut self) -> Result<(), EnvError> {
        if self.metric_uniform_continuous_init {
            return Ok(());
        }

        // Dependencies
        self.init_metric_space()?;
        self.init_metric_continuous()?;
        self.init_metric_lipschitz()?;
        self.init_rat_ord()?;
        self.init_rat()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

        let metric_space = |lvl: Level| Expr::const_(Name::from_string("MetricSpace"), vec![lvl]);
        let metric_dist =
            Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);

        // Silence unused variable warnings for dependencies
        let _ = (&rat_lt, &rat_le, &rat_zero, &metric_dist);

        // ================================================================
        // Metric.UniformContinuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
        //                            (α → β) → Prop
        // ================================================================
        let uniform_continuous_type = {
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

        // Silence unused variable warnings for dependencies
        let _ = (&rat_lt, &rat_le, &rat_zero, &metric_dist);

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.UniformContinuous"),
            level_params: vec![u.clone()],
            type_: uniform_continuous_type,
        })?;

        let uniform_cont_const = Expr::const_(
            Name::from_string("Metric.UniformContinuous"),
            vec![u_level.clone()],
        );
        let continuous_const = Expr::const_(
            Name::from_string("Metric.Continuous"),
            vec![u_level.clone()],
        );
        let lipschitz_const =
            Expr::const_(Name::from_string("Metric.Lipschitz"), vec![u_level.clone()]);

        // Helpers for UC/C/Lip applications
        let mk_uc = |alpha: &Expr, beta: &Expr, inst_a: &Expr, inst_b: &Expr, f: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(uniform_cont_const.clone(), alpha.clone()),
                            beta.clone(),
                        ),
                        inst_a.clone(),
                    ),
                    inst_b.clone(),
                ),
                f.clone(),
            )
        };
        let mk_cont = |alpha: &Expr, beta: &Expr, inst_a: &Expr, inst_b: &Expr, f: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(continuous_const.clone(), alpha.clone()),
                            beta.clone(),
                        ),
                        inst_a.clone(),
                    ),
                    inst_b.clone(),
                ),
                f.clone(),
            )
        };
        let mk_lip =
            |alpha: &Expr, beta: &Expr, inst_a: &Expr, inst_b: &Expr, k: &Expr, f: &Expr| {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(lipschitz_const.clone(), alpha.clone()),
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

        // ================================================================
        // Metric.uniform_continuous_continuous
        // ================================================================
        let uc_implies_c_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let ms_beta = Expr::app(metric_space(u_level.clone()), beta.clone());
            let (inst_a_id, inst_a) = b.fresh_local(ms_alpha.clone());
            let (inst_b_id, inst_b) = b.fresh_local(ms_beta.clone());
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let uc_f = mk_uc(&alpha, &beta, &inst_a, &inst_b, &f);
            let (huc_id, _huc) = b.fresh_local(uc_f.clone());
            let conclusion = mk_cont(&alpha, &beta, &inst_a, &inst_b, &f);
            let e = b.mk_pi(huc_id, BinderInfo::Default, uc_f, conclusion);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.uniform_continuous_continuous"),
            level_params: vec![u.clone()],
            type_: uc_implies_c_type,
        })?;

        // ================================================================
        // Metric.lipschitz_uniform_continuous
        // ================================================================
        let lipschitz_implies_uc_type = {
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
            let lip_kf = mk_lip(&alpha, &beta, &inst_a, &inst_b, &k, &f);
            let (hl_id, _hl) = b.fresh_local(lip_kf.clone());
            let conclusion = mk_uc(&alpha, &beta, &inst_a, &inst_b, &f);
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
            name: Name::from_string("Metric.lipschitz_uniform_continuous"),
            level_params: vec![u.clone()],
            type_: lipschitz_implies_uc_type,
        })?;

        // ================================================================
        // Metric.uniform_continuous_id
        // ================================================================
        let uc_id_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(metric_space(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let id_fun = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), x);
            let conclusion = mk_uc(&alpha, &alpha, &inst, &inst, &id_fun);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha, conclusion);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.uniform_continuous_id"),
            level_params: vec![u.clone()],
            type_: uc_id_type,
        })?;

        // ================================================================
        // Metric.uniform_continuous_const
        // ================================================================
        let uc_const_type = {
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
            let conclusion = mk_uc(&alpha, &beta, &inst_a, &inst_b, &const_fun);
            let e = b.mk_pi(c_id, BinderInfo::Default, beta.clone(), conclusion);
            let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ms_beta, e);
            let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ms_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.uniform_continuous_const"),
            level_params: vec![u.clone()],
            type_: uc_const_type,
        })?;

        // ================================================================
        // Metric.uniform_continuous_comp
        // ================================================================
        let uc_comp_type = {
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
            let uc_f = mk_uc(&alpha, &beta, &inst_a, &inst_b, &f);
            let (hf_id, _hf) = b.fresh_local(uc_f.clone());
            let uc_g = mk_uc(&beta, &gamma, &inst_b, &inst_g, &g);
            let (hg_id, _hg) = b.fresh_local(uc_g.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let comp_fun = b.mk_lam(
                x_id,
                BinderInfo::Default,
                alpha.clone(),
                Expr::app(g, Expr::app(f, x)),
            );
            let conclusion = mk_uc(&alpha, &gamma, &inst_a, &inst_g, &comp_fun);
            let e = b.mk_pi(hg_id, BinderInfo::Default, uc_g, conclusion);
            let e = b.mk_pi(hf_id, BinderInfo::Default, uc_f, e);
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
            name: Name::from_string("Metric.uniform_continuous_comp"),
            level_params: vec![u],
            type_: uc_comp_type,
        })?;

        self.metric_uniform_continuous_init = true;
        Ok(())
    }

    /// Check if Metric.UniformContinuous has been initialized
    #[cfg(test)]
    pub(crate) fn has_metric_uniform_continuous(&self) -> bool {
        self.metric_uniform_continuous_init
    }
}
