// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metric completeness axioms
//!
//! Split from metric_completeness.rs (#307). Contains:
//! - Metric.Complete type and axioms (complete_spec, complete_of_seq_limit,
//!   converges_unique, converges_of_cauchy_complete)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Metric.Complete and related axioms for complete metric spaces.
    ///
    /// Adds: Metric.Complete, complete_spec, complete_of_seq_limit,
    ///       converges_unique, converges_of_cauchy_complete
    pub(crate) fn init_metric_complete(&mut self) -> Result<(), EnvError> {
        if self.metric_complete_init {
            return Ok(());
        }
        self.init_metric_cauchy_seq()?;
        self.init_eq()?;
        self.init_exists()?;

        self.add_metric_complete_type()?;
        self.add_metric_complete_spec()?;
        self.add_metric_complete_of_seq_limit()?;
        self.add_metric_converges_unique()?;
        self.add_metric_converges_of_cauchy_complete()?;

        self.metric_complete_init = true;
        Ok(())
    }

    pub(crate) fn has_metric_complete(&self) -> bool {
        self.metric_complete_init
    }

    fn add_metric_complete_type(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, _inst) = b.fresh_local(metric_alpha.clone());

        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, prop);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.Complete"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_complete_spec(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let cauchy_seq_const =
            Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);
        let converges_const =
            Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);
        let complete_const =
            Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let complete_alpha = Expr::app(Expr::app(complete_const, alpha.clone()), inst.clone());
        let (hcomp_id, _hcomp) = b.fresh_local(complete_alpha.clone());

        let seq_type = Expr::arrow(nat_const, alpha.clone());
        let (seq_id, seq) = b.fresh_local(seq_type.clone());

        let cauchy_seq_of_seq = Expr::app(
            Expr::app(Expr::app(cauchy_seq_const, alpha.clone()), inst.clone()),
            seq.clone(),
        );
        let (hcauchy_id, _hcauchy) = b.fresh_local(cauchy_seq_of_seq.clone());

        let (limit_id, limit) = b.fresh_local(alpha.clone());
        let converges_seq_limit = Expr::app(
            Expr::app(
                Expr::app(Expr::app(converges_const, alpha.clone()), inst.clone()),
                seq.clone(),
            ),
            limit.clone(),
        );
        let exists_body = b.mk_lam(
            limit_id,
            BinderInfo::Default,
            alpha.clone(),
            converges_seq_limit,
        );
        let exists_limit = Expr::app(Expr::app(exists_const, alpha.clone()), exists_body);

        let e = b.mk_pi(
            hcauchy_id,
            BinderInfo::Default,
            cauchy_seq_of_seq,
            exists_limit,
        );
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(hcomp_id, BinderInfo::Default, complete_alpha, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.complete_spec"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_complete_of_seq_limit(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let cauchy_seq_const =
            Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);
        let converges_const =
            Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);
        let complete_const =
            Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let seq_type = Expr::arrow(nat_const, alpha.clone());
        let (seq_id, seq) = b.fresh_local(seq_type.clone());

        let cauchy_seq_intro = Expr::app(
            Expr::app(Expr::app(cauchy_seq_const, alpha.clone()), inst.clone()),
            seq.clone(),
        );

        let (limit_id, limit) = b.fresh_local(alpha.clone());
        let converges_intro = Expr::app(
            Expr::app(
                Expr::app(Expr::app(converges_const, alpha.clone()), inst.clone()),
                seq.clone(),
            ),
            limit.clone(),
        );
        let exists_limit_intro = Expr::app(
            Expr::app(exists_const, alpha.clone()),
            b.mk_lam(
                limit_id,
                BinderInfo::Default,
                alpha.clone(),
                converges_intro,
            ),
        );

        let forall_seq_type = b.mk_pi(
            seq_id,
            BinderInfo::Default,
            seq_type,
            Expr::arrow(cauchy_seq_intro, exists_limit_intro),
        );
        let (h_id, _h) = b.fresh_local(forall_seq_type.clone());

        let complete_result = Expr::app(Expr::app(complete_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(h_id, BinderInfo::Default, forall_seq_type, complete_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.complete_of_seq_limit"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_converges_unique(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let converges_const =
            Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let seq_type = Expr::arrow(nat_const, alpha.clone());
        let (seq_id, seq) = b.fresh_local(seq_type.clone());
        let (limit1_id, limit1) = b.fresh_local(alpha.clone());
        let (limit2_id, limit2) = b.fresh_local(alpha.clone());

        let converges_seq_limit1 = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(converges_const.clone(), alpha.clone()),
                    inst.clone(),
                ),
                seq.clone(),
            ),
            limit1.clone(),
        );
        let (hconv1_id, _hconv1) = b.fresh_local(converges_seq_limit1.clone());

        let converges_seq_limit2 = Expr::app(
            Expr::app(
                Expr::app(Expr::app(converges_const, alpha.clone()), inst.clone()),
                seq.clone(),
            ),
            limit2.clone(),
        );
        let (hconv2_id, _hconv2) = b.fresh_local(converges_seq_limit2.clone());

        let eq_limits = Expr::app(
            Expr::app(Expr::app(eq_const, alpha.clone()), limit1),
            limit2,
        );

        let e = b.mk_pi(
            hconv2_id,
            BinderInfo::Default,
            converges_seq_limit2,
            eq_limits,
        );
        let e = b.mk_pi(hconv1_id, BinderInfo::Default, converges_seq_limit1, e);
        let e = b.mk_pi(limit2_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(limit1_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.converges_unique"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_converges_of_cauchy_complete(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let cauchy_seq_const =
            Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);
        let converges_const =
            Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);
        let complete_const =
            Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let complete_alt = Expr::app(Expr::app(complete_const, alpha.clone()), inst.clone());
        let (hcomp_id, _hcomp) = b.fresh_local(complete_alt.clone());

        let seq_type = Expr::arrow(nat_const, alpha.clone());
        let (seq_id, seq) = b.fresh_local(seq_type.clone());

        let cauchy_alt = Expr::app(
            Expr::app(Expr::app(cauchy_seq_const, alpha.clone()), inst.clone()),
            seq.clone(),
        );
        let (hcauchy_id, _hcauchy) = b.fresh_local(cauchy_alt.clone());

        let (limit_id, limit) = b.fresh_local(alpha.clone());
        let converges_alt = Expr::app(
            Expr::app(
                Expr::app(Expr::app(converges_const, alpha.clone()), inst.clone()),
                seq.clone(),
            ),
            limit.clone(),
        );
        let exists_alt = Expr::app(
            Expr::app(exists_const, alpha.clone()),
            b.mk_lam(limit_id, BinderInfo::Default, alpha.clone(), converges_alt),
        );

        let e = b.mk_pi(hcauchy_id, BinderInfo::Default, cauchy_alt, exists_alt);
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(hcomp_id, BinderInfo::Default, complete_alt, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.converges_of_cauchy_complete"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }
}
