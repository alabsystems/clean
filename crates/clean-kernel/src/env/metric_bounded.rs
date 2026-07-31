// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metric boundedness axioms
//!
//! Split from metric_completeness.rs (#307). Contains:
//! - Metric.Bounded type and axioms (bounded_spec, bounded_of_diam,
//!   bounded_dist_le, complete_bounded_cauchy)

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
    /// Initialize Metric.Bounded and related axioms.
    ///
    /// Adds: Metric.Bounded, bounded_spec, bounded_of_diam,
    ///       bounded_dist_le, complete_bounded_cauchy
    #[cfg(test)]
    pub(crate) fn init_metric_bounded(&mut self) -> Result<(), EnvError> {
        if self.metric_bounded_init {
            return Ok(());
        }
        self.init_metric_space()?;
        self.init_metric_complete()?;
        self.init_eq()?;
        self.init_exists()?;

        self.add_metric_bounded_type()?;
        self.add_metric_bounded_spec()?;
        self.add_metric_bounded_of_diam()?;
        self.add_metric_bounded_dist_le()?;
        self.add_metric_complete_bounded_cauchy()?;

        self.metric_bounded_init = true;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn has_metric_bounded(&self) -> bool {
        self.metric_bounded_init
    }

    #[cfg(test)]
    fn add_metric_bounded_type(&mut self) -> Result<(), EnvError> {
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
            name: Name::from_string("Metric.Bounded"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_bounded_spec(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let dist_const = Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);
        let le_const = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let bounded_const =
            Expr::const_(Name::from_string("Metric.Bounded"), vec![u_level.clone()]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let bounded_alpha = Expr::app(Expr::app(bounded_const, alpha.clone()), inst.clone());
        let (hbounded_id, _hbounded) = b.fresh_local(bounded_alpha.clone());

        let (m_id, m) = b.fresh_local(rat_const.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());

        let dist_x_y = Expr::app(
            Expr::app(
                Expr::app(Expr::app(dist_const, alpha.clone()), inst.clone()),
                x.clone(),
            ),
            y.clone(),
        );
        let le_dist_m = Expr::app(Expr::app(le_const, dist_x_y), m.clone());

        let forall_y = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), le_dist_m);
        let forall_xy = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), forall_y);
        let exists_body = b.mk_lam(m_id, BinderInfo::Default, rat_const.clone(), forall_xy);
        let exists_m = Expr::app(Expr::app(exists_const, rat_const), exists_body);

        let e = b.mk_pi(hbounded_id, BinderInfo::Default, bounded_alpha, exists_m);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.bounded_spec"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_bounded_of_diam(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let dist_const = Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);
        let le_const = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let bounded_const =
            Expr::const_(Name::from_string("Metric.Bounded"), vec![u_level.clone()]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let (m_id, m) = b.fresh_local(rat_const.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());

        let dist_x_y = Expr::app(
            Expr::app(
                Expr::app(Expr::app(dist_const, alpha.clone()), inst.clone()),
                x.clone(),
            ),
            y.clone(),
        );
        let le_dist_m = Expr::app(Expr::app(le_const, dist_x_y), m.clone());

        let forall_y = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), le_dist_m);
        let forall_xy = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), forall_y);
        let exists_body = b.mk_lam(m_id, BinderInfo::Default, rat_const.clone(), forall_xy);
        let exists_m = Expr::app(Expr::app(exists_const, rat_const), exists_body);
        let (h_id, _h) = b.fresh_local(exists_m.clone());

        let bounded_result = Expr::app(Expr::app(bounded_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(h_id, BinderInfo::Default, exists_m, bounded_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.bounded_of_diam"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_bounded_dist_le(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let dist_const = Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);
        let le_const = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let bounded_const =
            Expr::const_(Name::from_string("Metric.Bounded"), vec![u_level.clone()]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let bounded_alpha = Expr::app(Expr::app(bounded_const, alpha.clone()), inst.clone());
        let (hbounded_id, _hbounded) = b.fresh_local(bounded_alpha.clone());

        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());

        let (m_id, m) = b.fresh_local(rat_const.clone());
        let dist_x_y = Expr::app(
            Expr::app(
                Expr::app(Expr::app(dist_const, alpha.clone()), inst.clone()),
                x.clone(),
            ),
            y.clone(),
        );
        let le_dist_m = Expr::app(Expr::app(le_const, dist_x_y), m.clone());
        let exists_body = b.mk_lam(m_id, BinderInfo::Default, rat_const.clone(), le_dist_m);
        let exists_m = Expr::app(Expr::app(exists_const, rat_const), exists_body);

        let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), exists_m);
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(hbounded_id, BinderInfo::Default, bounded_alpha, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.bounded_dist_le"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_complete_bounded_cauchy(&mut self) -> Result<(), EnvError> {
        self.init_metric_cauchy_seq()?;

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
        let bounded_const =
            Expr::const_(Name::from_string("Metric.Bounded"), vec![u_level.clone()]);
        let exists_u = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let complete_alpha = Expr::app(Expr::app(complete_const, alpha.clone()), inst.clone());
        let (hcomp_id, _hcomp) = b.fresh_local(complete_alpha.clone());

        let bounded_alpha = Expr::app(Expr::app(bounded_const, alpha.clone()), inst.clone());
        let (hbounded_id, _hbounded) = b.fresh_local(bounded_alpha.clone());

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
        let exists_limit = Expr::app(Expr::app(exists_u, alpha.clone()), exists_body);

        let e = b.mk_pi(
            hcauchy_id,
            BinderInfo::Default,
            cauchy_seq_of_seq,
            exists_limit,
        );
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(hbounded_id, BinderInfo::Default, bounded_alpha, e);
        let e = b.mk_pi(hcomp_id, BinderInfo::Default, complete_alpha, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.complete_bounded_cauchy"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }
}
