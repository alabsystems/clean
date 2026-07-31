// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metric compactness axioms
//!
//! Split from metric_completeness.rs (#307). Contains:
//! - Metric.Compact type and axioms (bounded_of_compact, complete_of_compact,
//!   compact_cauchy_converges)

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
    /// Initialize Metric.Compact and related axioms.
    ///
    /// Adds: Metric.Compact, bounded_of_compact, complete_of_compact,
    ///       compact_cauchy_converges
    #[cfg(test)]
    pub(crate) fn init_metric_compact(&mut self) -> Result<(), EnvError> {
        if self.metric_compact_init {
            return Ok(());
        }
        self.init_metric_bounded()?;
        self.init_metric_complete()?;
        self.init_metric_cauchy_seq()?;

        self.add_metric_compact_type()?;
        self.add_metric_bounded_of_compact()?;
        self.add_metric_complete_of_compact()?;
        self.add_metric_compact_cauchy_converges()?;

        self.metric_compact_init = true;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn has_metric_compact(&self) -> bool {
        self.metric_compact_init
    }

    #[cfg(test)]
    fn add_metric_compact_type(&mut self) -> Result<(), EnvError> {
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
            name: Name::from_string("Metric.Compact"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_bounded_of_compact(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let compact_const =
            Expr::const_(Name::from_string("Metric.Compact"), vec![u_level.clone()]);
        let bounded_const =
            Expr::const_(Name::from_string("Metric.Bounded"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let compact_alpha = Expr::app(Expr::app(compact_const, alpha.clone()), inst.clone());
        let (hcompact_id, _hcompact) = b.fresh_local(compact_alpha.clone());

        let bounded_result = Expr::app(Expr::app(bounded_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(
            hcompact_id,
            BinderInfo::Default,
            compact_alpha,
            bounded_result,
        );
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.bounded_of_compact"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_complete_of_compact(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let compact_const =
            Expr::const_(Name::from_string("Metric.Compact"), vec![u_level.clone()]);
        let complete_const =
            Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let compact_alpha = Expr::app(Expr::app(compact_const, alpha.clone()), inst.clone());
        let (hcompact_id, _hcompact) = b.fresh_local(compact_alpha.clone());

        let complete_result = Expr::app(Expr::app(complete_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(
            hcompact_id,
            BinderInfo::Default,
            compact_alpha,
            complete_result,
        );
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.complete_of_compact"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_compact_cauchy_converges(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let compact_const =
            Expr::const_(Name::from_string("Metric.Compact"), vec![u_level.clone()]);
        let cauchy_seq_const =
            Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);
        let converges_const =
            Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);
        let exists_u = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let compact_alpha = Expr::app(Expr::app(compact_const, alpha.clone()), inst.clone());
        let (hcompact_id, _hcompact) = b.fresh_local(compact_alpha.clone());

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
        let e = b.mk_pi(hcompact_id, BinderInfo::Default, compact_alpha, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.compact_cauchy_converges"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }
}
