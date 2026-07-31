// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metric total boundedness axioms
//!
//! Split from metric_completeness.rs (#307). Contains:
//! - Metric.TotallyBounded type and axioms (totally_bounded_of_compact,
//!   bounded_of_totally_bounded, compact_iff_complete_totally_bounded,
//!   totally_bounded_spec, totally_bounded_of_eps_net)

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
    /// Initialize Metric.TotallyBounded and related axioms.
    ///
    /// Adds: Metric.TotallyBounded, totally_bounded_of_compact,
    ///       bounded_of_totally_bounded, compact_iff_complete_totally_bounded,
    ///       totally_bounded_spec, totally_bounded_of_eps_net
    #[cfg(test)]
    pub(crate) fn init_metric_totally_bounded(&mut self) -> Result<(), EnvError> {
        if self.metric_totally_bounded_init {
            return Ok(());
        }
        self.init_metric_compact()?;
        self.init_and()?;
        self.init_iff()?;

        self.add_metric_totally_bounded_type()?;
        self.add_metric_totally_bounded_of_compact()?;
        self.add_metric_bounded_of_totally_bounded()?;
        self.add_metric_compact_iff_complete_tb()?;
        self.add_metric_totally_bounded_spec()?;
        self.add_metric_totally_bounded_of_eps_net()?;

        self.metric_totally_bounded_init = true;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn has_metric_totally_bounded(&self) -> bool {
        self.metric_totally_bounded_init
    }

    #[cfg(test)]
    fn add_metric_totally_bounded_type(&mut self) -> Result<(), EnvError> {
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
            name: Name::from_string("Metric.TotallyBounded"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_totally_bounded_of_compact(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let compact_const =
            Expr::const_(Name::from_string("Metric.Compact"), vec![u_level.clone()]);
        let tb_const = Expr::const_(
            Name::from_string("Metric.TotallyBounded"),
            vec![u_level.clone()],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let compact_alpha = Expr::app(Expr::app(compact_const, alpha.clone()), inst.clone());
        let (hcompact_id, _) = b.fresh_local(compact_alpha.clone());

        let tb_result = Expr::app(Expr::app(tb_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(hcompact_id, BinderInfo::Default, compact_alpha, tb_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.totally_bounded_of_compact"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_bounded_of_totally_bounded(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let tb_const = Expr::const_(
            Name::from_string("Metric.TotallyBounded"),
            vec![u_level.clone()],
        );
        let bounded_const =
            Expr::const_(Name::from_string("Metric.Bounded"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let tb_alpha = Expr::app(Expr::app(tb_const, alpha.clone()), inst.clone());
        let (htb_id, _) = b.fresh_local(tb_alpha.clone());

        let bounded_result = Expr::app(Expr::app(bounded_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(htb_id, BinderInfo::Default, tb_alpha, bounded_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.bounded_of_totally_bounded"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_compact_iff_complete_tb(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let compact_const =
            Expr::const_(Name::from_string("Metric.Compact"), vec![u_level.clone()]);
        let complete_const =
            Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);
        let tb_const = Expr::const_(
            Name::from_string("Metric.TotallyBounded"),
            vec![u_level.clone()],
        );
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let compact_alpha = Expr::app(Expr::app(compact_const, alpha.clone()), inst.clone());
        let complete_alpha = Expr::app(Expr::app(complete_const, alpha.clone()), inst.clone());
        let tb_alpha = Expr::app(Expr::app(tb_const, alpha.clone()), inst.clone());

        let complete_and_tb = Expr::app(Expr::app(and_const, complete_alpha), tb_alpha);
        let iff_body = Expr::app(Expr::app(iff_const, compact_alpha), complete_and_tb);

        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, iff_body);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.compact_iff_complete_totally_bounded"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_totally_bounded_spec(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let dist_const = Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);
        let lt_const = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let tb_const = Expr::const_(
            Name::from_string("Metric.TotallyBounded"),
            vec![u_level.clone()],
        );
        let exists_u = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let tb_alpha = Expr::app(Expr::app(tb_const, alpha.clone()), inst.clone());
        let (htb_id, _) = b.fresh_local(tb_alpha.clone());

        let eps_net = build_eps_net_prop(
            &mut b,
            &alpha,
            &inst,
            &rat_const,
            &lt_const,
            &zero,
            &dist_const,
            &exists_u,
        );

        let e = b.mk_pi(htb_id, BinderInfo::Default, tb_alpha, eps_net);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.totally_bounded_spec"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    fn add_metric_totally_bounded_of_eps_net(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let dist_const = Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);
        let lt_const = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let tb_const = Expr::const_(
            Name::from_string("Metric.TotallyBounded"),
            vec![u_level.clone()],
        );
        let exists_u = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let eps_net = build_eps_net_prop(
            &mut b,
            &alpha,
            &inst,
            &rat_const,
            &lt_const,
            &zero,
            &dist_const,
            &exists_u,
        );
        let (h_id, _) = b.fresh_local(eps_net.clone());

        let tb_result = Expr::app(Expr::app(tb_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(h_id, BinderInfo::Default, eps_net, tb_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.totally_bounded_of_eps_net"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }
}

/// Build: ∀ ε : Rat, 0 < ε → ∀ x : α, ∃ c : α, dist x c < ε
#[cfg(test)]
fn build_eps_net_prop(
    b: &mut EnvDeclBuilder,
    alpha: &Expr,
    inst: &Expr,
    rat_const: &Expr,
    lt_const: &Expr,
    zero: &Expr,
    dist_const: &Expr,
    exists_u: &Expr,
) -> Expr {
    let (eps_id, eps) = b.fresh_local(rat_const.clone());
    let eps_gt_zero = Expr::app(Expr::app(lt_const.clone(), zero.clone()), eps.clone());
    let (hpos_id, _) = b.fresh_local(eps_gt_zero.clone());

    let (x_id, x) = b.fresh_local(alpha.clone());
    let (c_id, c) = b.fresh_local(alpha.clone());

    let dist_x_c = Expr::app(
        Expr::app(
            Expr::app(Expr::app(dist_const.clone(), alpha.clone()), inst.clone()),
            x.clone(),
        ),
        c.clone(),
    );
    let dist_lt_eps = Expr::app(Expr::app(lt_const.clone(), dist_x_c), eps.clone());

    let exists_body = b.mk_lam(c_id, BinderInfo::Default, alpha.clone(), dist_lt_eps);
    let exists_c = Expr::app(Expr::app(exists_u.clone(), alpha.clone()), exists_body);

    let forall_x = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), exists_c);
    let eps_implies = b.mk_pi(hpos_id, BinderInfo::Default, eps_gt_zero, forall_x);
    b.mk_pi(eps_id, BinderInfo::Default, rat_const.clone(), eps_implies)
}
