// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metric separability axioms
//!
//! Split from metric_completeness.rs (#307). Contains:
//! - Metric.Dense and Metric.Separable types
//! - Axioms: separable_of_totally_bounded, separable_of_compact,
//!   separable_spec, separable_of_dense_exists

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Metric.Separable and related axioms.
    ///
    /// Adds: Metric.Dense, Metric.Separable, separable_of_totally_bounded,
    ///       separable_of_compact, separable_spec, separable_of_dense_exists
    pub(crate) fn init_metric_separable(&mut self) -> Result<(), EnvError> {
        if self.metric_separable_init {
            return Ok(());
        }
        self.init_metric_totally_bounded()?;
        self.init_and()?;

        self.add_metric_dense_type()?;
        self.add_metric_separable_type()?;
        self.add_metric_separable_of_tb()?;
        self.add_metric_separable_of_compact()?;
        self.add_metric_separable_spec()?;
        self.add_metric_separable_of_dense_exists()?;

        self.metric_separable_init = true;
        Ok(())
    }

    pub(crate) fn has_metric_separable(&self) -> bool {
        self.metric_separable_init
    }

    fn add_metric_dense_type(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, _inst) = b.fresh_local(metric_alpha.clone());
        let (d_id, _d) = b.fresh_local(alpha.clone());

        let e = b.mk_pi(d_id, BinderInfo::Default, alpha.clone(), prop);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.Dense"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_separable_type(&mut self) -> Result<(), EnvError> {
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
            name: Name::from_string("Metric.Separable"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_separable_of_tb(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let tb_const = Expr::const_(
            Name::from_string("Metric.TotallyBounded"),
            vec![u_level.clone()],
        );
        let sep_const = Expr::const_(Name::from_string("Metric.Separable"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let tb_alpha = Expr::app(Expr::app(tb_const, alpha.clone()), inst.clone());
        let (htb_id, _) = b.fresh_local(tb_alpha.clone());

        let sep_result = Expr::app(Expr::app(sep_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(htb_id, BinderInfo::Default, tb_alpha, sep_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.separable_of_totally_bounded"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_separable_of_compact(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let compact_const =
            Expr::const_(Name::from_string("Metric.Compact"), vec![u_level.clone()]);
        let sep_const = Expr::const_(Name::from_string("Metric.Separable"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let compact_alpha = Expr::app(Expr::app(compact_const, alpha.clone()), inst.clone());
        let (hcompact_id, _) = b.fresh_local(compact_alpha.clone());

        let sep_result = Expr::app(Expr::app(sep_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(hcompact_id, BinderInfo::Default, compact_alpha, sep_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.separable_of_compact"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_separable_spec(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let dist_const = Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);
        let lt_const = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let dense_const = Expr::const_(Name::from_string("Metric.Dense"), vec![u_level.clone()]);
        let sep_const = Expr::const_(Name::from_string("Metric.Separable"), vec![u_level.clone()]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let exists_u = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let sep_alpha = Expr::app(Expr::app(sep_const, alpha.clone()), inst.clone());
        let (hsep_id, _) = b.fresh_local(sep_alpha.clone());

        let dense_exists = build_dense_exists_prop(
            &mut b,
            &alpha,
            &inst,
            &rat_const,
            &lt_const,
            &zero,
            &dist_const,
            &dense_const,
            &and_const,
            &exists_u,
        );

        let e = b.mk_pi(hsep_id, BinderInfo::Default, sep_alpha, dense_exists);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.separable_spec"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    fn add_metric_separable_of_dense_exists(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let dist_const = Expr::const_(Name::from_string("MetricSpace.dist"), vec![u_level.clone()]);
        let lt_const = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let dense_const = Expr::const_(Name::from_string("Metric.Dense"), vec![u_level.clone()]);
        let sep_const = Expr::const_(Name::from_string("Metric.Separable"), vec![u_level.clone()]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let exists_u = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());

        let dense_exists = build_dense_exists_prop(
            &mut b,
            &alpha,
            &inst,
            &rat_const,
            &lt_const,
            &zero,
            &dist_const,
            &dense_const,
            &and_const,
            &exists_u,
        );
        let (h_id, _) = b.fresh_local(dense_exists.clone());

        let sep_result = Expr::app(Expr::app(sep_const, alpha.clone()), inst.clone());

        let e = b.mk_pi(h_id, BinderInfo::Default, dense_exists, sep_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.separable_of_dense_exists"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }
}

/// Build: ∀ x : α, ∀ ε : Rat, 0 < ε → ∃ d : α, Dense d ∧ dist x d < ε
fn build_dense_exists_prop(
    b: &mut EnvDeclBuilder,
    alpha: &Expr,
    inst: &Expr,
    rat_const: &Expr,
    lt_const: &Expr,
    zero: &Expr,
    dist_const: &Expr,
    dense_const: &Expr,
    and_const: &Expr,
    exists_u: &Expr,
) -> Expr {
    let (x_id, x) = b.fresh_local(alpha.clone());
    let (eps_id, eps) = b.fresh_local(rat_const.clone());
    let eps_gt_zero = Expr::app(Expr::app(lt_const.clone(), zero.clone()), eps.clone());
    let (hpos_id, _) = b.fresh_local(eps_gt_zero.clone());

    let (d_id, d) = b.fresh_local(alpha.clone());

    let dense_d = Expr::app(
        Expr::app(Expr::app(dense_const.clone(), alpha.clone()), inst.clone()),
        d.clone(),
    );

    let dist_x_d = Expr::app(
        Expr::app(
            Expr::app(Expr::app(dist_const.clone(), alpha.clone()), inst.clone()),
            x.clone(),
        ),
        d.clone(),
    );
    let dist_lt_eps = Expr::app(Expr::app(lt_const.clone(), dist_x_d), eps.clone());

    let dense_and_close = Expr::app(Expr::app(and_const.clone(), dense_d), dist_lt_eps);

    let exists_body = b.mk_lam(d_id, BinderInfo::Default, alpha.clone(), dense_and_close);
    let exists_d = Expr::app(Expr::app(exists_u.clone(), alpha.clone()), exists_body);

    let eps_implies = b.mk_pi(hpos_id, BinderInfo::Default, eps_gt_zero, exists_d);
    let forall_eps = b.mk_pi(eps_id, BinderInfo::Default, rat_const.clone(), eps_implies);
    b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), forall_eps)
}
