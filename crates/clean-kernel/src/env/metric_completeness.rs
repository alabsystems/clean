// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metric Cauchy sequence axioms
//!
//! Split from original metric_completeness.rs (#307). Contains only CauchySeq
//! and Converges axioms. Other groups moved to:
//! - metric_complete.rs: Metric.Complete
//! - metric_bounded.rs: Metric.Bounded
//! - metric_compact.rs: Metric.Compact
//! - metric_totally_bounded.rs: Metric.TotallyBounded
//! - metric_separable.rs: Metric.Dense, Metric.Separable

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
    /// Initialize Cauchy sequence type and related axioms for metric spaces.
    ///
    /// Adds: Metric.CauchySeq, cauchy_const, cauchy_tail,
    ///       cauchy_of_uniform_continuous, Metric.Converges,
    ///       cauchy_of_converges, converges_const
    #[cfg(test)]
    pub(crate) fn init_metric_cauchy_seq(&mut self) -> Result<(), EnvError> {
        if self.metric_cauchy_seq_init {
            return Ok(());
        }
        self.init_metric_space()?;
        self.init_metric_uniform_continuous()?;
        self.init_nat()?;
        self.init_nat_arith_lemmas()?;
        self.init_rat()?;

        self.add_metric_cauchy_seq_type()?;
        self.add_metric_cauchy_const()?;
        self.add_metric_cauchy_tail()?;
        self.add_metric_cauchy_of_uc()?;
        self.add_metric_converges_type()?;
        self.add_metric_cauchy_of_converges()?;
        self.add_metric_converges_const()?;

        self.metric_cauchy_seq_init = true;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn has_metric_cauchy_seq(&self) -> bool {
        self.metric_cauchy_seq_init
    }

    /// Metric.CauchySeq : {α : Type u} → [MetricSpace α] → (Nat → α) → Prop
    #[cfg(test)]
    fn add_metric_cauchy_seq_type(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, _inst) = b.fresh_local(metric_alpha.clone());
        let seq_type = Expr::arrow(nat_const, alpha.clone());
        let (seq_id, _seq) = b.fresh_local(seq_type.clone());
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, prop);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.CauchySeq"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    /// Metric.cauchy_const : ∀ (c : α), Metric.CauchySeq (fun _ => c)
    #[cfg(test)]
    fn add_metric_cauchy_const(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let cauchy_seq = Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());
        let (c_id, c) = b.fresh_local(alpha.clone());

        let (n_id, _n) = b.fresh_local(nat_const.clone());
        let const_fun = b.mk_lam(n_id, BinderInfo::Default, nat_const, c.clone());
        let cauchy_const_fun = Expr::app(
            Expr::app(Expr::app(cauchy_seq, alpha.clone()), inst.clone()),
            const_fun,
        );

        let e = b.mk_pi(c_id, BinderInfo::Default, alpha.clone(), cauchy_const_fun);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.cauchy_const"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    /// Metric.cauchy_tail : CauchySeq seq → CauchySeq (fun n => seq (n + k))
    #[cfg(test)]
    fn add_metric_cauchy_tail(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let cauchy_seq = Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());
        let seq_type = Expr::arrow(nat_const.clone(), alpha.clone());
        let (seq_id, seq) = b.fresh_local(seq_type.clone());
        let (k_id, k) = b.fresh_local(nat_const.clone());
        let cauchy_seq_for_seq = Expr::app(
            Expr::app(Expr::app(cauchy_seq.clone(), alpha.clone()), inst.clone()),
            seq.clone(),
        );
        let (hc_id, _hc) = b.fresh_local(cauchy_seq_for_seq.clone());

        let (n_id, n) = b.fresh_local(nat_const.clone());
        let tail_fun = b.mk_lam(
            n_id,
            BinderInfo::Default,
            nat_const,
            Expr::app(
                seq.clone(),
                Expr::app(Expr::app(nat_add, n.clone()), k.clone()),
            ),
        );
        let cauchy_tail_result = Expr::app(
            Expr::app(Expr::app(cauchy_seq, alpha.clone()), inst.clone()),
            tail_fun,
        );

        let e = b.mk_pi(
            hc_id,
            BinderInfo::Default,
            cauchy_seq_for_seq,
            cauchy_tail_result,
        );
        let e = b.mk_pi(
            k_id,
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            e,
        );
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.cauchy_tail"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    /// Metric.cauchy_of_uniform_continuous : UC f → CauchySeq seq → CauchySeq (f ∘ seq)
    #[cfg(test)]
    fn add_metric_cauchy_of_uc(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let cauchy_seq = Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);
        let uc_const = Expr::const_(
            Name::from_string("Metric.UniformContinuous"),
            vec![u_level.clone()],
        );

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space.clone(), alpha.clone());
        let metric_beta = Expr::app(metric_space, beta.clone());
        let (inst_alpha_id, inst_alpha) = b.fresh_local(metric_alpha.clone());
        let (inst_beta_id, inst_beta) = b.fresh_local(metric_beta.clone());
        let f_type = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_type.clone());
        let seq_type = Expr::arrow(nat_const.clone(), alpha.clone());
        let (seq_id, seq) = b.fresh_local(seq_type.clone());

        let uc_f = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(uc_const, alpha.clone()), beta.clone()),
                    inst_alpha.clone(),
                ),
                inst_beta.clone(),
            ),
            f.clone(),
        );
        let (huc_id, _huc) = b.fresh_local(uc_f.clone());

        let cauchy_seq_alpha = Expr::app(
            Expr::app(
                Expr::app(cauchy_seq.clone(), alpha.clone()),
                inst_alpha.clone(),
            ),
            seq.clone(),
        );
        let (hc_id, _hc) = b.fresh_local(cauchy_seq_alpha.clone());

        let (n_id, n) = b.fresh_local(nat_const.clone());
        let composed_seq = b.mk_lam(
            n_id,
            BinderInfo::Default,
            nat_const,
            Expr::app(f.clone(), Expr::app(seq.clone(), n.clone())),
        );
        let cauchy_composed_result = Expr::app(
            Expr::app(Expr::app(cauchy_seq, beta.clone()), inst_beta.clone()),
            composed_seq,
        );

        let e = b.mk_pi(
            hc_id,
            BinderInfo::Default,
            cauchy_seq_alpha,
            cauchy_composed_result,
        );
        let e = b.mk_pi(huc_id, BinderInfo::Default, uc_f, e);
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_type, e);
        let e = b.mk_pi(inst_beta_id, BinderInfo::InstImplicit, metric_beta, e);
        let e = b.mk_pi(inst_alpha_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.cauchy_of_uniform_continuous"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    /// Metric.Converges : {α : Type u} → [MetricSpace α] → (Nat → α) → α → Prop
    #[cfg(test)]
    fn add_metric_converges_type(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, _inst) = b.fresh_local(metric_alpha.clone());
        let seq_type = Expr::arrow(nat_const, alpha.clone());
        let (seq_id, _seq) = b.fresh_local(seq_type.clone());
        let (limit_id, _limit) = b.fresh_local(alpha.clone());

        let e = b.mk_pi(limit_id, BinderInfo::Default, alpha.clone(), prop);
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.Converges"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    /// Metric.cauchy_of_converges : Converges seq limit → CauchySeq seq
    #[cfg(test)]
    fn add_metric_cauchy_of_converges(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let cauchy_seq = Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);
        let converges = Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());
        let seq_type = Expr::arrow(nat_const, alpha.clone());
        let (seq_id, seq) = b.fresh_local(seq_type.clone());
        let (limit_id, limit) = b.fresh_local(alpha.clone());

        let converges_seq_limit = Expr::app(
            Expr::app(
                Expr::app(Expr::app(converges, alpha.clone()), inst.clone()),
                seq.clone(),
            ),
            limit.clone(),
        );
        let (hconv_id, _hconv) = b.fresh_local(converges_seq_limit.clone());

        let cauchy_result = Expr::app(
            Expr::app(Expr::app(cauchy_seq, alpha.clone()), inst.clone()),
            seq.clone(),
        );

        let e = b.mk_pi(
            hconv_id,
            BinderInfo::Default,
            converges_seq_limit,
            cauchy_result,
        );
        let e = b.mk_pi(limit_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(seq_id, BinderInfo::Default, seq_type, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.cauchy_of_converges"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }

    /// Metric.converges_const : ∀ (c : α), Converges (fun _ => c) c
    #[cfg(test)]
    fn add_metric_converges_const(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let converges = Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let metric_alpha = Expr::app(metric_space, alpha.clone());
        let (inst_id, inst) = b.fresh_local(metric_alpha.clone());
        let (c_id, c) = b.fresh_local(alpha.clone());

        let (n_id, _n) = b.fresh_local(nat_const.clone());
        let const_fun = b.mk_lam(n_id, BinderInfo::Default, nat_const, c.clone());

        let converges_result = Expr::app(
            Expr::app(
                Expr::app(Expr::app(converges, alpha.clone()), inst.clone()),
                const_fun,
            ),
            c.clone(),
        );

        let e = b.mk_pi(c_id, BinderInfo::Default, alpha.clone(), converges_result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, metric_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Metric.converges_const"),
            level_params: vec![u],
            type_: b.finish(e),
        })
    }
}
