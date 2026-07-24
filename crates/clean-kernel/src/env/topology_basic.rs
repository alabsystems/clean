// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TopologicalSpace infrastructure and continuous maps
//!
//! This module contains the core TopologicalSpace initialization and the
//! continuous function declaration templates. Other topology concepts are
//! split into dedicated modules:
//! - topology_connected: Connected spaces and clopen sets
//! - topology_compact: Compact and locally compact spaces
//! - topology_hausdorff: Hausdorff (T2) separation axiom
//! - topology_homeomorphism: Homeomorphisms between topological spaces

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::generated_overlay::{
    load_generated_namespace_overlay, TOPOLOGICAL_SPACE_NAMESPACE,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Build the sequence of declarations for `Topology.Continuous` and related axioms.
///
/// Returns declarations in registration order. Does not include the conditional
/// `metric_continuous_iff` declaration (pass `include_metric_iff=true` for that).
///
/// This is a pure function with no side effects. Both the production init function
/// and the test harness can call it to get the same declaration list.
pub(crate) fn topology_continuous_decl_templates(include_metric_iff: bool) -> Vec<Declaration> {
    let mut decls = Vec::new();

    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let type_v = Expr::sort(Level::succ(v_level.clone()));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let is_open = |lvl: Level| Expr::const_(Name::from_string("IsOpen"), vec![lvl]);

    // Topology.Continuous
    let continuous_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (inst_a_id, _inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, _inst_b) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let f_type = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, _f) = b.fresh_local(f_type.clone());
        let result = prop.clone();
        let e = b.mk_pi(f_id, BinderInfo::Default, f_type, result);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.Continuous"),
        level_params: vec![u.clone(), v.clone()],
        type_: continuous_type,
    });

    let topology_continuous = |u_lvl: Level, v_lvl: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![u_lvl, v_lvl])
    };

    // Topology.continuous_def
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
    let continuous_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let f_type = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_type.clone());

        let continuous_f = Expr::apps(
            topology_continuous(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
            ],
        );

        let beta_to_prop = Expr::arrow(beta.clone(), prop.clone());
        let (u_set_id, u_set) = b.fresh_local(beta_to_prop.clone());
        let is_open_u = Expr::apps(
            is_open(v_level.clone()),
            [beta.clone(), inst_b.clone(), u_set.clone()],
        );
        let (h_open_id, _h_open) = b.fresh_local(is_open_u.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let preimage_body = Expr::app(u_set.clone(), Expr::app(f.clone(), x.clone()));
        let preimage_set = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), preimage_body);
        let is_open_preimage = Expr::apps(
            is_open(u_level.clone()),
            [alpha.clone(), inst_a.clone(), preimage_set],
        );
        let e = b.mk_pi(h_open_id, BinderInfo::Default, is_open_u, is_open_preimage);
        let forall_u = b.mk_pi(u_set_id, BinderInfo::Default, beta_to_prop, e);
        let iff_expr = Expr::app(Expr::app(iff_const.clone(), continuous_f.clone()), forall_u);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_type, iff_expr);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.continuous_def"),
        level_params: vec![u.clone(), v.clone()],
        type_: continuous_def_type,
    });

    // Topology.continuous_id
    let continuous_id_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x_id, x) = b.fresh_local(alpha.clone());
        let id_fun = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), x);
        let result = Expr::apps(
            topology_continuous(u_level.clone(), u_level.clone()),
            [
                alpha.clone(),
                alpha.clone(),
                inst.clone(),
                inst.clone(),
                id_fun,
            ],
        );
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            result,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.continuous_id"),
        level_params: vec![u.clone()],
        type_: continuous_id_type,
    });

    // Topology.continuous_const
    let continuous_const_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let (c_id, c) = b.fresh_local(beta.clone());
        let (x_id, _x) = b.fresh_local(alpha.clone());
        let const_fun = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), c.clone());
        let result = Expr::apps(
            topology_continuous(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                const_fun,
            ],
        );
        let e = b.mk_pi(c_id, BinderInfo::Default, beta.clone(), result);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.continuous_const"),
        level_params: vec![u.clone(), v.clone()],
        type_: continuous_const_type,
    });

    // Topology.continuous_comp
    let w = Name::from_string("w");
    let w_level = Level::param(w.clone());
    let type_w = Expr::sort(Level::succ(w_level.clone()));

    let continuous_comp_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (gamma_id, gamma) = b.fresh_local(type_w.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let (inst_c_id, inst_c) =
            b.fresh_local(Expr::app(topological_space(w_level.clone()), gamma.clone()));
        let f_type = Expr::arrow(alpha.clone(), beta.clone());
        let g_type = Expr::arrow(beta.clone(), gamma.clone());
        let (f_id, f) = b.fresh_local(f_type.clone());
        let (g_id, g) = b.fresh_local(g_type.clone());

        let continuous_f = Expr::apps(
            topology_continuous(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
            ],
        );
        let continuous_g = Expr::apps(
            topology_continuous(v_level.clone(), w_level.clone()),
            [
                beta.clone(),
                gamma.clone(),
                inst_b.clone(),
                inst_c.clone(),
                g.clone(),
            ],
        );

        let (hf_id, _hf) = b.fresh_local(continuous_f.clone());
        let (hg_id, _hg) = b.fresh_local(continuous_g.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let comp_body = Expr::app(g.clone(), Expr::app(f.clone(), x.clone()));
        let comp_fun = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), comp_body);
        let result = Expr::apps(
            topology_continuous(u_level.clone(), w_level.clone()),
            [
                alpha.clone(),
                gamma.clone(),
                inst_a.clone(),
                inst_c.clone(),
                comp_fun,
            ],
        );
        let e = b.mk_pi(hg_id, BinderInfo::Default, continuous_g, result);
        let e = b.mk_pi(hf_id, BinderInfo::Default, continuous_f, e);
        let e = b.mk_pi(g_id, BinderInfo::Default, g_type, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_type, e);
        let e = b.mk_pi(
            inst_c_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(w_level.clone()), gamma.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_w.clone(), e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.continuous_comp"),
        level_params: vec![u.clone(), v.clone(), w.clone()],
        type_: continuous_comp_type,
    });

    // Topology.metric_continuous_iff (conditional)
    if include_metric_iff {
        let metric_space_const =
            Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
        let metric_continuous_const = Expr::const_(
            Name::from_string("Metric.Continuous"),
            vec![u_level.clone()],
        );
        let metric_to_topology_const = Expr::const_(
            Name::from_string("Topology.metric_to_topology"),
            vec![u_level.clone()],
        );

        let metric_continuous_iff_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let (inst_a_id, inst_a) =
                b.fresh_local(Expr::app(metric_space_const.clone(), alpha.clone()));
            let (inst_b_id, inst_b) =
                b.fresh_local(Expr::app(metric_space_const.clone(), beta.clone()));
            let f_type = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_type.clone());

            let metric_cont_f = Expr::apps(
                metric_continuous_const.clone(),
                [
                    alpha.clone(),
                    beta.clone(),
                    inst_a.clone(),
                    inst_b.clone(),
                    f.clone(),
                ],
            );
            let topo_inst_alpha = Expr::app(
                Expr::app(metric_to_topology_const.clone(), alpha.clone()),
                inst_a.clone(),
            );
            let topo_inst_beta = Expr::app(
                Expr::app(metric_to_topology_const.clone(), beta.clone()),
                inst_b.clone(),
            );
            let topo_cont_f = Expr::apps(
                topology_continuous(u_level.clone(), u_level.clone()),
                [
                    alpha.clone(),
                    beta.clone(),
                    topo_inst_alpha,
                    topo_inst_beta,
                    f.clone(),
                ],
            );
            let result = Expr::app(Expr::app(iff_const.clone(), metric_cont_f), topo_cont_f);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_type, result);
            let e = b.mk_pi(
                inst_b_id,
                BinderInfo::InstImplicit,
                Expr::app(metric_space_const.clone(), beta.clone()),
                e,
            );
            let e = b.mk_pi(
                inst_a_id,
                BinderInfo::InstImplicit,
                Expr::app(metric_space_const.clone(), alpha.clone()),
                e,
            );
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        decls.push(Declaration::Axiom {
            name: Name::from_string("Topology.metric_continuous_iff"),
            level_params: vec![u.clone()],
            type_: metric_continuous_iff_type,
        });
    }

    decls
}

impl Environment {
    /// Initializes topological space infrastructure in the environment.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topological_space_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_topological_space(&mut self) -> Result<(), EnvError> {
        if self.topological_space_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_and()?;
            self.init_exists()?;
            self.init_true_false()?;
            self.init_iff()?;

            load_generated_namespace_overlay(self, TOPOLOGICAL_SPACE_NAMESPACE)?;

            let u = Name::from_string("u");
            let u_level = Level::param(u.clone());
            let type_u = Expr::sort(Level::succ(u_level.clone()));
            let topological_space =
                |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);

            if self.has_metric_space() {
                let metric_space_const =
                    Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

                let metric_to_topology_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let ms_alpha = Expr::app(metric_space_const.clone(), alpha.clone());
                    let (inst_id, _inst) = b.fresh_local(ms_alpha.clone());
                    let result = Expr::app(topological_space(u_level.clone()), alpha.clone());
                    let e = b.mk_pi(inst_id, BinderInfo::Default, ms_alpha, result);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };

                self.add_decl(Declaration::Axiom {
                    name: Name::from_string("Topology.metric_to_topology"),
                    level_params: vec![u.clone()],
                    type_: metric_to_topology_type,
                })?;
            }

            self.topological_space_init = true;
            Ok(())
        })
    }

    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topological_space_init == true`
    pub(crate) fn has_topological_space(&self) -> bool {
        self.topological_space_init
    }

    /// Initialize Topology.Continuous for continuous maps between topological spaces.
    ///
    /// A function f : α → β is continuous iff for every open set U in β,
    /// the preimage f⁻¹(U) is open in α.
    ///
    /// Constants added:
    /// - `Topology.Continuous : {α β : Type u} → [TopologicalSpace α] → [TopologicalSpace β] →
    ///                         (α → β) → Prop`
    /// - `Topology.continuous_def : Continuous f ↔ ∀ U, IsOpen U → IsOpen (fun x => U (f x))`
    /// - `Topology.continuous_id : Continuous (fun x => x)`
    /// - `Topology.continuous_const : ∀ c, Continuous (fun _ => c)`
    /// - `Topology.continuous_comp : Continuous f → Continuous g → Continuous (fun x => g (f x))`
    /// - `Topology.metric_continuous_iff : (MetricSpace topology) Metric.Continuous f ↔ Topology.Continuous f`
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_continuous_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_topology_continuous(&mut self) -> Result<(), EnvError> {
        if self.topology_continuous_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain
        crate::expr::stack_safe(|| {
            self.init_topological_space()?;
            self.init_iff()?;

            let include_metric_iff = self.has_metric_space() && self.has_topology_continuous();
            self.add_init_decls(topology_continuous_decl_templates(include_metric_iff))?;

            self.topology_continuous_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Continuous has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_continuous_init == true`
    pub(crate) fn has_topology_continuous(&self) -> bool {
        self.topology_continuous_init
    }
}
