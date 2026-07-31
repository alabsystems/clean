// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Connected topological spaces
//!
//! This module contains declaration templates and init/has functions for connected
//! spaces and clopen sets. A topological space is connected if it cannot be written
//! as the disjoint union of two nonempty open sets.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Build the sequence of declarations for `Topology.Connected` and related axioms.
///
/// Returns declarations in registration order. Requires that TopologicalSpace,
/// Continuous, Iff, And, and Classical (Or) are already initialized.
pub(crate) fn topology_connected_decl_templates() -> Vec<Declaration> {
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
    let is_closed = |lvl: Level| Expr::const_(Name::from_string("IsClosed"), vec![lvl]);
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let or_const = Expr::const_(Name::from_string("Or"), vec![]);
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);

    // Topology.IsClopen
    let is_clopen_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let s_type = Expr::arrow(alpha.clone(), prop.clone());
        let (s_id, _s) = b.fresh_local(s_type.clone());
        let e = b.mk_pi(s_id, BinderInfo::Default, s_type, prop.clone());
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.IsClopen"),
        level_params: vec![u.clone()],
        type_: is_clopen_type,
    });

    let is_clopen = |lvl: Level| Expr::const_(Name::from_string("Topology.IsClopen"), vec![lvl]);

    // Topology.isClopen_def
    let isclopen_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let s_type = Expr::arrow(alpha.clone(), prop.clone());
        let (s_id, s) = b.fresh_local(s_type.clone());

        let isclopen_s = Expr::apps(
            is_clopen(u_level.clone()),
            [alpha.clone(), inst.clone(), s.clone()],
        );
        let isopen_s = Expr::apps(
            is_open(u_level.clone()),
            [alpha.clone(), inst.clone(), s.clone()],
        );
        let isclosed_s = Expr::apps(
            is_closed(u_level.clone()),
            [alpha.clone(), inst.clone(), s.clone()],
        );

        let and_open_closed = Expr::app(Expr::app(and_const.clone(), isopen_s), isclosed_s);
        let iff_clopen = Expr::app(Expr::app(iff_const.clone(), isclopen_s), and_open_closed);

        let e = b.mk_pi(s_id, BinderInfo::Default, s_type, iff_clopen);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.isClopen_def"),
        level_params: vec![u.clone()],
        type_: isclopen_def_type,
    });

    // Topology.Connected
    let connected_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            prop.clone(),
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.Connected"),
        level_params: vec![u.clone()],
        type_: connected_type,
    });

    let topology_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Connected"), vec![lvl]);

    let eq_name = Name::from_string("Eq");

    // Topology.connected_def
    let connected_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        let connected_inst = Expr::app(
            Expr::app(topology_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );

        let forall_s = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let s_type = Expr::arrow(alpha.clone(), prop.clone());
            let (s_id, s) = sub.fresh_local(s_type.clone());
            let isclopen_s = Expr::apps(
                is_clopen(u_level.clone()),
                [alpha.clone(), inst.clone(), s.clone()],
            );
            let (hclopen_id, _hclopen) = sub.fresh_local(isclopen_s.clone());

            let empty_set = {
                let mut sub2 = EnvDeclBuilder::child_of(&sub);
                let (x_id, _x) = sub2.fresh_local(alpha.clone());
                sub2.mk_lam(
                    x_id,
                    BinderInfo::Default,
                    alpha.clone(),
                    false_const.clone(),
                )
            };
            let univ_set = {
                let mut sub2 = EnvDeclBuilder::child_of(&sub);
                let (x_id, _x) = sub2.fresh_local(alpha.clone());
                sub2.mk_lam(x_id, BinderInfo::Default, alpha.clone(), true_const.clone())
            };

            let eq_level = Level::succ(u_level.clone());
            let eq_empty = Expr::apps(
                Expr::const_(eq_name.clone(), vec![eq_level.clone()]),
                [s_type.clone(), s.clone(), empty_set],
            );
            let eq_univ = Expr::apps(
                Expr::const_(eq_name.clone(), vec![eq_level]),
                [s_type.clone(), s.clone(), univ_set],
            );
            let or_trivial = Expr::app(Expr::app(or_const.clone(), eq_empty), eq_univ);
            let e = sub.mk_pi(hclopen_id, BinderInfo::Default, isclopen_s, or_trivial);
            sub.mk_pi(s_id, BinderInfo::Default, s_type, e)
        };

        let iff_connected = Expr::app(Expr::app(iff_const.clone(), connected_inst), forall_s);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            iff_connected,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.connected_def"),
        level_params: vec![u.clone()],
        type_: connected_def_type,
    });

    // Topology.clopen_empty
    let clopen_empty_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let empty_set = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (x_id, _x) = sub.fresh_local(alpha.clone());
            sub.mk_lam(
                x_id,
                BinderInfo::Default,
                alpha.clone(),
                false_const.clone(),
            )
        };
        let result = Expr::apps(
            is_clopen(u_level.clone()),
            [alpha.clone(), inst.clone(), empty_set],
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
        name: Name::from_string("Topology.clopen_empty"),
        level_params: vec![u.clone()],
        type_: clopen_empty_type,
    });

    // Topology.clopen_univ
    let clopen_univ_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let univ_set = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (x_id, _x) = sub.fresh_local(alpha.clone());
            sub.mk_lam(x_id, BinderInfo::Default, alpha.clone(), true_const.clone())
        };
        let result = Expr::apps(
            is_clopen(u_level.clone()),
            [alpha.clone(), inst.clone(), univ_set],
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
        name: Name::from_string("Topology.clopen_univ"),
        level_params: vec![u.clone()],
        type_: clopen_univ_type,
    });

    // Topology.continuous_image_connected
    let topology_continuous_const = |u_lvl: Level, v_lvl: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![u_lvl, v_lvl])
    };

    let continuous_image_connected_type = {
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
            topology_continuous_const(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
            ],
        );
        let (hf_id, _hf) = b.fresh_local(continuous_f.clone());
        let connected_alpha = Expr::app(
            Expr::app(topology_connected(u_level.clone()), alpha.clone()),
            inst_a.clone(),
        );
        let (hc_id, _hc) = b.fresh_local(connected_alpha.clone());
        let connected_beta = Expr::app(
            Expr::app(topology_connected(v_level.clone()), beta.clone()),
            inst_b.clone(),
        );

        let e = b.mk_pi(hc_id, BinderInfo::Default, connected_alpha, connected_beta);
        let e = b.mk_pi(hf_id, BinderInfo::Default, continuous_f, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_type, e);
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
        name: Name::from_string("Topology.continuous_image_connected"),
        level_params: vec![u.clone(), v.clone()],
        type_: continuous_image_connected_type,
    });

    decls
}

impl Environment {
    /// Initialize Topology.Connected and related theorems about connected topological spaces.
    ///
    /// A topological space is connected if it cannot be written as the disjoint union
    /// of two nonempty open sets. Equivalently, the only clopen (simultaneously open
    /// and closed) sets are the empty set and the whole space.
    ///
    /// This adds:
    /// - `Topology.Connected`: Predicate for connected topological spaces
    /// - `Topology.connected_def`: Characterization via clopen sets
    /// - `Topology.IsClopen`: Predicate for clopen (simultaneously open and closed) sets
    /// - `Topology.isClopen_def`: Clopen iff both open and closed
    /// - `Topology.connected_iff_clopen`: Connected iff only trivial clopen sets
    /// - `Topology.continuous_image_connected`: Continuous image of connected is connected
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_connected_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_connected(&mut self) -> Result<(), EnvError> {
        if self.topology_connected_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain
        crate::expr::stack_safe(|| {
            self.init_topological_space()?;
            self.init_topology_continuous()?;
            self.init_iff()?;
            self.init_and()?;
            self.init_classical()?;

            self.add_init_decls(topology_connected_decl_templates())?;

            self.topology_connected_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Connected has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_connected_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_connected(&self) -> bool {
        self.topology_connected_init
    }
}
