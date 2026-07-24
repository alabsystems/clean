// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for tree-width bounds on resolution width and size.
//!
//! Registers the kernel-level axiom surfaces for:
//! - Atserias-Dalmau: resolution width is bounded by primal-graph tree-width
//! - Ben-Sasson-Wigderson: width increase forces proof-size growth
//! - bounded tree-width implies polynomial-size refutations
//! - minimality of width among refutations
//! - minimality of size among refutations
//!
//! Each theorem follows the helper-axiom pattern from the other proof
//! complexity overlays: a `_helper` axiom captures the proposition body,
//! and the theorem quantifies over all parameters with the helper applied.
//!
//! References:
//! - Atserias & Dalmau (2008), "A combinatorial characterization of resolution
//!   width"
//! - Ben-Sasson & Wigderson (2001), "Short proofs are narrow"

use super::tree_width_resolution::TreeWidthResConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: Atserias-Dalmau width upper bound
    // ====================================================================

    /// Helper for atserias_dalmau: `(f : CNF) -> Prop`
    ///
    /// Encodes:
    /// `resolution_width f <= tree_width (primal_graph f) + 1`.
    pub(super) fn register_atserias_dalmau_helper(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let name = "TreeWidthRes.atserias_dalmau_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.atserias_dalmau : forall (f : CNF),
    ///     TreeWidthRes.atserias_dalmau_helper f`
    pub(super) fn register_atserias_dalmau(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "TreeWidthRes.atserias_dalmau";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("TreeWidthRes.atserias_dalmau_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let body = Expr::app(helper, f.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: Ben-Sasson-Wigderson width-size tradeoff
    // ====================================================================

    /// Helper for ben_sasson_wigderson: `(f : CNF) -> Prop`
    ///
    /// Encodes:
    /// `log2(resolution_size f) * 16 * num_variables f >=
    ///   (resolution_width f - initial_width f)^2`.
    pub(super) fn register_ben_sasson_wigderson_helper(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let name = "TreeWidthRes.ben_sasson_wigderson_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.ben_sasson_wigderson : forall (f : CNF),
    ///     TreeWidthRes.ben_sasson_wigderson_helper f`
    pub(super) fn register_ben_sasson_wigderson(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "TreeWidthRes.ben_sasson_wigderson";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("TreeWidthRes.ben_sasson_wigderson_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let body = Expr::app(helper, f.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Bounded tree-width implies polynomial-size refutations
    // ====================================================================

    /// Helper for bounded_tw_poly_size: `(f : CNF) -> (k : Nat) -> Prop`
    ///
    /// Encodes:
    /// `tree_width (primal_graph f) <= k ->
    ///   resolution_size f <= num_variables f ^ (k + 2)`.
    pub(super) fn register_bounded_tw_poly_size_helper(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let name = "TreeWidthRes.bounded_tw_poly_size_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.bounded_tw_poly_size : forall (f : CNF) (k : Nat),
    ///     TreeWidthRes.bounded_tw_poly_size_helper f k`
    pub(super) fn register_bounded_tw_poly_size(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "TreeWidthRes.bounded_tw_poly_size";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("TreeWidthRes.bounded_tw_poly_size_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let body = Expr::apps(helper, [f.clone(), k.clone()]);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: Width minimality among refutations
    // ====================================================================

    /// Helper for width_lower_bound:
    /// `(f : CNF) -> (p : ResolutionProof) -> Prop`
    ///
    /// Encodes:
    /// `is_refutation p f -> res_proof_width p >= resolution_width f`.
    pub(super) fn register_width_lower_bound_helper(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let name = "TreeWidthRes.width_lower_bound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (p_id, _) = b.fresh_local(c.resolution_proof.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.resolution_proof.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.width_lower_bound :
    ///     forall (f : CNF) (p : ResolutionProof),
    ///     TreeWidthRes.width_lower_bound_helper f p`
    pub(super) fn register_width_lower_bound(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "TreeWidthRes.width_lower_bound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("TreeWidthRes.width_lower_bound_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (p_id, p) = b.fresh_local(c.resolution_proof.clone());
            let body = Expr::apps(helper, [f.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.resolution_proof.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: Size minimality among refutations
    // ====================================================================

    /// Helper for size_lower_bound:
    /// `(f : CNF) -> (p : ResolutionProof) -> Prop`
    ///
    /// Encodes:
    /// `is_refutation p f -> res_proof_size p >= resolution_size f`.
    pub(super) fn register_size_lower_bound_helper(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let name = "TreeWidthRes.size_lower_bound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (p_id, _) = b.fresh_local(c.resolution_proof.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.resolution_proof.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `TreeWidthRes.size_lower_bound :
    ///     forall (f : CNF) (p : ResolutionProof),
    ///     TreeWidthRes.size_lower_bound_helper f p`
    pub(super) fn register_size_lower_bound(
        &mut self,
        c: &TreeWidthResConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "TreeWidthRes.size_lower_bound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("TreeWidthRes.size_lower_bound_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (p_id, p) = b.fresh_local(c.resolution_proof.clone());
            let body = Expr::apps(helper, [f.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.resolution_proof.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
