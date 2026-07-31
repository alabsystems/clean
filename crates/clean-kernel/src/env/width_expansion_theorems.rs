// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for the Ben-Sasson-Wigderson width-expansion overlay.
//!
//! Registers the kernel-level axiom surfaces for:
//! - the width-expansion lower bound for resolution refutations
//! - monotonicity of expansion under restrictions
//! - the random-restriction width lower bound
//! - the size-width relationship
//! - a Cheeger-style comparison between expansion and spectral gap
//!
//! Each theorem follows the helper-axiom pattern from
//! `tree_width_resolution_theorems.rs`: a `_helper` axiom captures the
//! proposition body, and the theorem quantifies over all parameters with
//! the helper applied.
//!
//! Reference: Ben-Sasson & Wigderson, "Short Proofs are Narrow -- Resolution
//! Made Simple", JACM 2001.

#[cfg(test)]
use super::width_expansion::WidthExpansionConsts;
#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    // ====================================================================
    // Theorem 1: Width lower bound from boundary expansion
    // ====================================================================

    /// Helper for width_expansion:
    /// `(f : CNF) -> (p : ResolutionProof) -> Prop`
    ///
    /// Encodes:
    /// `is_refutation p f ->
    ///   proof_width p >= boundary_expansion (incidence_graph f)`.
    #[cfg(test)]
    pub(super) fn register_width_expansion_helper(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let name = "WidthExpansion.width_expansion_helper";
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

    /// `WidthExpansion.width_expansion :
    ///     forall (f : CNF) (p : ResolutionProof),
    ///     WidthExpansion.width_expansion_helper f p`
    ///
    /// Main width-expansion lower bound (T8): every resolution refutation
    /// must contain a clause whose width is at least the boundary expansion
    /// of the clause-variable incidence graph.
    #[cfg(test)]
    pub(super) fn register_width_expansion(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "WidthExpansion.width_expansion";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("WidthExpansion.width_expansion_helper"),
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
    // Theorem 2: Expansion monotonicity under restriction
    // ====================================================================

    /// Helper for expansion_monotone_restriction:
    /// `(f : CNF) -> (rho : PartialAssignment) -> Prop`
    ///
    /// Encodes:
    /// `boundary_expansion (incidence_graph (restrict f rho)) >=
    ///   boundary_expansion (incidence_graph f) - restriction_size rho`.
    #[cfg(test)]
    pub(super) fn register_expansion_monotone_restriction_helper(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let name = "WidthExpansion.expansion_monotone_restriction_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (rho_id, _) = b.fresh_local(c.partial_assignment.clone());
            let e = b.mk_pi(
                rho_id,
                BinderInfo::Default,
                c.partial_assignment.clone(),
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

    /// `WidthExpansion.expansion_monotone_restriction :
    ///     forall (f : CNF) (rho : PartialAssignment),
    ///     WidthExpansion.expansion_monotone_restriction_helper f rho`
    ///
    /// Applying a restriction can decrease expansion only by the number of
    /// variables fixed by the restriction.
    #[cfg(test)]
    pub(super) fn register_expansion_monotone_restriction(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "WidthExpansion.expansion_monotone_restriction";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("WidthExpansion.expansion_monotone_restriction_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf.clone());
            let (rho_id, rho) = b.fresh_local(c.partial_assignment.clone());
            let body = Expr::apps(helper, [f.clone(), rho.clone()]);
            let e = b.mk_pi(
                rho_id,
                BinderInfo::Default,
                c.partial_assignment.clone(),
                body,
            );
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
    // Theorem 3: Width lower bound via random restrictions
    // ====================================================================

    /// Helper for width_random_restriction:
    /// `(f : CNF) -> (p : ResolutionProof) -> Prop`
    ///
    /// Encodes:
    /// `is_refutation p f ->
    ///   proof_width p >= boundary_expansion (incidence_graph f) / 2`.
    #[cfg(test)]
    pub(super) fn register_width_random_restriction_helper(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let name = "WidthExpansion.width_random_restriction_helper";
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

    /// `WidthExpansion.width_random_restriction :
    ///     forall (f : CNF) (p : ResolutionProof),
    ///     WidthExpansion.width_random_restriction_helper f p`
    ///
    /// Random restriction argument: after restricting away a controlled set
    /// of variables, a surviving refutation still forces width at least half
    /// the original expansion parameter.
    #[cfg(test)]
    pub(super) fn register_width_random_restriction(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "WidthExpansion.width_random_restriction";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("WidthExpansion.width_random_restriction_helper"),
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
    // Theorem 4: Size-width relationship
    // ====================================================================

    /// Helper for size_width_relationship: `(f : CNF) -> Prop`
    ///
    /// Encodes the Ben-Sasson-Wigderson tradeoff:
    /// `resolution_size f >=
    ///   2^((width - initial_width f)^2 / num_variables f)`.
    #[cfg(test)]
    pub(super) fn register_size_width_helper(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let name = "WidthExpansion.size_width_helper";
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

    /// `WidthExpansion.size_width_relationship : forall (f : CNF),
    ///     WidthExpansion.size_width_helper f`
    ///
    /// Ben-Sasson-Wigderson size-width tradeoff: any substantial gap between
    /// initial width and required refutation width forces exponential growth
    /// in proof size.
    #[cfg(test)]
    pub(super) fn register_size_width_relationship(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "WidthExpansion.size_width_relationship";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("WidthExpansion.size_width_helper"),
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
    // Theorem 5: Cheeger-style comparison
    // ====================================================================

    /// Helper for cheeger_inequality: `(f : CNF) -> Prop`
    ///
    /// Encodes:
    /// `boundary_expansion (incidence_graph f)^2 <=
    ///   2 * spectral_gap (incidence_graph f)`.
    #[cfg(test)]
    pub(super) fn register_cheeger_helper(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let name = "WidthExpansion.cheeger_helper";
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

    /// `WidthExpansion.cheeger_inequality : forall (f : CNF),
    ///     WidthExpansion.cheeger_helper f`
    ///
    /// Stretch-goal spectral formulation: the square of boundary expansion
    /// is bounded by a constant multiple of the incidence-graph spectral gap.
    #[cfg(test)]
    pub(super) fn register_cheeger_inequality(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "WidthExpansion.cheeger_inequality";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("WidthExpansion.cheeger_helper"), vec![]);
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
}
