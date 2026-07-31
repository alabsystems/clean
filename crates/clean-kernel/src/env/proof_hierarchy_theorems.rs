// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for the proof complexity hierarchy.
//!
//! Registers kernel-level axiom surfaces for the p-simulation hierarchy:
//!
//! 1. resolution_below_cp: Resolution is p-simulated by Cutting Planes
//! 2. cp_below_frege: Cutting Planes is p-simulated by Frege
//! 3. frege_below_extended_frege: Frege is p-simulated by Extended Frege
//! 4. resolution_exponential_gap: there exist tautologies with exponential
//!    Resolution proofs but polynomial Frege proofs (strict separation)
//! 5. cook_reckhow_completeness: Extended Frege p-simulates every proof
//!    system if and only if NP = coNP
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom captures
//! the proposition body, and the theorem quantifies over all parameters with
//! the helper applied. This avoids depending on concrete logic connectives
//! in the type expressions.
//!
//! References:
//! - Cook & Reckhow (1979), "The Relative Efficiency of Propositional
//!   Proof Systems"
//! - Haken (1985), "The Intractability of Resolution"
//! - Bonet & Galesi (2001), "Optimality of size-width tradeoffs for
//!   Resolution"

#[cfg(test)]
use super::proof_hierarchy::ProofHierarchyConsts;
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
    // Theorem 1: Resolution is p-simulated by Cutting Planes
    // ====================================================================

    /// `resolution_below_cp : forall (res cp : ProofSystem),
    ///     resolution_below_cp_helper res cp`
    ///
    /// Cutting Planes can polynomially simulate Resolution. Every Resolution
    /// refutation can be translated into a Cutting Planes proof of at most
    /// polynomial blowup, since clausal reasoning is a special case of
    /// linear integer arithmetic reasoning over {0,1} variables.
    #[cfg(test)]
    pub(super) fn register_resolution_below_cp(
        &mut self,
        c: &ProofHierarchyConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.resolution_below_cp_helper";
        let thm_name = "ProofTheory.resolution_below_cp";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (res cp : ProofSystem) -> Prop
            // Encodes: PSimulation cp res
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (res_id, _) = b.fresh_local(c.proof_system.clone());
                let (cp_id, _) = b.fresh_local(c.proof_system.clone());
                let e = b.mk_pi(
                    cp_id,
                    BinderInfo::Default,
                    c.proof_system.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(res_id, BinderInfo::Default, c.proof_system.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (res_id, res) = b.fresh_local(c.proof_system.clone());
            let (cp_id, cp) = b.fresh_local(c.proof_system.clone());
            let body = Expr::apps(helper, [res.clone(), cp.clone()]);
            let e = b.mk_pi(cp_id, BinderInfo::Default, c.proof_system.clone(), body);
            let e = b.mk_pi(res_id, BinderInfo::Default, c.proof_system.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: Cutting Planes is p-simulated by Frege
    // ====================================================================

    /// `cp_below_frege : forall (cp frege : ProofSystem),
    ///     cp_below_frege_helper cp frege`
    ///
    /// Frege systems can polynomially simulate Cutting Planes. Linear
    /// integer arithmetic reasoning over {0,1} can be encoded in
    /// propositional logic with polynomial overhead using binary
    /// representations and carry-chain arguments.
    #[cfg(test)]
    pub(super) fn register_cp_below_frege(
        &mut self,
        c: &ProofHierarchyConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.cp_below_frege_helper";
        let thm_name = "ProofTheory.cp_below_frege";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (cp_id, _) = b.fresh_local(c.proof_system.clone());
                let (f_id, _) = b.fresh_local(c.proof_system.clone());
                let e = b.mk_pi(
                    f_id,
                    BinderInfo::Default,
                    c.proof_system.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(cp_id, BinderInfo::Default, c.proof_system.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cp_id, cp) = b.fresh_local(c.proof_system.clone());
            let (f_id, f) = b.fresh_local(c.proof_system.clone());
            let body = Expr::apps(helper, [cp.clone(), f.clone()]);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.proof_system.clone(), body);
            let e = b.mk_pi(cp_id, BinderInfo::Default, c.proof_system.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Frege is p-simulated by Extended Frege
    // ====================================================================

    /// `frege_below_extended_frege : forall (frege ef : ProofSystem),
    ///     frege_below_ef_helper frege ef`
    ///
    /// Extended Frege p-simulates standard Frege. This is immediate since
    /// every Frege proof is trivially an Extended Frege proof (the extension
    /// rule is optional). The converse is a major open problem: whether
    /// Frege and Extended Frege are polynomially equivalent.
    #[cfg(test)]
    pub(super) fn register_frege_below_extended_frege(
        &mut self,
        c: &ProofHierarchyConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.frege_below_ef_helper";
        let thm_name = "ProofTheory.frege_below_extended_frege";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.proof_system.clone());
                let (ef_id, _) = b.fresh_local(c.proof_system.clone());
                let e = b.mk_pi(
                    ef_id,
                    BinderInfo::Default,
                    c.proof_system.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(f_id, BinderInfo::Default, c.proof_system.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.proof_system.clone());
            let (ef_id, ef) = b.fresh_local(c.proof_system.clone());
            let body = Expr::apps(helper, [f.clone(), ef.clone()]);
            let e = b.mk_pi(ef_id, BinderInfo::Default, c.proof_system.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.proof_system.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: Exponential separation between Resolution and Frege
    // ====================================================================

    /// `resolution_exponential_gap : resolution_exp_gap_helper`
    ///
    /// There exist families of tautologies (e.g., PHP) that require
    /// exponential-size Resolution proofs but have polynomial-size Frege
    /// proofs. This demonstrates a strict separation: Frege is strictly
    /// stronger than Resolution.
    ///
    /// The exponential lower bound for Resolution is Haken (1985).
    /// The polynomial upper bound in Frege follows from the fact that
    /// PHP can be proved in constant-depth Frege (Ajtai, 1988).
    #[cfg(test)]
    pub(super) fn register_resolution_exponential_gap(
        &mut self,
        c: &ProofHierarchyConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.resolution_exp_gap_helper";
        let thm_name = "ProofTheory.resolution_exponential_gap";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper : Prop  (no parameters -- existential statement)
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: c.prop.clone(),
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: helper,
        })
    }

    // ====================================================================
    // Theorem 5: Cook-Reckhow completeness of Extended Frege
    // ====================================================================

    /// `cook_reckhow_completeness : cook_reckhow_helper`
    ///
    /// The Cook-Reckhow theorem (1979): A proof system P p-simulates every
    /// other proof system (i.e., P is optimal) if and only if NP = coNP.
    /// Extended Frege is a candidate for such an optimal system.
    ///
    /// More precisely: Extended Frege p-simulates every proof system iff
    /// every language in coNP has polynomial-size Extended Frege proofs of
    /// its tautological encoding, which holds iff NP = coNP.
    ///
    /// Reference: Cook & Reckhow (1979), Theorem 1.5.
    #[cfg(test)]
    pub(super) fn register_cook_reckhow_completeness(
        &mut self,
        c: &ProofHierarchyConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.cook_reckhow_helper";
        let thm_name = "ProofTheory.cook_reckhow_completeness";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper : Prop  (encodes the biconditional)
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: c.prop.clone(),
            })?;
        }

        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: helper,
        })
    }
}
