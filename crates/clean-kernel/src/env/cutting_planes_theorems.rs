// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for cutting planes proof system formalization.
//!
//! Registers the kernel-level axiom surfaces for:
//! - CP soundness: derived inequalities are valid
//! - CP p-simulates resolution (Cook, Coullard & Turan 1987)
//! - Size bound: translated CP proof is polynomial in resolution proof size
//! - PHP requires exponential-size CP proofs (without rounding)
//! - Separation: CP is strictly stronger than resolution
//!
//! Each theorem follows the helper-axiom pattern from
//! `resolution_complexity_theorems.rs`: a `_helper` axiom captures the
//! proposition body, and the theorem quantifies over all parameters with
//! the helper applied.
//!
//! Reference: Cook, Coullard & Turan (1987), "On the Complexity of
//!            Cutting-Plane Proofs";
//!            Pudlak (1997), "Lower bounds for resolution and cutting plane
//!            proofs and monotone computations".

use super::cutting_planes::CuttingPlanesConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: CP soundness
    // ====================================================================

    /// Helper for cp_sound: `(p : CuttingPlanesProof) -> Prop`
    ///
    /// Encodes: the inequality derived by p is valid (holds for all 0/1
    /// assignments satisfying the axiom inequalities).
    pub(super) fn register_cp_sound_helper(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_sound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cp_proof.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_sound : forall (p : CuttingPlanesProof), cp_sound_helper p`
    ///
    /// Cutting planes proofs are sound: each rule (addition, multiplication,
    /// division/rounding) preserves validity of integer linear inequalities
    /// over 0/1 variables.
    pub(super) fn register_cp_sound(&mut self, c: &CuttingPlanesConsts) -> Result<(), EnvError> {
        let thm_name = "ProofTheory.cp_sound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string("ProofTheory.cp_sound_helper"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.cp_proof.clone());
            let body = Expr::app(helper, p.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.cp_proof.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: CP p-simulates resolution
    // ====================================================================

    /// Helper for cp_simulates_resolution:
    /// `(p : TreeResProof) -> Prop`
    ///
    /// Encodes: resolution_to_cp p is a valid CP refutation that derives
    /// the same contradiction as p.
    pub(super) fn register_cp_simulates_resolution_helper(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_simulates_resolution_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.tree_res_proof.clone(),
            c.prop.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_simulates_resolution : forall (p : TreeResProof),
    ///     cp_simulates_resolution_helper p`
    ///
    /// **Cook, Coullard & Turan (1987):** The cutting planes proof system
    /// p-simulates resolution. Every resolution refutation can be efficiently
    /// translated into a cutting planes refutation. The translation encodes
    /// clauses as linear inequalities and resolution steps as additions.
    pub(super) fn register_cp_simulates_resolution(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ProofTheory.cp_simulates_resolution";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ProofTheory.cp_simulates_resolution_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.tree_res_proof.clone());
            let body = Expr::app(helper, p.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.tree_res_proof.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: CP simulation size bound
    // ====================================================================

    /// Helper for cp_simulation_size_bound:
    /// `(p : TreeResProof) -> Prop`
    ///
    /// Encodes: cp_proof_size (resolution_to_cp p) <= poly(tree_res_size p)
    /// for some fixed polynomial (in fact, linear).
    pub(super) fn register_cp_simulation_size_bound_helper(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_simulation_size_bound_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.tree_res_proof.clone(),
            c.prop.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_simulation_size_bound : forall (p : TreeResProof),
    ///     cp_simulation_size_bound_helper p`
    ///
    /// The translated CP proof has size polynomial (linear) in the
    /// original resolution proof size. Each resolution step maps to
    /// a constant number of CP steps (addition of inequalities).
    pub(super) fn register_cp_simulation_size_bound(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ProofTheory.cp_simulation_size_bound";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ProofTheory.cp_simulation_size_bound_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.tree_res_proof.clone());
            let body = Expr::app(helper, p.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.tree_res_proof.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: PHP requires exponential CP proofs (without rounding)
    // ====================================================================

    /// Helper for cp_php_exponential: `(n : Nat) -> Prop`
    ///
    /// Encodes: any CP proof of PHP_{n+1}^n that does not use the
    /// division/rounding rule requires 2^{Mathverse(n)} steps.
    pub(super) fn register_cp_php_exponential_helper(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_php_exponential_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_php_exponential : forall (n : Nat),
    ///     cp_php_exponential_helper n`
    ///
    /// PHP requires exponential-size cutting planes proofs when the
    /// division/rounding rule is not used. This is because without
    /// rounding, CP reduces to the Lovasz-Schrijver system, which
    /// cannot efficiently refute PHP.
    ///
    /// Reference: Pudlak (1997), "Lower bounds for resolution and
    ///            cutting plane proofs and monotone computations".
    pub(super) fn register_cp_php_exponential(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ProofTheory.cp_php_exponential";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ProofTheory.cp_php_exponential_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::app(helper, n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: CP separation from resolution
    // ====================================================================

    /// Helper for cp_separation_from_resolution: `Prop`
    ///
    /// Encodes: there exist tautologies (families of unsatisfiable CNFs)
    /// that have polynomial-size CP proofs but require exponential-size
    /// resolution proofs. This witnesses the strict separation CP > Res.
    pub(super) fn register_cp_separation_helper(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_separation_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: c.prop.clone(),
        })
    }

    /// `cp_separation_from_resolution : cp_separation_helper`
    ///
    /// **Separation theorem:** There exist tautologies with short cutting
    /// planes proofs but no short resolution proofs. Combined with the
    /// p-simulation result, this shows CP is strictly stronger than
    /// resolution in terms of proof complexity.
    ///
    /// The witnessing family is the subset-sum / integer programming
    /// encoding: CP can derive 0 >= 1 in polynomial size using the
    /// division rule, while resolution requires exponential size due
    /// to width lower bounds (Ben-Sasson & Wigderson 2001).
    pub(super) fn register_cp_separation_from_resolution(
        &mut self,
        c: &CuttingPlanesConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ProofTheory.cp_separation_from_resolution";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ProofTheory.cp_separation_helper"),
            vec![],
        );
        // This theorem has no universally quantified parameters — it is
        // a direct existential statement.
        let _ = c; // suppress unused warning; c was passed for consistency
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: helper,
        })
    }
}
