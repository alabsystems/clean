// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for cutting planes proof system formalization.
//!
//! Registers the foundational types and definitions needed to state:
//! - The cutting planes proof system (CP) for integer linear inequalities
//! - CP p-simulation of resolution (Cook, Coullard & Turan, 1987)
//! - CP separation from resolution (exponential gaps)
//! - PHP exponential lower bounds for CP without rounding
//!
//! Type and operation definitions live here; theorem registrations are in
//! `cutting_planes_theorems.rs`.
//!
//! Reference: Cook, Coullard & Turan (1987), "On the Complexity of
//!            Cutting-Plane Proofs".

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all cutting planes declarations.
pub(super) struct CuttingPlanesConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.LinearInequality : Type
    pub(super) linear_ineq: Expr,
    /// ProofTheory.CuttingPlanesProof : Type
    pub(super) cp_proof: Expr,
    /// ResComplexity.CNF : Type
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) cnf: Expr,
    /// ResComplexity.TreeResProof : Type
    pub(super) tree_res_proof: Expr,
}

impl CuttingPlanesConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            linear_ineq: Expr::const_(Name::from_string("ProofTheory.LinearInequality"), vec![]),
            cp_proof: Expr::const_(Name::from_string("ProofTheory.CuttingPlanesProof"), vec![]),
            #[cfg(test)]
            cnf: Expr::const_(Name::from_string("ResComplexity.CNF"), vec![]),
            tree_res_proof: Expr::const_(Name::from_string("ResComplexity.TreeResProof"), vec![]),
        }
    }
}

impl Environment {
    /// Initialize cutting planes proof system declarations.
    ///
    /// Depends on: `init_nat()`, `init_resolution_complexity()`.
    pub(crate) fn init_cutting_planes(&mut self) -> Result<(), EnvError> {
        if self.cutting_planes_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_resolution_complexity()?;

        let c = CuttingPlanesConsts::new();
        self.register_linear_inequality(&c)?;
        self.register_cp_proof(&c)?;
        self.register_cp_proof_size(&c)?;
        self.register_cp_degree(&c)?;
        self.register_resolution_to_cp(&c)?;
        // Theorem registrations (in cutting_planes_theorems.rs)
        self.register_cp_sound_helper(&c)?;
        self.register_cp_sound(&c)?;
        self.register_cp_simulates_resolution_helper(&c)?;
        self.register_cp_simulates_resolution(&c)?;
        self.register_cp_simulation_size_bound_helper(&c)?;
        self.register_cp_simulation_size_bound(&c)?;
        self.register_cp_php_exponential_helper(&c)?;
        self.register_cp_php_exponential(&c)?;
        self.register_cp_separation_helper(&c)?;
        self.register_cp_separation_from_resolution(&c)?;

        self.cutting_planes_init = true;
        Ok(())
    }

    /// `LinearInequality : Type` — integer linear inequality a . x >= b.
    ///
    /// Abstractly represents a constraint sum_i a_i * x_i >= b where
    /// a_i, b are integers and x_i are 0/1 variables.
    fn register_linear_inequality(&mut self, c: &CuttingPlanesConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.LinearInequality"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LinearInequality"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `CuttingPlanesProof : Type` — cutting planes proof structure.
    ///
    /// A proof in the cutting planes system is a sequence of steps:
    /// - `Axiom (ineq : LinearInequality)` — initial axiom
    /// - `Add (p1 p2 : CuttingPlanesProof)` — add two derived inequalities
    /// - `Multiply (p : CuttingPlanesProof) (c : Nat)` — multiply by positive constant
    /// - `Divide (p : CuttingPlanesProof) (c : Nat)` — divide and round up (integer rounding)
    fn register_cp_proof(&mut self, c: &CuttingPlanesConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.CuttingPlanesProof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.CuttingPlanesProof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Axiom constructor
        let axiom_ty = Expr::pi(
            BinderInfo::Default,
            c.linear_ineq.clone(),
            c.cp_proof.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.CuttingPlanesProof.Axiom"),
            level_params: vec![],
            type_: axiom_ty,
        })?;
        // Add constructor
        let add_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p1_id, _) = b.fresh_local(c.cp_proof.clone());
            let (p2_id, _) = b.fresh_local(c.cp_proof.clone());
            let e = b.mk_pi(
                p2_id,
                BinderInfo::Default,
                c.cp_proof.clone(),
                c.cp_proof.clone(),
            );
            let e = b.mk_pi(p1_id, BinderInfo::Default, c.cp_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.CuttingPlanesProof.Add"),
            level_params: vec![],
            type_: add_ty,
        })?;
        // Multiply constructor
        let mul_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.cp_proof.clone());
            let (c_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(c_id, BinderInfo::Default, c.nat.clone(), c.cp_proof.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.cp_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.CuttingPlanesProof.Multiply"),
            level_params: vec![],
            type_: mul_ty,
        })?;
        // Divide constructor (integer rounding)
        let div_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.cp_proof.clone());
            let (c_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(c_id, BinderInfo::Default, c.nat.clone(), c.cp_proof.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.cp_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.CuttingPlanesProof.Divide"),
            level_params: vec![],
            type_: div_ty,
        })
    }

    /// `cp_proof_size (p : CuttingPlanesProof) : Nat` — number of steps.
    fn register_cp_proof_size(&mut self, c: &CuttingPlanesConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.cp_proof_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cp_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.cp_proof_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_degree (p : CuttingPlanesProof) : Nat` — maximum coefficient degree.
    ///
    /// The degree of a CP proof is the maximum over all inequalities derived
    /// in the proof of the sum of absolute values of coefficients.
    fn register_cp_degree(&mut self, c: &CuttingPlanesConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.cp_degree"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.cp_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.cp_degree"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `resolution_to_cp (p : TreeResProof) : CuttingPlanesProof`
    ///
    /// Translation from resolution proofs to cutting planes proofs.
    /// Each clause {l_1, ..., l_k} is encoded as the inequality
    /// l_1 + ... + l_k >= 1 (where negative literal ~x_i becomes 1 - x_i).
    /// Resolution steps become addition of inequalities.
    fn register_resolution_to_cp(&mut self, c: &CuttingPlanesConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.resolution_to_cp"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.tree_res_proof.clone(),
            c.cp_proof.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.resolution_to_cp"),
            level_params: vec![],
            type_: ty,
        })
    }
}
