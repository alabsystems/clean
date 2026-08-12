// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for pseudo-Boolean (PB) proofs of the
//! pigeonhole principle and exponential separation from resolution.
//!
//! Registers the foundational types and definitions needed to state:
//! - Pseudo-Boolean constraints (sum a_i * x_i >= b)
//! - PB proof system (axiom, addition, multiplication, division, saturation)
//! - Pigeonhole formula PHP^n_{n+1}
//! - PB has polynomial proofs of PHP (vs exponential resolution)
//! - PB p-simulates cutting planes
//!
//! Type and operation definitions live here; theorem registrations are in
//! `pb_pigeonhole_theorems.rs`.
//!
//! References:
//!   Cook (1987), "A Short Proof of the Pigeon Hole Principle using
//!     Extended Resolution";
//!   Haken (1985), "The Intractability of Resolution";
//!   Razborov (2003), "Resolution Lower Bounds for the Weak Pigeonhole
//!     Principle".

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

/// Shared constants used across all PB pigeonhole declarations.
#[cfg(test)]
pub(super) struct PBPigeonholeConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.PBConstraint : Type
    pub(super) pb_constraint: Expr,
    /// ProofTheory.PBProof : Type
    pub(super) pb_proof: Expr,
    /// ResComplexity.CNF : Type
    pub(super) cnf: Expr,
    /// ResComplexity.TreeResProof : Type
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) tree_res_proof: Expr,
    /// ProofTheory.CuttingPlanesProof : Type
    pub(super) cp_proof: Expr,
}

#[cfg(test)]
impl PBPigeonholeConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            pb_constraint: Expr::const_(Name::from_string("ProofTheory.PBConstraint"), vec![]),
            pb_proof: Expr::const_(Name::from_string("ProofTheory.PBProof"), vec![]),
            cnf: Expr::const_(Name::from_string("ResComplexity.CNF"), vec![]),
            tree_res_proof: Expr::const_(Name::from_string("ResComplexity.TreeResProof"), vec![]),
            cp_proof: Expr::const_(Name::from_string("ProofTheory.CuttingPlanesProof"), vec![]),
        }
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize PB pigeonhole declarations for exponential separation.
    ///
    /// Depends on: `init_nat()`, `init_cutting_planes()`.
    #[cfg(test)]
    pub(crate) fn init_pb_pigeonhole(&mut self) -> Result<(), EnvError> {
        if self.pb_pigeonhole_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_cutting_planes()?;

        let c = PBPigeonholeConsts::new();
        // Definitions
        self.register_pb_constraint(&c)?;
        self.register_pb_proof(&c)?;
        self.register_pb_proof_size(&c)?;
        self.register_pigeonhole_formula(&c)?;
        self.register_pb_degree(&c)?;
        // Theorems (in pb_pigeonhole_theorems.rs)
        self.register_pb_sound_helper(&c)?;
        self.register_pb_sound(&c)?;
        self.register_pb_php_polynomial_helper(&c)?;
        self.register_pb_php_polynomial(&c)?;
        self.register_resolution_php_exponential_helper(&c)?;
        self.register_resolution_php_exponential(&c)?;
        self.register_pb_resolution_separation_helper(&c)?;
        self.register_pb_resolution_separation(&c)?;
        self.register_pb_simulates_cp_helper(&c)?;
        self.register_pb_simulates_cp(&c)?;

        self.pb_pigeonhole_init = true;
        Ok(())
    }

    // ====================================================================
    // Definition 1: PBConstraint
    // ====================================================================

    /// `PBConstraint : Type` -- pseudo-Boolean constraint: sum(a_i * x_i) >= b.
    ///
    /// Abstractly represents a constraint where a_i are integer coefficients,
    /// x_i are 0/1 variables, and b is an integer threshold.
    #[cfg(test)]
    fn register_pb_constraint(&mut self, c: &PBPigeonholeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.PBConstraint"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PBConstraint"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    // ====================================================================
    // Definition 2: PBProof
    // ====================================================================

    /// `PBProof : Type` -- pseudo-Boolean proof structure.
    ///
    /// A proof in the PB system is a sequence of steps:
    /// - `Axiom (cst : PBConstraint)` -- initial axiom constraint
    /// - `Addition (p1 p2 : PBProof)` -- add two derived constraints
    /// - `Multiplication (p : PBProof) (c : Nat)` -- multiply by positive constant
    /// - `Division (p : PBProof) (c : Nat)` -- divide and round up
    /// - `Saturation (p : PBProof)` -- replace coefficient > b with b
    ///
    /// The saturation rule is what distinguishes PB from cutting planes:
    /// in sum(a_i * x_i) >= b, any coefficient a_i > b can be replaced
    /// by b since x_i in {0,1} and a_i * 1 >= b already suffices.
    #[cfg(test)]
    fn register_pb_proof(&mut self, c: &PBPigeonholeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.PBProof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PBProof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Axiom constructor
        let axiom_ty = Expr::pi(
            BinderInfo::Default,
            c.pb_constraint.clone(),
            c.pb_proof.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PBProof.Axiom"),
            level_params: vec![],
            type_: axiom_ty,
        })?;
        // Addition constructor
        let add_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p1_id, _) = b.fresh_local(c.pb_proof.clone());
            let (p2_id, _) = b.fresh_local(c.pb_proof.clone());
            let e = b.mk_pi(
                p2_id,
                BinderInfo::Default,
                c.pb_proof.clone(),
                c.pb_proof.clone(),
            );
            let e = b.mk_pi(p1_id, BinderInfo::Default, c.pb_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PBProof.Addition"),
            level_params: vec![],
            type_: add_ty,
        })?;
        // Multiplication constructor
        let mul_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.pb_proof.clone());
            let (c_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(c_id, BinderInfo::Default, c.nat.clone(), c.pb_proof.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.pb_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PBProof.Multiplication"),
            level_params: vec![],
            type_: mul_ty,
        })?;
        // Division constructor
        let div_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.pb_proof.clone());
            let (c_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(c_id, BinderInfo::Default, c.nat.clone(), c.pb_proof.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.pb_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PBProof.Division"),
            level_params: vec![],
            type_: div_ty,
        })?;
        // Saturation constructor (the key PB-specific rule)
        let sat_ty = Expr::pi(BinderInfo::Default, c.pb_proof.clone(), c.pb_proof.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PBProof.Saturation"),
            level_params: vec![],
            type_: sat_ty,
        })
    }

    // ====================================================================
    // Definition 3: pb_proof_size
    // ====================================================================

    /// `pb_proof_size (p : PBProof) : Nat` -- number of proof steps.
    #[cfg(test)]
    fn register_pb_proof_size(&mut self, c: &PBPigeonholeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.pb_proof_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.pb_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.pb_proof_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 4: pigeonhole_formula
    // ====================================================================

    /// `pigeonhole_formula (n : Nat) : CNF` -- PHP^n_{n+1}.
    ///
    /// The pigeonhole principle formula with n+1 pigeons and n holes.
    /// Variables p_{i,j} mean "pigeon i goes to hole j" for
    /// i in {0,...,n} and j in {0,...,n-1}.
    /// Clauses: (1) at-least-one hole per pigeon,
    ///          (2) at-most-one pigeon per hole.
    #[cfg(test)]
    fn register_pigeonhole_formula(&mut self, c: &PBPigeonholeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.pigeonhole_formula"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.cnf.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.pigeonhole_formula"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 5: pb_degree
    // ====================================================================

    /// `pb_degree (p : PBProof) : Nat` -- maximum coefficient in PB proof.
    ///
    /// The degree of a PB proof is the maximum over all constraints derived
    /// in the proof of the largest absolute value of any coefficient.
    #[cfg(test)]
    fn register_pb_degree(&mut self, c: &PBPigeonholeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.pb_degree"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.pb_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.pb_degree"),
            level_params: vec![],
            type_: ty,
        })
    }
}
