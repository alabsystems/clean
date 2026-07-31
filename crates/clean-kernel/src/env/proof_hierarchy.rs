// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for the proof complexity hierarchy formalization.
//!
//! Formalizes the p-simulation hierarchy among propositional proof systems:
//!   Resolution < Cutting Planes < Frege < Extended Frege
//!
//! This captures the foundational structure of proof complexity theory,
//! following Cook & Reckhow (1979) and the subsequent separation results
//! by Haken (1985), Bonet & Galesi (1997/2001), and Cook & Reckhow (1974).
//!
//! Type and operation definitions live here; theorem registrations are in
//! `proof_hierarchy_theorems.rs`.

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

/// Shared constants used across all proof hierarchy declarations.
#[cfg(test)]
pub(super) struct ProofHierarchyConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.ProofSystem : Type
    pub(super) proof_system: Expr,
    /// ProofTheory.Formula : Type
    pub(super) formula: Expr,
    /// ProofTheory.FregeProof : Type
    pub(super) frege_proof: Expr,
    /// ProofTheory.ExtendedFregeProof : Type
    pub(super) extended_frege_proof: Expr,
}

#[cfg(test)]
impl ProofHierarchyConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            proof_system: Expr::const_(Name::from_string("ProofTheory.ProofSystem"), vec![]),
            formula: Expr::const_(Name::from_string("ProofTheory.Formula"), vec![]),
            frege_proof: Expr::const_(Name::from_string("ProofTheory.FregeProof"), vec![]),
            extended_frege_proof: Expr::const_(
                Name::from_string("ProofTheory.ExtendedFregeProof"),
                vec![],
            ),
        }
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize proof hierarchy declarations for p-simulation relations.
    ///
    /// Depends on: `init_nat()`.
    #[cfg(test)]
    pub(crate) fn init_proof_hierarchy(&mut self) -> Result<(), EnvError> {
        if self.proof_hierarchy_init {
            return Ok(());
        }
        self.init_nat()?;

        let c = ProofHierarchyConsts::new();
        // Definitions (6)
        self.register_formula(&c)?;
        self.register_proof_system(&c)?;
        self.register_p_simulation(&c)?;
        self.register_frege_proof(&c)?;
        self.register_extended_frege_proof(&c)?;
        self.register_frege_proof_size(&c)?;
        self.register_simulation_gap(&c)?;
        // Theorems (in proof_hierarchy_theorems.rs)
        self.register_resolution_below_cp(&c)?;
        self.register_cp_below_frege(&c)?;
        self.register_frege_below_extended_frege(&c)?;
        self.register_resolution_exponential_gap(&c)?;
        self.register_cook_reckhow_completeness(&c)?;

        self.proof_hierarchy_init = true;
        Ok(())
    }

    /// `Formula : Type` -- abstract propositional formula type.
    ///
    /// Represents tautologies / propositional formulas that proof systems
    /// operate on.
    #[cfg(test)]
    fn register_formula(&mut self, c: &ProofHierarchyConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.Formula"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.Formula"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `ProofSystem : Type` -- abstract proof system (Cook-Reckhow, 1979).
    ///
    /// A proof system is a polynomial-time computable function
    /// `verify : String -> Formula -> Bool` such that for every tautology f,
    /// there exists a proof string pi with `verify pi f = true`.
    /// Registered as an opaque axiom type.
    #[cfg(test)]
    fn register_proof_system(&mut self, c: &ProofHierarchyConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.ProofSystem"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ProofSystem"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `PSimulation (P Q : ProofSystem) : Prop` -- proof system P p-simulates Q.
    ///
    /// P p-simulates Q iff there exists a polynomial-time computable function
    /// that translates any Q-proof of a tautology f into a P-proof of f.
    /// Equivalently: proof size in P is at most polynomially larger than in Q
    /// for every tautology.
    ///
    /// Reference: Cook & Reckhow (1979), "The Relative Efficiency of
    /// Propositional Proof Systems".
    #[cfg(test)]
    fn register_p_simulation(&mut self, c: &ProofHierarchyConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.PSimulation"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.proof_system.clone());
            let (q_id, _) = b.fresh_local(c.proof_system.clone());
            let e = b.mk_pi(
                q_id,
                BinderInfo::Default,
                c.proof_system.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(p_id, BinderInfo::Default, c.proof_system.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PSimulation"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `FregeProof : Type` -- Frege proof structure.
    ///
    /// A Frege proof consists of a sequence of lines, each of which is either:
    /// - an instance of a propositional axiom schema, or
    /// - derived by modus ponens from two earlier lines.
    ///
    /// The axiom schemas are a fixed, finite set that is implicationally
    /// complete for propositional logic.
    #[cfg(test)]
    fn register_frege_proof(&mut self, c: &ProofHierarchyConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.FregeProof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.FregeProof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `ExtendedFregeProof : Type` -- Extended Frege proof structure.
    ///
    /// Extends Frege proofs with the extension rule: the ability to introduce
    /// new propositional variables as abbreviations for complex subformulas.
    /// This can provide exponential compression over standard Frege proofs.
    ///
    /// Extended Frege is equivalent to substitution Frege (up to polynomial
    /// simulation).
    #[cfg(test)]
    fn register_extended_frege_proof(&mut self, c: &ProofHierarchyConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.ExtendedFregeProof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtendedFregeProof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `frege_proof_size (p : FregeProof) : Nat` -- size of a Frege proof.
    ///
    /// The number of symbols (lines times average line length) in the proof.
    /// This is the standard size measure for proof complexity lower bounds.
    #[cfg(test)]
    fn register_frege_proof_size(&mut self, c: &ProofHierarchyConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.frege_proof_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.frege_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.frege_proof_size"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `simulation_gap (P Q : ProofSystem) (f : Formula) : Nat`
    ///
    /// The ratio of proof sizes: max over all proofs of f in Q of
    /// (min proof size in P) / (proof size in Q). Captures how much
    /// more expensive P-proofs are compared to Q-proofs for formula f.
    #[cfg(test)]
    fn register_simulation_gap(&mut self, c: &ProofHierarchyConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.simulation_gap"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.proof_system.clone());
            let (q_id, _) = b.fresh_local(c.proof_system.clone());
            let (f_id, _) = b.fresh_local(c.formula.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.formula.clone(), c.nat.clone());
            let e = b.mk_pi(q_id, BinderInfo::Default, c.proof_system.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.proof_system.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.simulation_gap"),
            level_params: vec![],
            type_: ty,
        })
    }
}
