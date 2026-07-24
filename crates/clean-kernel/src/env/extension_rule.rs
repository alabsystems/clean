// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for extension rule soundness in SAT Extended
//! Resolution.
//!
//! Formalizes the extension rule x <-> (A op B) for propositional proof
//! complexity, including:
//! - Extension variables and Extended Resolution proofs
//! - Extension complexity measure
//! - Tseitin transformation (formula to CNF via extension variables)
//!
//! The extension rule is the key mechanism behind Extended Resolution (ER),
//! which is polynomially equivalent to Extended Frege systems. Adding fresh
//! variables as abbreviations for subformulas can provide exponential speedup
//! over ordinary Resolution.
//!
//! Type and operation definitions live here; theorem registrations are in
//! `extension_rule_theorems.rs`.
//!
//! References:
//! - Tseitin (1968), "On the Complexity of Derivation in Propositional Calculus"
//! - Cook (1975), "Feasibly constructive proofs and the propositional calculus"
//! - Krajicek (1995), "Bounded Arithmetic, Propositional Logic and Complexity
//!   Theory", Chapter 14

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all extension rule declarations.
pub(super) struct ExtensionRuleConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.Formula : Type (from proof_hierarchy)
    pub(super) formula: Expr,
    /// ProofTheory.ProofSystem : Type (from proof_hierarchy)
    pub(super) proof_system: Expr,
    /// ResComplexity.CNF : Type (from resolution_complexity)
    pub(super) cnf: Expr,
    /// ProofTheory.ExtensionVariable : Type
    pub(super) extension_variable: Expr,
    /// ProofTheory.ExtendedResolutionProof : Type
    pub(super) er_proof: Expr,
}

impl ExtensionRuleConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            formula: Expr::const_(Name::from_string("ProofTheory.Formula"), vec![]),
            proof_system: Expr::const_(Name::from_string("ProofTheory.ProofSystem"), vec![]),
            cnf: Expr::const_(Name::from_string("ResComplexity.CNF"), vec![]),
            extension_variable: Expr::const_(
                Name::from_string("ProofTheory.ExtensionVariable"),
                vec![],
            ),
            er_proof: Expr::const_(
                Name::from_string("ProofTheory.ExtendedResolutionProof"),
                vec![],
            ),
        }
    }
}

impl Environment {
    /// Initialize extension rule declarations for SAT Extended Resolution.
    ///
    /// Depends on: `init_nat()`, `init_resolution_complexity()`,
    /// `init_proof_hierarchy()`.
    pub(crate) fn init_extension_rule(&mut self) -> Result<(), EnvError> {
        if self.extension_rule_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_resolution_complexity()?;
        self.init_proof_hierarchy()?;

        let c = ExtensionRuleConsts::new();
        // Definitions (4)
        self.register_extension_variable(&c)?;
        self.register_extended_resolution_proof(&c)?;
        self.register_extension_complexity(&c)?;
        self.register_tseitin_transform(&c)?;
        // Theorems (in extension_rule_theorems.rs) (5)
        self.register_extension_rule_sound_helper(&c)?;
        self.register_extension_rule_sound(&c)?;
        self.register_extended_resolution_complete_helper(&c)?;
        self.register_extended_resolution_complete(&c)?;
        self.register_tseitin_equisatisfiable_helper(&c)?;
        self.register_tseitin_equisatisfiable(&c)?;
        self.register_extension_exponential_speedup_helper(&c)?;
        self.register_extension_exponential_speedup(&c)?;
        self.register_er_simulates_frege_helper(&c)?;
        self.register_er_simulates_frege(&c)?;

        self.extension_rule_init = true;
        Ok(())
    }

    /// `ExtensionVariable : Type` -- a fresh variable defined as equivalent
    /// to a formula.
    ///
    /// An extension variable x is introduced with the axiom x <-> phi(A, B)
    /// where phi is a boolean connective and A, B are existing formulas.
    /// The variable index, the connective, and the operand formulas are
    /// abstract -- only the equivalence relationship matters for soundness.
    fn register_extension_variable(&mut self, c: &ExtensionRuleConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.ExtensionVariable"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtensionVariable"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Constructor: mk (var_index : Nat) (defining_formula : Formula) : ExtensionVariable
        let mk_ty = {
            let mut b = EnvDeclBuilder::new();
            let (vi_id, _) = b.fresh_local(c.nat.clone());
            let (df_id, _) = b.fresh_local(c.formula.clone());
            let e = b.mk_pi(
                df_id,
                BinderInfo::Default,
                c.formula.clone(),
                c.extension_variable.clone(),
            );
            let e = b.mk_pi(vi_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtensionVariable.mk"),
            level_params: vec![],
            type_: mk_ty,
        })?;
        // Projection: var_index
        let vi_ty = Expr::pi(
            BinderInfo::Default,
            c.extension_variable.clone(),
            c.nat.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtensionVariable.var_index"),
            level_params: vec![],
            type_: vi_ty,
        })?;
        // Projection: defining_formula
        let df_ty = Expr::pi(
            BinderInfo::Default,
            c.extension_variable.clone(),
            c.formula.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtensionVariable.defining_formula"),
            level_params: vec![],
            type_: df_ty,
        })
    }

    /// `ExtendedResolutionProof : Type` -- resolution proof with extension
    /// variables.
    ///
    /// An Extended Resolution proof consists of:
    /// 1. A set of extension variable definitions (x_i <-> phi_i)
    /// 2. A standard resolution proof over the extended clause set
    ///
    /// Constructors:
    /// - `Base (p : ResComplexity.CNF)` -- original CNF formula
    /// - `Extend (ev : ExtensionVariable) (rest : ExtendedResolutionProof)` --
    ///   introduce an extension variable and continue
    fn register_extended_resolution_proof(
        &mut self,
        c: &ExtensionRuleConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.ExtendedResolutionProof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtendedResolutionProof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Base constructor
        let base_ty = Expr::pi(BinderInfo::Default, c.cnf.clone(), c.er_proof.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtendedResolutionProof.Base"),
            level_params: vec![],
            type_: base_ty,
        })?;
        // Extend constructor
        let extend_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ev_id, _) = b.fresh_local(c.extension_variable.clone());
            let (rest_id, _) = b.fresh_local(c.er_proof.clone());
            let e = b.mk_pi(
                rest_id,
                BinderInfo::Default,
                c.er_proof.clone(),
                c.er_proof.clone(),
            );
            let e = b.mk_pi(ev_id, BinderInfo::Default, c.extension_variable.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ExtendedResolutionProof.Extend"),
            level_params: vec![],
            type_: extend_ty,
        })
    }

    /// `extension_complexity (p : ExtendedResolutionProof) : Nat`
    ///
    /// The number of extension variables used in an Extended Resolution proof.
    /// This measures the additional definitional complexity beyond the
    /// original formula variables.
    fn register_extension_complexity(&mut self, c: &ExtensionRuleConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.extension_complexity"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.er_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.extension_complexity"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `tseitin_transform (f : Formula) : ExtendedResolutionProof`
    ///
    /// The Tseitin transformation converts an arbitrary propositional formula
    /// into an equisatisfiable CNF using extension variables. For each
    /// subformula phi, a fresh variable x_phi is introduced with the
    /// defining clause x_phi <-> phi. The result is a CNF of size linear
    /// in the original formula.
    ///
    /// Reference: Tseitin (1968), "On the Complexity of Derivation in
    ///            Propositional Calculus"
    fn register_tseitin_transform(&mut self, c: &ExtensionRuleConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.tseitin_transform"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.formula.clone(), c.er_proof.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.tseitin_transform"),
            level_params: vec![],
            type_: ty,
        })
    }
}
