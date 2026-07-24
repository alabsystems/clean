// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for Craig interpolation formalization.
//!
//! Registers the foundational types and definitions needed to state
//! Craig's interpolation theorem with constructive interpolant extraction
//! from resolution proofs.
//!
//! Craig's interpolation theorem (1957): If A ∧ B is unsatisfiable, then
//! there exists a formula I (the interpolant) using only variables shared
//! between A and B such that A → I and I ∧ B is unsatisfiable.
//!
//! The constructive version extracts an explicit interpolant from a
//! resolution refutation of A ∧ B, following Krajicek (1997) and
//! Pudlak (1997).
//!
//! Type and operation definitions live here; theorem registrations are in
//! `craig_interpolation_theorems.rs`.
//!
//! Reference: Craig (1957), "Three uses of the Herbrand-Gentzen theorem";
//!            Krajicek (1997), "Interpolation theorems, lower bounds for proof systems";
//!            Pudlak (1997), "Lower bounds for resolution and cutting plane proofs".

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all Craig interpolation declarations.
pub(super) struct CraigInterpolationConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.PropFormula : Type
    pub(super) prop_formula: Expr,
    /// ProofTheory.Resolution.Proof : Type
    pub(super) res_proof: Expr,
    /// ProofTheory.VarSet : Type (set of variable indices)
    pub(super) var_set: Expr,
}

impl CraigInterpolationConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop_formula: Expr::const_(Name::from_string("ProofTheory.PropFormula"), vec![]),
            res_proof: Expr::const_(Name::from_string("ProofTheory.Resolution.Proof"), vec![]),
            var_set: Expr::const_(Name::from_string("ProofTheory.VarSet"), vec![]),
        }
    }
}

impl Environment {
    /// Initialize Craig interpolation declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`.
    pub(crate) fn init_craig_interpolation(&mut self) -> Result<(), EnvError> {
        if self.craig_interpolation_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;

        let c = CraigInterpolationConsts::new();
        self.register_prop_formula(&c)?;
        self.register_var_set(&c)?;
        self.register_resolution_proof(&c)?;
        self.register_shared_variables(&c)?;
        self.register_interpolant(&c)?;
        self.register_proof_complexity(&c)?;
        self.register_formula_size(&c)?;
        // Theorem registrations (in craig_interpolation_theorems.rs)
        self.register_craig_interpolation_thm(&c)?;
        self.register_interpolant_uses_shared_vars(&c)?;
        self.register_interpolant_size_bound(&c)?;
        self.register_interpolant_from_resolution(&c)?;
        self.register_reverse_interpolation(&c)?;

        self.craig_interpolation_init = true;
        Ok(())
    }

    // ====================================================================
    // Definition 1: PropFormula — propositional formula type
    // ====================================================================

    /// `PropFormula : Type` — propositional formula (var, neg, and, or, implies).
    ///
    /// Constructors:
    /// - `Var (v : Nat)` — propositional variable
    /// - `Neg (f : PropFormula)` — negation
    /// - `And (a b : PropFormula)` — conjunction
    /// - `Or (a b : PropFormula)` — disjunction
    /// - `Implies (a b : PropFormula)` — implication
    fn register_prop_formula(&mut self, c: &CraigInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.PropFormula"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PropFormula"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Var constructor: (v : Nat) -> PropFormula
        let var_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop_formula.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PropFormula.Var"),
            level_params: vec![],
            type_: var_ty,
        })?;
        // Neg constructor: (f : PropFormula) -> PropFormula
        let neg_ty = Expr::pi(
            BinderInfo::Default,
            c.prop_formula.clone(),
            c.prop_formula.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PropFormula.Neg"),
            level_params: vec![],
            type_: neg_ty,
        })?;
        // And constructor: (a b : PropFormula) -> PropFormula
        let and_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_formula.clone(),
                c.prop_formula.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PropFormula.And"),
            level_params: vec![],
            type_: and_ty,
        })?;
        // Or constructor: (a b : PropFormula) -> PropFormula
        let or_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_formula.clone(),
                c.prop_formula.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PropFormula.Or"),
            level_params: vec![],
            type_: or_ty,
        })?;
        // Implies constructor: (a b : PropFormula) -> PropFormula
        let implies_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_formula.clone(),
                c.prop_formula.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.PropFormula.Implies"),
            level_params: vec![],
            type_: implies_ty,
        })
    }

    // ====================================================================
    // Definition: VarSet — set of variable indices
    // ====================================================================

    /// `VarSet : Type` — abstract set of variable indices.
    ///
    /// Used to represent the set of variables appearing in a formula,
    /// and the shared variables between two formulas.
    fn register_var_set(&mut self, c: &CraigInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.VarSet"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.VarSet"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // variables_of : PropFormula -> VarSet
        let vars_of_ty = Expr::pi(
            BinderInfo::Default,
            c.prop_formula.clone(),
            c.var_set.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.variables_of"),
            level_params: vec![],
            type_: vars_of_ty,
        })?;
        // uses_only : PropFormula -> VarSet -> Prop
        let uses_only_ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.prop_formula.clone());
            let (s_id, _) = b.fresh_local(c.var_set.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, c.var_set.clone(), c.prop.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.uses_only"),
            level_params: vec![],
            type_: uses_only_ty,
        })
    }

    // ====================================================================
    // Definition 2: Resolution.Proof — resolution proof structure
    // ====================================================================

    /// `Resolution.Proof : Type` — resolution proof tree.
    ///
    /// Constructors:
    /// - `Axiom (cl : PropFormula)` — leaf: an axiom clause
    /// - `Resolve (p1 p2 : Resolution.Proof) (v : Nat)` — resolve on variable v
    fn register_resolution_proof(&mut self, c: &CraigInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.Resolution.Proof"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.Resolution.Proof"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // Axiom constructor: (cl : PropFormula) -> Resolution.Proof
        let axiom_ty = Expr::pi(
            BinderInfo::Default,
            c.prop_formula.clone(),
            c.res_proof.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.Resolution.Proof.Axiom"),
            level_params: vec![],
            type_: axiom_ty,
        })?;
        // Resolve constructor: (p1 p2 : Proof) (v : Nat) -> Proof
        let resolve_ty = {
            let mut b = EnvDeclBuilder::new();
            let (p1_id, _) = b.fresh_local(c.res_proof.clone());
            let (p2_id, _) = b.fresh_local(c.res_proof.clone());
            let (v_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(
                v_id,
                BinderInfo::Default,
                c.nat.clone(),
                c.res_proof.clone(),
            );
            let e = b.mk_pi(p2_id, BinderInfo::Default, c.res_proof.clone(), e);
            let e = b.mk_pi(p1_id, BinderInfo::Default, c.res_proof.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.Resolution.Proof.Resolve"),
            level_params: vec![],
            type_: resolve_ty,
        })
    }

    // ====================================================================
    // Definition 3: shared_variables
    // ====================================================================

    /// `shared_variables (a b : PropFormula) : VarSet`
    ///
    /// The set of propositional variables appearing in both formula A and
    /// formula B. This is the intersection of variables_of(A) and variables_of(B).
    fn register_shared_variables(&mut self, c: &CraigInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.shared_variables"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_formula.clone(),
                c.var_set.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.shared_variables"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 4: interpolant — interpolant extraction function
    // ====================================================================

    /// `interpolant (a b : PropFormula) (p : Resolution.Proof) : PropFormula`
    ///
    /// Constructive extraction of an interpolant from a resolution refutation
    /// of A ∧ B. Given formulas A, B and a proof that A ∧ B is unsatisfiable,
    /// returns a formula I such that:
    /// - A → I (I is implied by A)
    /// - I ∧ B is unsatisfiable
    /// - I uses only variables in shared_variables(A, B)
    ///
    /// Reference: Krajicek (1997), Pudlak (1997).
    fn register_interpolant(&mut self, c: &CraigInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.interpolant"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let (p_id, _) = b.fresh_local(c.res_proof.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.res_proof.clone(),
                c.prop_formula.clone(),
            );
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.interpolant"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 5: proof_complexity — size of a resolution proof
    // ====================================================================

    /// `proof_complexity (p : Resolution.Proof) : Nat`
    ///
    /// The number of resolve steps in a resolution proof. Leaf axiom
    /// nodes contribute 0; each Resolve node contributes 1.
    fn register_proof_complexity(&mut self, c: &CraigInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.proof_complexity"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.res_proof.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.proof_complexity"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition: formula_size — size of a propositional formula
    // ====================================================================

    /// `formula_size (f : PropFormula) : Nat`
    ///
    /// The number of connective nodes in a propositional formula.
    /// Used in the interpolant size bound.
    fn register_formula_size(&mut self, c: &CraigInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.formula_size"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.prop_formula.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.formula_size"),
            level_params: vec![],
            type_: ty,
        })
    }
}
