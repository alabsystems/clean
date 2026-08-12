// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for labelled interpolation minimality.
//!
//! Formalizes D'Silva's result (ESOP 2010) that McMillan interpolants
//! have minimal variable support among all labelled interpolation systems
//! applied to the same resolution proof, and that extractable interpolants
//! form a complete lattice under logical implication.
//!
//! For a fixed resolution refutation pi of (A AND B), let L be any
//! labelling function for a labelled interpolation system. Then:
//!
//! 1. The McMillan interpolant I_McM(pi) satisfies:
//!    Var(I_McM(pi)) is a subset of Var(I_L(pi)) for all valid L.
//! 2. Extractable interpolants form a complete lattice under |=.
//! 3. McMillan is the bottom (weakest) of the lattice.
//! 4. Reverse McMillan is the top (strongest) of the lattice.
//!
//! Type and operation definitions live here; theorem registrations are in
//! `labelled_interpolation_minimality_theorems.rs`.
//!
//! Reference: D'Silva et al. (2010), "Propositional Interpolation and
//!            Abstract Interpretation", ESOP 2010;
//!            D'Silva et al. (2010), "Interpolant Strength", VMCAI 2010;
//!            Schlaipfer & Weissenbacher (2016), "Labelled Interpolation
//!            Systems for Hyper-Resolution, Clausal, and Local Proofs", JAR.

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

/// Shared constants used across all labelled interpolation minimality declarations.
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) struct LabelledInterpolationConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.PropFormula : Type (from craig_interpolation)
    pub(super) prop_formula: Expr,
    /// ProofTheory.Resolution.Proof : Type (from craig_interpolation)
    pub(super) res_proof: Expr,
    /// ProofTheory.VarSet : Type (from craig_interpolation)
    pub(super) var_set: Expr,
    /// ProofTheory.LabelledInterpolation.LabellingFunction : Type
    pub(super) labelling_fn: Expr,
    /// ProofTheory.LabelledInterpolation.InterpolationSystem : Type
    pub(super) interp_system: Expr,
}

#[cfg(test)]
impl LabelledInterpolationConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop_formula: Expr::const_(Name::from_string("ProofTheory.PropFormula"), vec![]),
            res_proof: Expr::const_(Name::from_string("ProofTheory.Resolution.Proof"), vec![]),
            var_set: Expr::const_(Name::from_string("ProofTheory.VarSet"), vec![]),
            labelling_fn: Expr::const_(
                Name::from_string("ProofTheory.LabelledInterpolation.LabellingFunction"),
                vec![],
            ),
            interp_system: Expr::const_(
                Name::from_string("ProofTheory.LabelledInterpolation.InterpolationSystem"),
                vec![],
            ),
        }
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize labelled interpolation minimality declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_craig_interpolation()`.
    #[cfg(test)]
    pub(crate) fn init_labelled_interpolation_minimality(&mut self) -> Result<(), EnvError> {
        if self.labelled_interpolation_minimality_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_craig_interpolation()?;

        let c = LabelledInterpolationConsts::new();

        // Definitions
        self.register_labelling_function(&c)?;
        self.register_interpolation_system(&c)?;
        self.register_labelled_interpolant(&c)?;
        self.register_mcmillan_labelling(&c)?;
        self.register_reverse_mcmillan_labelling(&c)?;
        self.register_variable_support(&c)?;
        self.register_var_subset(&c)?;
        self.register_interpolant_implies(&c)?;

        // Theorems (in labelled_interpolation_minimality_theorems.rs)
        self.register_labelled_interpolant_valid(&c)?;
        self.register_mcmillan_support_minimal(&c)?;
        self.register_interpolant_lattice_complete(&c)?;
        self.register_mcmillan_is_lattice_bottom(&c)?;
        self.register_reverse_mcmillan_is_lattice_top(&c)?;

        self.labelled_interpolation_minimality_init = true;
        Ok(())
    }

    // ====================================================================
    // Definition 1: LabellingFunction — pivot classification function
    // ====================================================================

    /// `LabellingFunction : Type` — labels pivots as A-local or B-local/shared.
    /// Determines the interpolation rule at each resolution DAG node.
    #[cfg(test)]
    fn register_labelling_function(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.LabellingFunction",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.LabellingFunction"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    // ====================================================================
    // Definition 2: InterpolationSystem — labelling + validity predicate
    // ====================================================================

    /// `InterpolationSystem : Type` — bundles a labelling with validity.
    /// Projections: `labelling`, `valid`.
    #[cfg(test)]
    fn register_interpolation_system(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.InterpolationSystem",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.InterpolationSystem"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // labelling : InterpolationSystem -> LabellingFunction
        let labelling_ty = Expr::pi(
            BinderInfo::Default,
            c.interp_system.clone(),
            c.labelling_fn.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(
                "ProofTheory.LabelledInterpolation.InterpolationSystem.labelling",
            ),
            level_params: vec![],
            type_: labelling_ty,
        })?;
        // valid : InterpolationSystem -> Prop
        let valid_ty = Expr::pi(BinderInfo::Default, c.interp_system.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.InterpolationSystem.valid"),
            level_params: vec![],
            type_: valid_ty,
        })
    }

    // ====================================================================
    // Definition 3: labelled_interpolant — extraction parameterized by L
    // ====================================================================

    /// `labelled_interpolant : PropFormula -> PropFormula -> Proof -> LabellingFunction -> PropFormula`
    /// Extract interpolant from (A, B, proof) parameterized by labelling L.
    #[cfg(test)]
    fn register_labelled_interpolant(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.labelled_interpolant",
            ))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_formula.clone());
            let (b_id, _) = b.fresh_local(c.prop_formula.clone());
            let (pi_id, _) = b.fresh_local(c.res_proof.clone());
            let (l_id, _) = b.fresh_local(c.labelling_fn.clone());
            let e = b.mk_pi(
                l_id,
                BinderInfo::Default,
                c.labelling_fn.clone(),
                c.prop_formula.clone(),
            );
            let e = b.mk_pi(pi_id, BinderInfo::Default, c.res_proof.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.labelled_interpolant"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 4: mcmillan_labelling — McMillan's specific labelling
    // ====================================================================

    /// `mcmillan_labelling : PropFormula -> PropFormula -> LabellingFunction`
    /// McMillan's labelling: A-only pivots are A-local, rest B-local.
    /// Produces the weakest interpolant (D'Silva lattice bottom).
    #[cfg(test)]
    fn register_mcmillan_labelling(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.mcmillan_labelling",
            ))
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
                c.labelling_fn.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.mcmillan_labelling"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 5: reverse_mcmillan_labelling — dual labelling
    // ====================================================================

    /// `reverse_mcmillan_labelling : PropFormula -> PropFormula -> LabellingFunction`
    /// Reverse McMillan: B-only pivots are B-local, rest A-local.
    /// Produces the strongest interpolant (D'Silva lattice top).
    #[cfg(test)]
    fn register_reverse_mcmillan_labelling(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.reverse_mcmillan_labelling",
            ))
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
                c.labelling_fn.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.reverse_mcmillan_labelling"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 6: variable_support — Var(I) for a formula I
    // ====================================================================

    /// `variable_support : PropFormula -> VarSet`
    /// Variables appearing in formula f. Used in minimality statements.
    #[cfg(test)]
    fn register_variable_support(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.variable_support",
            ))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.prop_formula.clone(),
            c.var_set.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.variable_support"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 7: var_subset — subset relation on variable sets
    // ====================================================================

    /// `var_subset : VarSet -> VarSet -> Prop` — subset relation on variable sets.
    #[cfg(test)]
    fn register_var_subset(&mut self, c: &LabelledInterpolationConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.var_subset",
            ))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s1_id, _) = b.fresh_local(c.var_set.clone());
            let (s2_id, _) = b.fresh_local(c.var_set.clone());
            let e = b.mk_pi(
                s2_id,
                BinderInfo::Default,
                c.var_set.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(s1_id, BinderInfo::Default, c.var_set.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.var_subset"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 8: interpolant_implies — logical implication ordering
    // ====================================================================

    /// `interpolant_implies : PropFormula -> PropFormula -> Prop`
    /// Logical implication i1 |= i2. The lattice ordering.
    #[cfg(test)]
    fn register_interpolant_implies(
        &mut self,
        c: &LabelledInterpolationConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "ProofTheory.LabelledInterpolation.interpolant_implies",
            ))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i1_id, _) = b.fresh_local(c.prop_formula.clone());
            let (i2_id, _) = b.fresh_local(c.prop_formula.clone());
            let e = b.mk_pi(
                i2_id,
                BinderInfo::Default,
                c.prop_formula.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(i1_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LabelledInterpolation.interpolant_implies"),
            level_params: vec![],
            type_: ty,
        })
    }
}
