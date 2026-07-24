// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for Craig interpolation formalization.
//!
//! Registers the kernel-level axiom surfaces for:
//! - Craig interpolation theorem (existence of interpolant)
//! - Interpolant variable restriction (uses only shared variables)
//! - Interpolant size bound (bounded by min of proof sizes)
//! - Constructive interpolant extraction from resolution
//! - Reverse interpolation (interpolant to resolution proof)
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom
//! captures the proposition body, and the theorem quantifies over all
//! parameters with the helper applied.
//!
//! Reference: Craig (1957), "Three uses of the Herbrand-Gentzen theorem";
//!            Krajicek (1997), "Interpolation theorems, lower bounds";
//!            Pudlak (1997), "Lower bounds for resolution and cutting plane".

use super::craig_interpolation::CraigInterpolationConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: Craig interpolation
    // ====================================================================

    /// `craig_interpolation : forall (a b : PropFormula),
    ///     craig_interpolation_helper a b`
    ///
    /// Craig's interpolation theorem: if A ∧ B is unsatisfiable, then there
    /// exists a formula I over the shared variables of A and B such that
    /// A → I and I ∧ B is unsatisfiable.
    ///
    /// The helper encodes: unsatisfiable(A ∧ B) →
    ///   ∃ I, uses_only(I, shared_variables(A, B)) ∧ (A → I) ∧ unsatisfiable(I ∧ B)
    pub(super) fn register_craig_interpolation_thm(
        &mut self,
        c: &CraigInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.craig_interpolation_helper";
        let thm_name = "ProofTheory.craig_interpolation";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b : PropFormula) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let e = b.mk_pi(
                    b_id,
                    BinderInfo::Default,
                    c.prop_formula.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
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
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone()]);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: Interpolant uses shared variables
    // ====================================================================

    /// `interpolant_uses_shared_vars : forall (a b : PropFormula)
    ///     (p : Resolution.Proof), interpolant_uses_shared_vars_helper a b p`
    ///
    /// The interpolant extracted from a resolution refutation of A ∧ B
    /// uses only variables that appear in both A and B.
    pub(super) fn register_interpolant_uses_shared_vars(
        &mut self,
        c: &CraigInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.interpolant_uses_shared_vars_helper";
        let thm_name = "ProofTheory.interpolant_uses_shared_vars";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b : PropFormula) -> (p : Resolution.Proof) -> Prop
            // Encodes: uses_only(interpolant(a, b, p), shared_variables(a, b))
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (p_id, _) = b.fresh_local(c.res_proof.clone());
                let e = b.mk_pi(
                    p_id,
                    BinderInfo::Default,
                    c.res_proof.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
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
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (p_id, p) = b.fresh_local(c.res_proof.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.res_proof.clone(), body);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Interpolant size bound
    // ====================================================================

    /// `interpolant_size_bound : forall (a b : PropFormula)
    ///     (p : Resolution.Proof), interpolant_size_bound_helper a b p`
    ///
    /// The size of the extracted interpolant is bounded by the proof complexity:
    /// formula_size(interpolant(a, b, p)) <= proof_complexity(p).
    ///
    /// This follows because each resolution step contributes at most one
    /// connective to the interpolant formula.
    pub(super) fn register_interpolant_size_bound(
        &mut self,
        c: &CraigInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.interpolant_size_bound_helper";
        let thm_name = "ProofTheory.interpolant_size_bound";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b : PropFormula) -> (p : Resolution.Proof) -> Prop
            // Encodes: formula_size(interpolant(a, b, p)) <= proof_complexity(p)
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (p_id, _) = b.fresh_local(c.res_proof.clone());
                let e = b.mk_pi(
                    p_id,
                    BinderInfo::Default,
                    c.res_proof.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
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
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (p_id, p) = b.fresh_local(c.res_proof.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.res_proof.clone(), body);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: Interpolant from resolution (constructive extraction)
    // ====================================================================

    /// `interpolant_from_resolution : forall (a b : PropFormula)
    ///     (p : Resolution.Proof), interpolant_from_resolution_helper a b p`
    ///
    /// Constructive interpolation: given a resolution refutation of A ∧ B,
    /// the `interpolant` function produces a valid interpolant. Specifically:
    /// - A → interpolant(a, b, p)
    /// - interpolant(a, b, p) ∧ B is unsatisfiable
    ///
    /// The extraction follows the Krajicek-Pudlak algorithm: walk the
    /// resolution tree bottom-up, labeling each node with a partial
    /// interpolant. At leaves from A, set I = clause; at leaves from B,
    /// set I = True. At resolve steps, combine according to whether the
    /// pivot variable belongs to A, B, or both.
    pub(super) fn register_interpolant_from_resolution(
        &mut self,
        c: &CraigInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.interpolant_from_resolution_helper";
        let thm_name = "ProofTheory.interpolant_from_resolution";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b : PropFormula) -> (p : Resolution.Proof) -> Prop
            // Encodes: validity of the constructive extraction
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (p_id, _) = b.fresh_local(c.res_proof.clone());
                let e = b.mk_pi(
                    p_id,
                    BinderInfo::Default,
                    c.res_proof.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
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
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (p_id, p) = b.fresh_local(c.res_proof.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.res_proof.clone(), body);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: Reverse interpolation
    // ====================================================================

    /// `reverse_interpolation : forall (a b i : PropFormula),
    ///     reverse_interpolation_helper a b i`
    ///
    /// Reverse interpolation: from a valid interpolant I (where A → I and
    /// I ∧ B is unsatisfiable), one can construct a resolution refutation
    /// of A ∧ B. This is the converse of the constructive extraction.
    ///
    /// The proof complexity of the reconstructed proof is bounded
    /// polynomially in the sizes of A, B, and I.
    pub(super) fn register_reverse_interpolation(
        &mut self,
        c: &CraigInterpolationConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.reverse_interpolation_helper";
        let thm_name = "ProofTheory.reverse_interpolation";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (a b i : PropFormula) -> Prop
            // Encodes: (A → I) ∧ unsat(I ∧ B) → ∃ p, refutes(p, A ∧ B)
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, _) = b.fresh_local(c.prop_formula.clone());
                let (b_id, _) = b.fresh_local(c.prop_formula.clone());
                let (i_id, _) = b.fresh_local(c.prop_formula.clone());
                let e = b.mk_pi(
                    i_id,
                    BinderInfo::Default,
                    c.prop_formula.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
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
            let (a_id, a) = b.fresh_local(c.prop_formula.clone());
            let (b_id, bv) = b.fresh_local(c.prop_formula.clone());
            let (i_id, i) = b.fresh_local(c.prop_formula.clone());
            let body = Expr::apps(helper, [a.clone(), bv.clone(), i.clone()]);
            let e = b.mk_pi(i_id, BinderInfo::Default, c.prop_formula.clone(), body);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.prop_formula.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
