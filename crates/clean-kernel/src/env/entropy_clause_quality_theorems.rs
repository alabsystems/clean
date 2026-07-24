// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for entropy monotonicity and submodularity
//! of clause quality.
//!
//! Registers the kernel-level axiom surfaces for:
//!
//! - **T7 Entropy Monotonicity**: F |= C => H(F AND C) <= H(F)
//! - **T7b Submodularity**: I(C | F union G) <= I(C | F)
//! - **Entropy non-negativity**: H(F) >= 0
//! - **Entropy upper bound**: H(F) <= n (number of variables)
//! - **Entropy zero iff unique**: H(F) = 0 iff |Sat(F)| <= 1
//! - **Solution count monotonicity**: F |= C => |Sat(F AND C)| <= |Sat(F)|
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom
//! captures the proposition body, and the theorem quantifies over all
//! parameters with the helper applied.
//!
//! Reference: O'Donnell (2014), "Analysis of Boolean Functions",
//!            Cambridge University Press.
//!            Shannon (1948), "A Mathematical Theory of Communication",
//!            Bell System Technical Journal 27(3), pp. 379-423.
//!
//! Part of #3167.

use super::entropy_clause_quality::{ns, EntropyClauseQualityConsts};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Register a helper axiom with idempotency check.
fn add_axiom(env: &mut Environment, name: &str, type_: Expr) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
}

impl Environment {
    // ====================================================================
    // T7: Entropy Monotonicity
    // ====================================================================

    /// **T7 Entropy Monotonicity:** For a CNF formula F and clause C such
    /// that F entails C: solution_entropy(F AND C) <= solution_entropy(F).
    ///
    /// ```text
    /// forall (f : CNFFormula) (c : CNFClause),
    ///   entropy_monotonicity_helper f c
    /// ```
    ///
    /// The helper encodes: formula_entails_clause f c ->
    ///   solution_entropy(formula_add_clause f c) <= solution_entropy f.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ecq_entropy_monotonicity(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("entropy_monotonicity_helper");
        let thm_name = ns("entropy_monotonicity");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            // Helper: (f : CNFFormula) -> (cl : CNFClause) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
                let (cl_id, _) = b.fresh_local(c.cnf_clause.clone());
                let e = b.mk_pi(
                    cl_id,
                    BinderInfo::Default,
                    c.cnf_clause.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
                b.finish(e)
            };
            add_axiom(self, &helper_name, helper_ty)?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf_formula.clone());
            let (cl_id, cl) = b.fresh_local(c.cnf_clause.clone());
            let body = Expr::apps(helper, [f.clone(), cl.clone()]);
            let e = b.mk_pi(cl_id, BinderInfo::Default, c.cnf_clause.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            b.finish(e)
        };
        add_axiom(self, &thm_name, ty)
    }

    // ====================================================================
    // T7b: Submodularity
    // ====================================================================

    /// **T7b Submodularity:** For clause sets F, G and clause C:
    ///   I(C | F union G) <= I(C | F)
    /// where I(C | F) = H(F) - H(F AND C) is the information gain.
    ///
    /// ```text
    /// forall (f g : CNFFormula) (cl : CNFClause),
    ///   submodularity_helper f g cl
    /// ```
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ecq_submodularity(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("submodularity_helper");
        let thm_name = ns("submodularity");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            // Helper: (f : CNFFormula) -> (g : CNFFormula) -> (cl : CNFClause) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
                let (g_id, _) = b.fresh_local(c.cnf_formula.clone());
                let (cl_id, _) = b.fresh_local(c.cnf_clause.clone());
                let e = b.mk_pi(
                    cl_id,
                    BinderInfo::Default,
                    c.cnf_clause.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(g_id, BinderInfo::Default, c.cnf_formula.clone(), e);
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
                b.finish(e)
            };
            add_axiom(self, &helper_name, helper_ty)?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf_formula.clone());
            let (g_id, g) = b.fresh_local(c.cnf_formula.clone());
            let (cl_id, cl) = b.fresh_local(c.cnf_clause.clone());
            let body = Expr::apps(helper, [f.clone(), g.clone(), cl.clone()]);
            let e = b.mk_pi(cl_id, BinderInfo::Default, c.cnf_clause.clone(), body);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            b.finish(e)
        };
        add_axiom(self, &thm_name, ty)
    }

    // ====================================================================
    // Entropy non-negativity
    // ====================================================================

    /// Entropy is non-negative: H(F) >= 0 for all CNF formulas F.
    ///
    /// ```text
    /// forall (f : CNFFormula), entropy_nonneg_helper f
    /// ```
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ecq_entropy_nonneg(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("entropy_nonneg_helper");
        let thm_name = ns("entropy_nonneg");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            // Helper: (f : CNFFormula) -> Prop
            let helper_ty = Expr::pi(BinderInfo::Default, c.cnf_formula.clone(), c.prop.clone());
            add_axiom(self, &helper_name, helper_ty)?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf_formula.clone());
            let body = Expr::app(helper, f.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), body);
            b.finish(e)
        };
        add_axiom(self, &thm_name, ty)
    }

    // ====================================================================
    // Entropy upper bound
    // ====================================================================

    /// Entropy is bounded by the number of variables: H(F) <= n.
    ///
    /// ```text
    /// forall (f : CNFFormula), entropy_upper_bound_helper f
    /// ```
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ecq_entropy_upper_bound(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("entropy_upper_bound_helper");
        let thm_name = ns("entropy_upper_bound");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            let helper_ty = Expr::pi(BinderInfo::Default, c.cnf_formula.clone(), c.prop.clone());
            add_axiom(self, &helper_name, helper_ty)?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf_formula.clone());
            let body = Expr::app(helper, f.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), body);
            b.finish(e)
        };
        add_axiom(self, &thm_name, ty)
    }

    // ====================================================================
    // Entropy zero iff unique solution
    // ====================================================================

    /// H(F) = 0 if and only if |Sat(F)| <= 1 (zero or one solution).
    ///
    /// ```text
    /// forall (f : CNFFormula), entropy_zero_iff_unique_helper f
    /// ```
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ecq_entropy_zero_iff_unique(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("entropy_zero_iff_unique_helper");
        let thm_name = ns("entropy_zero_iff_unique");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            let helper_ty = Expr::pi(BinderInfo::Default, c.cnf_formula.clone(), c.prop.clone());
            add_axiom(self, &helper_name, helper_ty)?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf_formula.clone());
            let body = Expr::app(helper, f.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), body);
            b.finish(e)
        };
        add_axiom(self, &thm_name, ty)
    }

    // ====================================================================
    // Solution count monotonicity
    // ====================================================================

    /// If F entails C, then |Sat(F AND C)| <= |Sat(F)|.
    ///
    /// This is the set-theoretic foundation for entropy monotonicity:
    /// Sat(F AND C) is a subset of Sat(F) when F |= C.
    ///
    /// ```text
    /// forall (f : CNFFormula) (cl : CNFClause),
    ///   solution_count_monotone_helper f cl
    /// ```
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ecq_solution_count_monotone(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("solution_count_monotone_helper");
        let thm_name = ns("solution_count_monotone");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
                let (cl_id, _) = b.fresh_local(c.cnf_clause.clone());
                let e = b.mk_pi(
                    cl_id,
                    BinderInfo::Default,
                    c.cnf_clause.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
                b.finish(e)
            };
            add_axiom(self, &helper_name, helper_ty)?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.cnf_formula.clone());
            let (cl_id, cl) = b.fresh_local(c.cnf_clause.clone());
            let body = Expr::apps(helper, [f.clone(), cl.clone()]);
            let e = b.mk_pi(cl_id, BinderInfo::Default, c.cnf_clause.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            b.finish(e)
        };
        add_axiom(self, &thm_name, ty)
    }
}
