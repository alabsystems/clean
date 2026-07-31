// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for GF(2) Polynomial Calculus soundness.
//!
//! Registers the kernel-level axiom surfaces for:
//! - Clause encoding soundness (clause satisfaction iff polynomial = 0)
//! - GF(2) field idempotency (x^2 = x for all elements)
//! - Ideal closure under addition and multiplication
//! - PC soundness: 1 in ideal implies UNSAT (the main theorem T5)
//! - S-polynomial reduction preserves ideal membership
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom
//! captures the proposition body, and the theorem quantifies over all
//! parameters with the helper applied.
//!
//! Reference: Clegg, Edmonds, Impagliazzo (1996), "Using the Groebner
//!            basis algorithm to find proofs of unsatisfiability", STOC'96.
//!            Razborov (1998), "Lower bounds for the polynomial calculus",
//!            Computational Complexity 7(4), pp. 291-324.
//!
//! Part of #3165.

#[cfg(test)]
use super::gf2_polynomial_calculus::{ns, GF2PCConsts};
#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

/// Build the 4-parameter type `(p q : GF2Polynomial) -> (f : CNFFormula) -> (n : Nat) -> Prop`
/// used by theorems 3, 4, and 6.
#[cfg(test)]
fn build_pqfn_type(c: &GF2PCConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, _) = b.fresh_local(c.gf2_poly.clone());
    let (q_id, _) = b.fresh_local(c.gf2_poly.clone());
    let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
    let (n_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
    let e = b.mk_pi(q_id, BinderInfo::Default, c.gf2_poly.clone(), e);
    let e = b.mk_pi(p_id, BinderInfo::Default, c.gf2_poly.clone(), e);
    b.finish(e)
}

/// Build `forall (p q : GF2Polynomial) (f : CNFFormula) (n : Nat), helper p q f n`
#[cfg(test)]
fn build_pqfn_thm(c: &GF2PCConsts, helper: Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.gf2_poly.clone());
    let (q_id, q) = b.fresh_local(c.gf2_poly.clone());
    let (f_id, f) = b.fresh_local(c.cnf_formula.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(helper, [p.clone(), q.clone(), f.clone(), n.clone()]);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
    let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
    let e = b.mk_pi(q_id, BinderInfo::Default, c.gf2_poly.clone(), e);
    let e = b.mk_pi(p_id, BinderInfo::Default, c.gf2_poly.clone(), e);
    b.finish(e)
}

#[cfg(test)]
impl Environment {
    // ====================================================================
    // Theorem 1: Clause encoding soundness
    // ====================================================================

    /// Satisfaction iff clause polynomial evaluates to 0.
    #[cfg(test)]
    pub(super) fn register_gf2pc_clause_encoding_soundness(
        &mut self,
        c: &GF2PCConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("clause_encoding_soundness_helper");
        let thm_name = ns("clause_encoding_soundness");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            // Helper: (cl : CNFClause) -> (a : BooleanAssignment) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (cl_id, _) = b.fresh_local(c.cnf_clause.clone());
                let (a_id, _) = b.fresh_local(c.bool_assignment.clone());
                let e = b.mk_pi(
                    a_id,
                    BinderInfo::Default,
                    c.bool_assignment.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(cl_id, BinderInfo::Default, c.cnf_clause.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cl_id, cl) = b.fresh_local(c.cnf_clause.clone());
            let (a_id, a) = b.fresh_local(c.bool_assignment.clone());
            let body = Expr::apps(helper, [cl.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.bool_assignment.clone(), body);
            let e = b.mk_pi(cl_id, BinderInfo::Default, c.cnf_clause.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: GF(2) field idempotency (x^2 = x)
    // ====================================================================

    /// For any variable index i and any formula f with n variables,
    /// the polynomial x_i^2 - x_i is in the ideal (Boolean axiom).
    ///
    /// ```text
    /// forall (i : Nat) (f : CNFFormula) (n : Nat),
    ///   gf2_field_idempotent_helper i f n
    /// ```
    #[cfg(test)]
    pub(super) fn register_gf2pc_field_idempotent(
        &mut self,
        c: &GF2PCConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("gf2_field_idempotent_helper");
        let thm_name = ns("gf2_field_idempotent");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (i_id, _) = b.fresh_local(c.nat.clone());
                let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
                let (n_id, _) = b.fresh_local(c.nat.clone());
                let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
                let e = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i_var) = b.fresh_local(c.nat.clone());
            let (f_id, f_var) = b.fresh_local(c.cnf_formula.clone());
            let (n_id, n_var) = b.fresh_local(c.nat.clone());
            let body = Expr::apps(helper, [i_var.clone(), f_var.clone(), n_var.clone()]);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            let e = b.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Ideal is closed under addition
    // ====================================================================

    /// If p and q are in the ideal, then p + q is in the ideal.
    #[cfg(test)]
    pub(super) fn register_gf2pc_ideal_closed_addition(
        &mut self,
        c: &GF2PCConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("ideal_closed_addition_helper");
        let thm_name = ns("ideal_closed_addition");
        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&helper_name),
                level_params: vec![],
                type_: build_pqfn_type(c),
            })?;
        }
        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&thm_name),
            level_params: vec![],
            type_: build_pqfn_thm(c, helper),
        })
    }

    // ====================================================================
    // Theorem 4: Ideal is closed under multiplication (absorption)
    // ====================================================================

    /// If p is in the ideal and q is any polynomial, then p * q is in the ideal.
    #[cfg(test)]
    pub(super) fn register_gf2pc_ideal_closed_multiplication(
        &mut self,
        c: &GF2PCConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("ideal_closed_multiplication_helper");
        let thm_name = ns("ideal_closed_multiplication");
        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&helper_name),
                level_params: vec![],
                type_: build_pqfn_type(c),
            })?;
        }
        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&thm_name),
            level_params: vec![],
            type_: build_pqfn_thm(c, helper),
        })
    }

    // ====================================================================
    // Theorem 5: PC Soundness over GF(2) -- THE MAIN THEOREM (T5)
    // ====================================================================

    /// **T5 PC Soundness:** If 1 is in the ideal generated by clause
    /// polynomials and Boolean axioms, then the formula is unsatisfiable.
    #[cfg(test)]
    pub(super) fn register_gf2pc_pc_soundness(&mut self, c: &GF2PCConsts) -> Result<(), EnvError> {
        let helper_name = ns("pc_soundness_gf2_helper");
        let thm_name = ns("pc_soundness_gf2");

        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            // Helper: (f : CNFFormula) -> (n : Nat) -> Prop
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
                let (n_id, _) = b.fresh_local(c.nat.clone());
                let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
                let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f_var) = b.fresh_local(c.cnf_formula.clone());
            let (n_id, n_var) = b.fresh_local(c.nat.clone());
            let body = Expr::apps(helper, [f_var.clone(), n_var.clone()]);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 6: S-polynomial reduction preserves ideal membership
    // ====================================================================

    /// S-polynomial reduction preserves ideal membership.
    #[cfg(test)]
    pub(super) fn register_gf2pc_spoly_preserves_ideal(
        &mut self,
        c: &GF2PCConsts,
    ) -> Result<(), EnvError> {
        let helper_name = ns("spoly_preserves_ideal_helper");
        let thm_name = ns("spoly_preserves_ideal");
        if self.get_const(&Name::from_string(&helper_name)).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(&helper_name),
                level_params: vec![],
                type_: build_pqfn_type(c),
            })?;
        }
        if self.get_const(&Name::from_string(&thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(Name::from_string(&helper_name), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&thm_name),
            level_params: vec![],
            type_: build_pqfn_thm(c, helper),
        })
    }
}
