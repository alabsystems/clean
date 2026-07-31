// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for entropy monotonicity and submodularity
//! of clause quality in SAT solving.
//!
//! Formalizes information-theoretic properties of clause learning:
//!
//! - **Solution space entropy** H(F) = log(|Sat(F)|), measuring the
//!   remaining uncertainty in the solution space of a CNF formula.
//! - **Information gain** I(C|F) = H(F) - H(F AND C), measuring how
//!   much a clause C reduces uncertainty about the solution.
//! - **Entropy monotonicity** (T7): Adding an entailed clause cannot
//!   increase solution space entropy.
//! - **Submodularity** (T7b): Entropy reduction has diminishing returns
//!   as more clauses are added.
//!
//! Type and operation definitions live here; theorem registrations are
//! in `entropy_clause_quality_theorems.rs`.
//!
//! Reference: O'Donnell (2014), "Analysis of Boolean Functions",
//!            Cambridge University Press.
//!            Shannon (1948), "A Mathematical Theory of Communication",
//!            Bell System Technical Journal 27(3), pp. 379-423.
//!
//! Part of #3167.

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

#[cfg(test)]
const NS: &str = "InfoTheory.EntropyClauseQuality";

#[cfg(test)]
pub(super) fn ns(suffix: &str) -> String {
    format!("{NS}.{suffix}")
}

/// Shared constants used across all entropy clause quality declarations.
#[cfg(test)]
pub(super) struct EntropyClauseQualityConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// InfoTheory.EntropyClauseQuality.AssignmentSpace : Type
    pub(super) assignment_space: Expr,
    /// InfoTheory.EntropyClauseQuality.CNFFormula : Type
    pub(super) cnf_formula: Expr,
    /// InfoTheory.EntropyClauseQuality.CNFClause : Type
    pub(super) cnf_clause: Expr,
    /// InfoTheory.EntropyClauseQuality.SatisfyingSet : Type
    pub(super) satisfying_set: Expr,
    /// InfoTheory.EntropyClauseQuality.RealNonneg : Type
    pub(super) real_nonneg: Expr,
}

#[cfg(test)]
impl EntropyClauseQualityConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            assignment_space: Expr::const_(Name::from_string(&ns("AssignmentSpace")), vec![]),
            cnf_formula: Expr::const_(Name::from_string(&ns("CNFFormula")), vec![]),
            cnf_clause: Expr::const_(Name::from_string(&ns("CNFClause")), vec![]),
            satisfying_set: Expr::const_(Name::from_string(&ns("SatisfyingSet")), vec![]),
            real_nonneg: Expr::const_(Name::from_string(&ns("RealNonneg")), vec![]),
        }
    }
}

/// Register an axiom with idempotency check.
#[cfg(test)]
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

#[cfg(test)]
impl Environment {
    /// Initialize entropy-based clause quality declarations.
    ///
    /// Depends on: `init_nat()`.
    #[cfg(test)]
    pub(crate) fn init_entropy_clause_quality(&mut self) -> Result<(), EnvError> {
        if self.entropy_clause_quality_init {
            return Ok(());
        }
        self.init_nat()?;

        let c = EntropyClauseQualityConsts::new();

        // Types
        self.register_entropy_clause_quality_assignment_space(&c)?;
        self.register_entropy_clause_quality_cnf_formula(&c)?;
        self.register_entropy_clause_quality_cnf_clause(&c)?;
        self.register_entropy_clause_quality_satisfying_set_type(&c)?;
        self.register_entropy_clause_quality_real_nonneg(&c)?;

        // Operations
        self.register_entropy_clause_quality_num_variables(&c)?;
        self.register_entropy_clause_quality_satisfying_set(&c)?;
        self.register_entropy_clause_quality_sat_count(&c)?;
        self.register_entropy_clause_quality_solution_entropy(&c)?;
        self.register_entropy_clause_quality_information_gain(&c)?;
        self.register_entropy_clause_quality_formula_union(&c)?;
        self.register_entropy_clause_quality_formula_add_clause(&c)?;
        self.register_entropy_clause_quality_formula_entails_clause(&c)?;
        self.register_entropy_clause_quality_assignment_satisfies_formula(&c)?;

        // Theorems (in entropy_clause_quality_theorems.rs)
        self.register_ecq_entropy_monotonicity(&c)?;
        self.register_ecq_submodularity(&c)?;
        self.register_ecq_entropy_nonneg(&c)?;
        self.register_ecq_entropy_upper_bound(&c)?;
        self.register_ecq_entropy_zero_iff_unique(&c)?;
        self.register_ecq_solution_count_monotone(&c)?;

        self.entropy_clause_quality_init = true;
        Ok(())
    }

    // ====================================================================
    // Types
    // ====================================================================

    /// `AssignmentSpace : Type` -- the `2^n` Boolean assignment space.
    #[cfg(test)]
    fn register_entropy_clause_quality_assignment_space(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(self, &ns("AssignmentSpace"), c.type0.clone())
    }

    /// `CNFFormula : Type` -- an abstract CNF formula.
    #[cfg(test)]
    fn register_entropy_clause_quality_cnf_formula(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(self, &ns("CNFFormula"), c.type0.clone())
    }

    /// `CNFClause : Type` -- a single clause in a CNF formula.
    #[cfg(test)]
    fn register_entropy_clause_quality_cnf_clause(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(self, &ns("CNFClause"), c.type0.clone())
    }

    /// `SatisfyingSet : Type` -- the set of satisfying assignments of a CNF.
    #[cfg(test)]
    fn register_entropy_clause_quality_satisfying_set_type(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(self, &ns("SatisfyingSet"), c.type0.clone())
    }

    /// `RealNonneg : Type` -- non-negative real values used for entropy.
    #[cfg(test)]
    fn register_entropy_clause_quality_real_nonneg(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(self, &ns("RealNonneg"), c.type0.clone())
    }

    // ====================================================================
    // Operations
    // ====================================================================

    /// `num_variables : CNFFormula -> Nat`
    #[cfg(test)]
    fn register_entropy_clause_quality_num_variables(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(
            self,
            &ns("num_variables"),
            Expr::pi(BinderInfo::Default, c.cnf_formula.clone(), c.nat.clone()),
        )
    }

    /// `satisfying_set : CNFFormula -> SatisfyingSet`
    #[cfg(test)]
    fn register_entropy_clause_quality_satisfying_set(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(
            self,
            &ns("satisfying_set"),
            Expr::pi(
                BinderInfo::Default,
                c.cnf_formula.clone(),
                c.satisfying_set.clone(),
            ),
        )
    }

    /// `sat_count : SatisfyingSet -> Nat`
    #[cfg(test)]
    fn register_entropy_clause_quality_sat_count(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(
            self,
            &ns("sat_count"),
            Expr::pi(BinderInfo::Default, c.satisfying_set.clone(), c.nat.clone()),
        )
    }

    /// `solution_entropy : CNFFormula -> RealNonneg`
    ///
    /// Intended semantics: `H(F) = log(|Sat(F)|)`.
    #[cfg(test)]
    fn register_entropy_clause_quality_solution_entropy(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        add_axiom(
            self,
            &ns("solution_entropy"),
            Expr::pi(
                BinderInfo::Default,
                c.cnf_formula.clone(),
                c.real_nonneg.clone(),
            ),
        )
    }

    /// `information_gain : CNFClause -> CNFFormula -> RealNonneg`
    ///
    /// Intended semantics: `I(C|F) = H(F) - H(F AND C)`.
    #[cfg(test)]
    fn register_entropy_clause_quality_information_gain(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cl_id, _) = b.fresh_local(c.cnf_clause.clone());
            let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
            let e = b.mk_pi(
                f_id,
                BinderInfo::Default,
                c.cnf_formula.clone(),
                c.real_nonneg.clone(),
            );
            let e = b.mk_pi(cl_id, BinderInfo::Default, c.cnf_clause.clone(), e);
            b.finish(e)
        };
        add_axiom(self, &ns("information_gain"), ty)
    }

    /// `formula_union : CNFFormula -> CNFFormula -> CNFFormula`
    #[cfg(test)]
    fn register_entropy_clause_quality_formula_union(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
            let (g_id, _) = b.fresh_local(c.cnf_formula.clone());
            let e = b.mk_pi(
                g_id,
                BinderInfo::Default,
                c.cnf_formula.clone(),
                c.cnf_formula.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            b.finish(e)
        };
        add_axiom(self, &ns("formula_union"), ty)
    }

    /// `formula_add_clause : CNFFormula -> CNFClause -> CNFFormula`
    ///
    /// Intended semantics: `F AND C`.
    #[cfg(test)]
    fn register_entropy_clause_quality_formula_add_clause(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
            let (cl_id, _) = b.fresh_local(c.cnf_clause.clone());
            let e = b.mk_pi(
                cl_id,
                BinderInfo::Default,
                c.cnf_clause.clone(),
                c.cnf_formula.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf_formula.clone(), e);
            b.finish(e)
        };
        add_axiom(self, &ns("formula_add_clause"), ty)
    }

    /// `formula_entails_clause : CNFFormula -> CNFClause -> Prop`
    ///
    /// Intended semantics: `F |= C`.
    #[cfg(test)]
    fn register_entropy_clause_quality_formula_entails_clause(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let ty = {
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
        add_axiom(self, &ns("formula_entails_clause"), ty)
    }

    /// `assignment_satisfies_formula : AssignmentSpace -> CNFFormula -> Prop`
    #[cfg(test)]
    fn register_entropy_clause_quality_assignment_satisfies_formula(
        &mut self,
        c: &EntropyClauseQualityConsts,
    ) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.assignment_space.clone());
            let (f_id, _) = b.fresh_local(c.cnf_formula.clone());
            let e = b.mk_pi(
                f_id,
                BinderInfo::Default,
                c.cnf_formula.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment_space.clone(), e);
            b.finish(e)
        };
        add_axiom(self, &ns("assignment_satisfies_formula"), ty)
    }
}
