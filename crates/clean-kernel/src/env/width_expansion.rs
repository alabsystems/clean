// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for the Ben-Sasson-Wigderson width-expansion
//! theorem formalization.
//!
//! Registers the foundational types and definitions needed to state:
//! - resolution width lower bounds from CNF incidence-graph expansion
//! - monotonicity of expansion under partial assignments
//! - random-restriction width lower bounds
//! - the Ben-Sasson-Wigderson size-width relationship
//! - a Cheeger-style spectral upper bound for boundary expansion
//!
//! Type and operation definitions live here; theorem registrations are in
//! `width_expansion_theorems.rs`.
//!
//! Reference: Ben-Sasson & Wigderson, "Short Proofs are Narrow -- Resolution
//! Made Simple", JACM 2001.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all width-expansion declarations.
pub(super) struct WidthExpansionConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ResComplexity.CNF : Type (from resolution_complexity)
    pub(super) cnf: Expr,
    /// WidthExpansion.IncidenceGraph : Type
    pub(super) incidence_graph: Expr,
    /// WidthExpansion.VariableSet : Type
    pub(super) variable_set: Expr,
    /// WidthExpansion.ClauseSet : Type
    pub(super) clause_set: Expr,
    /// WidthExpansion.ResolutionProof : Type
    pub(super) resolution_proof: Expr,
    /// WidthExpansion.PartialAssignment : Type
    pub(super) partial_assignment: Expr,
}

impl WidthExpansionConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            cnf: Expr::const_(Name::from_string("ResComplexity.CNF"), vec![]),
            incidence_graph: Expr::const_(
                Name::from_string("WidthExpansion.IncidenceGraph"),
                vec![],
            ),
            variable_set: Expr::const_(Name::from_string("WidthExpansion.VariableSet"), vec![]),
            clause_set: Expr::const_(Name::from_string("WidthExpansion.ClauseSet"), vec![]),
            resolution_proof: Expr::const_(
                Name::from_string("WidthExpansion.ResolutionProof"),
                vec![],
            ),
            partial_assignment: Expr::const_(
                Name::from_string("WidthExpansion.PartialAssignment"),
                vec![],
            ),
        }
    }
}

/// Register an axiom with idempotency check.
pub(super) fn add_width_expansion_axiom(
    env: &mut Environment,
    name: &str,
    type_: Expr,
) -> Result<(), EnvError> {
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
    /// Initialize width-expansion declarations for general resolution proofs.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_resolution_complexity()`.
    pub(crate) fn init_width_expansion(&mut self) -> Result<(), EnvError> {
        if self.width_expansion_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_resolution_complexity()?;

        let c = WidthExpansionConsts::new();
        // Definitions
        self.register_incidence_graph_type(&c)?;
        self.register_variable_set_type(&c)?;
        self.register_clause_set_type(&c)?;
        self.register_incidence_graph(&c)?;
        self.register_variables(&c)?;
        self.register_clauses(&c)?;
        self.register_we_num_variables(&c)?;
        self.register_we_num_clauses(&c)?;
        self.register_neighborhood(&c)?;
        self.register_clause_neighborhood(&c)?;
        self.register_set_size_var(&c)?;
        self.register_set_size_clause(&c)?;
        self.register_boundary_expansion(&c)?;
        self.register_width_expansion_resolution_proof(&c)?;
        self.register_we_is_refutation(&c)?;
        self.register_proof_width(&c)?;
        self.register_partial_assignment(&c)?;
        self.register_restrict(&c)?;
        self.register_restriction_size(&c)?;
        self.register_we_initial_width(&c)?;
        self.register_spectral_gap(&c)?;
        // Theorems (in width_expansion_theorems.rs)
        self.register_width_expansion_helper(&c)?;
        self.register_width_expansion(&c)?;
        self.register_expansion_monotone_restriction_helper(&c)?;
        self.register_expansion_monotone_restriction(&c)?;
        self.register_width_random_restriction_helper(&c)?;
        self.register_width_random_restriction(&c)?;
        self.register_size_width_helper(&c)?;
        self.register_size_width_relationship(&c)?;
        self.register_cheeger_helper(&c)?;
        self.register_cheeger_inequality(&c)?;

        self.width_expansion_init = true;
        Ok(())
    }

    /// `WidthExpansion.IncidenceGraph : Type` -- the clause-variable incidence
    /// graph of a CNF formula.
    fn register_incidence_graph_type(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(self, "WidthExpansion.IncidenceGraph", c.type0.clone())
    }

    /// `WidthExpansion.VariableSet : Type` -- a set of propositional variables.
    fn register_variable_set_type(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(self, "WidthExpansion.VariableSet", c.type0.clone())
    }

    /// `WidthExpansion.ClauseSet : Type` -- a set of clauses.
    fn register_clause_set_type(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(self, "WidthExpansion.ClauseSet", c.type0.clone())
    }

    /// `WidthExpansion.incidence_graph :
    ///     ResComplexity.CNF -> WidthExpansion.IncidenceGraph`
    fn register_incidence_graph(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.incidence_graph",
            Expr::pi(
                BinderInfo::Default,
                c.cnf.clone(),
                c.incidence_graph.clone(),
            ),
        )
    }

    /// `WidthExpansion.variables : ResComplexity.CNF -> WidthExpansion.VariableSet`
    fn register_variables(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.variables",
            Expr::pi(BinderInfo::Default, c.cnf.clone(), c.variable_set.clone()),
        )
    }

    /// `WidthExpansion.clauses : ResComplexity.CNF -> WidthExpansion.ClauseSet`
    fn register_clauses(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.clauses",
            Expr::pi(BinderInfo::Default, c.cnf.clone(), c.clause_set.clone()),
        )
    }

    /// `WidthExpansion.num_variables : ResComplexity.CNF -> Nat`
    fn register_we_num_variables(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.num_variables",
            Expr::pi(BinderInfo::Default, c.cnf.clone(), c.nat.clone()),
        )
    }

    /// `WidthExpansion.num_clauses : ResComplexity.CNF -> Nat`
    fn register_we_num_clauses(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.num_clauses",
            Expr::pi(BinderInfo::Default, c.cnf.clone(), c.nat.clone()),
        )
    }

    /// `WidthExpansion.neighborhood :
    ///     WidthExpansion.IncidenceGraph ->
    ///     WidthExpansion.VariableSet ->
    ///     WidthExpansion.ClauseSet`
    fn register_neighborhood(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, _) = b.fresh_local(c.incidence_graph.clone());
            let (s_id, _) = b.fresh_local(c.variable_set.clone());
            let e = b.mk_pi(
                s_id,
                BinderInfo::Default,
                c.variable_set.clone(),
                c.clause_set.clone(),
            );
            let e = b.mk_pi(g_id, BinderInfo::Default, c.incidence_graph.clone(), e);
            b.finish(e)
        };
        add_width_expansion_axiom(self, "WidthExpansion.neighborhood", ty)
    }

    /// `WidthExpansion.clause_neighborhood :
    ///     WidthExpansion.IncidenceGraph ->
    ///     WidthExpansion.ClauseSet ->
    ///     WidthExpansion.VariableSet`
    fn register_clause_neighborhood(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, _) = b.fresh_local(c.incidence_graph.clone());
            let (cs_id, _) = b.fresh_local(c.clause_set.clone());
            let e = b.mk_pi(
                cs_id,
                BinderInfo::Default,
                c.clause_set.clone(),
                c.variable_set.clone(),
            );
            let e = b.mk_pi(g_id, BinderInfo::Default, c.incidence_graph.clone(), e);
            b.finish(e)
        };
        add_width_expansion_axiom(self, "WidthExpansion.clause_neighborhood", ty)
    }

    /// `WidthExpansion.set_size_var : WidthExpansion.VariableSet -> Nat`
    fn register_set_size_var(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.set_size_var",
            Expr::pi(BinderInfo::Default, c.variable_set.clone(), c.nat.clone()),
        )
    }

    /// `WidthExpansion.set_size_clause : WidthExpansion.ClauseSet -> Nat`
    fn register_set_size_clause(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.set_size_clause",
            Expr::pi(BinderInfo::Default, c.clause_set.clone(), c.nat.clone()),
        )
    }

    /// `WidthExpansion.boundary_expansion :
    ///     WidthExpansion.IncidenceGraph -> Nat`
    ///
    /// Abstracts the Ben-Sasson-Wigderson expansion parameter
    /// `h(F) = min |N(S)| / |S|` over `|S| <= n/2`, represented here as an
    /// opaque Nat-valued invariant of the incidence graph.
    fn register_boundary_expansion(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.boundary_expansion",
            Expr::pi(
                BinderInfo::Default,
                c.incidence_graph.clone(),
                c.nat.clone(),
            ),
        )
    }

    /// `WidthExpansion.ResolutionProof : Type` -- a general DAG-like
    /// resolution proof.
    fn register_width_expansion_resolution_proof(
        &mut self,
        c: &WidthExpansionConsts,
    ) -> Result<(), EnvError> {
        add_width_expansion_axiom(self, "WidthExpansion.ResolutionProof", c.type0.clone())
    }

    /// `WidthExpansion.is_refutation :
    ///     WidthExpansion.ResolutionProof -> ResComplexity.CNF -> Prop`
    fn register_we_is_refutation(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(c.resolution_proof.clone());
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), c.prop.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, c.resolution_proof.clone(), e);
            b.finish(e)
        };
        add_width_expansion_axiom(self, "WidthExpansion.is_refutation", ty)
    }

    /// `WidthExpansion.proof_width : WidthExpansion.ResolutionProof -> Nat`
    fn register_proof_width(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.proof_width",
            Expr::pi(
                BinderInfo::Default,
                c.resolution_proof.clone(),
                c.nat.clone(),
            ),
        )
    }

    /// `WidthExpansion.PartialAssignment : Type` -- a restriction / partial
    /// assignment.
    fn register_partial_assignment(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(self, "WidthExpansion.PartialAssignment", c.type0.clone())
    }

    /// `WidthExpansion.restrict :
    ///     ResComplexity.CNF ->
    ///     WidthExpansion.PartialAssignment ->
    ///     ResComplexity.CNF`
    fn register_restrict(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.cnf.clone());
            let (rho_id, _) = b.fresh_local(c.partial_assignment.clone());
            let e = b.mk_pi(
                rho_id,
                BinderInfo::Default,
                c.partial_assignment.clone(),
                c.cnf.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, c.cnf.clone(), e);
            b.finish(e)
        };
        add_width_expansion_axiom(self, "WidthExpansion.restrict", ty)
    }

    /// `WidthExpansion.restriction_size :
    ///     WidthExpansion.PartialAssignment -> Nat`
    fn register_restriction_size(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.restriction_size",
            Expr::pi(
                BinderInfo::Default,
                c.partial_assignment.clone(),
                c.nat.clone(),
            ),
        )
    }

    /// `WidthExpansion.initial_width : ResComplexity.CNF -> Nat`
    fn register_we_initial_width(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.initial_width",
            Expr::pi(BinderInfo::Default, c.cnf.clone(), c.nat.clone()),
        )
    }

    /// `WidthExpansion.spectral_gap : WidthExpansion.IncidenceGraph -> Nat`
    ///
    /// An abstract spectral expansion parameter for the incidence graph,
    /// included to state a Cheeger-style comparison theorem.
    fn register_spectral_gap(&mut self, c: &WidthExpansionConsts) -> Result<(), EnvError> {
        add_width_expansion_axiom(
            self,
            "WidthExpansion.spectral_gap",
            Expr::pi(
                BinderInfo::Default,
                c.incidence_graph.clone(),
                c.nat.clone(),
            ),
        )
    }
}
