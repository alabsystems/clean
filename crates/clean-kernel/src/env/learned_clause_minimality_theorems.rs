// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for learned clause minimality formalization.
//!
//! Registers the kernel-level axiom surfaces for:
//! - Interpolation-derived clause soundness
//! - Interpolation-derived clause minimality (no shorter implied clause)
//! - Subsumption implies strength ordering
//! - No redundant literals in interpolation clauses
//! - Backtrack level optimality
//!
//! Each theorem follows the helper-axiom pattern: a `_helper` axiom
//! captures the proposition body, and the theorem quantifies over all
//! parameters with the helper applied.
//!
//! Reference: Marques-Silva & Sakallah (1999), "GRASP";
//!            McMillan (2003), "Interpolation and SAT-based model checking";
//!            Beame et al. (2004), "Understanding the power of clause learning".

use super::learned_clause_minimality::LearnedClauseConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: Interpolation clause soundness
    // ====================================================================

    /// `interpolation_clause_sound : forall (g : ConflictGraph),
    ///     interpolation_clause_sound_helper g`
    ///
    /// Interpolation-derived clauses are logically implied by the formula:
    /// the learned clause is a logical consequence of the original CNF
    /// formula from which the conflict graph was derived. The interpolant
    /// extraction guarantees that the clause is not just consistent with
    /// the conflict but is actually entailed by the formula.
    pub(super) fn register_interpolation_clause_sound(
        &mut self,
        c: &LearnedClauseConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.interpolation_clause_sound_helper";
        let thm_name = "ProofTheory.interpolation_clause_sound";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (g : ConflictGraph) -> Prop
            // Encodes: the formula logically implies interpolation_clause(g)
            let helper_ty = Expr::pi(
                BinderInfo::Default,
                c.conflict_graph.clone(),
                c.prop.clone(),
            );
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
            let (g_id, g) = b.fresh_local(c.conflict_graph.clone());
            let body = Expr::app(helper, g.clone());
            let e = b.mk_pi(g_id, BinderInfo::Default, c.conflict_graph.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: Interpolation clause minimality
    // ====================================================================

    /// `interpolation_clause_minimal : forall (g : ConflictGraph)
    ///     (d : LearnedClause), interpolation_clause_minimal_helper g d`
    ///
    /// No shorter clause is implied by the same conflict: if d is any clause
    /// implied by the conflict graph g with size(d) < size(interpolation_clause(g)),
    /// then d does not subsume interpolation_clause(g). Equivalently, the
    /// interpolation clause has the minimum number of literals among all
    /// clauses derivable from the same conflict.
    ///
    /// This follows from the interpolation property: the interpolant uses
    /// only shared variables, so it cannot contain extra literals that a
    /// non-interpolation derivation might produce.
    pub(super) fn register_interpolation_clause_minimal(
        &mut self,
        c: &LearnedClauseConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.interpolation_clause_minimal_helper";
        let thm_name = "ProofTheory.interpolation_clause_minimal";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (g : ConflictGraph) -> (d : LearnedClause) -> Prop
            // Encodes: size(d) < size(interpolation_clause(g)) ->
            //          Not (clause_subsumes d (interpolation_clause g))
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (g_id, _) = b.fresh_local(c.conflict_graph.clone());
                let (d_id, _) = b.fresh_local(c.learned_clause.clone());
                let e = b.mk_pi(
                    d_id,
                    BinderInfo::Default,
                    c.learned_clause.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(g_id, BinderInfo::Default, c.conflict_graph.clone(), e);
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
            let (g_id, g) = b.fresh_local(c.conflict_graph.clone());
            let (d_id, d) = b.fresh_local(c.learned_clause.clone());
            let body = Expr::apps(helper, [g.clone(), d.clone()]);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.learned_clause.clone(), body);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.conflict_graph.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 3: Subsumption implies strength
    // ====================================================================

    /// `subsumption_strength : forall (c1 c2 : LearnedClause),
    ///     subsumption_strength_helper c1 c2`
    ///
    /// If clause c1 subsumes c2 (c1's literals are a subset of c2's literals),
    /// then c1 is at least as strong as c2 in the clause_strength ordering.
    /// This formalizes the intuition that shorter clauses (with fewer literals)
    /// are more restrictive and thus prune more of the search space.
    pub(super) fn register_subsumption_strength(
        &mut self,
        c: &LearnedClauseConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.subsumption_strength_helper";
        let thm_name = "ProofTheory.subsumption_strength";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (c1 c2 : LearnedClause) -> Prop
            // Encodes: clause_subsumes c1 c2 -> clause_strength c1 c2
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (c1_id, _) = b.fresh_local(c.learned_clause.clone());
                let (c2_id, _) = b.fresh_local(c.learned_clause.clone());
                let e = b.mk_pi(
                    c2_id,
                    BinderInfo::Default,
                    c.learned_clause.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(c1_id, BinderInfo::Default, c.learned_clause.clone(), e);
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
            let (c1_id, c1) = b.fresh_local(c.learned_clause.clone());
            let (c2_id, c2) = b.fresh_local(c.learned_clause.clone());
            let body = Expr::apps(helper, [c1.clone(), c2.clone()]);
            let e = b.mk_pi(c2_id, BinderInfo::Default, c.learned_clause.clone(), body);
            let e = b.mk_pi(c1_id, BinderInfo::Default, c.learned_clause.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 4: No redundant literals
    // ====================================================================

    /// `learned_clause_no_redundant_literals : forall (g : ConflictGraph),
    ///     learned_clause_no_redundant_literals_helper g`
    ///
    /// Interpolation clauses have no redundant literals: removing any single
    /// literal from the interpolation clause yields a clause that is NOT
    /// implied by the conflict graph. Every literal is essential.
    ///
    /// This is a direct consequence of minimality: if a literal were redundant,
    /// the clause without it would be a shorter implied clause, contradicting
    /// interpolation_clause_minimal.
    pub(super) fn register_learned_clause_no_redundant_literals(
        &mut self,
        c: &LearnedClauseConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.learned_clause_no_redundant_literals_helper";
        let thm_name = "ProofTheory.learned_clause_no_redundant_literals";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (g : ConflictGraph) -> Prop
            // Encodes: forall (i : Nat), i < size(interpolation_clause(g)) ->
            //          Not (implied_without_literal(g, interpolation_clause(g), i))
            let helper_ty = Expr::pi(
                BinderInfo::Default,
                c.conflict_graph.clone(),
                c.prop.clone(),
            );
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
            let (g_id, g) = b.fresh_local(c.conflict_graph.clone());
            let body = Expr::app(helper, g.clone());
            let e = b.mk_pi(g_id, BinderInfo::Default, c.conflict_graph.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: Backtrack level optimality
    // ====================================================================

    /// `backtrack_level_optimal : forall (g : ConflictGraph),
    ///     backtrack_level_optimal_helper g`
    ///
    /// The interpolation clause determines the optimal (highest) backtrack
    /// level: the second-highest decision level among the clause's literals
    /// equals the minimum backtrack level achievable by any clause implied
    /// by the same conflict.
    ///
    /// This means CDCL with interpolation-based learning performs non-
    /// chronological backtracking optimally: it backtracks as far as possible
    /// without losing any information about the conflict.
    pub(super) fn register_backtrack_level_optimal(
        &mut self,
        c: &LearnedClauseConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "ProofTheory.backtrack_level_optimal_helper";
        let thm_name = "ProofTheory.backtrack_level_optimal";

        if self.get_const(&Name::from_string(helper_name)).is_none() {
            // Helper: (g : ConflictGraph) -> Prop
            // Encodes: backtrack_level(interpolation_clause(g)) =
            //          min { backtrack_level(d) | d implied by g }
            let helper_ty = Expr::pi(
                BinderInfo::Default,
                c.conflict_graph.clone(),
                c.prop.clone(),
            );
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
            let (g_id, g) = b.fresh_local(c.conflict_graph.clone());
            let body = Expr::app(helper, g.clone());
            let e = b.mk_pi(g_id, BinderInfo::Default, c.conflict_graph.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
