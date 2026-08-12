// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for learned clause minimality formalization.
//!
//! Registers the foundational types and definitions needed to state that
//! interpolation-based learned clauses are minimal: no shorter clause is
//! implied by the same conflict, and no literal is redundant.
//!
//! In CDCL SAT solving, conflict analysis produces learned clauses that
//! prune the search space. Craig interpolation provides a systematic way
//! to derive these clauses from the implication graph, yielding clauses
//! that are provably minimal in two senses:
//!
//! 1. **Subsumption minimality**: no proper subset of the clause is implied
//!    by the same conflict (no redundant literals).
//! 2. **Backtrack optimality**: the clause determines the optimal backtrack
//!    level, i.e., the highest decision level that can be undone.
//!
//! Type and operation definitions live here; theorem registrations are in
//! `learned_clause_minimality_theorems.rs`.
//!
//! Reference: Marques-Silva & Sakallah (1999), "GRASP: A search algorithm
//!            for propositional satisfiability";
//!            McMillan (2003), "Interpolation and SAT-based model checking";
//!            Beame et al. (2004), "Understanding the power of clause learning".

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

/// Shared constants used across all learned clause minimality declarations.
#[cfg(test)]
pub(super) struct LearnedClauseConsts {
    pub(super) nat: Expr,
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ProofTheory.PropFormula : Type (reuse from craig_interpolation)
    pub(super) prop_formula: Expr,
    /// ProofTheory.LearnedClause : Type
    pub(super) learned_clause: Expr,
    /// ProofTheory.ConflictGraph : Type
    pub(super) conflict_graph: Expr,
}

#[cfg(test)]
impl LearnedClauseConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop_formula: Expr::const_(Name::from_string("ProofTheory.PropFormula"), vec![]),
            learned_clause: Expr::const_(Name::from_string("ProofTheory.LearnedClause"), vec![]),
            conflict_graph: Expr::const_(Name::from_string("ProofTheory.ConflictGraph"), vec![]),
        }
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize learned clause minimality declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_craig_interpolation()`.
    #[cfg(test)]
    pub(crate) fn init_learned_clause_minimality(&mut self) -> Result<(), EnvError> {
        if self.learned_clause_minimality_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_craig_interpolation()?;

        let c = LearnedClauseConsts::new();
        self.register_learned_clause(&c)?;
        self.register_conflict_graph(&c)?;
        self.register_clause_strength(&c)?;
        self.register_interpolation_clause(&c)?;
        self.register_clause_subsumes(&c)?;
        // Theorem registrations (in learned_clause_minimality_theorems.rs)
        self.register_interpolation_clause_sound(&c)?;
        self.register_interpolation_clause_minimal(&c)?;
        self.register_subsumption_strength(&c)?;
        self.register_learned_clause_no_redundant_literals(&c)?;
        self.register_backtrack_level_optimal(&c)?;

        self.learned_clause_minimality_init = true;
        Ok(())
    }

    // ====================================================================
    // Definition 1: LearnedClause — clause derived during CDCL search
    // ====================================================================

    /// `LearnedClause : Type` — a clause derived during CDCL conflict analysis.
    ///
    /// Abstractly a set of literals. Registered as an opaque axiom type
    /// with constructors for building from literal lists and projecting
    /// the literal set and its size.
    #[cfg(test)]
    fn register_learned_clause(&mut self, c: &LearnedClauseConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.LearnedClause"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LearnedClause"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // literals : LearnedClause -> PropFormula (clause as disjunction)
        let literals_ty = Expr::pi(
            BinderInfo::Default,
            c.learned_clause.clone(),
            c.prop_formula.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LearnedClause.literals"),
            level_params: vec![],
            type_: literals_ty,
        })?;
        // size : LearnedClause -> Nat (number of literals)
        let size_ty = Expr::pi(BinderInfo::Default, c.learned_clause.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.LearnedClause.size"),
            level_params: vec![],
            type_: size_ty,
        })
    }

    // ====================================================================
    // Definition 2: clause_strength — partial order on clause strength
    // ====================================================================

    /// `clause_strength (c1 c2 : LearnedClause) : Prop`
    ///
    /// Partial order on clause informativeness: c1 is at least as strong
    /// as c2 if every assignment falsified by c1 is also falsified by c2.
    /// A stronger clause prunes more of the search space.
    #[cfg(test)]
    fn register_clause_strength(&mut self, c: &LearnedClauseConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.clause_strength"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
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
            name: Name::from_string("ProofTheory.clause_strength"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 3: interpolation_clause — clause via Craig interpolation
    // ====================================================================

    /// `interpolation_clause (g : ConflictGraph) : LearnedClause`
    ///
    /// Derives a learned clause from a conflict graph using Craig interpolation.
    /// The implication graph is partitioned into A (decisions + propagations
    /// at the conflict level) and B (earlier decisions), and the interpolant
    /// of this partition yields the learned clause.
    ///
    /// Reference: McMillan (2003), "Interpolation and SAT-based model checking".
    #[cfg(test)]
    fn register_interpolation_clause(&mut self, c: &LearnedClauseConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.interpolation_clause"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.conflict_graph.clone(),
            c.learned_clause.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.interpolation_clause"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 4: clause_subsumes — clause subsumption relation
    // ====================================================================

    /// `clause_subsumes (c1 c2 : LearnedClause) : Prop`
    ///
    /// Clause c1 subsumes c2 if the literal set of c1 is a subset of the
    /// literal set of c2. Subsumption implies that c1 is at least as strong
    /// as c2 (fewer literals = more restrictive = more pruning).
    #[cfg(test)]
    fn register_clause_subsumes(&mut self, c: &LearnedClauseConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.clause_subsumes"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
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
            name: Name::from_string("ProofTheory.clause_subsumes"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 5: ConflictGraph — implication graph from BCP
    // ====================================================================

    /// `ConflictGraph : Type` — implication graph recording BCP derivations.
    ///
    /// An abstract type representing the trail of decisions and unit
    /// propagations that led to a conflict in CDCL search. Contains:
    /// - Decision literals at each decision level
    /// - Propagation chains with reason clauses
    /// - The conflict clause that triggered analysis
    ///
    /// Projections:
    /// - `conflict_level : ConflictGraph -> Nat` — the decision level of the conflict
    /// - `num_literals : ConflictGraph -> Nat` — total literals in the trail
    #[cfg(test)]
    fn register_conflict_graph(&mut self, c: &LearnedClauseConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofTheory.ConflictGraph"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ConflictGraph"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;
        // conflict_level : ConflictGraph -> Nat
        let level_ty = Expr::pi(BinderInfo::Default, c.conflict_graph.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ConflictGraph.conflict_level"),
            level_params: vec![],
            type_: level_ty,
        })?;
        // num_literals : ConflictGraph -> Nat
        let nlits_ty = Expr::pi(BinderInfo::Default, c.conflict_graph.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofTheory.ConflictGraph.num_literals"),
            level_params: vec![],
            type_: nlits_ty,
        })
    }
}
