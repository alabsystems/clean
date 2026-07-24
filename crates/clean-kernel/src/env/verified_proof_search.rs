// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for verified proof search correctness.
//!
//! Registers the abstract types, operations, and predicates needed to
//! state and prove correctness of the proof search algorithm:
//!
//! 1. **Soundness**: If search returns a proof, the proof type-checks
//!    against the goal — composition of tactic applications is valid.
//! 2. **Completeness (relative)**: If a proof exists within the depth/width
//!    bounds, the search algorithm finds it.
//! 3. **Termination**: Given finite bounds, the search always terminates.
//!
//! Type and operation definitions live here; theorem registrations are in
//! `verified_proof_search_theorems.rs`.
//!
//! Reference: Lean 4 aesop tactic (Limperg & From, 2023),
//!            AND-OR tree search (Nilsson, 1980).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all verified proof search declarations.
pub(super) struct VerifiedProofSearchConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) goal: Expr,
    pub(super) proof_term: Expr,
    pub(super) search_bound: Expr,
    pub(super) tactic_application: Expr,
    pub(super) search_tree: Expr,
    pub(super) search_state: Expr,
    pub(super) search_result: Expr,
}

impl VerifiedProofSearchConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            goal: Expr::const_(Name::from_string("VerifiedProofSearch.Goal"), vec![]),
            proof_term: Expr::const_(Name::from_string("VerifiedProofSearch.ProofTerm"), vec![]),
            search_bound: Expr::const_(
                Name::from_string("VerifiedProofSearch.SearchBound"),
                vec![],
            ),
            tactic_application: Expr::const_(
                Name::from_string("VerifiedProofSearch.TacticApplication"),
                vec![],
            ),
            search_tree: Expr::const_(Name::from_string("VerifiedProofSearch.SearchTree"), vec![]),
            search_state: Expr::const_(
                Name::from_string("VerifiedProofSearch.SearchState"),
                vec![],
            ),
            search_result: Expr::const_(
                Name::from_string("VerifiedProofSearch.SearchResult"),
                vec![],
            ),
        }
    }
}

/// Register an axiom with idempotency check.
fn add_proof_search_axiom(env: &mut Environment, name: &str, type_: Expr) -> Result<(), EnvError> {
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
    /// Initialize verified proof search declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_verified_proof_search(&mut self) -> Result<(), EnvError> {
        if self.verified_proof_search_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;

        let c = VerifiedProofSearchConsts::new();

        // Types
        self.register_proof_search_types(&c)?;

        // Operations
        self.register_proof_search_operations(&c)?;

        // Predicates
        self.register_proof_search_predicates(&c)?;

        // Theorems (in verified_proof_search_theorems.rs)
        self.register_soundness_theorem(&c)?;
        self.register_completeness_theorem(&c)?;
        self.register_termination_theorem(&c)?;
        self.register_budget_monotonicity_theorem(&c)?;
        self.register_composition_soundness_theorem(&c)?;

        self.verified_proof_search_init = true;
        Ok(())
    }

    // ====================================================================
    // Types
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_proof_search_types(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        // Goal : Type 0
        add_proof_search_axiom(self, "VerifiedProofSearch.Goal", c.type0.clone())?;
        // Goal.target : Goal -> Type 0
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.Goal.target",
            Expr::pi(BinderInfo::Default, c.goal.clone(), c.type0.clone()),
        )?;
        // Goal.context : Goal -> Type 0
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.Goal.context",
            Expr::pi(BinderInfo::Default, c.goal.clone(), c.type0.clone()),
        )?;

        // ProofTerm : Type 0
        add_proof_search_axiom(self, "VerifiedProofSearch.ProofTerm", c.type0.clone())?;

        // SearchBound : Type 0
        add_proof_search_axiom(self, "VerifiedProofSearch.SearchBound", c.type0.clone())?;
        // SearchBound.max_depth : SearchBound -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchBound.max_depth",
            Expr::pi(BinderInfo::Default, c.search_bound.clone(), c.nat.clone()),
        )?;
        // SearchBound.max_width : SearchBound -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchBound.max_width",
            Expr::pi(BinderInfo::Default, c.search_bound.clone(), c.nat.clone()),
        )?;
        // SearchBound.max_nodes : SearchBound -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchBound.max_nodes",
            Expr::pi(BinderInfo::Default, c.search_bound.clone(), c.nat.clone()),
        )?;

        // TacticApplication : Type 0
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.TacticApplication",
            c.type0.clone(),
        )?;
        // TacticApplication.tactic_name : TacticApplication -> Type 0
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.TacticApplication.tactic_name",
            Expr::pi(
                BinderInfo::Default,
                c.tactic_application.clone(),
                c.type0.clone(),
            ),
        )?;
        // TacticApplication.produces_subgoals : TacticApplication -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.TacticApplication.produces_subgoals",
            Expr::pi(
                BinderInfo::Default,
                c.tactic_application.clone(),
                c.nat.clone(),
            ),
        )?;

        // SearchTree : Type 0
        add_proof_search_axiom(self, "VerifiedProofSearch.SearchTree", c.type0.clone())?;
        // SearchTree.root : SearchTree -> Goal
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchTree.root",
            Expr::pi(BinderInfo::Default, c.search_tree.clone(), c.goal.clone()),
        )?;
        // SearchTree.node_count : SearchTree -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchTree.node_count",
            Expr::pi(BinderInfo::Default, c.search_tree.clone(), c.nat.clone()),
        )?;
        // SearchTree.depth : SearchTree -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchTree.depth",
            Expr::pi(BinderInfo::Default, c.search_tree.clone(), c.nat.clone()),
        )?;

        // SearchState : Type 0
        add_proof_search_axiom(self, "VerifiedProofSearch.SearchState", c.type0.clone())?;
        // SearchState.frontier_size : SearchState -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchState.frontier_size",
            Expr::pi(BinderInfo::Default, c.search_state.clone(), c.nat.clone()),
        )?;
        // SearchState.explored_count : SearchState -> Nat
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchState.explored_count",
            Expr::pi(BinderInfo::Default, c.search_state.clone(), c.nat.clone()),
        )?;
        // SearchState.current_tree : SearchState -> SearchTree
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchState.current_tree",
            Expr::pi(
                BinderInfo::Default,
                c.search_state.clone(),
                c.search_tree.clone(),
            ),
        )?;

        // SearchResult : Type 0
        add_proof_search_axiom(self, "VerifiedProofSearch.SearchResult", c.type0.clone())?;
        // SearchResult.is_proved : SearchResult -> Bool
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchResult.is_proved",
            Expr::pi(
                BinderInfo::Default,
                c.search_result.clone(),
                c.bool_.clone(),
            ),
        )?;
        // SearchResult.is_exhausted : SearchResult -> Bool
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchResult.is_exhausted",
            Expr::pi(
                BinderInfo::Default,
                c.search_result.clone(),
                c.bool_.clone(),
            ),
        )?;
        // SearchResult.proof : SearchResult -> ProofTerm
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.SearchResult.proof",
            Expr::pi(
                BinderInfo::Default,
                c.search_result.clone(),
                c.proof_term.clone(),
            ),
        )
    }

    // ====================================================================
    // Operations
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_proof_search_operations(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        // search_step : SearchState -> SearchBound -> SearchState
        let search_step_ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.search_state.clone());
            let (bd_id, _) = b.fresh_local(c.search_bound.clone());
            let e = b.mk_pi(
                bd_id,
                BinderInfo::Default,
                c.search_bound.clone(),
                c.search_state.clone(),
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, c.search_state.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(self, "VerifiedProofSearch.search_step", search_step_ty)?;

        // apply_tactic : Goal -> TacticApplication -> SearchResult
        let apply_tactic_ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, _) = b.fresh_local(c.goal.clone());
            let (t_id, _) = b.fresh_local(c.tactic_application.clone());
            let e = b.mk_pi(
                t_id,
                BinderInfo::Default,
                c.tactic_application.clone(),
                c.search_result.clone(),
            );
            let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(self, "VerifiedProofSearch.apply_tactic", apply_tactic_ty)?;

        // run_search : Goal -> SearchBound -> SearchResult
        let run_search_ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, _) = b.fresh_local(c.goal.clone());
            let (bd_id, _) = b.fresh_local(c.search_bound.clone());
            let e = b.mk_pi(
                bd_id,
                BinderInfo::Default,
                c.search_bound.clone(),
                c.search_result.clone(),
            );
            let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(self, "VerifiedProofSearch.run_search", run_search_ty)
    }

    // ====================================================================
    // Predicates
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_proof_search_predicates(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        // type_checks : Goal -> ProofTerm -> Prop
        let type_checks_ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, _) = b.fresh_local(c.goal.clone());
            let (p_id, _) = b.fresh_local(c.proof_term.clone());
            let e = b.mk_pi(
                p_id,
                BinderInfo::Default,
                c.proof_term.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(self, "VerifiedProofSearch.type_checks", type_checks_ty)?;

        // within_bounds : SearchState -> SearchBound -> Prop
        let within_bounds_ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.search_state.clone());
            let (bd_id, _) = b.fresh_local(c.search_bound.clone());
            let e = b.mk_pi(
                bd_id,
                BinderInfo::Default,
                c.search_bound.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, c.search_state.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(self, "VerifiedProofSearch.within_bounds", within_bounds_ty)?;

        // proof_exists_within : Goal -> SearchBound -> Prop
        let proof_exists_ty = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, _) = b.fresh_local(c.goal.clone());
            let (bd_id, _) = b.fresh_local(c.search_bound.clone());
            let e = b.mk_pi(
                bd_id,
                BinderInfo::Default,
                c.search_bound.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.proof_exists_within",
            proof_exists_ty,
        )?;

        // search_space_finite : SearchBound -> Prop
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.search_space_finite",
            Expr::pi(BinderInfo::Default, c.search_bound.clone(), c.prop.clone()),
        )?;

        // bound_le : SearchBound -> SearchBound -> Prop
        let bound_le_ty = {
            let mut b = EnvDeclBuilder::new();
            let (b1_id, _) = b.fresh_local(c.search_bound.clone());
            let (b2_id, _) = b.fresh_local(c.search_bound.clone());
            let e = b.mk_pi(
                b2_id,
                BinderInfo::Default,
                c.search_bound.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(b1_id, BinderInfo::Default, c.search_bound.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(self, "VerifiedProofSearch.bound_le", bound_le_ty)?;

        // tactic_preserves_validity : TacticApplication -> Goal -> Prop
        let tactic_valid_ty = {
            let mut b = EnvDeclBuilder::new();
            let (t_id, _) = b.fresh_local(c.tactic_application.clone());
            let (g_id, _) = b.fresh_local(c.goal.clone());
            let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), c.prop.clone());
            let e = b.mk_pi(t_id, BinderInfo::Default, c.tactic_application.clone(), e);
            b.finish(e)
        };
        add_proof_search_axiom(
            self,
            "VerifiedProofSearch.tactic_preserves_validity",
            tactic_valid_ty,
        )
    }
}
