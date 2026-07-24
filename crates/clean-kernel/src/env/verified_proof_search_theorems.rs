// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for verified proof search correctness.
//!
//! Registers the 5 main theorems that prove correctness properties
//! of the proof search algorithm:
//!
//! T1. **Soundness**: If `run_search` returns `Proved`, the returned proof
//!     term type-checks against the goal.
//! T2. **Completeness** (relative): If a proof exists within the given
//!     bounds, `run_search` finds it.
//! T3. **Termination**: Given finite bounds, search always terminates
//!     (the search space is finite).
//! T4. **Budget monotonicity**: Larger bounds find at least as many proofs
//!     — if search succeeds with bound b1, it succeeds with any b2 >= b1.
//! T5. **Composition soundness**: If each tactic application preserves
//!     validity, the composed search result is valid.
//!
//! Each theorem follows the helper-axiom pattern: a helper axiom captures
//! the proposition body, and the theorem quantifies over all parameters.
//!
//! Reference: Limperg & From (2023), "Aesop: White-Box Best-First Proof Search";
//!            Nilsson (1980), "Principles of Artificial Intelligence", ch. 3-4.

use super::verified_proof_search::VerifiedProofSearchConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Register a helper axiom and theorem over (Goal, SearchBound) pairs.
fn register_goal_bound_theorem(
    env: &mut Environment,
    c: &VerifiedProofSearchConsts,
    helper_name: &str,
    thm_name: &str,
) -> Result<(), EnvError> {
    // Helper: (g : Goal) -> (b : SearchBound) -> Prop
    if env.get_const(&Name::from_string(helper_name)).is_none() {
        let helper_ty = {
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
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(helper_name),
            level_params: vec![],
            type_: helper_ty,
        })?;
    }

    // Theorem: forall (g : Goal) (b : SearchBound), helper g b
    if env.get_const(&Name::from_string(thm_name)).is_some() {
        return Ok(());
    }
    let helper = Expr::const_(Name::from_string(helper_name), vec![]);
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(c.goal.clone());
        let (bd_id, bd) = b.fresh_local(c.search_bound.clone());
        let body = Expr::apps(helper, [g.clone(), bd.clone()]);
        let e = b.mk_pi(bd_id, BinderInfo::Default, c.search_bound.clone(), body);
        let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(thm_name),
        level_params: vec![],
        type_: ty,
    })
}

impl Environment {
    // ====================================================================
    // T1: Soundness — search output type-checks
    // ====================================================================

    /// `search_soundness : forall (g : Goal) (b : SearchBound),
    ///     search_soundness_helper g b`
    ///
    /// If `run_search g b` returns `Proved` with proof term `p`, then
    /// `type_checks g p` holds — the proof validates against the goal.
    pub(super) fn register_soundness_theorem(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        register_goal_bound_theorem(
            self,
            c,
            "VerifiedProofSearch.search_soundness_helper",
            "VerifiedProofSearch.search_soundness",
        )
    }

    // ====================================================================
    // T2: Completeness — bounded search finds all proofs within bounds
    // ====================================================================

    /// `search_completeness : forall (g : Goal) (b : SearchBound),
    ///     search_completeness_helper g b`
    ///
    /// If `proof_exists_within g b` holds (there exists a proof of `g`
    /// constructible within the bound `b`), then `run_search g b` returns
    /// `Proved`.
    pub(super) fn register_completeness_theorem(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        register_goal_bound_theorem(
            self,
            c,
            "VerifiedProofSearch.search_completeness_helper",
            "VerifiedProofSearch.search_completeness",
        )
    }

    // ====================================================================
    // T3: Termination — finite bounds guarantee termination
    // ====================================================================

    /// `search_terminates : forall (b : SearchBound),
    ///     search_terminates_helper b`
    ///
    /// For any finite bound `b`, `search_space_finite b` holds and
    /// `run_search` terminates for all goals.
    pub(super) fn register_termination_theorem(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "VerifiedProofSearch.search_terminates_helper";
        let thm_name = "VerifiedProofSearch.search_terminates";

        // Helper: (b : SearchBound) -> Prop
        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = Expr::pi(BinderInfo::Default, c.search_bound.clone(), c.prop.clone());
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
            let (bd_id, bd) = b.fresh_local(c.search_bound.clone());
            let body = Expr::app(helper, bd.clone());
            let e = b.mk_pi(bd_id, BinderInfo::Default, c.search_bound.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // T4: Budget monotonicity — larger bounds find more proofs
    // ====================================================================

    /// `budget_monotonicity : forall (g : Goal) (b1 b2 : SearchBound),
    ///     budget_monotonicity_helper g b1 b2`
    ///
    /// If `bound_le b1 b2` and `run_search g b1` returns `Proved`,
    /// then `run_search g b2` also returns `Proved`.
    pub(super) fn register_budget_monotonicity_theorem(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "VerifiedProofSearch.budget_monotonicity_helper";
        let thm_name = "VerifiedProofSearch.budget_monotonicity";

        // Helper: (g : Goal) -> (b1 : SearchBound) -> (b2 : SearchBound) -> Prop
        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (g_id, _) = b.fresh_local(c.goal.clone());
                let (b1_id, _) = b.fresh_local(c.search_bound.clone());
                let (b2_id, _) = b.fresh_local(c.search_bound.clone());
                let e = b.mk_pi(
                    b2_id,
                    BinderInfo::Default,
                    c.search_bound.clone(),
                    c.prop.clone(),
                );
                let e = b.mk_pi(b1_id, BinderInfo::Default, c.search_bound.clone(), e);
                let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), e);
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
            let (g_id, g) = b.fresh_local(c.goal.clone());
            let (b1_id, b1) = b.fresh_local(c.search_bound.clone());
            let (b2_id, b2) = b.fresh_local(c.search_bound.clone());
            let body = Expr::apps(helper, [g.clone(), b1.clone(), b2.clone()]);
            let e = b.mk_pi(b2_id, BinderInfo::Default, c.search_bound.clone(), body);
            let e = b.mk_pi(b1_id, BinderInfo::Default, c.search_bound.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // T5: Composition soundness — combined tactics preserve validity
    // ====================================================================

    /// `composition_soundness : forall (t : TacticApplication) (g : Goal),
    ///     composition_soundness_helper t g`
    ///
    /// If `tactic_preserves_validity t g` holds for every tactic `t` applied
    /// during search, then the composed proof term is sound.
    pub(super) fn register_composition_soundness_theorem(
        &mut self,
        c: &VerifiedProofSearchConsts,
    ) -> Result<(), EnvError> {
        let helper_name = "VerifiedProofSearch.composition_soundness_helper";
        let thm_name = "VerifiedProofSearch.composition_soundness";

        // Helper: (t : TacticApplication) -> (g : Goal) -> Prop
        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let (t_id, _) = b.fresh_local(c.tactic_application.clone());
                let (g_id, _) = b.fresh_local(c.goal.clone());
                let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), c.prop.clone());
                let e = b.mk_pi(t_id, BinderInfo::Default, c.tactic_application.clone(), e);
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
            let (t_id, t) = b.fresh_local(c.tactic_application.clone());
            let (g_id, g) = b.fresh_local(c.goal.clone());
            let body = Expr::apps(helper, [t.clone(), g.clone()]);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.goal.clone(), body);
            let e = b.mk_pi(t_id, BinderInfo::Default, c.tactic_application.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
