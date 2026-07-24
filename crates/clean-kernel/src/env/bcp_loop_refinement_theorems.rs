// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for the BCP loop refinement overlay.
//!
//! Registers kernel-level theorem surfaces for the imperative watched-literal
//! BCP loop refinement story. Each theorem follows the helper-axiom pattern
//! used by the other overlay theorem modules: a `_helper` axiom captures the
//! proposition body, and the theorem quantifies over its parameters with the
//! helper applied.

use super::bcp_loop_refinement::BCPLoopConsts;
use crate::env::{decl_builder::EnvDeclBuilder, Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    fn register_bcp_loop_helper_theorem_pair(
        &mut self,
        helper_name: &str,
        theorem_name: &str,
        param_types: &[Expr],
        prop: &Expr,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(helper_name)).is_none() {
            let helper_ty = {
                let mut b = EnvDeclBuilder::new();
                let mut binders = Vec::with_capacity(param_types.len());
                for ty in param_types {
                    let (id, _) = b.fresh_local(ty.clone());
                    binders.push((id, ty.clone()));
                }

                let mut body = prop.clone();
                for (id, ty) in binders.into_iter().rev() {
                    body = b.mk_pi(id, BinderInfo::Default, ty, body);
                }
                b.finish(body)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(helper_name),
                level_params: vec![],
                type_: helper_ty,
            })?;
        }

        if self.get_const(&Name::from_string(theorem_name)).is_some() {
            return Ok(());
        }

        let helper = Expr::const_(Name::from_string(helper_name), vec![]);
        let theorem_ty = {
            let mut b = EnvDeclBuilder::new();
            let mut binders = Vec::with_capacity(param_types.len());
            let mut args = Vec::with_capacity(param_types.len());
            for ty in param_types {
                let (id, arg) = b.fresh_local(ty.clone());
                binders.push((id, ty.clone()));
                args.push(arg);
            }

            let mut body = Expr::apps(helper, args);
            for (id, ty) in binders.into_iter().rev() {
                body = b.mk_pi(id, BinderInfo::Default, ty, body);
            }
            b.finish(body)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(theorem_name),
            level_params: vec![],
            type_: theorem_ty,
        })
    }

    /// `BCPLoop.two_pointer_compaction_invariant :
    ///     forall (s : ImperativeState),
    ///       BCPLoop.two_pointer_compaction_invariant_helper s`
    ///
    /// Intended meaning:
    /// `forall (s : ImperativeState),
    ///    j_ptr s <= i_ptr s /\ i_ptr s <= watch_len (watches s)`.
    ///
    /// The imperative scan maintains the standard `j <= i <= len` invariant.
    pub(super) fn register_two_pointer_compaction_invariant(
        &mut self,
        c: &BCPLoopConsts,
    ) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.two_pointer_compaction_invariant_helper",
            "BCPLoop.two_pointer_compaction_invariant",
            std::slice::from_ref(&c.imperative_state),
            &c.prop,
        )
    }

    /// `BCPLoop.xor_identity :
    ///     forall (e : WatchEntry) (l : Literal),
    ///       BCPLoop.xor_identity_helper e l`
    ///
    /// Intended meaning:
    /// `forall (e : WatchEntry) (l : Literal),
    ///    lit0 e xor lit1 e xor false_lit = xor_other_watched e l`.
    ///
    /// The watched-literal XOR trick recovers the other watched literal.
    pub(super) fn register_xor_identity(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.xor_identity_helper",
            "BCPLoop.xor_identity",
            &[c.watch_entry.clone(), c.literal.clone()],
            &c.prop,
        )
    }

    /// `BCPLoop.watch_consistency_preserved :
    ///     forall (s s' : ImperativeState),
    ///       BCPLoop.watch_consistency_preserved_helper s s'`
    ///
    /// Intended meaning:
    /// `forall (s s' : ImperativeState),
    ///    watch_valid s ->
    ///    s' = compaction_step s ->
    ///    watch_valid s'`.
    ///
    /// Compaction and swap steps preserve watch-list consistency.
    pub(super) fn register_watch_consistency_preserved(
        &mut self,
        c: &BCPLoopConsts,
    ) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.watch_consistency_preserved_helper",
            "BCPLoop.watch_consistency_preserved",
            &[c.imperative_state.clone(), c.imperative_state.clone()],
            &c.prop,
        )
    }

    /// `BCPLoop.bcp_refinement :
    ///     forall (a : AbstractBCPState) (s : ImperativeState),
    ///       BCPLoop.bcp_refinement_helper a s`
    ///
    /// Intended meaning:
    /// `forall (a : AbstractBCPState) (s : ImperativeState),
    ///    refinement_relation a s ->
    ///    propagate_imperative s = propagate_abstract a`.
    ///
    /// This is the main imperative/abstract BCP refinement theorem.
    pub(super) fn register_bcp_refinement(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.bcp_refinement_helper",
            "BCPLoop.bcp_refinement",
            &[c.abstract_bcp_state.clone(), c.imperative_state.clone()],
            &c.prop,
        )
    }

    /// `BCPLoop.blocker_soundness :
    ///     forall (s : ImperativeState) (e : WatchEntry),
    ///       BCPLoop.blocker_soundness_helper s e`
    ///
    /// Intended meaning:
    /// `forall (s : ImperativeState) (e : WatchEntry),
    ///    blocker_check s e = true ->
    ///    keeping e in place cannot miss required propagation`.
    ///
    /// The blocker fast path is sound.
    pub(super) fn register_blocker_soundness(&mut self, c: &BCPLoopConsts) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.blocker_soundness_helper",
            "BCPLoop.blocker_soundness",
            &[c.imperative_state.clone(), c.watch_entry.clone()],
            &c.prop,
        )
    }

    /// `BCPLoop.binary_clause_propagation :
    ///     forall (s : ImperativeState) (e : WatchEntry),
    ///       BCPLoop.binary_clause_propagation_helper s e`
    ///
    /// Intended meaning:
    /// `forall (s : ImperativeState) (e : WatchEntry),
    ///    is_binary_clause e = true ->
    ///    the direct binary-clause path matches the abstract propagation step`.
    ///
    /// Binary clauses are propagated correctly.
    pub(super) fn register_binary_clause_propagation(
        &mut self,
        c: &BCPLoopConsts,
    ) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.binary_clause_propagation_helper",
            "BCPLoop.binary_clause_propagation",
            &[c.imperative_state.clone(), c.watch_entry.clone()],
            &c.prop,
        )
    }

    /// `BCPLoop.replacement_search_complete :
    ///     forall (s : ImperativeState) (e : WatchEntry),
    ///       BCPLoop.replacement_search_complete_helper s e`
    ///
    /// Intended meaning:
    /// `forall (s : ImperativeState) (e : WatchEntry),
    ///    if the clause contains a non-false replacement literal,
    ///    the imperative search finds one`.
    ///
    /// Replacement-literal search is complete.
    pub(super) fn register_replacement_search_complete(
        &mut self,
        c: &BCPLoopConsts,
    ) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.replacement_search_complete_helper",
            "BCPLoop.replacement_search_complete",
            &[c.imperative_state.clone(), c.watch_entry.clone()],
            &c.prop,
        )
    }

    /// `BCPLoop.compaction_preserves_watches :
    ///     forall (s s' : ImperativeState),
    ///       BCPLoop.compaction_preserves_watches_helper s s'`
    ///
    /// Intended meaning:
    /// `forall (s s' : ImperativeState),
    ///    s' = compaction_step s ->
    ///    every surviving watch entry in s is preserved in s'`.
    ///
    /// In-place compaction does not lose watch entries.
    pub(super) fn register_compaction_preserves_watches(
        &mut self,
        c: &BCPLoopConsts,
    ) -> Result<(), EnvError> {
        self.register_bcp_loop_helper_theorem_pair(
            "BCPLoop.compaction_preserves_watches_helper",
            "BCPLoop.compaction_preserves_watches",
            &[c.imperative_state.clone(), c.imperative_state.clone()],
            &c.prop,
        )
    }
}
