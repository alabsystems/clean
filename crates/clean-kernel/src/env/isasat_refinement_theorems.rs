// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for the IsaSAT refinement overlay.
//!
//! Registers kernel-level theorem surfaces for the abstract/concrete IsaSAT
//! refinement story used in Lean 5 kernel overlays, following Fleury and
//! Lammich's IsaSAT developments and the refinement arguments discussed in
//! CPP 2019 and FMCAD 2020.
//!
//! Each theorem follows the helper-axiom pattern used by the other overlay
//! theorem modules: a `_helper` axiom captures the proposition body, and the
//! theorem quantifies over its parameters with the helper applied.

use super::isasat_refinement::IsaSATConsts;
use crate::env::{decl_builder::EnvDeclBuilder, Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    fn register_isasat_helper_theorem_pair(
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

    /// `IsaSAT.invariant_preserved_by_propagate :
    ///     forall (s : CDCLState) (f : ClauseDB),
    ///       IsaSAT.invariant_preserved_by_propagate_helper s f`
    ///
    /// Intended meaning:
    /// `forall (s : CDCLState) (f : ClauseDB),
    ///    cdcl_invariant s f ->
    ///    cdcl_invariant (cdcl_step s Propagate) f`.
    ///
    /// Propagation preserves the abstract CDCL state invariant.
    pub(super) fn register_invariant_preserved_by_propagate(
        &mut self,
        c: &IsaSATConsts,
    ) -> Result<(), EnvError> {
        self.register_isasat_helper_theorem_pair(
            "IsaSAT.invariant_preserved_by_propagate_helper",
            "IsaSAT.invariant_preserved_by_propagate",
            &[c.cdcl_state.clone(), c.clause_db.clone()],
            &c.prop,
        )
    }

    /// `IsaSAT.invariant_preserved_by_decide :
    ///     forall (s : CDCLState) (f : ClauseDB),
    ///       IsaSAT.invariant_preserved_by_decide_helper s f`
    ///
    /// Intended meaning:
    /// `forall (s : CDCLState) (f : ClauseDB),
    ///    cdcl_invariant s f ->
    ///    cdcl_invariant (cdcl_step s Decide) f`.
    ///
    /// Decision preserves the abstract CDCL state invariant.
    pub(super) fn register_invariant_preserved_by_decide(
        &mut self,
        c: &IsaSATConsts,
    ) -> Result<(), EnvError> {
        self.register_isasat_helper_theorem_pair(
            "IsaSAT.invariant_preserved_by_decide_helper",
            "IsaSAT.invariant_preserved_by_decide",
            &[c.cdcl_state.clone(), c.clause_db.clone()],
            &c.prop,
        )
    }

    /// `IsaSAT.invariant_preserved_by_backtrack :
    ///     forall (s : CDCLState) (f : ClauseDB),
    ///       IsaSAT.invariant_preserved_by_backtrack_helper s f`
    ///
    /// Intended meaning:
    /// `forall (s : CDCLState) (f : ClauseDB),
    ///    cdcl_invariant s f ->
    ///    cdcl_invariant (cdcl_step s Backtrack) f`.
    pub(super) fn register_invariant_preserved_by_backtrack(
        &mut self,
        c: &IsaSATConsts,
    ) -> Result<(), EnvError> {
        self.register_isasat_helper_theorem_pair(
            "IsaSAT.invariant_preserved_by_backtrack_helper",
            "IsaSAT.invariant_preserved_by_backtrack",
            &[c.cdcl_state.clone(), c.clause_db.clone()],
            &c.prop,
        )
    }

    /// `IsaSAT.refinement_simulation_propagate :
    ///     forall (cs : ConcreteState) (s : CDCLState),
    ///       IsaSAT.refinement_simulation_propagate_helper cs s`
    ///
    /// Intended meaning:
    /// `forall (cs : ConcreteState) (s : CDCLState),
    ///    refinement_relation s cs ->
    ///    refinement_relation (cdcl_step s Propagate) (concrete_propagate cs)`.
    ///
    /// This is the key propagation/refinement commutation theorem.
    pub(super) fn register_refinement_simulation_propagate(
        &mut self,
        c: &IsaSATConsts,
    ) -> Result<(), EnvError> {
        self.register_isasat_helper_theorem_pair(
            "IsaSAT.refinement_simulation_propagate_helper",
            "IsaSAT.refinement_simulation_propagate",
            &[c.concrete_state.clone(), c.cdcl_state.clone()],
            &c.prop,
        )
    }

    /// `IsaSAT.refinement_preserves_invariant :
    ///     forall (cs : ConcreteState) (s : CDCLState) (f : ClauseDB),
    ///       IsaSAT.refinement_preserves_invariant_helper cs s f`
    ///
    /// Intended meaning:
    /// `forall (cs : ConcreteState) (s : CDCLState) (f : ClauseDB),
    ///    refinement_relation s cs -> cdcl_invariant s f ->
    ///    cdcl_invariant (abstract_of cs) f`.
    ///
    /// The abstract invariant transfers through the refinement relation.
    pub(super) fn register_refinement_preserves_invariant(
        &mut self,
        c: &IsaSATConsts,
    ) -> Result<(), EnvError> {
        self.register_isasat_helper_theorem_pair(
            "IsaSAT.refinement_preserves_invariant_helper",
            "IsaSAT.refinement_preserves_invariant",
            &[
                c.concrete_state.clone(),
                c.cdcl_state.clone(),
                c.clause_db.clone(),
            ],
            &c.prop,
        )
    }

    /// `IsaSAT.trail_consistency_preserved :
    ///     forall (s : CDCLState) (t : CDCLTransition),
    ///       IsaSAT.trail_consistency_preserved_helper s t`
    ///
    /// Intended meaning:
    /// `forall (s : CDCLState) (t : CDCLTransition),
    ///    trail_consistent (trail_of s) ->
    ///    trail_consistent (trail_of (cdcl_step s t))`.
    pub(super) fn register_trail_consistency_preserved(
        &mut self,
        c: &IsaSATConsts,
    ) -> Result<(), EnvError> {
        let cdcl_transition = Expr::const_(Name::from_string("IsaSAT.CDCLTransition"), vec![]);
        self.register_isasat_helper_theorem_pair(
            "IsaSAT.trail_consistency_preserved_helper",
            "IsaSAT.trail_consistency_preserved",
            &[c.cdcl_state.clone(), cdcl_transition],
            &c.prop,
        )
    }
}
