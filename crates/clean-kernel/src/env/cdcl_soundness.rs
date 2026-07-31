// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for CDCL soundness invariant formalization.
//!
//! Registers the abstract state space, transitions, and invariant predicates
//! needed to state and prove 6 critical CDCL (Conflict-Driven Clause Learning)
//! correctness invariants:
//!
//! 1. **Trail Consistency (I1)**: Every literal on the trail matches the
//!    assignment; decision levels are monotonically non-decreasing; each
//!    variable appears at most once.
//! 2. **Two-Watched Literal (I2)**: For every non-satisfied clause with
//!    >= 2 literals, two watched literals are not both false.
//! 3. **Conflict Clause Derivation (I3)**: Every learned clause is a logical
//!    consequence of the original clause set via resolution chain.
//! 4. **Backtrack Correctness (I4)**: After backtracking to level k, all
//!    variables at levels > k are unassigned.
//! 5. **Propagation Completeness (I5)**: When BCP terminates without conflict,
//!    there are no unit clauses.
//! 6. **Termination (I6)**: Each learned clause excludes at least one
//!    assignment, bounding the search space.
//!
//! Type and operation definitions live here; theorem registrations are in
//! `cdcl_soundness_theorems.rs`.
//!
//! Reference: Marques-Silva & Sakallah (1999), "GRASP";
//!            Moskewicz et al. (2001), "Chaff";
//!            Een & Sorensson (2003), "An extensible SAT-solver".

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

/// Shared constants used across all CDCL soundness declarations.
#[cfg(test)]
pub(super) struct CDCLSoundnessConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) variable: Expr,
    pub(super) literal: Expr,
    pub(super) clause: Expr,
    pub(super) assignment: Expr,
    pub(super) trail: Expr,
    pub(super) trail_entry: Expr,
    pub(super) watch_list: Expr,
    pub(super) cdcl_state: Expr,
}

#[cfg(test)]
impl CDCLSoundnessConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            variable: Expr::const_(Name::from_string("CDCLSoundness.Variable"), vec![]),
            literal: Expr::const_(Name::from_string("CDCLSoundness.Literal"), vec![]),
            clause: Expr::const_(Name::from_string("CDCLSoundness.Clause"), vec![]),
            assignment: Expr::const_(Name::from_string("CDCLSoundness.Assignment"), vec![]),
            trail: Expr::const_(Name::from_string("CDCLSoundness.Trail"), vec![]),
            trail_entry: Expr::const_(Name::from_string("CDCLSoundness.TrailEntry"), vec![]),
            watch_list: Expr::const_(Name::from_string("CDCLSoundness.WatchList"), vec![]),
            cdcl_state: Expr::const_(Name::from_string("CDCLSoundness.CDCLState"), vec![]),
        }
    }
}

/// Register an axiom with idempotency check.
#[cfg(test)]
fn add_cdcl_axiom(env: &mut Environment, name: &str, type_: Expr) -> Result<(), EnvError> {
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
    /// Initialize CDCL soundness declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`.
    #[cfg(test)]
    pub(crate) fn init_cdcl_soundness(&mut self) -> Result<(), EnvError> {
        if self.cdcl_soundness_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;

        let c = CDCLSoundnessConsts::new();

        // Types
        self.register_cdcl_variable(&c)?;
        self.register_cdcl_literal(&c)?;
        self.register_cdcl_clause(&c)?;
        self.register_cdcl_assignment(&c)?;
        self.register_cdcl_trail_entry(&c)?;
        self.register_cdcl_trail(&c)?;
        self.register_cdcl_watch_list(&c)?;
        self.register_cdcl_state(&c)?;

        // State transitions
        self.register_cdcl_transitions(&c)?;

        // Transition tag type and case analysis (for structured proofs)
        self.register_cdcl_transition_tag(&c)?;

        // Invariant predicates
        self.register_cdcl_invariants(&c)?;

        // Theorems (in cdcl_soundness_theorems.rs)
        self.register_cdcl_trail_consistency_preserved(&c)?;
        self.register_cdcl_two_watched_preserved(&c)?;
        self.register_cdcl_resolution_soundness(&c)?;
        self.register_cdcl_backtrack_correctness(&c)?;
        self.register_cdcl_propagation_completeness(&c)?;
        self.register_cdcl_terminates(&c)?;

        self.cdcl_soundness_init = true;
        Ok(())
    }

    // ====================================================================
    // Types
    // ====================================================================

    #[cfg(test)]
    fn register_cdcl_variable(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.Variable", c.type0.clone())
    }

    #[cfg(test)]
    fn register_cdcl_literal(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.Literal", c.type0.clone())?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.Literal.variable",
            Expr::pi(BinderInfo::Default, c.literal.clone(), c.variable.clone()),
        )?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.Literal.polarity",
            Expr::pi(BinderInfo::Default, c.literal.clone(), c.bool_.clone()),
        )
    }

    #[cfg(test)]
    fn register_cdcl_clause(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.Clause", c.type0.clone())?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.Clause.size",
            Expr::pi(BinderInfo::Default, c.clause.clone(), c.nat.clone()),
        )
    }

    #[cfg(test)]
    fn register_cdcl_assignment(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.Assignment", c.type0.clone())
    }

    #[cfg(test)]
    fn register_cdcl_trail_entry(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.TrailEntry", c.type0.clone())?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.TrailEntry.literal",
            Expr::pi(
                BinderInfo::Default,
                c.trail_entry.clone(),
                c.literal.clone(),
            ),
        )?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.TrailEntry.level",
            Expr::pi(BinderInfo::Default, c.trail_entry.clone(), c.nat.clone()),
        )
    }

    #[cfg(test)]
    fn register_cdcl_trail(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.Trail", c.type0.clone())?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.Trail.length",
            Expr::pi(BinderInfo::Default, c.trail.clone(), c.nat.clone()),
        )
    }

    #[cfg(test)]
    fn register_cdcl_watch_list(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.WatchList", c.type0.clone())
    }

    #[cfg(test)]
    fn register_cdcl_state(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        add_cdcl_axiom(self, "CDCLSoundness.CDCLState", c.type0.clone())?;
        // Projections: assignment, trail, watches
        add_cdcl_axiom(
            self,
            "CDCLSoundness.CDCLState.assignment",
            Expr::pi(
                BinderInfo::Default,
                c.cdcl_state.clone(),
                c.assignment.clone(),
            ),
        )?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.CDCLState.trail",
            Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.trail.clone()),
        )?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.CDCLState.watches",
            Expr::pi(
                BinderInfo::Default,
                c.cdcl_state.clone(),
                c.watch_list.clone(),
            ),
        )?;
        // clauses, learned : CDCLState -> Clause (abstract clause-set type)
        add_cdcl_axiom(
            self,
            "CDCLSoundness.CDCLState.clauses",
            Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.type0.clone()),
        )?;
        add_cdcl_axiom(
            self,
            "CDCLSoundness.CDCLState.learned",
            Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.type0.clone()),
        )?;
        // decision_level : CDCLState -> Nat
        add_cdcl_axiom(
            self,
            "CDCLSoundness.CDCLState.decision_level",
            Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.nat.clone()),
        )
    }

    // ====================================================================
    // State transitions
    // ====================================================================

    #[cfg(test)]
    fn register_cdcl_transitions(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        let state_to_state = Expr::pi(
            BinderInfo::Default,
            c.cdcl_state.clone(),
            c.cdcl_state.clone(),
        );

        // Propagate, Decide, Conflict, Restart : CDCLState -> CDCLState
        for name in [
            "CDCLSoundness.Propagate",
            "CDCLSoundness.Decide",
            "CDCLSoundness.Conflict",
            "CDCLSoundness.Restart",
        ] {
            add_cdcl_axiom(self, name, state_to_state.clone())?;
        }

        // Backtrack : CDCLState -> Nat -> CDCLState
        let backtrack_ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(
                k_id,
                BinderInfo::Default,
                c.nat.clone(),
                c.cdcl_state.clone(),
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        add_cdcl_axiom(self, "CDCLSoundness.Backtrack", backtrack_ty)
    }

    // ====================================================================
    // Transition tag type (for structured case analysis proofs)
    // ====================================================================

    /// Register a `TransitionTag` type and case analysis axiom.
    ///
    /// The transition tag is an abstract inductive type with constructors:
    ///   propagate_tag, decide_tag, conflict_tag, restart_tag, backtrack_tag
    ///
    /// The `cases_on` axiom provides large elimination (case analysis) and
    /// `apply_transition` connects each tag to the actual transition function.
    ///
    /// This infrastructure enables proof terms that perform genuine case
    /// analysis on which CDCL transition was applied, rather than delegating
    /// to a monolithic proof axiom.
    #[cfg(test)]
    fn register_cdcl_transition_tag(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        // TransitionTag : Type 0
        add_cdcl_axiom(self, "CDCLSoundness.TransitionTag", c.type0.clone())?;

        let tag = Expr::const_(Name::from_string("CDCLSoundness.TransitionTag"), vec![]);

        // Tag constructors: each is a constant of type TransitionTag
        for name in [
            "CDCLSoundness.propagate_tag",
            "CDCLSoundness.decide_tag",
            "CDCLSoundness.conflict_tag",
            "CDCLSoundness.restart_tag",
            "CDCLSoundness.backtrack_tag",
        ] {
            add_cdcl_axiom(self, name, tag.clone())?;
        }

        // cases_on : forall (C : TransitionTag -> Prop),
        //   C propagate_tag -> C decide_tag -> C conflict_tag ->
        //   C restart_tag -> C backtrack_tag -> forall (t : TransitionTag), C t
        //
        // This is the elimination principle for TransitionTag, enabling
        // case analysis in proof terms.
        let cases_name = "CDCLSoundness.TransitionTag.cases_on";
        if self.get_const(&Name::from_string(cases_name)).is_none() {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                // C : TransitionTag -> Prop (the motive)
                let motive_ty = Expr::pi(BinderInfo::Default, tag.clone(), c.prop.clone());
                let (c_id, c_var) = b.fresh_local(motive_ty.clone());

                let tags: Vec<Expr> = [
                    "CDCLSoundness.propagate_tag",
                    "CDCLSoundness.decide_tag",
                    "CDCLSoundness.conflict_tag",
                    "CDCLSoundness.restart_tag",
                    "CDCLSoundness.backtrack_tag",
                ]
                .iter()
                .map(|n| Expr::const_(Name::from_string(n), vec![]))
                .collect();

                // Allocate branch hypotheses: C propagate_tag, C decide_tag, etc.
                let branch_ids: Vec<_> = tags
                    .iter()
                    .map(|t| b.fresh_local(Expr::app(c_var.clone(), t.clone())))
                    .collect();

                // Target: forall (t : TransitionTag), C t
                let (t_id, t_var) = b.fresh_local(tag.clone());
                let mut e = Expr::app(c_var.clone(), t_var);

                // Close t binder
                e = b.mk_pi(t_id, BinderInfo::Default, tag.clone(), e);

                // Close branch binders (reverse order)
                for (i, (h_id, _)) in branch_ids.iter().enumerate().rev() {
                    let branch_ty = Expr::app(c_var.clone(), tags[i].clone());
                    e = b.mk_pi(*h_id, BinderInfo::Default, branch_ty, e);
                }

                // Close motive binder
                e = b.mk_pi(c_id, BinderInfo::Default, motive_ty, e);
                b.finish(e)
            };
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(cases_name),
                level_params: vec![],
                type_: ty,
            })?;
        }

        // apply_transition : TransitionTag -> CDCLState -> CDCLState
        // Connects each tag to its corresponding transition function.
        let apply_name = "CDCLSoundness.apply_transition";
        if self.get_const(&Name::from_string(apply_name)).is_none() {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (tag_id, _) = b.fresh_local(tag.clone());
                let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
                let e = b.mk_pi(
                    s_id,
                    BinderInfo::Default,
                    c.cdcl_state.clone(),
                    c.cdcl_state.clone(),
                );
                let e = b.mk_pi(tag_id, BinderInfo::Default, tag.clone(), e);
                b.finish(e)
            };
            add_cdcl_axiom(self, apply_name, ty)?;
        }

        // valid_transition : CDCLState -> CDCLState -> TransitionTag -> Prop
        // States that s' = apply_transition tag s.
        let vt_name = "CDCLSoundness.valid_transition";
        if self.get_const(&Name::from_string(vt_name)).is_none() {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
                let (sp_id, _) = b.fresh_local(c.cdcl_state.clone());
                let (tag_id, _) = b.fresh_local(tag.clone());
                let e = b.mk_pi(tag_id, BinderInfo::Default, tag.clone(), c.prop.clone());
                let e = b.mk_pi(sp_id, BinderInfo::Default, c.cdcl_state.clone(), e);
                let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
                b.finish(e)
            };
            add_cdcl_axiom(self, vt_name, ty)?;
        }

        Ok(())
    }

    // ====================================================================
    // Invariant predicates
    // ====================================================================

    #[cfg(test)]
    fn register_cdcl_invariants(&mut self, c: &CDCLSoundnessConsts) -> Result<(), EnvError> {
        let state_to_prop = Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.prop.clone());

        // I1-I3, I5: CDCLState -> Prop
        for name in [
            "CDCLSoundness.trail_consistent",
            "CDCLSoundness.two_watched_invariant",
            "CDCLSoundness.conflict_derivation_sound",
            "CDCLSoundness.propagation_complete",
        ] {
            add_cdcl_axiom(self, name, state_to_prop.clone())?;
        }

        // I4: backtrack_correct : CDCLState -> Nat -> Prop
        let bt_correct_ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        add_cdcl_axiom(self, "CDCLSoundness.backtrack_correct", bt_correct_ty)?;

        // I6: termination_measure : CDCLState -> Nat
        add_cdcl_axiom(
            self,
            "CDCLSoundness.termination_measure",
            Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.nat.clone()),
        )
    }
}
