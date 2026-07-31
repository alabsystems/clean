// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CDCL soundness invariant claims S01-S06.
//!
//! **#3630 demasquerade status:** these six declarations were previously
//! registered as `Declaration::Theorem` whose proof terms were alias
//! wrappers around same-type `_proof` / combinator axioms (the classic
//! wave-10 MASQUERADE pattern documented in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`). Per the
//! design doc Proof Soundness Rules ("Declaration::Theorem wrapping
//! Declaration::Axiom is NOT a proof. It is a restatement."), they
//! have been demoted to honest `Declaration::Axiom` on their original
//! Pi types.
//!
//! The per-transition induction step axioms registered in
//! `cdcl_soundness_proofs.rs` (e.g. `propagate_preserves_trail`,
//! `backtrack_step_correct`, `bcp_fixpoint_complete`) remain as
//! per-case domain axioms — they encode the genuine proof obligations
//! from IsaSAT Lemmas 3.1/3.2/Theorem 4.2 and are honest statements of
//! partial content even if a constructive combined proof is not yet
//! available in-kernel.
//!
//! Registered claims (S01-S06):
//!
//! - S01 `trail_consistency_preserved`: trail consistency survives every
//!   CDCL transition (Propagate / Decide / Conflict / Restart / Backtrack).
//! - S02 `two_watched_preserved`: the two-watched-literal invariant is
//!   maintained by BCP watchlist updates.
//! - S03 `resolution_soundness`: learned clauses are logical consequences
//!   of the original clause set via resolution.
//! - S04 `backtrack_correctness`: after backtracking to level k, all
//!   variables assigned at levels > k are unassigned.
//! - S05 `propagation_completeness`: when BCP terminates without a
//!   conflict, no unit clauses remain.
//! - S06 `cdcl_terminates`: the well-founded termination measure
//!   (unassigned variables, clause DB size) strictly decreases on each
//!   learning step.
//!
//! Reference: Nieuwenhuis, Oliveras & Tinelli (2006), "Solving SAT and
//!            SAT Modulo Theories"; Fleury (2019), "A verified SAT
//!            solver framework with learn, forget, restart, and
//!            incrementality" (FMCAD); Marques-Silva & Sakallah (1999),
//!            "GRASP"; Een & Sorensson (2003), "An extensible SAT-solver".
//!
//! A Branch B follow-up (genuine in-kernel proofs via case analysis on
//! `TransitionTag.cases_on` and structural induction over the CDCL
//! inductive types already imported from `clean-verify`) is tracked
//! under issue #3630.

#[cfg(test)]
use super::cdcl_soundness::CDCLSoundnessConsts;
#[cfg(test)]
use super::cdcl_soundness_proofs;
#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    // ====================================================================
    // S01: Trail consistency preservation
    // ====================================================================

    /// `trail_consistency_preserved : forall (s s' : CDCLState),
    ///     trail_consistency_preserved_helper s s'`
    ///
    /// Registered as an honest `Declaration::Axiom` post-#3630
    /// demasquerade. The per-transition induction step axioms in
    /// `cdcl_soundness_proofs::register_s01_step_axioms` capture the
    /// case-by-case proof obligations from IsaSAT Lemma 3.1.
    #[cfg(test)]
    pub(super) fn register_cdcl_trail_consistency_preserved(
        &mut self,
        c: &CDCLSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "CDCLSoundness.trail_consistency_preserved";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        register_helper_state_pair(self, c, "CDCLSoundness.trail_consistency_preserved_helper")?;
        cdcl_soundness_proofs::register_s01_step_axioms(self, c)?;

        let ty = build_state_pair_claim_type(c, "CDCLSoundness.trail_consistency_preserved_helper");
        register_axiom_claim(self, thm_name, ty)
    }

    // ====================================================================
    // S02: Two-watched literal invariant preservation
    // ====================================================================

    /// `two_watched_preserved : forall (s s' : CDCLState),
    ///     two_watched_preserved_helper s s'`
    ///
    /// Registered as an honest `Declaration::Axiom` post-#3630
    /// demasquerade. The per-transition induction step axioms in
    /// `cdcl_soundness_proofs::register_s02_step_axioms` capture each
    /// BCP watchlist-update case.
    #[cfg(test)]
    pub(super) fn register_cdcl_two_watched_preserved(
        &mut self,
        c: &CDCLSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "CDCLSoundness.two_watched_preserved";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        register_helper_state_pair(self, c, "CDCLSoundness.two_watched_preserved_helper")?;
        cdcl_soundness_proofs::register_s02_step_axioms(self, c)?;

        let ty = build_state_pair_claim_type(c, "CDCLSoundness.two_watched_preserved_helper");
        register_axiom_claim(self, thm_name, ty)
    }

    // ====================================================================
    // S03: Resolution soundness of learned clauses
    // ====================================================================

    /// `resolution_soundness : forall (s s' : CDCLState),
    ///     resolution_soundness_helper s s'`
    ///
    /// Registered as an honest `Declaration::Axiom` post-#3630
    /// demasquerade. The per-transition induction step axioms in
    /// `cdcl_soundness_proofs::register_s03_step_axioms` (including
    /// `resolution_step_sound`) encode the resolution-chain obligation
    /// from IsaSAT Theorem 4.2.
    #[cfg(test)]
    pub(super) fn register_cdcl_resolution_soundness(
        &mut self,
        c: &CDCLSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "CDCLSoundness.resolution_soundness";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        register_helper_state_pair(self, c, "CDCLSoundness.resolution_soundness_helper")?;
        cdcl_soundness_proofs::register_s03_step_axioms(self, c)?;

        let ty = build_state_pair_claim_type(c, "CDCLSoundness.resolution_soundness_helper");
        register_axiom_claim(self, thm_name, ty)
    }

    // ====================================================================
    // S04: Backtrack correctness
    // ====================================================================

    /// `backtrack_correctness : forall (s : CDCLState) (k : Nat)
    ///     (s' : CDCLState), backtrack_correctness_helper s k s'`
    ///
    /// Registered as an honest `Declaration::Axiom` post-#3630
    /// demasquerade. The supporting `backtrack_step_correct` step
    /// axiom remains registered by `register_s04_step_axioms`.
    #[cfg(test)]
    pub(super) fn register_cdcl_backtrack_correctness(
        &mut self,
        c: &CDCLSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "CDCLSoundness.backtrack_correctness";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        register_helper_state_nat_state(self, c, "CDCLSoundness.backtrack_correctness_helper")?;
        cdcl_soundness_proofs::register_s04_step_axioms(self, c)?;

        let ty = build_state_nat_state_claim_type(c, "CDCLSoundness.backtrack_correctness_helper");
        register_axiom_claim(self, thm_name, ty)
    }

    // ====================================================================
    // S05: Propagation completeness
    // ====================================================================

    /// `propagation_completeness : forall (s : CDCLState),
    ///     propagation_completeness_helper s`
    ///
    /// Registered as an honest `Declaration::Axiom` post-#3630
    /// demasquerade. The supporting `bcp_fixpoint_complete` step axiom
    /// remains registered by `register_s05_step_axioms`.
    #[cfg(test)]
    pub(super) fn register_cdcl_propagation_completeness(
        &mut self,
        c: &CDCLSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "CDCLSoundness.propagation_completeness";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        register_helper_state_prop(self, c, "CDCLSoundness.propagation_completeness_helper")?;
        cdcl_soundness_proofs::register_s05_step_axioms(self, c)?;

        let ty = build_state_claim_type(c, "CDCLSoundness.propagation_completeness_helper");
        register_axiom_claim(self, thm_name, ty)
    }

    // ====================================================================
    // S06: Termination
    // ====================================================================

    /// `cdcl_terminates : forall (s s' : CDCLState),
    ///     cdcl_terminates_helper s s'`
    ///
    /// Registered as an honest `Declaration::Axiom` post-#3630
    /// demasquerade. The supporting `measure_decreases` /
    /// `conflict_decreases_measure` / `measure_well_founded` step
    /// axioms remain registered by `register_s06_step_axioms`.
    #[cfg(test)]
    pub(super) fn register_cdcl_terminates(
        &mut self,
        c: &CDCLSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "CDCLSoundness.cdcl_terminates";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        register_helper_state_pair(self, c, "CDCLSoundness.cdcl_terminates_helper")?;
        cdcl_soundness_proofs::register_s06_step_axioms(self, c)?;

        let ty = build_state_pair_claim_type(c, "CDCLSoundness.cdcl_terminates_helper");
        register_axiom_claim(self, thm_name, ty)
    }
}

// ============================================================================
// Helper registration functions
// ============================================================================

/// Register a helper axiom: (s : CDCLState) -> (s' : CDCLState) -> Prop
#[cfg(test)]
fn register_helper_state_pair(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
    name: &str,
) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
        let (sp_id, _) = b.fresh_local(c.cdcl_state.clone());
        let e = b.mk_pi(
            sp_id,
            BinderInfo::Default,
            c.cdcl_state.clone(),
            c.prop.clone(),
        );
        let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
}

/// Register a helper axiom: (s : CDCLState) -> (k : Nat) -> (s' : CDCLState) -> Prop
#[cfg(test)]
fn register_helper_state_nat_state(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
    name: &str,
) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, _) = b.fresh_local(c.cdcl_state.clone());
        let (k_id, _) = b.fresh_local(c.nat.clone());
        let (sp_id, _) = b.fresh_local(c.cdcl_state.clone());
        let e = b.mk_pi(
            sp_id,
            BinderInfo::Default,
            c.cdcl_state.clone(),
            c.prop.clone(),
        );
        let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
        let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
        b.finish(e)
    };
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
}

/// Register a helper axiom: (s : CDCLState) -> Prop
#[cfg(test)]
fn register_helper_state_prop(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
    name: &str,
) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    let ty = Expr::pi(BinderInfo::Default, c.cdcl_state.clone(), c.prop.clone());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
}

/// Build the claim type `forall (s s' : CDCLState), helper s s'` for a
/// state-pair helper.
#[cfg(test)]
fn build_state_pair_claim_type(c: &CDCLSoundnessConsts, helper_name: &str) -> Expr {
    let helper = Expr::const_(Name::from_string(helper_name), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
    let (sp_id, sp) = b.fresh_local(c.cdcl_state.clone());
    let body = Expr::apps(helper, [s.clone(), sp.clone()]);
    let e = b.mk_pi(sp_id, BinderInfo::Default, c.cdcl_state.clone(), body);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
    b.finish(e)
}

/// Build the claim type `forall (s : CDCLState) (k : Nat) (s' : CDCLState),
/// helper s k s'`.
#[cfg(test)]
fn build_state_nat_state_claim_type(c: &CDCLSoundnessConsts, helper_name: &str) -> Expr {
    let helper = Expr::const_(Name::from_string(helper_name), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (sp_id, sp) = b.fresh_local(c.cdcl_state.clone());
    let body = Expr::apps(helper, [s.clone(), k.clone(), sp.clone()]);
    let e = b.mk_pi(sp_id, BinderInfo::Default, c.cdcl_state.clone(), body);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
    b.finish(e)
}

/// Build the claim type `forall (s : CDCLState), helper s`.
#[cfg(test)]
fn build_state_claim_type(c: &CDCLSoundnessConsts, helper_name: &str) -> Expr {
    let helper = Expr::const_(Name::from_string(helper_name), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
    let body = Expr::app(helper, s.clone());
    let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), body);
    b.finish(e)
}

/// Register a top-level CDCL soundness claim as an honest
/// `Declaration::Axiom` (post-#3630 demasquerade).
#[cfg(test)]
fn register_axiom_claim(env: &mut Environment, name: &str, ty: Expr) -> Result<(), EnvError> {
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
}
