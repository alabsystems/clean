// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-transition induction-step axioms for CDCL soundness claims S01-S06.
//!
//! **#3630 demasquerade status:** prior revisions of this module also
//! exposed `build_sNN_proof` / `register_and_build_case_analysis_proof`
//! / `build_state_pair_proof` / `register_proof_axiom` helpers that
//! manufactured lambda proof terms which merely wrapped same-type
//! `_proof` axioms and combinator axioms. The top-level CDCL soundness
//! claims were registered as `Declaration::Theorem` with those lambda
//! wrappers as their values — the wave-10 MASQUERADE pattern documented
//! in `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
//!
//! Per the design doc Proof Soundness Rules, those six claims have been
//! demoted to honest `Declaration::Axiom` (see
//! `cdcl_soundness_theorems.rs`). The dead proof-builder scaffolding —
//! which also transitively registered the `*_preserved_proof`,
//! `backtrack_correctness_proof`, `propagation_completeness_proof`,
//! `cdcl_terminates_proof` axioms and the `resolution_case_split`
//! combinator axiom — has been removed. Only the genuine
//! per-transition domain axioms remain here.
//!
//! Each `register_sNN_step_axioms` function captures the case-by-case
//! proof obligations from IsaSAT Lemma 3.1 / Lemma 3.2 / Theorem 4.2 as
//! honest axioms. A Branch B follow-up (structural induction over
//! `TransitionTag.cases_on`) is tracked under issue #3630.
//!
//! Reference: Nieuwenhuis, Oliveras & Tinelli (2006), "Solving SAT and
//!            SAT Modulo Theories"; Fleury (2019), "A verified SAT solver
//!            framework with learn, forget, restart, and incrementality".

#[cfg(test)]
use super::cdcl_soundness::CDCLSoundnessConsts;
#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::name::Name;

// ============================================================================
// S01: Trail consistency preservation
// ============================================================================

/// Register induction-step axioms for trail consistency preservation.
///
/// Each axiom captures one case of the induction: if trail_consistent holds
/// for state s, then after applying the specific transition, trail_consistent
/// still holds. These are the genuine proof obligations from IsaSAT Lemma 3.1.
#[cfg(test)]
pub(super) fn register_s01_step_axioms(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
) -> Result<(), EnvError> {
    // For each transition: (s : CDCLState) -> trail_consistent s -> trail_consistent (T s)
    let trail_consistent =
        Expr::const_(Name::from_string("CDCLSoundness.trail_consistent"), vec![]);

    let transitions = [
        (
            "CDCLSoundness.propagate_preserves_trail",
            "CDCLSoundness.Propagate",
        ),
        (
            "CDCLSoundness.decide_preserves_trail",
            "CDCLSoundness.Decide",
        ),
        (
            "CDCLSoundness.conflict_preserves_trail",
            "CDCLSoundness.Conflict",
        ),
        (
            "CDCLSoundness.restart_preserves_trail",
            "CDCLSoundness.Restart",
        ),
    ];

    for (axiom_name, transition_name) in &transitions {
        if env.get_const(&Name::from_string(axiom_name)).is_some() {
            continue;
        }
        let transition = Expr::const_(Name::from_string(transition_name), vec![]);
        // (s : CDCLState) -> trail_consistent s -> trail_consistent (T s)
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let tc_s = Expr::app(trail_consistent.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(tc_s.clone());
            let t_s = Expr::app(transition.clone(), s);
            let tc_ts = Expr::app(trail_consistent.clone(), t_s);
            let e = b.mk_pi(h_id, BinderInfo::Default, tc_s, tc_ts);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // Backtrack: (s : CDCLState) -> (k : Nat) -> trail_consistent s ->
    //            trail_consistent (Backtrack s k)
    let bt_axiom_name = "CDCLSoundness.backtrack_preserves_trail";
    if env.get_const(&Name::from_string(bt_axiom_name)).is_none() {
        let backtrack = Expr::const_(Name::from_string("CDCLSoundness.Backtrack"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let tc_s = Expr::app(trail_consistent.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(tc_s.clone());
            let bt_s_k = Expr::app(Expr::app(backtrack, s), k);
            let tc_bt = Expr::app(trail_consistent.clone(), bt_s_k);
            let e = b.mk_pi(h_id, BinderInfo::Default, tc_s, tc_bt);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(bt_axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    Ok(())
}

// ============================================================================
// S02: Two-watched-literal invariant preservation
// ============================================================================

/// Register induction-step axioms for two-watched-literal preservation.
///
/// Each axiom captures that the 2WL invariant is maintained when BCP
/// updates watched literals during propagation.
#[cfg(test)]
pub(super) fn register_s02_step_axioms(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
) -> Result<(), EnvError> {
    let two_watched = Expr::const_(
        Name::from_string("CDCLSoundness.two_watched_invariant"),
        vec![],
    );

    let transitions = [
        (
            "CDCLSoundness.propagate_preserves_2wl",
            "CDCLSoundness.Propagate",
        ),
        ("CDCLSoundness.decide_preserves_2wl", "CDCLSoundness.Decide"),
        (
            "CDCLSoundness.conflict_preserves_2wl",
            "CDCLSoundness.Conflict",
        ),
        (
            "CDCLSoundness.restart_preserves_2wl",
            "CDCLSoundness.Restart",
        ),
    ];

    for (axiom_name, transition_name) in &transitions {
        if env.get_const(&Name::from_string(axiom_name)).is_some() {
            continue;
        }
        let transition = Expr::const_(Name::from_string(transition_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let tw_s = Expr::app(two_watched.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(tw_s.clone());
            let t_s = Expr::app(transition.clone(), s);
            let tw_ts = Expr::app(two_watched.clone(), t_s);
            let e = b.mk_pi(h_id, BinderInfo::Default, tw_s, tw_ts);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // Backtrack case
    let bt_axiom_name = "CDCLSoundness.backtrack_preserves_2wl";
    if env.get_const(&Name::from_string(bt_axiom_name)).is_none() {
        let backtrack = Expr::const_(Name::from_string("CDCLSoundness.Backtrack"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let tw_s = Expr::app(two_watched.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(tw_s.clone());
            let bt_s_k = Expr::app(Expr::app(backtrack, s), k);
            let tw_bt = Expr::app(two_watched.clone(), bt_s_k);
            let e = b.mk_pi(h_id, BinderInfo::Default, tw_s, tw_bt);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(bt_axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    Ok(())
}

// ============================================================================
// S03: Resolution soundness (learned clauses are logical consequences)
// ============================================================================

/// Register induction-step axioms for resolution soundness.
///
/// For each CDCL transition, we need a proof that conflict_derivation_sound
/// is preserved. The key axiom is that each resolution step in conflict
/// analysis produces a clause that is a logical consequence of the original
/// clause set. This corresponds to IsaSAT Theorem 4.2.
///
/// We register per-transition axioms for all 5 transitions:
/// - Conflict: the resolution step that actually learns new clauses
/// - Propagate: unit propagation doesn't learn new clauses
/// - Decide: decision doesn't learn new clauses
/// - Restart: restart doesn't change learned clauses
/// - Backtrack: backtracking doesn't change learned clauses
#[cfg(test)]
pub(super) fn register_s03_step_axioms(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
) -> Result<(), EnvError> {
    let conflict_sound = Expr::const_(
        Name::from_string("CDCLSoundness.conflict_derivation_sound"),
        vec![],
    );

    // Resolution step axiom: resolving two clauses that are consequences
    // of the original set yields a clause that is also a consequence.
    // (s : CDCLState) -> conflict_derivation_sound s -> conflict_derivation_sound (Conflict s)
    let axiom_name = "CDCLSoundness.resolution_step_sound";
    if env.get_const(&Name::from_string(axiom_name)).is_none() {
        let conflict = Expr::const_(Name::from_string("CDCLSoundness.Conflict"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let cs_s = Expr::app(conflict_sound.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(cs_s.clone());
            let c_s = Expr::app(conflict.clone(), s);
            let cs_cs = Expr::app(conflict_sound.clone(), c_s);
            let e = b.mk_pi(h_id, BinderInfo::Default, cs_s, cs_cs);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // Propagation preserves derivation soundness (no new learned clauses)
    let prop_axiom_name = "CDCLSoundness.propagate_preserves_resolution";
    if env.get_const(&Name::from_string(prop_axiom_name)).is_none() {
        let propagate = Expr::const_(Name::from_string("CDCLSoundness.Propagate"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let cs_s = Expr::app(conflict_sound.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(cs_s.clone());
            let p_s = Expr::app(propagate, s);
            let cs_ps = Expr::app(conflict_sound.clone(), p_s);
            let e = b.mk_pi(h_id, BinderInfo::Default, cs_s, cs_ps);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(prop_axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // Decision preserves derivation soundness (no new learned clauses)
    let decide_axiom_name = "CDCLSoundness.decide_preserves_resolution";
    if env
        .get_const(&Name::from_string(decide_axiom_name))
        .is_none()
    {
        let decide = Expr::const_(Name::from_string("CDCLSoundness.Decide"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let cs_s = Expr::app(conflict_sound.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(cs_s.clone());
            let d_s = Expr::app(decide, s);
            let cs_ds = Expr::app(conflict_sound.clone(), d_s);
            let e = b.mk_pi(h_id, BinderInfo::Default, cs_s, cs_ds);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(decide_axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // Restart preserves derivation soundness (learned clauses are kept)
    let restart_axiom_name = "CDCLSoundness.restart_preserves_resolution";
    if env
        .get_const(&Name::from_string(restart_axiom_name))
        .is_none()
    {
        let restart = Expr::const_(Name::from_string("CDCLSoundness.Restart"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let cs_s = Expr::app(conflict_sound.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(cs_s.clone());
            let r_s = Expr::app(restart, s);
            let cs_rs = Expr::app(conflict_sound.clone(), r_s);
            let e = b.mk_pi(h_id, BinderInfo::Default, cs_s, cs_rs);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(restart_axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // Backtrack preserves derivation soundness (learned clauses are kept)
    let bt_axiom_name = "CDCLSoundness.backtrack_preserves_resolution";
    if env.get_const(&Name::from_string(bt_axiom_name)).is_none() {
        let backtrack = Expr::const_(Name::from_string("CDCLSoundness.Backtrack"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let cs_s = Expr::app(conflict_sound.clone(), s.clone());
            let (h_id, _h) = b.fresh_local(cs_s.clone());
            let bt_s_k = Expr::app(Expr::app(backtrack, s), k);
            let cs_bt = Expr::app(conflict_sound.clone(), bt_s_k);
            let e = b.mk_pi(h_id, BinderInfo::Default, cs_s, cs_bt);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(bt_axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    Ok(())
}

// ============================================================================
// S04: Backtrack correctness
// ============================================================================

/// Register induction-step axioms for backtrack correctness.
///
/// The key axiom: after backtracking to level k, the trail prefix up to k
/// is unchanged and all entries above k are removed.
#[cfg(test)]
pub(super) fn register_s04_step_axioms(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
) -> Result<(), EnvError> {
    let bt_correct = Expr::const_(Name::from_string("CDCLSoundness.backtrack_correct"), vec![]);
    let backtrack = Expr::const_(Name::from_string("CDCLSoundness.Backtrack"), vec![]);

    // Backtrack induction axiom: backtracking preserves the invariant
    // that all variables above level k are unassigned.
    // (s : CDCLState) -> (k : Nat) -> backtrack_correct (Backtrack s k) k
    let axiom_name = "CDCLSoundness.backtrack_step_correct";
    if env.get_const(&Name::from_string(axiom_name)).is_none() {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let bt_s_k = Expr::app(Expr::app(backtrack, s), k.clone());
            let body = Expr::app(Expr::app(bt_correct, bt_s_k), k);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), e);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    Ok(())
}

// ============================================================================
// S05: Propagation completeness
// ============================================================================

/// Register induction-step axioms for propagation completeness.
///
/// The key axiom: when BCP reaches a fixpoint (no more unit propagations),
/// every clause is either satisfied or has >= 2 unassigned literals.
#[cfg(test)]
pub(super) fn register_s05_step_axioms(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
) -> Result<(), EnvError> {
    let propagation_complete = Expr::const_(
        Name::from_string("CDCLSoundness.propagation_complete"),
        vec![],
    );
    let propagate = Expr::const_(Name::from_string("CDCLSoundness.Propagate"), vec![]);

    // BCP fixpoint axiom: repeated propagation reaches completeness.
    // (s : CDCLState) -> propagation_complete (Propagate s)
    // This captures that Propagate is defined as the fixpoint of unit propagation.
    let axiom_name = "CDCLSoundness.bcp_fixpoint_complete";
    if env.get_const(&Name::from_string(axiom_name)).is_none() {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let p_s = Expr::app(propagate, s);
            let body = Expr::app(propagation_complete, p_s);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), body);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    Ok(())
}

// ============================================================================
// S06: Termination
// ============================================================================

/// Register induction-step axioms for termination.
///
/// The key axiom: each learned clause excludes at least one assignment,
/// ensuring the termination measure decreases. This corresponds to the
/// well-founded ordering on (number of unassigned variables, clause DB size).
///
/// We use an abstract measure-decrease predicate rather than `Nat.lt`
/// directly to avoid pulling in the `init_lt()` dependency chain.
#[cfg(test)]
pub(super) fn register_s06_step_axioms(
    env: &mut Environment,
    c: &CDCLSoundnessConsts,
) -> Result<(), EnvError> {
    // measure_decreases : CDCLState -> CDCLState -> Prop
    // Abstract predicate stating the termination measure strictly decreases.
    let md_name = "CDCLSoundness.measure_decreases";
    if env.get_const(&Name::from_string(md_name)).is_none() {
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
            name: Name::from_string(md_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // conflict_decreases_measure :
    //   (s : CDCLState) -> measure_decreases s (Conflict s)
    // Each conflict analysis step that learns a clause strictly decreases
    // the termination measure.
    let cd_name = "CDCLSoundness.conflict_decreases_measure";
    if env.get_const(&Name::from_string(cd_name)).is_none() {
        let conflict = Expr::const_(Name::from_string("CDCLSoundness.Conflict"), vec![]);
        let measure_decreases = Expr::const_(Name::from_string(md_name), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.cdcl_state.clone());
            let c_s = Expr::app(conflict, s.clone());
            let body = Expr::app(Expr::app(measure_decreases, s), c_s);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.cdcl_state.clone(), body);
            b.finish(e)
        };
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(cd_name),
            level_params: vec![],
            type_: ty,
        })?;
    }

    // measure_well_founded : Prop
    // The measure ordering is well-founded (bounded below by 0).
    let wf_name = "CDCLSoundness.measure_well_founded";
    if env.get_const(&Name::from_string(wf_name)).is_none() {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(wf_name),
            level_params: vec![],
            type_: c.prop.clone(),
        })?;
    }

    Ok(())
}
