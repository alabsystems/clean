// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opt-in observations of the normal elaborator's actual tactic states.
//! Recording clones state only. Validation and rendering run after elaboration,
//! against each snapshot's own environment and exact local/metavariable world.

use std::collections::HashSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use clean_kernel::env::DomainAxiomClosure;
use clean_kernel::{ExprKind, Name};

use super::core::{Goal, LocalDecl, ProofState, ProofTrustLedger};
use super::display::format_goal;
use super::TacticPostSnapshotRange;

/// Goal data from a real proof state, checked in its captured local context.
#[derive(Debug, Clone)]
pub struct ObservedTacticGoals {
    /// Instantiated actual goals; every original local retains its FVar identity.
    pub goals: Vec<Goal>,
    /// The shared tactic formatter's view of those same goals.
    pub rendered_targets: Vec<String>,
}

/// Why an actual tactic state cannot supply an authoritative goal view.
#[derive(Debug, Clone, thiserror::Error)]
pub enum TacticGoalObservationUnavailable {
    #[error("tactic state carries trusted fallback debt: {0:?}")]
    Trusted(ProofTrustLedger),
    #[error("captured terms reach trust markers: {0:?}")]
    TrustedTerms(Vec<Name>),
    #[error("captured goal/local context failed full type validation: {0}")]
    InvalidType(String),
}

/// Observation-only identity of one actual `by` invocation within one collector. Proof-state
/// metavariable IDs overlap between independent blocks and cannot identify it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TacticGoalBlockId(u64);

#[derive(Debug, Clone, Copy)]
pub(crate) struct TacticGoalBlock {
    pub id: TacticGoalBlockId,
    pub range: Option<TacticPostSnapshotRange>,
}

/// Whether a snapshot observes a tactic or its actual enclosing `by` prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TacticGoalObservationKind {
    Tactic,
    ByPrefix,
}

/// Actual states before and after one normal SurfaceTactic dispatch.
/// This observes goals; it does not certify the enclosing declaration.
#[derive(Debug, Clone)]
pub struct TacticGoalObservation {
    pub block_id: TacticGoalBlockId,
    pub kind: TacticGoalObservationKind,
    /// Rewrite rule-level states are not recorded here. The complete rewrite's
    /// after-state is exposed at its tail; its interior retains the pre-state.
    pub after_at_tail: bool,
    pub tactic_range: TacticPostSnapshotRange,
    pub before: Result<ObservedTacticGoals, TacticGoalObservationUnavailable>,
    /// None means the tactic failed; a trusted successful state is an explicit Err.
    pub after: Option<Result<ObservedTacticGoals, TacticGoalObservationUnavailable>>,
}

#[derive(Debug)]
struct RawObservation {
    block_id: TacticGoalBlockId,
    kind: TacticGoalObservationKind,
    after_at_tail: bool,
    range: TacticPostSnapshotRange,
    before: Box<ProofState>,
    after: Option<Box<ProofState>>,
}

/// Observation failed independently of declaration checking.
#[derive(Debug, thiserror::Error)]
pub enum TacticGoalCaptureError {
    #[error("tactic goal observation collector is poisoned")]
    Poisoned,
}

/// A fresh, optional collector attached to a FileContext by an IDE caller.
/// Only the normal elaborator can append snapshots; callers can drain them.
#[derive(Debug, Clone, Default)]
pub struct TacticGoalCapture {
    observations: Arc<Mutex<Vec<RawObservation>>>,
    next_block: Arc<AtomicU64>,
}

impl TacticGoalCapture {
    pub(crate) fn start_block(
        &self,
        range: Option<TacticPostSnapshotRange>,
    ) -> Option<TacticGoalBlock> {
        // Identity exhaustion makes observation unavailable; it never reuses
        // an identity or changes the declaration's elaboration behavior.
        self.next_block
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .ok()
            .map(|id| TacticGoalBlock {
                id: TacticGoalBlockId(id),
                range,
            })
    }

    pub(crate) fn record(
        &self,
        block: TacticGoalBlock,
        kind: TacticGoalObservationKind,
        after_at_tail: bool,
        range: TacticPostSnapshotRange,
        before: Box<ProofState>,
        after: Option<Box<ProofState>>,
    ) {
        // A poisoned collector remains unavailable to take(); observing must
        // never turn an error in display bookkeeping into a proof verdict.
        if let Ok(mut observations) = self.observations.lock() {
            observations.push(RawObservation {
                block_id: block.id,
                kind,
                after_at_tail,
                range,
                before,
                after,
            });
        }
    }

    /// Drain, validate and render captured clones after the real elaboration.
    /// No checker query here can modify the original proof state or verdict.
    /// A module frontend keeps `module_driver::module_elaboration_lock` while
    /// draining, so shared kernel attribution counters remain isolated.
    pub fn take(&self) -> Result<Vec<TacticGoalObservation>, TacticGoalCaptureError> {
        let raw = {
            let mut observations = self
                .observations
                .lock()
                .map_err(|_| TacticGoalCaptureError::Poisoned)?;
            std::mem::take(&mut *observations)
        };
        Ok(raw
            .into_iter()
            .map(|raw| TacticGoalObservation {
                block_id: raw.block_id,
                kind: raw.kind,
                after_at_tail: raw.after_at_tail,
                tactic_range: raw.range,
                before: observed_goals(&raw.before),
                after: raw.after.as_deref().map(observed_goals),
            })
            .collect())
    }
}

fn observed_goals(
    state: &ProofState,
) -> Result<ObservedTacticGoals, TacticGoalObservationUnavailable> {
    let trust = state.trust_ledger();
    if trust.trusted_axiom_count() > 0 {
        return Err(TacticGoalObservationUnavailable::Trusted(trust));
    }
    let goals: Vec<_> = state
        .goals()
        .iter()
        .map(|goal| Goal {
            meta_id: goal.meta_id,
            target: state.instantiate_for_kernel(&goal.target),
            local_ctx: goal
                .local_ctx
                .iter()
                .map(|decl| LocalDecl {
                    binder_info: decl.binder_info,
                    fvar: decl.fvar,
                    name: decl.name.clone(),
                    ty: state.instantiate_for_kernel(&decl.ty),
                    value: decl.value.as_ref().map(|v| state.instantiate_for_kernel(v)),
                })
                .collect(),
            case_binders: goal.case_binders.clone(),
            tag: goal.tag.clone(),
        })
        .collect();
    // A closed goal list must not hide an invalid declaration parameter.
    // Validate the actual root metavariable's captured telescope as well;
    // this is a validation view of producer metadata, never a new proof state.
    let root_meta = state.metas.get(state.root_meta_id).ok_or_else(|| {
        TacticGoalObservationUnavailable::InvalidType("captured proof root is absent".into())
    })?;
    // Elaboration locals retain even unused header parameters. Root metadata
    // can be narrowed when metavariables are adopted, so validate their union,
    // preferring the actual elaborator declaration for a shared identity.
    let mut root_locals = state.elab_locals.clone();
    let mut seen: HashSet<_> = root_locals.iter().map(|decl| decl.fvar).collect();
    for (name, fvar, ty) in &root_meta.locals {
        if seen.insert(*fvar) {
            root_locals.push(LocalDecl {
                binder_info: Default::default(),
                fvar: *fvar,
                name: name.clone(),
                ty: ty.clone(),
                value: None,
            });
        }
    }
    // Build instantiated display copies; never rewrite a proof-state local
    // declaration outside the existing checked local-operations boundary.
    let root_locals = root_locals
        .into_iter()
        .map(|decl| LocalDecl {
            binder_info: decl.binder_info,
            fvar: decl.fvar,
            name: decl.name,
            ty: state.instantiate_for_kernel(&decl.ty),
            value: decl.value.as_ref().map(|v| state.instantiate_for_kernel(v)),
        })
        .collect();
    let root = Goal {
        meta_id: state.root_meta_id,
        target: state.instantiate_for_kernel(&root_meta.ty),
        local_ctx: root_locals,
        case_binders: Vec::new(),
        tag: None,
    };
    let root_value = root_meta
        .assignment
        .as_ref()
        .map(|v| state.instantiate_for_kernel(v));
    let mut assumptions = DomainAxiomClosure::new();
    for term in std::iter::once(&root)
        .chain(&goals)
        .flat_map(|goal| {
            std::iter::once(&goal.target).chain(
                goal.local_ctx
                    .iter()
                    .flat_map(|decl| std::iter::once(&decl.ty).chain(decl.value.as_ref())),
            )
        })
        .chain(root_value.as_ref())
    {
        let markers = assumptions.trust_markers_of_expr(state.env(), term);
        if !markers.is_empty() {
            return Err(TacticGoalObservationUnavailable::TrustedTerms(
                markers.into_iter().collect(),
            ));
        }
    }
    for goal in std::iter::once(&root).chain(&goals) {
        // A root validation view and an active goal can share a MetaId but
        // have different telescopes. Never carry typing answers between them.
        state.invalidate_tc_cache();
        for ty in goal
            .local_ctx
            .iter()
            .map(|decl| &decl.ty)
            .chain(std::iter::once(&goal.target))
        {
            reject_term_metas(ty)?;
            let sort = state
                .infer_type_strict(goal, ty)
                .map_err(|e| TacticGoalObservationUnavailable::InvalidType(e.to_string()))?;
            if !matches!(state.whnf(goal, &sort).kind(), ExprKind::Sort(_)) {
                return Err(TacticGoalObservationUnavailable::InvalidType(format!(
                    "{ty} has non-sort type {sort}"
                )));
            }
        }
        for decl in &goal.local_ctx {
            if let Some(value) = &decl.value {
                reject_term_metas(value)?;
                state
                    .check_type_strict(goal, value, &decl.ty)
                    .map_err(|e| TacticGoalObservationUnavailable::InvalidType(e.to_string()))?;
            }
        }
    }
    if goals.is_empty() {
        let value = root_value.as_ref().ok_or_else(|| {
            TacticGoalObservationUnavailable::InvalidType(
                "closed state has no root assignment".into(),
            )
        })?;
        reject_term_metas(value)?;
        state.invalidate_tc_cache();
        state
            .check_type_strict(&root, value, &root.target)
            .map_err(|e| TacticGoalObservationUnavailable::InvalidType(e.to_string()))?;
    }
    let rendered_targets = goals
        .iter()
        .map(|goal| format_goal(goal, state.env()))
        .collect();
    Ok(ObservedTacticGoals {
        goals,
        rendered_targets,
    })
}

fn reject_term_metas(term: &clean_kernel::Expr) -> Result<(), TacticGoalObservationUnavailable> {
    // Strict tactic checking intentionally registers metavariables as typed
    // FVars. That supports proof construction, but cannot certify their
    // absence from an IDE's closed-root view. Genuine header FVars remain.
    if let Some(meta) = super::hypothesis::collect_fvars(term)
        .into_iter()
        .find_map(crate::unify::MetaState::from_fvar)
    {
        return Err(TacticGoalObservationUnavailable::InvalidType(format!(
            "captured term retains unresolved metavariable {meta:?}"
        )));
    }
    Ok(())
}
