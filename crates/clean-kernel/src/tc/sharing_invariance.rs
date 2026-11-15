// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private suspended-prefix state for an exact, universal sharing replay.
//!
//! A prefix describes individual dynamic encounters, never a global choice
//! of a favorable normalization strategy. An unanswered encounter suspends
//! the check: its apparent result cannot be accepted. Every complete child
//! path must be checked before a caller can establish invariance.

use std::cell::RefCell;

use super::TypeChecker;
use crate::env::{Environment, KernelTheory};
use crate::expr::Expr;
use crate::level::{Level, SharingChoices};
use crate::name::Name;

const MAX_REPLAY_STATES: usize = 256;
const MAX_REPLAY_DECISIONS: usize = 32;

/// Work observations for this call, not a reusable certificate or body license.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SharingInvariantSummary {
    pub completed_paths: usize,
    pub attempted_states: usize,
    pub maximum_decisions: usize,
}

/// No success is returned for a favorable path or an unresolved execution.
#[derive(Debug, thiserror::Error)]
pub enum SharingInvariantFailure {
    #[error("sharing invariance requires the original closed safe Lean check context")]
    UnsupportedContext,
    #[error("sharing invariance exhausted its {0} budget")]
    Exhausted(&'static str),
    #[error("sharing replay could not establish a stable complete encounter trace")]
    Unresolved,
    #[error("sharing invariance was not established in every execution: {0}")]
    NotEstablished(super::TypeError),
}

/// One fresh execution's decisions. It is never serialized as authority.
pub(crate) struct SharingReplay {
    prefix: Box<[Decision]>,
    consumed: usize,
    pending: Option<Encounter>,
    diverged: bool,
}

#[derive(Clone)]
struct Decision {
    encounter: Encounter,
    rebuild: bool,
}

#[derive(Clone, PartialEq, Eq)]
struct Encounter {
    constant: Name,
    expression: Expr,
    parameters: Box<[Name]>,
    replacements: Box<[Level]>,
    original: Level,
}

/// Bind a decision to the exact enclosing instantiation, not merely to a
/// structurally equal level met in another operation or source constant.
pub(super) struct SharingInstantiation<'a> {
    replay: &'a RefCell<SharingReplay>,
    constant: &'a Name,
    expression: &'a Expr,
    parameters: &'a [Name],
    replacements: &'a [Level],
}

impl SharingReplay {
    fn new(prefix: Vec<Decision>) -> Self {
        Self {
            prefix: prefix.into_boxed_slice(),
            consumed: 0,
            pending: None,
            diverged: false,
        }
    }

    /// Whether this execution reached the first unanswered encounter.
    pub(crate) fn suspended(&self) -> bool {
        self.pending.is_some()
    }

    /// All prescribed encounters must actually have occurred.
    pub(crate) fn complete(&self) -> bool {
        !self.suspended() && !self.diverged && self.consumed == self.prefix.len()
    }
}

impl SharingChoices for SharingInstantiation<'_> {
    fn choose_rebuild(&self, original: &Level) -> Option<bool> {
        let mut state = self.replay.borrow_mut();
        if state.suspended() || state.diverged {
            return None;
        }
        let Some(decision) = state.prefix.get(state.consumed) else {
            state.pending = Some(Encounter {
                constant: self.constant.clone(),
                expression: self.expression.clone(),
                parameters: self.parameters.into(),
                replacements: self.replacements.into(),
                original: original.clone(),
            });
            return None;
        };
        let encounter = &decision.encounter;
        if encounter.constant != *self.constant
            || encounter.expression != *self.expression
            || encounter.parameters.as_ref() != self.parameters
            || encounter.replacements.as_ref() != self.replacements
            || encounter.original != *original
        {
            state.diverged = true;
            return None;
        }
        let rebuild = decision.rebuild;
        state.consumed += 1;
        Some(rebuild)
    }
}

impl<'env> TypeChecker<'env> {
    pub(super) fn sharing_choices<'a>(
        &'a self,
        constant: &'a Name,
        expression: &'a Expr,
        parameters: &'a [Name],
        replacements: &'a [Level],
    ) -> Option<SharingInstantiation<'a>> {
        self.sharing_replay
            .as_ref()
            .map(|replay| SharingInstantiation {
                replay,
                constant,
                expression,
                parameters,
                replacements,
            })
    }

    /// Only the universal owner constructs this checker. No retained cache,
    /// local context, favorable decision or serialized receipt can create it.
    fn for_sharing_prefix(
        env: &'env Environment,
        theory: KernelTheory,
        prefix: Vec<Decision>,
        heartbeats: u32,
    ) -> Self {
        let mut tc = Self::new(env);
        tc.set_kernel_theory(theory);
        tc.set_heartbeat_limit(heartbeats);
        tc.whnf_cache.get_mut().disable_for_sharing_replay();
        tc.whnf_core_cache.get_mut().disable_for_sharing_replay();
        tc.def_eq_cache.get_mut().disable_for_sharing_replay();
        tc.proj_type_cache.get_mut().disable_for_sharing_replay();
        tc.unfold_cache.get_mut().disable_for_sharing_replay();
        tc.quick_infer_cache.get_mut().disable_for_sharing_replay();
        tc.args_failure_cache.get_mut().disable_for_sharing_replay();
        tc.equiv_manager.get_mut().disable_for_sharing_replay();
        tc.branch_sharing_cache = None;
        *tc.type_cache.get_mut() = None;
        tc.max_cache_entries = 0;
        tc.infer_arc_memo.get_mut().clear();
        tc.sharing_replay = Some(RefCell::new(SharingReplay::new(prefix)));
        tc
    }

    /// Establish this exact type check under every overapproximated dynamic
    /// sharing outcome. The ordinary checker still refuses sharing hazards.
    ///
    /// This entry supports only the empty, safe Lean context used by eager
    /// declaration replay. Its environment is borrowed unchanged, every path
    /// has fresh local IDs/state and disabled answer/memo reuse, and the total
    /// heartbeat allowance is what remains of the original failed check.
    /// An abstract counterexample means "not established", not that the
    /// declaration is invalid in its actual Lean heap. Callers retain the
    /// original sharing refusal on every error here.
    pub fn recheck_type_sharing_invariant(
        &self,
        value: &Expr,
        expected: &Expr,
    ) -> Result<SharingInvariantSummary, SharingInvariantFailure> {
        self.recheck_type_sharing_with_limits(
            value,
            expected,
            MAX_REPLAY_STATES,
            MAX_REPLAY_DECISIONS,
        )
    }

    fn recheck_type_sharing_with_limits(
        &self,
        value: &Expr,
        expected: &Expr,
        max_states: usize,
        max_decisions: usize,
    ) -> Result<SharingInvariantSummary, SharingInvariantFailure> {
        if self.kernel_theory() != KernelTheory::Lean
            || self.sharing_replay.is_some()
            || !self.level_sharing_recorded()
            || !self.ctx.borrow().is_empty()
            || self.mode != self.env.mode()
            || self.honor_reducibility.get()
            || self.level_eq_override.is_some()
            || self.level_params.is_some()
            || self.allow_unsafe
            || self.allow_partial
            || self.cumulative
            || self.eager_reduce.get()
            || self.nat_probe_depth.get() != 0
            || self.trace_collector.is_some()
            || self.env.has_constant_source()
        {
            return Err(SharingInvariantFailure::UnsupportedContext);
        }
        if self.heartbeat_spent() {
            return Err(SharingInvariantFailure::Exhausted(
                "heartbeat/declaration/deadline",
            ));
        }
        let source = (
            self.env.generation(),
            self.env.mode(),
            self.env.kernel_theory(),
            self.env.models_lean_init(),
            self.env.lean_level_profile(),
        );
        let bounded = self.heartbeat_limit != 0;
        let mut remaining = if bounded {
            self.heartbeat_counter.get()
        } else {
            0
        };
        let mut pending = vec![Vec::<Decision>::new()];
        let mut summary = SharingInvariantSummary {
            completed_paths: 0,
            attempted_states: 0,
            maximum_decisions: 0,
        };
        while let Some(prefix) = pending.pop() {
            if summary.attempted_states == max_states {
                return Err(SharingInvariantFailure::Exhausted("state"));
            }
            if bounded && remaining == 0 {
                return Err(SharingInvariantFailure::Exhausted("heartbeat"));
            }
            let tc =
                Self::for_sharing_prefix(self.env, KernelTheory::Lean, prefix.clone(), remaining);
            summary.attempted_states += 1;
            let outcome = tc.check_type(value, expected);
            if tc.heartbeat_spent() {
                return Err(SharingInvariantFailure::Exhausted(
                    "heartbeat/declaration/deadline",
                ));
            }
            if bounded {
                let after = tc.heartbeat_counter.get();
                if after > remaining {
                    return Err(SharingInvariantFailure::Unresolved);
                }
                remaining = after;
            }
            if source
                != (
                    self.env.generation(),
                    self.env.mode(),
                    self.env.kernel_theory(),
                    self.env.models_lean_init(),
                    self.env.lean_level_profile(),
                )
            {
                return Err(SharingInvariantFailure::Unresolved);
            }
            let Some(replay) = tc.sharing_replay.as_ref() else {
                return Err(SharingInvariantFailure::Unresolved);
            };
            let replay = replay.borrow();
            if replay.diverged {
                return Err(SharingInvariantFailure::Unresolved);
            }
            if let Some(encounter) = &replay.pending {
                if replay.consumed != prefix.len() || prefix.len() == max_decisions {
                    return Err(SharingInvariantFailure::Exhausted("decision/trace"));
                }
                summary.maximum_decisions = summary.maximum_decisions.max(prefix.len() + 1);
                for rebuild in [true, false] {
                    let mut next = prefix.clone();
                    next.push(Decision {
                        encounter: encounter.clone(),
                        rebuild,
                    });
                    pending.push(next);
                }
                continue;
            }
            if !replay.complete() || tc.level_sharing_error().is_some() {
                return Err(SharingInvariantFailure::Unresolved);
            }
            outcome.map_err(SharingInvariantFailure::NotEstablished)?;
            summary.completed_paths += 1;
        }
        if summary.completed_paths == 0 {
            return Err(SharingInvariantFailure::Unresolved);
        }
        Ok(summary)
    }
}

#[cfg(test)]
#[path = "sharing_invariance_tests.rs"]
mod tests;
