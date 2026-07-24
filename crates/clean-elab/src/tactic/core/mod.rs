// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core tactic types and proof state.
//!
//! This module contains the fundamental types for the tactic framework:
//! - [`Goal`] - A proof goal with target and local context
//! - [`LocalDecl`] - A local declaration (hypothesis or let-binding)
//! - [`ProofState`] - The proof state containing goals and meta state
//! - [`TacticError`] - Error types for tactic execution
//! - [`TacticResult`] - Result type for tactics

mod close_fvars;
mod conv_focus_tree;
mod conv_witness;
mod error;
mod factory;
mod goal_ops;
mod local_ops;
mod trust;
mod type_check;

#[cfg(test)]
pub(crate) use self::close_fvars::close_fvars;
pub(crate) use conv_focus_tree::{ConvFocus, ConvNav};
pub(crate) use conv_witness::ConvFocusWitness;
pub use error::{RewriteCandidate, TacticError, TacticResult};
pub use trust::{
    ProofTrustLedger, SmtRecoveryLedger, TrustedArithProvenanceLedger, TrustedAyProvenanceLedger,
};

use crate::instances::InstanceTable;
use crate::unify::{MetaId, MetaState};
use clean_kernel::{Environment, Expr, FVarId, TcCaches};
use std::collections::VecDeque;

use super::options::ProofOptions;

use super::conv::ConvPosition;

#[cfg(test)]
mod ratchet;
#[cfg(test)]
pub(crate) use ratchet::{
    CLOSE_GOAL_UNCHECKED_RATCHET, ELAB_SORRY_SOURCE_SITE_RATCHET,
    LOCAL_DECL_REWRITE_SOURCE_SITE_RATCHET, METAS_ASSIGN_BYPASS_RATCHET,
    TRUSTED_ARITH_SOURCE_SITE_RATCHET, TRUSTED_AY_CALL_SITE_RATCHET,
};

// =============================================================================
// Core types
// =============================================================================

/// A goal in the proof state
#[derive(Debug, Clone)]
pub struct Goal {
    /// Unique identifier for this goal (corresponds to a metavariable)
    pub meta_id: MetaId,
    /// The type to prove (target)
    pub target: Expr,
    /// Local context (hypotheses available)
    pub local_ctx: Vec<LocalDecl>,
    /// Optional tag for goal focusing (e.g., constructor name from `cases`/`induction`)
    pub tag: Option<String>,
}

/// A local declaration in the goal context
#[derive(Debug, Clone)]
pub struct LocalDecl {
    /// Free variable id
    pub fvar: FVarId,
    /// Name for display
    pub name: String,
    /// Type of this hypothesis
    pub ty: Expr,
    /// Optional value (for let-bindings)
    pub value: Option<Expr>,
}

/// The proof state containing all goals
#[derive(Debug)]
pub struct ProofState {
    /// The environment
    pub(crate) env: Environment,
    /// All goals (first is the main goal)
    pub(crate) goals: VecDeque<Goal>,
    /// Metavariable state for tracking assignments
    pub(crate) metas: MetaState,
    /// Metavariable that represents this proof state's top-level goal.
    /// Main proof states usually use `MetaId(0)`; nested/focused states may not.
    pub(crate) root_meta_id: MetaId,
    /// Next fresh free variable id
    pub(crate) next_fvar: u64,
    /// Instance table for typeclass resolution (None → sorry fallback).
    pub(crate) instances: Option<InstanceTable>,
    /// Universe parameter names from `fresh_universe_param` (#1828).
    pub(crate) universe_params: Vec<String>,
    /// Counter for fresh universe parameter generation (#1828).
    pub(crate) next_universe: u64,
    /// Cached TypeChecker state; invalidated when goal changes (#1671).
    tc_cache: std::sync::Mutex<Option<(MetaId, TcCaches)>>,
    /// Elaborator-scope FVars visible to tactics but not tactic-created (#2212).
    pub(crate) elab_locals: Vec<LocalDecl>,
    /// Base FVar ID: tactic FVars have id >= fvar_base (#2212).
    pub(crate) fvar_base: u64,
    /// Per-proof trust provenance for server-visible trust summaries.
    pub(crate) trust_ledger: ProofTrustLedger,
    /// Conv navigation state: `(original_expr, path)` for `eval_conv_goal`
    /// reconstruction after `lhs`/`rhs`/`enter` focus + body rewrite. #2477.
    pub(crate) conv_nav: Option<(Expr, Vec<ConvPosition>)>,
    /// Accumulated equality witness for focused `conv` body rewrites (#2555).
    pub(crate) conv_focus_witness: Option<ConvFocusWitness>,
    /// N-ary multi-focus `conv => congr` tree (#2477 Phase 4). When present,
    /// `conv => congr` opened one sub-focus per head + argument; the body
    /// sequencer advances through the opened sub-goals and the reconstruction
    /// boundary recombines the per-focus equalities into one kernel-checked
    /// whole-application proof. `None` outside a congr'd conv body; the proven
    /// single-focus path (`conv_nav` + `conv_focus_witness`) is left untouched.
    pub(crate) conv_focus_tree: Option<ConvNav>,
    /// Currently-selected sub-focus PATH within `conv_focus_tree` (#2477 Phase
    /// 4). Each component selects a child: at a node with `[head, a1, .., an]`,
    /// `0` = head, `i` (1..=n) = `args[i-1]` (SOURCE order). A multi-component
    /// path descends through nested `congr`s. `None` when no focus is selected.
    pub(crate) conv_congr_cursor: Option<Vec<usize>>,
    /// Local proof options set via `set_option` tactic (#1881).
    pub(crate) options: ProofOptions,
    /// Opened-namespace context inherited from the elaborator at the tactic
    /// entry point. Lets `simp [extra_lemma]` resolve unqualified extra-lemma
    /// names (e.g. `add_zero` after `open Nat`) through the same
    /// `resolve_identifier` order the term elaborator uses, instead of only
    /// trying the literal name. `None` when no enclosing namespace context is
    /// available (lemma names then resolve by literal name only).
    pub(crate) namespace_state: Option<crate::namespace::NamespaceState>,
}

impl Clone for ProofState {
    fn clone(&self) -> Self {
        Self {
            env: self.env.clone(),
            goals: self.goals.clone(),
            metas: self.metas.clone(),
            root_meta_id: self.root_meta_id,
            next_fvar: self.next_fvar,
            instances: self.instances.clone(),
            universe_params: self.universe_params.clone(),
            next_universe: self.next_universe,
            tc_cache: std::sync::Mutex::new(None),
            elab_locals: self.elab_locals.clone(),
            fvar_base: self.fvar_base,
            trust_ledger: self.trust_ledger,
            conv_nav: self.conv_nav.clone(),
            conv_focus_witness: self.conv_focus_witness.clone(),
            conv_focus_tree: self.conv_focus_tree.clone(),
            conv_congr_cursor: self.conv_congr_cursor.clone(),
            options: self.options.clone(),
            namespace_state: self.namespace_state.clone(),
        }
    }
}

// =============================================================================
// ProofState constructors and core methods
// =============================================================================

impl ProofState {
    /// Create a new proof state for a goal type
    ///
    /// # Contract
    ///
    /// REQUIRES: `env` is a valid Lean environment
    /// REQUIRES: `target` is a well-formed type expression
    /// ENSURES: `self.goals.len() == 1` (single main goal)
    /// ENSURES: `self.goals[0].target == target`
    /// ENSURES: `self.is_complete() == false`
    /// ENSURES: `self.next_fvar == 0` and `self.fvar_base == 0`
    pub fn new(env: Environment, target: Expr) -> Self {
        let mut metas = MetaState::new();

        // Create a metavariable for the main goal
        let meta_id = metas.fresh_with_locals(target.clone(), Vec::new());

        let main_goal = Goal {
            meta_id,
            target,
            local_ctx: Vec::new(),
            tag: None,
        };

        ProofState {
            env,
            goals: VecDeque::from([main_goal]),
            metas,
            root_meta_id: meta_id,
            next_fvar: 0,
            instances: None,
            universe_params: Vec::new(),
            next_universe: 0,
            tc_cache: std::sync::Mutex::new(None),
            elab_locals: Vec::new(),
            fvar_base: 0,
            trust_ledger: ProofTrustLedger::default(),
            conv_nav: None,
            conv_focus_witness: None,
            conv_focus_tree: None,
            conv_congr_cursor: None,
            options: ProofOptions::default(),
            namespace_state: None,
        }
    }

    /// Create a new proof state with an instance table for type class resolution
    ///
    /// # Contract
    ///
    /// REQUIRES: `env` is a valid Lean environment
    /// REQUIRES: `target` is a well-formed type expression
    /// ENSURES: `self.goals.len() == 1` (single main goal)
    /// ENSURES: `self.instances().is_some()`
    /// ENSURES: `self.is_complete() == false`
    pub fn with_instances(env: Environment, target: Expr, instances: InstanceTable) -> Self {
        let mut metas = MetaState::new();
        let meta_id = metas.fresh_with_locals(target.clone(), Vec::new());

        let main_goal = Goal {
            meta_id,
            target,
            local_ctx: Vec::new(),
            tag: None,
        };

        ProofState {
            env,
            goals: VecDeque::from([main_goal]),
            metas,
            root_meta_id: meta_id,
            next_fvar: 0,
            instances: Some(instances),
            universe_params: Vec::new(),
            next_universe: 0,
            tc_cache: std::sync::Mutex::new(None),
            elab_locals: Vec::new(),
            fvar_base: 0,
            trust_ledger: ProofTrustLedger::default(),
            conv_nav: None,
            conv_focus_witness: None,
            conv_focus_tree: None,
            conv_congr_cursor: None,
            options: ProofOptions::default(),
            namespace_state: None,
        }
    }

    /// Create a new proof state with an existing local context
    ///
    /// # Contract
    ///
    /// REQUIRES: `env` is a valid Lean environment
    /// REQUIRES: `target` is a well-formed type expression
    /// REQUIRES: all `ctx` entries have distinct `fvar` IDs
    /// ENSURES: `self.goals.len() == 1`
    /// ENSURES: `self.goals[0].local_ctx == ctx`
    /// ENSURES: `self.next_fvar > max(ctx.fvar.as_u64())` (no ID collisions)
    pub fn with_context(env: Environment, target: Expr, ctx: Vec<LocalDecl>) -> Self {
        let mut metas = MetaState::new();
        let root_scope = Self::scope_snapshot(&[], &ctx);
        let meta_id = metas.fresh_with_locals(target.clone(), root_scope);

        // Start one past the highest existing FVar, or at zero for an empty
        // context (matching `ProofState::new`).
        let next_fvar = ctx
            .iter()
            .map(|d| d.fvar.as_u64().saturating_add(1))
            .max()
            .unwrap_or(0);

        let main_goal = Goal {
            meta_id,
            target,
            local_ctx: ctx,
            tag: None,
        };

        ProofState {
            env,
            goals: VecDeque::from([main_goal]),
            metas,
            root_meta_id: meta_id,
            next_fvar,
            instances: None,
            universe_params: Vec::new(),
            next_universe: 0,
            tc_cache: std::sync::Mutex::new(None),
            elab_locals: Vec::new(),
            fvar_base: 0,
            trust_ledger: ProofTrustLedger::default(),
            conv_nav: None,
            conv_focus_witness: None,
            conv_focus_tree: None,
            conv_congr_cursor: None,
            options: ProofOptions::default(),
            namespace_state: None,
        }
    }

    /// Create a proof state whose initial local context comes from an enclosing
    /// elaboration or serialized obligation context.
    ///
    /// The locals remain visible in the focused goal for tactics such as
    /// `assumption`, but `closed_proof` treats their FVars as external rather
    /// than tactic-created binders. This is the right constructor for
    /// server-opened obligations with serialized local hypotheses.
    #[must_use]
    pub fn with_elab_context(env: Environment, target: Expr, ctx: Vec<LocalDecl>) -> Self {
        let mut state = Self::with_context(env, target, ctx.clone());
        let max_fvar = ctx.iter().map(|d| d.fvar.as_u64()).max();
        let base = max_fvar.map_or(0, |id| id + 1);
        state.fvar_base = base;
        state.next_fvar = state.next_fvar.max(base);
        state.elab_locals = ctx;
        state
    }

    /// Create a tactic proof state whose goal and exact local scope come from
    /// the enclosing elaborator, while retaining its instance table.
    pub(crate) fn with_instances_and_elab_context(
        env: Environment,
        target: Expr,
        instances: InstanceTable,
        ctx: Vec<LocalDecl>,
    ) -> Self {
        let mut state = Self::with_elab_context(env, target, ctx);
        state.instances = Some(instances);
        state
    }

    /// Get the instance table if available
    ///
    /// ENSURES: Returns `Some` iff an instance table was set via constructor or `set_instances`
    pub fn instances(&self) -> Option<&InstanceTable> {
        self.instances.as_ref()
    }

    /// Set the instance table for type class resolution
    ///
    /// ENSURES: `self.instances().is_some()` after call
    pub fn set_instances(&mut self, instances: InstanceTable) {
        self.instances = Some(instances);
    }

    /// Get the opened-namespace context, if one was inherited from the
    /// elaborator at the tactic entry point.
    ///
    /// ENSURES: Returns `Some` iff a namespace context was set via
    /// [`set_namespace_state`](Self::set_namespace_state).
    pub(crate) fn namespace_state(&self) -> Option<&crate::namespace::NamespaceState> {
        self.namespace_state.as_ref()
    }

    /// Set the opened-namespace context for name-based lemma resolution.
    ///
    /// Mirrors [`set_instances`](Self::set_instances): the enclosing
    /// elaborator threads its [`NamespaceState`](crate::namespace::NamespaceState)
    /// so that name-based tactics (e.g. `simp [extra_lemma]`) can resolve
    /// unqualified names through opened namespaces. The state is cloned, so
    /// the proof state is unaffected by later elaborator-side mutations.
    ///
    /// ENSURES: `self.namespace_state().is_some()` after call.
    pub(crate) fn set_namespace_state(&mut self, ns_state: crate::namespace::NamespaceState) {
        self.namespace_state = Some(ns_state);
    }

    /// Get the local proof options.
    pub fn options(&self) -> &ProofOptions {
        &self.options
    }

    /// Get mutable access to the local proof options (#1881).
    pub(crate) fn options_mut(&mut self) -> &mut ProofOptions {
        &mut self.options
    }

    /// Get the current (first) goal
    ///
    /// ENSURES: Returns `Some` iff `self.goals` is non-empty
    /// ENSURES: Returns `None` iff `self.is_complete()`
    pub fn current_goal(&self) -> Option<&Goal> {
        self.goals.front()
    }

    /// Get the current (first) goal mutably.
    ///
    /// Invalidates the TypeChecker cache since the caller is about to mutate
    /// the goal's target or local context.
    /// Part of #1671.
    pub fn current_goal_mut(&mut self) -> Option<&mut Goal> {
        self.invalidate_tc_cache();
        self.goals.front_mut()
    }

    /// Get all remaining goals
    ///
    /// ENSURES: Returns an empty deque iff `self.is_complete()`
    pub fn goals(&self) -> &VecDeque<Goal> {
        &self.goals
    }

    /// Run `tactic` with the goal at `index` focused as the current (front) goal.
    ///
    /// This generalizes the `{ ... }` / `·` focus mechanism (see
    /// [`crate::tactic::combinator::focus`]) from "goal 0" to an arbitrary goal
    /// index, which is how the server honors a non-first `goal_id` in
    /// `applyTactic`. The goals preceding `index` are removed, the focused goal
    /// is run as the front goal, and the preceding goals are restored ahead of
    /// whatever the tactic left behind. The relative order of every other goal
    /// is preserved, and any subgoals the tactic creates appear where the
    /// focused goal was (relative to the trailing goals).
    ///
    /// REQUIRES: `index < self.goals().len()`
    ///
    /// ENSURES: Returns `None` (without running `tactic`) iff `index` is out of
    /// range; otherwise returns `Some` with the tactic's result.
    ///
    /// ENSURES: On any tactic outcome (Ok or Err), goals `0..index` are restored
    /// at the front in their original order, so the proof state stays consistent.
    pub fn focus_goal<F>(&mut self, index: usize, tactic: F) -> Option<TacticResult>
    where
        F: FnOnce(&mut Self) -> TacticResult,
    {
        if index >= self.goals.len() {
            return None;
        }

        self.invalidate_tc_cache();

        // Detach the goals ahead of the focused one; the focused goal is now
        // front. `split_off(index)` leaves `prefix = [g0..gIndex)` in a fresh
        // deque and keeps `[gIndex, gIndex+1, ...]` in `self.goals`.
        let prefix = {
            let mut tail = self.goals.split_off(index);
            std::mem::swap(&mut self.goals, &mut tail);
            tail
        };

        let result = tactic(self);

        // Restore the prefix ahead of whatever the tactic left (subgoals of the
        // focused goal, or nothing if it closed). Order: prefix then current.
        for goal in prefix.into_iter().rev() {
            self.goals.push_front(goal);
        }

        self.invalidate_tc_cache();
        Some(result)
    }

    /// Check if the proof is complete (no goals remain)
    ///
    /// ENSURES: Returns `true` iff `self.goals().is_empty()`
    pub fn is_complete(&self) -> bool {
        self.goals.is_empty()
    }

    /// Get the original goal type (the type of the main metavariable).
    ///
    /// This is the target type that the proof must inhabit. Used by
    /// kernel verification to check that the proof term's type matches
    /// the stated theorem. Part of #2200.
    ///
    /// # Contract
    ///
    /// REQUIRES: none
    /// ENSURES: Returns `Some(ty)` iff the root goal metavariable exists in the meta context
    /// ENSURES: The returned type is the original goal target, not a simplified form
    pub fn goal_type(&self) -> Option<Expr> {
        self.metas.get(self.root_meta_id).map(|m| m.ty.clone())
    }

    /// Get the proof term (only valid when complete)
    ///
    /// # Contract
    ///
    /// REQUIRES: none
    /// ENSURES: Returns `Some(expr)` only when `self.is_complete()` and the root goal metavariable has an assignment
    /// ENSURES: Returns `None` when any goals remain open
    pub fn proof_term(&self) -> Option<Expr> {
        if !self.is_complete() {
            return None;
        }

        self.metas.get_assignment(self.root_meta_id).cloned()
    }

    /// Get the instantiated proof term with all metavariables resolved
    ///
    /// # Contract
    ///
    /// REQUIRES: none
    /// ENSURES: If `Some`, all metavariable placeholders in the returned expression are resolved
    /// ENSURES: Returns `None` when `proof_term()` returns `None`
    pub fn instantiated_proof(&self) -> Option<Expr> {
        self.proof_term().map(|p| self.metas.instantiate(&p))
    }

    /// Get the closed proof term (FVars converted to BVars)
    ///
    /// This is the proper proof term for verification. The `instantiated_proof`
    /// method returns a term with FVars (free variables) that were introduced
    /// during tactic execution. This method additionally closes the term by
    /// converting those FVars back to BVars (bound variables) so the result
    /// is a valid closed term suitable for type checking and verification.
    ///
    /// When `fvar_base > 0` (ProofState inherits elaborator locals, #2212),
    /// only tactic-created FVars (id >= fvar_base) are closed. Elaborator-
    /// scope FVars (id < fvar_base) are preserved — the enclosing elaborator
    /// abstracts them when constructing the final lambda term.
    ///
    /// # Contract
    ///
    /// REQUIRES: none
    /// ENSURES: If `Some`, no tactic-scope FVars (id in `[fvar_base, next_fvar)`) remain
    /// ENSURES: If `Some`, all metavariable placeholders are resolved
    /// ENSURES: Returns `None` when `instantiated_proof()` returns `None`
    /// ENSURES: Returns `None` (fail-closed) when the closed term would retain a
    ///          tactic-scope FVar with no matching binder (an ID-to-binder gap,
    ///          #2204). Such a term is malformed and MUST be rejected — this
    ///          method never returns a term containing a residual tactic FVar,
    ///          and never panics on one.
    pub fn closed_proof(&self) -> Option<Expr> {
        let p = self.instantiated_proof()?;
        // When `fvar_base > 0` (inherited elaborator locals, #2212) only
        // tactic-created FVars (id >= fvar_base) are closed; elaborator-scope
        // FVars below it are preserved. When `fvar_base == 0` this is just 0.
        let base = self.fvar_base;
        let outcome = close_fvars::close_fvars_validated(&p, 0, base, self.next_fvar);

        // #2204 FAIL CLOSED: a tactic-scope FVar with no matching binder means
        // the assembled proof term is genuinely malformed (an ID-to-binder gap).
        // Refuse it — return `None` so callers surface a normal elaboration
        // error — rather than panicking or handing a term with a residual free
        // variable to the kernel. The kernel would reject it anyway, but failing
        // here keeps the diagnostic and never aborts the worker thread.
        if let Some(diagnostic) = &outcome.gap {
            debug_assert!(
                outcome.closed.has_fvar_quick(),
                "close_fvars reported a gap but the closed term has no FVar: {diagnostic}",
            );
            tracing::debug!("closed_proof rejected (fail-closed): {diagnostic}");
            return None;
        }

        // Belt-and-suspenders: even with no reported gap, never return a term
        // that still carries a tactic-scope FVar (id in [base, next_fvar)).
        if outcome.closed.has_fvar_quick()
            && close_fvars::contains_tactic_fvar(&outcome.closed, base, self.next_fvar)
        {
            tracing::debug!(
                "closed_proof rejected (fail-closed): residual tactic FVar in [{base}, {})",
                self.next_fvar,
            );
            return None;
        }

        Some(outcome.closed)
    }

    /// Get the metavariable state
    ///
    /// ENSURES: Returns the shared metavariable context for this proof
    pub fn metas(&self) -> &MetaState {
        &self.metas
    }

    /// Get mutable metavariable state
    ///
    /// ENSURES: Mutations to the returned `MetaState` are reflected in this proof state
    pub fn metas_mut(&mut self) -> &mut MetaState {
        &mut self.metas
    }

    /// Get the environment
    ///
    /// ENSURES: Returns the Lean environment shared by all goals in this proof
    pub fn env(&self) -> &Environment {
        &self.env
    }

    /// Get a mutable reference to the environment.
    ///
    /// Used by automation tactics that need to register additional declarations
    /// (e.g., Classical.byContradiction, Skolem constants) that proof terms
    /// may reference. Part of #1164.
    pub(crate) fn env_mut(&mut self) -> &mut Environment {
        &mut self.env
    }

    /// Get both metas (mutable) and env (immutable) for unification
    ///
    /// This helper avoids borrow conflicts when calling `Unifier::with_env`.
    ///
    /// ENSURES: The returned MetaState and Environment are consistent with each other
    pub fn metas_and_env(&mut self) -> (&mut MetaState, &Environment) {
        (&mut self.metas, &self.env)
    }
}
