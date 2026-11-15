// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Heartbeat resource limits for the type checker.
//!
//! Prevents runaway type checking on pathological inputs by tracking a
//! decrementing counter across major operations (whnf, is_def_eq, infer_type).
//!
//! Design:
//! - `tick_heartbeat()` is called at `Result`-returning entry points
//!   (`infer_type`) and both decrements and checks the limit.
//! - `inc_heartbeat()` is called in non-`Result` hot paths (`whnf_impl`,
//!   `is_def_eq_impl`) and only decrements. The exceeded condition surfaces
//!   at the next `tick_heartbeat()` call.
//! - Every heartbeat site, and `heartbeat_exhausted()`, first settles the
//!   checker's account with the kernel work meter (`crate::work_meter`,
//!   `work_account.rs`): the structural walks its open operations ran since
//!   the last settlement (equality walks behind cache probes, the probes
//!   themselves, fold and equivalence walks) are checked against the walking
//!   its ticks already paid for, and the excess is converted into heartbeats
//!   and drawn from both budgets. A tick is one step plus a fixed allowance of
//!   walking; walking past that is no longer free.
//!
//! Lean 4 reference: `check_system` in `src/runtime/interrupt.h`, called at
//! `type_checker.cpp:274` (infer_type), `:402` (whnf), `:1057` (is_def_eq).

use super::heartbeat_profiler::{
    HeartbeatProfile, HeartbeatProfileCategory, HeartbeatProfiler, SourcePos,
};
use super::TypeChecker;
use crate::name::Name;
use std::cell::RefCell;

impl<'env> TypeChecker<'env> {
    /// Set the heartbeat limit.
    ///
    /// A limit of 0 disables heartbeat checking (unlimited). The counter is
    /// reset to the new limit value.
    ///
    /// Used by `add_decl` to apply the `maxHeartbeats` file-scope option
    /// from Environment, and by tests for fine-grained limit control.
    ///
    /// # Contract
    ///
    /// ENSURES: `self.heartbeat_limit() == limit` after call
    /// ENSURES: heartbeat counter is reset to `limit`
    pub fn set_heartbeat_limit(&mut self, limit: u32) {
        self.heartbeat_limit = limit;
        self.heartbeat_counter.set(limit);
        self.work.reset_budget();
    }

    /// Get the current heartbeat limit.
    ///
    /// Returns 0 if heartbeat checking is disabled.
    #[must_use]
    pub fn heartbeat_limit(&self) -> u32 {
        self.heartbeat_limit
    }

    /// Get the remaining heartbeat count.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn heartbeat_remaining(&self) -> u32 {
        self.heartbeat_counter.get()
    }

    /// Reset the heartbeat counter to the configured limit.
    ///
    /// Call this between independent type checking operations (e.g., per-constant
    /// verification in `verify-olean`) to give each operation a fresh budget.
    /// Without this, the counter exhausts across operations and subsequent ones
    /// fail immediately with `HeartbeatExceeded`.
    pub fn reset_heartbeat(&self) {
        self.heartbeat_counter.set(self.heartbeat_limit);
        self.work.reset_budget();
    }

    /// Decrement heartbeat and check limit.
    ///
    /// Called at the top of `infer_type`.
    /// Returns `Ok(())` if within budget, `Err(HeartbeatExceeded)` if
    /// the counter has been exhausted.
    ///
    /// When `heartbeat_limit == 0`, this is a no-op (unlimited).
    ///
    /// Lean 4 reference: `check_system("type checker", true)` in
    /// `type_checker.cpp:274`.
    #[inline]
    pub(super) fn tick_heartbeat(&self) -> Result<(), super::TypeError> {
        // Bill the walks this operation ran since the last heartbeat site
        // first, so a budget they spent is refused here and now.
        self.note_tick_scope();
        #[cfg(any(test, feature = "inference-stats"))]
        crate::work_meter::stats::record_step_tick();
        self.settle_kernel_work();
        self.work.grant_step();
        // An instantiation whose Lean answer depends on `.olean` object
        // sharing was met on a path that cannot fail (`tc/level_profile.rs`):
        // nothing this checker answers from here on is served.
        if let Some(err) = self.level_sharing_error() {
            return Err(err);
        }
        // The ambient DEADLINE (`deadline.rs`) is polled before any budget:
        // a caller that installed one is no longer waiting once it has passed.
        // No deadline installed (every caller but `clean-server`'s work pool)
        // = one TLS load, no branch taken, nothing below changes.
        if super::deadline::poll_deadline() {
            return Err(super::TypeError::Interrupted);
        }
        // The AMBIENT declaration budget is checked FIRST and unconditionally.
        // It must bind even when this checker's own heartbeat is disabled
        // (`limit == 0`), because "unlimited for this checker" is exactly the
        // configuration a runaway declaration reaches through — see
        // `decl_budget.rs`. Disabled ambient budget = one TLS load, no branch
        // taken, no behavior change.
        if !super::decl_budget::consume_declaration_budget() {
            return Err(super::TypeError::DeclarationBudgetExhausted {
                limit: super::decl_budget::declaration_budget_limit(),
            });
        }
        let limit = self.heartbeat_limit;
        if limit == 0 {
            return Ok(());
        }
        let current = self.heartbeat_counter.get();
        if current == 0 {
            return Err(self.heartbeat_exceeded_error());
        }
        self.heartbeat_counter.set(current - 1);
        if let Some(ref profiler) = self.profiler {
            profiler
                .borrow()
                .tick(HeartbeatProfileCategory::InferType, None);
        }
        Ok(())
    }

    /// Check if the heartbeat counter is exhausted (zero with a non-zero limit),
    /// the ambient declaration budget is spent, or the ambient deadline fired.
    ///
    /// Used by `whnf_impl` and `is_def_eq_impl` to bail early from long-running
    /// reductions when the budget is spent. Returns false when heartbeat is
    /// disabled (limit == 0) and neither ambient bound is installed.
    #[inline]
    pub(super) fn heartbeat_exhausted(&self) -> bool {
        // A bail check must see the walks billed so far, or a run of cache
        // hits could spend the budget without any bail ever firing.
        self.settle_kernel_work();
        (self.heartbeat_limit != 0 && self.heartbeat_counter.get() == 0)
            || super::decl_budget::declaration_budget_exhausted()
            || super::deadline::deadline_fired()
    }

    /// Public probe: has the current heartbeat budget been fully spent?
    ///
    /// `false` when heartbeat checking is disabled (`limit == 0`). Elaboration-
    /// side callers that run WHNF under a budget (discr-tree index-key builds)
    /// use this after the call to learn whether the result may be under-reduced
    /// — e.g., to discard the checker's caches instead of storing partially
    /// reduced entries back into an unbudgeted cache pool. Never changes a
    /// verdict or a budget: called between operations, it only re-reads the
    /// kernel work meter (`work_account.rs`), so nothing is billed.
    #[inline]
    #[must_use]
    pub fn heartbeat_spent(&self) -> bool {
        self.heartbeat_exhausted()
    }

    /// Decrement heartbeat counter without checking (WHNF category).
    ///
    /// Called from `whnf_impl` which returns non-Result types. The counter is
    /// decremented unconditionally (saturating at 0). The exceeded condition is
    /// detected at the next `tick_heartbeat()` call in a `Result`-returning
    /// entry point.
    #[inline]
    pub(super) fn inc_heartbeat(&self) {
        self.inc_heartbeat_categorized(HeartbeatProfileCategory::Whnf);
    }

    /// Decrement heartbeat counter without checking (IsDefEq category).
    ///
    /// Called from `is_def_eq_impl`. Same semantics as `inc_heartbeat` but
    /// attributes the tick to the IsDefEq profiler category.
    #[inline]
    pub(super) fn inc_heartbeat_def_eq(&self) {
        self.inc_heartbeat_categorized(HeartbeatProfileCategory::IsDefEq);
    }

    /// Decrement heartbeat counter without checking, with category attribution.
    #[inline]
    fn inc_heartbeat_categorized(&self, category: HeartbeatProfileCategory) {
        self.note_tick_scope();
        #[cfg(any(test, feature = "inference-stats"))]
        crate::work_meter::stats::record_step_tick();
        self.settle_kernel_work();
        self.work.grant_step();
        // Ambient budget first, for the same reason as `tick_heartbeat`: a
        // checker with its own heartbeat disabled must still draw down the
        // declaration's pot. Non-`Result` path, so exhaustion is not reported
        // here — `heartbeat_exhausted()` (which reads the ambient latch) makes
        // `whnf_impl` / `is_def_eq_impl` bail, and the next `tick_heartbeat`
        // turns it into a typed error.
        let _ = super::decl_budget::consume_declaration_budget();
        // The deadline latches here too; `heartbeat_exhausted()` reads it.
        let _ = super::deadline::poll_deadline();
        if self.heartbeat_limit == 0 {
            return;
        }
        let current = self.heartbeat_counter.get();
        if current == 0 {
            return;
        }
        self.heartbeat_counter.set(current - 1);
        if let Some(ref profiler) = self.profiler {
            profiler.borrow().tick(category, None);
        }
    }

    /// Draw `heartbeats` converted from kernel work units from the ambient
    /// declaration budget and from this checker's own (saturating at zero, as
    /// every non-`Result` site does). Exhaustion surfaces at the next
    /// `tick_heartbeat()` / `heartbeat_exhausted()`, exactly as for a tick.
    pub(super) fn consume_work_heartbeats(&self, heartbeats: u64) {
        #[cfg(any(test, feature = "inference-stats"))]
        crate::work_meter::stats::record_work_heartbeats(heartbeats);
        super::decl_budget::consume_declaration_budget_many(heartbeats);
        if self.heartbeat_limit == 0 {
            return;
        }
        let current = self.heartbeat_counter.get();
        let drawn = u32::try_from(heartbeats).unwrap_or(u32::MAX).min(current);
        self.heartbeat_counter.set(current - drawn);
        if drawn != 0 {
            if let Some(ref profiler) = self.profiler {
                profiler.borrow().tick_by(
                    HeartbeatProfileCategory::KernelWork,
                    None,
                    u64::from(drawn),
                );
            }
        }
    }

    /// Build the `HeartbeatExceeded` error, including a profiler snapshot if
    /// profiling is enabled.
    fn heartbeat_exceeded_error(&self) -> super::TypeError {
        let limit = self.heartbeat_limit;
        let profile = self
            .profiler
            .as_ref()
            .map(|p| Box::new(p.borrow().report(limit, 10)));
        super::TypeError::HeartbeatExceeded { limit, profile }
    }

    // ── Profiler control ──────────────────────────────────────────────

    /// Enable the heartbeat profiler.
    ///
    /// When enabled, heartbeat ticks are attributed to operation categories
    /// (whnf, is_def_eq, infer_type) and optionally to constant names.
    /// The profiler report is included in the `HeartbeatExceeded` error on
    /// timeout.
    ///
    /// Part of #3399.
    pub fn enable_heartbeat_profiler(&mut self) {
        self.profiler = Some(RefCell::new(HeartbeatProfiler::new()));
    }

    /// Disable the heartbeat profiler and discard accumulated data.
    pub fn disable_heartbeat_profiler(&mut self) {
        self.profiler = None;
    }

    /// Check if the heartbeat profiler is enabled.
    #[must_use]
    pub fn heartbeat_profiler_enabled(&self) -> bool {
        self.profiler.is_some()
    }

    /// Set the active name for profiler attribution.
    ///
    /// Heartbeat ticks recorded while this name is active will be attributed
    /// to it in the per-name breakdown of the profile report.
    pub(crate) fn set_profiler_active_name(&self, name: Name) {
        if let Some(ref profiler) = self.profiler {
            profiler.borrow().set_active_name(name);
        }
    }

    /// Clear the active profiler name.
    pub fn clear_profiler_active_name(&self) {
        if let Some(ref profiler) = self.profiler {
            profiler.borrow().clear_active_name();
        }
    }

    /// Get the current heartbeat profile report.
    ///
    /// Returns `None` if profiling is not enabled.
    #[must_use]
    pub fn heartbeat_profile(&self) -> Option<HeartbeatProfile> {
        self.profiler
            .as_ref()
            .map(|p| p.borrow().report(self.heartbeat_limit, 10))
    }

    // ── Tactic scope attribution (#3399 Phase A) ──────────────────────

    /// Push a tactic-name scope onto the profiler.
    ///
    /// Heartbeat ticks recorded while this scope is active will be
    /// attributed to the tactic, in the per-tactic breakdown of the
    /// profile report. Each push is counted as one invocation.
    ///
    /// No-op when the profiler is disabled. Paired pushes/pops are
    /// tolerated on panic unwind because pop is infallible — elab
    /// layers should still use an RAII guard to guarantee balance.
    #[inline]
    pub fn push_tactic_scope(&self, tactic: &str) {
        if let Some(ref profiler) = self.profiler {
            profiler.borrow().push_tactic(tactic);
        }
    }

    /// Pop the innermost tactic scope pushed by `push_tactic_scope`.
    ///
    /// No-op when the profiler is disabled or when the tactic stack is
    /// already empty.
    #[inline]
    pub fn pop_tactic_scope(&self) {
        if let Some(ref profiler) = self.profiler {
            profiler.borrow().pop_tactic();
        }
    }

    /// Push a source-position scope onto the profiler.
    ///
    /// Heartbeat ticks recorded while this scope is active will be
    /// attributed to the position in the per-position breakdown.
    ///
    /// No-op when the profiler is disabled.
    #[inline]
    pub fn push_source_pos(&self, pos: SourcePos) {
        if let Some(ref profiler) = self.profiler {
            profiler.borrow().push_position(pos);
        }
    }

    /// Pop the innermost source-position scope pushed by
    /// `push_source_pos`. No-op when the profiler is disabled or when
    /// the position stack is already empty.
    #[inline]
    pub fn pop_source_pos(&self) {
        if let Some(ref profiler) = self.profiler {
            profiler.borrow().pop_position();
        }
    }
}
