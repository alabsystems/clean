// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TypeChecker configuration, cache management, and context operations.
//!
//! Extracted from tc/mod.rs to keep the module root focused on the struct
//! definition and core constructors.

use crate::env::TransparencyMode;
use crate::expr::{BinderData, Expr, FVarId};
use crate::mode::CleanMode;
use crate::name::Name;
use std::hash::{Hash, Hasher};

use super::expr_location::ExprLocation;
use super::sliding_equiv_manager::SlidingEquivManager;
use super::{
    LocalContext, TcCaches, TypeChecker, DEFAULT_HEARTBEAT_LIMIT, DEFAULT_MAX_CACHE_ENTRIES,
};
use std::cell::{Cell, RefCell};

impl<'env> TypeChecker<'env> {
    /// Push a local declaration onto the context.
    ///
    /// # FVarId-unreachability invariant (#1773)
    ///
    /// No cache invalidation needed on push/pop. This is safe because of the
    /// **FVarId-unreachability invariant**: FVarIds are allocated from a
    /// monotonically increasing counter (`LocalContext::next_id`) and are
    /// never reused after `ctx_pop`. Consequently:
    ///
    /// 1. **Positive cache entries** involving pushed FVars are correct because
    ///    the FVar's meaning (type, value) is immutable once pushed.
    /// 2. **Negative cache entries** involving pushed FVars become unreachable
    ///    after pop — no future expression will contain the popped FVarId.
    /// 3. **Equiv_manager entries** follow the same reasoning.
    ///
    /// This matches Lean 4's strategy (type_checker.cpp never clears caches
    /// on push/pop). See #1411 F2, #1325.
    pub(super) fn ctx_push(&self, name: Name, ty: Expr, bi: impl Into<BinderData>) -> FVarId {
        self.ctx.borrow_mut().push(name, ty, bi)
    }

    /// Push a let-binding onto the context.
    ///
    /// No cache invalidation needed — see `ctx_push` rationale.
    pub(super) fn ctx_push_let(&self, name: Name, ty: Expr, val: Expr) -> FVarId {
        self.ctx.borrow_mut().push_let(name, ty, val)
    }

    /// Pop a local declaration from the context.
    ///
    /// No cache invalidation needed — see `ctx_push` FVarId-unreachability
    /// invariant (#1773). Popped FVarIds are never reused, so stale cache
    /// entries involving the popped FVar are unreachable: no future expression
    /// will contain the popped FVarId as a subterm.
    pub(super) fn ctx_pop(&self) {
        self.ctx.borrow_mut().pop();
    }

    /// Batch-restore context to a previous length.
    ///
    /// Used by `is_def_eq_binding` to pop all binder locals at once after
    /// iterating through a chain of consecutive same-kind binders.
    /// Same cache-safety rationale as `ctx_pop` — FVarId monotonicity (#1773).
    pub(super) fn ctx_truncate_to(&self, target_len: usize) {
        self.ctx.borrow_mut().truncate_to(target_len);
    }

    /// Current context length.
    pub(super) fn ctx_len(&self) -> usize {
        self.ctx.borrow().len()
    }

    /// Push a fresh local FVar of the given type onto the context and return
    /// its `FVarId`. Public so the elaborator's higher-order unifier can
    /// introduce a binder-local fvar when descending under a `Pi`/`Lam` body
    /// (mirroring Lean 4's `isDefEq` forallE/lambdaE path, which pushes an
    /// fvar, instantiates the bound variable, compares, and pops). The pushed
    /// fvar's type is then resolvable via `infer_type`, which the Miller-pattern
    /// solver needs to abstract it back out of a metavariable assignment.
    ///
    /// Callers MUST pair each `push_binder_local` with a `pop_binder_local`
    /// (FVarIds are never reused after pop — see `ctx_push`).
    pub fn push_binder_local(&self, name: Name, ty: Expr, bi: impl Into<BinderData>) -> FVarId {
        // Allocate in the low (non-meta-tagged) FVarId range so the elaborator
        // does not misclassify the binder local as a metavariable: meta-FVars
        // carry the `1<<63` tag bit, and registering them here can push the
        // ordinary `next_id` counter past that boundary. See
        // `LocalContext::push_low_local`.
        self.ctx.borrow_mut().push_low_local(name, ty, bi)
    }

    /// Pop the most recently pushed local declaration. Pairs with
    /// [`TypeChecker::push_binder_local`].
    pub fn pop_binder_local(&self) {
        self.ctx_pop();
    }

    // ── Expression location tracking (Part of #3425) ──────────────────

    /// Set the declaration name for error location tracking.
    ///
    /// Called by `check_type` and `infer_sort` (validation entry points used
    /// by `add_decl`) to label the location trail with the declaration being
    /// checked. Callers that don't set this get location trails without a
    /// declaration name prefix.
    pub fn set_expr_loc_decl_name(&self, name: Name) {
        self.expr_loc.borrow_mut().decl_name = Some(name);
    }

    /// Push a location step onto the expression trail.
    ///
    /// Called before descending into a sub-expression during type inference.
    /// Must be paired with `expr_loc_pop` after the recursive call returns.
    ///
    /// Borrow safety: short-lived `borrow_mut()` dropped before any recursive call.
    pub(super) fn expr_loc_push(&self, step: super::expr_location::ExprPathStep) {
        self.expr_loc.borrow_mut().push(step);
    }

    /// Pop the last location step from the expression trail.
    ///
    /// Called after returning from a sub-expression during type inference.
    pub(super) fn expr_loc_pop(&self) {
        self.expr_loc.borrow_mut().pop();
    }

    /// Snapshot the current expression location for attaching to an error.
    ///
    /// Returns `None` if the location is empty (no steps and no decl name).
    pub(super) fn expr_loc_snapshot(&self) -> Option<Box<ExprLocation>> {
        self.expr_loc.borrow().snapshot()
    }

    /// Check if type checking cache is enabled.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns true iff cache was enabled via `enable_type_cache()`
    /// ENSURES: Deterministic - same state yields same result
    pub fn type_cache_enabled(&self) -> bool {
        self.type_cache.borrow().is_some()
    }

    /// Get type cache statistics, if caching is enabled.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `Some(stats)` iff `type_cache_enabled() == true`
    /// ENSURES: Returns `None` iff `type_cache_enabled() == false`
    pub fn type_cache_stats(&self) -> Option<crate::cache::TypeCheckCacheStats> {
        self.type_cache.borrow().as_ref().map(|c| c.stats().clone())
    }

    // Cache entry count accessors.

    #[must_use]
    pub fn whnf_cache_entries(&self) -> usize {
        self.whnf_cache.borrow().len()
    }
    #[must_use]
    pub fn def_eq_cache_entries(&self) -> usize {
        self.def_eq_cache.borrow().len()
    }

    /// Check if tracing is enabled.
    ///
    /// Returns true if a trace collector is set AND the collector is enabled.
    /// This allows `NullCollector` to be set while still reporting disabled.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff collector is set and reports enabled
    /// ENSURES: Returns `false` if no collector set or collector reports disabled
    pub(crate) fn tracing_enabled(&self) -> bool {
        self.trace_collector
            .as_ref()
            .map(|c| c.enabled())
            .unwrap_or(false)
    }

    /// Compute a hash representing the current environment state (#1279).
    ///
    /// Uses the environment's monotonic generation counter, which is bumped
    /// on every mutation (add_decl, add_inductive, set_reducibility, etc.).
    /// This correctly invalidates the cache even when the constant count
    /// stays the same (e.g., a remove-then-add).
    pub(super) fn compute_env_hash(&self) -> u64 {
        self.env.generation()
    }

    /// Compute a hash of the current CleanMode and infer_only state for cache keying.
    ///
    /// Includes `infer_only` because type inference results from `infer_only=true`
    /// (which skips App/Let argument validation) must not be reused when
    /// `infer_only=false` (which performs full validation). Reusing infer_only=true
    /// results during check_type would silently skip argument type checks.
    /// Part of #3224.
    #[cfg(not(kani))]
    pub(super) fn compute_mode_hash(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.mode.hash(&mut hasher);
        self.infer_only.get().hash(&mut hasher);
        hasher.finish()
    }

    /// Compute a hash of the current CleanMode and infer_only state for cache keying.
    /// Part of #3224.
    #[cfg(kani)]
    pub(super) fn compute_mode_hash(&self) -> u64 {
        use crate::expr::KaniHasher;
        let mut hasher = KaniHasher::new();
        self.mode.hash(&mut hasher);
        self.infer_only.get().hash(&mut hasher);
        hasher.finish()
    }

    /// Get the current mode
    ///
    /// # Contract
    ///
    /// ENSURES: Returns the mode set at construction or via `set_mode()`
    /// ENSURES: Deterministic - same state yields same result
    pub fn mode(&self) -> CleanMode {
        self.mode
    }

    /// Set the mode
    ///
    /// Changing the mode invalidates the type cache, WHNF cache,
    /// projection-type cache, and definitional equality cache since results
    /// may differ under different modes (e.g. Classical vs Constructive).
    ///
    /// # Contract
    ///
    /// REQUIRES: `mode` is a valid CleanMode variant
    ///
    /// ENSURES: `self.mode() == mode` after call
    /// ENSURES: If mode changed, all caches are invalidated
    pub fn set_mode(&mut self, mode: CleanMode) {
        if self.mode != mode {
            self.mode = mode;
            self.whnf_cache.borrow_mut().clear();
            self.whnf_core_cache.borrow_mut().clear();
            self.def_eq_cache.borrow_mut().clear();
            if let Some(cache) = &self.branch_sharing_cache {
                cache.borrow_mut().clear();
            }
            self.args_failure_cache.borrow_mut().clear();
            self.proj_type_cache.borrow_mut().clear();
            self.unfold_cache.borrow_mut().clear();
            self.quick_infer_cache.borrow_mut().clear();
            self.equiv_manager.borrow_mut().clear();
            // Type cache: update mode hash (triggers clear if changed)
            let mode_hash = self.compute_mode_hash();
            let mut cache_ref = self.type_cache.borrow_mut();
            if let Some(cache) = cache_ref.as_mut() {
                cache.set_mode_hash(mode_hash);
            }
        }
    }

    /// Get the current transparency mode for definition unfolding.
    ///
    /// Reference: Lean 4 `type_checker.cpp` `m_transparency_mode`.
    pub fn transparency(&self) -> TransparencyMode {
        self.transparency
    }

    /// Enable/disable the opt-in elaboration-time reducibility gate (B14).
    ///
    /// See the `honor_reducibility` field doc. Off by default, so the trusted
    /// kernel `add_decl` path (and every other kernel-internal caller) stays
    /// transparency-blind and bit-identical. The elaborator/unifier turn it on
    /// so an `@[irreducible]` definition stays folded during elaboration-time
    /// def-eq/WHNF at a non-`All` transparency (matching MetaM `canUnfold`).
    ///
    /// Takes `&self` (interior `Cell`) so it can be set on a just-built checker.
    /// Callers set it before running any reduction, so the reduction caches
    /// only ever hold results computed under a single gate setting.
    pub fn set_honor_reducibility(&self, honor: bool) {
        self.honor_reducibility.set(honor);
    }

    /// Whether the opt-in elaboration-time reducibility gate is active.
    pub fn honors_reducibility(&self) -> bool {
        self.honor_reducibility.get()
    }

    /// Create a type checker with a specific transparency mode.
    ///
    /// Used by the elaborator to control definition unfolding:
    /// - `Reducible` for instance search
    /// - `All` for tactic evaluation
    /// - `Default` for normal type checking
    ///
    /// Reference: Lean 4 `mk_type_checker` with transparency parameter.
    /// Part of #1636.
    pub fn with_transparency(
        env: &'env crate::env::Environment,
        transparency: TransparencyMode,
    ) -> Self {
        Self {
            env,
            ctx: RefCell::new(LocalContext::new()),
            mode: env.mode(),
            transparency,
            honor_reducibility: Cell::new(false),
            whnf_cache: RefCell::new(Default::default()),
            whnf_core_cache: RefCell::new(Default::default()),
            def_eq_cache: RefCell::new(Default::default()),
            branch_sharing_cache: Some(RefCell::new(Default::default())),
            type_cache: RefCell::new(None),
            infer_arc_memo: RefCell::new(Default::default()),
            infer_memo_depth: Cell::new(0),
            proj_type_cache: RefCell::new(Default::default()),
            unfold_cache: RefCell::new(Default::default()),
            quick_infer_cache: RefCell::new(Default::default()),
            trace_collector: None,
            equiv_manager: RefCell::new(SlidingEquivManager::new()),
            max_cache_entries: DEFAULT_MAX_CACHE_ENTRIES,
            level_eq_override: None,
            args_failure_cache: RefCell::new(Default::default()),
            heartbeat_counter: Cell::new(DEFAULT_HEARTBEAT_LIMIT),
            heartbeat_limit: DEFAULT_HEARTBEAT_LIMIT,
            profiler: None,
            eager_reduce: Cell::new(false),
            nat_probe_depth: Cell::new(0),
            infer_only: Cell::new(true),
            level_params: None,
            allow_unsafe: true,
            allow_partial: true,
            cumulative: false,
            #[cfg(debug_assertions)]
            in_infer_type_assert: Cell::new(false),
            cert_retained: Cell::new(false),
            expr_loc: RefCell::new(ExprLocation::new()),
        }
    }

    /// Set the transparency mode for definition unfolding.
    ///
    /// Changing transparency invalidates WHNF, def-eq, projection-type, and
    /// equiv caches since unfolding decisions differ across transparency levels.
    ///
    /// Part of #1636.
    pub fn set_transparency(&mut self, transparency: TransparencyMode) {
        if self.transparency != transparency {
            self.transparency = transparency;
            self.whnf_cache.borrow_mut().clear();
            self.whnf_core_cache.borrow_mut().clear();
            self.def_eq_cache.borrow_mut().clear();
            if let Some(cache) = &self.branch_sharing_cache {
                cache.borrow_mut().clear();
            }
            self.args_failure_cache.borrow_mut().clear();
            self.proj_type_cache.borrow_mut().clear();
            self.unfold_cache.borrow_mut().clear();
            self.quick_infer_cache.borrow_mut().clear();
            self.equiv_manager.borrow_mut().clear();
        }
    }

    /// Set a level equality override for elaborator-driven level unification.
    /// Allows the elaborator to resolve fresh universe params during kernel type inference.
    pub fn set_level_eq_override(
        &mut self,
        f: impl Fn(&crate::level::Level, &crate::level::Level) -> bool + 'env,
    ) {
        self.level_eq_override = Some(Box::new(f));
    }

    /// Compare two universe levels, delegating to the override if set.
    pub(crate) fn levels_eq(&self, l1: &crate::level::Level, l2: &crate::level::Level) -> bool {
        if let Some(ref f) = self.level_eq_override {
            f(l1, l2)
        } else {
            crate::level::Level::is_def_eq(l1, l2)
        }
    }

    /// Create a type checker with pre-populated caches from a previous session.
    ///
    /// This enables cross-call caching: create a TC, run an operation, extract
    /// caches via `take_caches`, store them, then inject into the next TC via
    /// this constructor. Caches are only valid for the same goal context
    /// (same local declarations and same environment).
    ///
    /// Part of #1671.
    pub fn with_context_and_caches(
        env: &'env crate::env::Environment,
        mut ctx: LocalContext,
        caches: TcCaches,
    ) -> Self {
        ctx.advance_next_id(caches.next_fvar_id);
        Self {
            env,
            ctx: RefCell::new(ctx),
            mode: env.mode(),
            transparency: TransparencyMode::Default,
            honor_reducibility: Cell::new(false),
            whnf_cache: RefCell::new(caches.whnf),
            whnf_core_cache: RefCell::new(caches.whnf_core),
            def_eq_cache: RefCell::new(caches.def_eq),
            branch_sharing_cache: Some(RefCell::new(Default::default())),
            type_cache: RefCell::new(None),
            infer_arc_memo: RefCell::new(Default::default()),
            infer_memo_depth: Cell::new(0),
            proj_type_cache: RefCell::new(caches.proj_type),
            unfold_cache: RefCell::new(caches.unfold),
            quick_infer_cache: RefCell::new(Default::default()),
            trace_collector: None,
            equiv_manager: RefCell::new(caches.equiv),
            max_cache_entries: DEFAULT_MAX_CACHE_ENTRIES,
            level_eq_override: None,
            args_failure_cache: RefCell::new(Default::default()),
            heartbeat_counter: Cell::new(DEFAULT_HEARTBEAT_LIMIT),
            heartbeat_limit: DEFAULT_HEARTBEAT_LIMIT,
            profiler: None,
            eager_reduce: Cell::new(false),
            nat_probe_depth: Cell::new(0),
            infer_only: Cell::new(true),
            level_params: None,
            allow_unsafe: true,
            allow_partial: true,
            cumulative: false,
            #[cfg(debug_assertions)]
            in_infer_type_assert: Cell::new(false),
            cert_retained: Cell::new(false),
            expr_loc: RefCell::new(ExprLocation::new()),
        }
    }

    /// Create a type checker with a specific mode and pre-populated caches.
    ///
    /// Combines `with_mode` and `with_context_and_caches` — avoids the cache
    /// invalidation that would occur if calling `set_mode` after construction
    /// with a different default mode.
    ///
    /// Primary use case: batch verification where the same mode applies to all
    /// expressions and caches should be shared across calls.
    ///
    /// Part of #2382.
    pub(crate) fn with_mode_and_caches(
        env: &'env crate::env::Environment,
        mode: CleanMode,
        caches: TcCaches,
    ) -> Self {
        let mut ctx = LocalContext::new();
        ctx.advance_next_id(caches.next_fvar_id);
        Self {
            env,
            ctx: RefCell::new(ctx),
            mode,
            transparency: TransparencyMode::Default,
            honor_reducibility: Cell::new(false),
            whnf_cache: RefCell::new(caches.whnf),
            whnf_core_cache: RefCell::new(caches.whnf_core),
            def_eq_cache: RefCell::new(caches.def_eq),
            branch_sharing_cache: Some(RefCell::new(Default::default())),
            type_cache: RefCell::new(None),
            infer_arc_memo: RefCell::new(Default::default()),
            infer_memo_depth: Cell::new(0),
            proj_type_cache: RefCell::new(caches.proj_type),
            unfold_cache: RefCell::new(caches.unfold),
            quick_infer_cache: RefCell::new(Default::default()),
            trace_collector: None,
            equiv_manager: RefCell::new(caches.equiv),
            max_cache_entries: DEFAULT_MAX_CACHE_ENTRIES,
            level_eq_override: None,
            args_failure_cache: RefCell::new(Default::default()),
            heartbeat_counter: Cell::new(DEFAULT_HEARTBEAT_LIMIT),
            heartbeat_limit: DEFAULT_HEARTBEAT_LIMIT,
            profiler: None,
            eager_reduce: Cell::new(false),
            nat_probe_depth: Cell::new(0),
            infer_only: Cell::new(true),
            level_params: None,
            allow_unsafe: true,
            allow_partial: true,
            cumulative: false,
            #[cfg(debug_assertions)]
            in_infer_type_assert: Cell::new(false),
            cert_retained: Cell::new(false),
            expr_loc: RefCell::new(ExprLocation::new()),
        }
    }

    /// Extract caches from this TypeChecker for later reuse.
    ///
    /// After calling this, the TypeChecker's caches are empty.
    /// Store the returned `TcCaches` and pass them to
    /// `with_context_and_caches` to reuse in the next TC instance.
    ///
    /// Part of #1671.
    pub fn take_caches(&self) -> TcCaches {
        TcCaches {
            whnf: self.whnf_cache.take(),
            whnf_core: self.whnf_core_cache.take(),
            def_eq: self.def_eq_cache.take(),
            proj_type: self.proj_type_cache.take(),
            unfold: self.unfold_cache.take(),
            equiv: self.equiv_manager.take(),
            next_fvar_id: self.ctx.borrow().next_id(),
        }
    }
}

// Two cache-control methods exposed unconditionally so external
// integration tests (`tests/release_infer_parity.rs`) and benchmark
// harnesses can toggle the type-checking cache without depending on a
// feature flag.
impl<'env> TypeChecker<'env> {
    /// Enable type checking cache (public alias for the test-only
    /// `enable_type_cache` inside `#[cfg(test)]`).
    pub fn enable_type_cache_pub(&mut self) {
        let env_hash = self.compute_env_hash();
        let mode_hash = self.compute_mode_hash();
        *self.type_cache.borrow_mut() = Some(crate::cache::TypeCheckCache::with_hashes(
            env_hash, mode_hash,
        ));
    }

    /// Disable type checking cache.
    pub fn disable_type_cache_pub(&mut self) {
        *self.type_cache.borrow_mut() = None;
    }

    /// Reset the local context to empty between independent top-level checks,
    /// WITHOUT clearing the cross-call caches (notably the type cache).
    ///
    /// # Why this exists
    ///
    /// Batch re-validation (`clean-olean`'s `typecheck_constants_full*`) reuses a
    /// single long-lived, cache-enabled `TypeChecker` across many already-registered
    /// declarations checked against one immutable `&Environment`. A successful
    /// top-level `infer_sort`/`check_type` leaves the context empty (binder
    /// push/pop is balanced), but an *erroring* check can return early via `?`
    /// before its `ctx_pop`, leaving dangling free variables in the context. That
    /// would (a) make `infer_type`'s `can_cache = ctx.is_empty()` guard false for
    /// every subsequent declaration (silently disabling reuse), and (b) leak one
    /// declaration's binders into the next check's context. Calling this between
    /// declarations restores a clean starting context.
    ///
    /// # Soundness
    ///
    /// This calls `LocalContext::truncate_to(0)`, which drops all live binders but
    /// PRESERVES the monotonic `next_id` FVarId counter and the `used_ids` reuse
    /// guard. The FVarId-unreachability invariant (#1773) therefore still holds:
    /// FVarIds are never reused, so any stale FVar-keyed cache entry (whnf, def_eq,
    /// equiv, quick-infer, infer-arc) is simply unreachable from future terms — no
    /// invalidation is required, exactly as for `ctx_pop`. The `type_cache` is keyed
    /// on closed terms plus the env/mode hash and is independent of the local
    /// context, so it stays valid across the reset; that is the whole point —
    /// cross-declaration type reuse must survive a context reset.
    ///
    /// This deliberately does NOT clear caches (unlike the test-only
    /// `local_context_mut`), because the env is fixed for the checker's lifetime
    /// and cache reuse across declarations is the intended optimization.
    pub fn reset_local_context(&self) {
        self.ctx_truncate_to(0);
    }

    /// Number of entries currently in the local context. READ-ONLY observer.
    ///
    /// Exposed so callers and tests can assert STATE NEUTRALITY: a completed
    /// `infer_type` / `check_type` must leave this exactly as it found it,
    /// including on the error path. Every binder arm pushes an FVar and pops it,
    /// so a nonzero value after a top-level call means a `?` escaped before its
    /// `ctx_pop` — the defect `reset_local_context` above was introduced to work
    /// around. Enforced by
    /// `tests/infer_error_path_state_neutrality.rs`.
    #[must_use]
    pub fn local_context_len(&self) -> usize {
        self.ctx.borrow().len()
    }

    /// Set the maximum whnf/def-eq memoization-cache size (entries).
    ///
    /// A pure PERFORMANCE knob: it changes only how much reduction is memoized,
    /// never the reduction RESULT, so it has ZERO soundness effect (an
    /// under-budget cache merely re-derives the same normal form). Exposed for
    /// reduction-heavy reflection paths — notably the `checkRefutes3`
    /// resolution-cert reduction, whose `go3`-threaded trie accumulator has a
    /// working set far above the 100k default at width ≥32; without a larger
    /// budget the growing trie thrashes the cache and the cert re-checks
    /// super-linearly. See `bv_blast_reflection::reflection_tc`.
    pub fn set_max_cache_entries(&mut self, max: usize) {
        self.max_cache_entries = max;
    }
}

// Test-only TypeChecker methods: cache observability, context mutation, tracing.
#[cfg(test)]
impl<'env> TypeChecker<'env> {
    /// Get mutable reference to the local context
    ///
    /// Note: This clears WHNF, def_eq, and projection-type caches since free
    /// variables may have different meanings after context modification.
    pub(crate) fn local_context_mut(&mut self) -> &mut LocalContext {
        self.whnf_cache.borrow_mut().clear();
        self.whnf_core_cache.borrow_mut().clear();
        self.def_eq_cache.borrow_mut().clear();
        if let Some(cache) = &self.branch_sharing_cache {
            cache.borrow_mut().clear();
        }
        self.args_failure_cache.borrow_mut().clear();
        self.proj_type_cache.borrow_mut().clear();
        self.unfold_cache.borrow_mut().clear();
        self.quick_infer_cache.borrow_mut().clear();
        self.equiv_manager.borrow_mut().clear();
        // Track WW: Arc-identity infer memo is FVar/context-sensitive; drop it on
        // wholesale context replacement alongside the other FVar-sensitive caches.
        self.infer_arc_memo.borrow_mut().clear();
        let ctx = self.ctx.get_mut();
        ctx.clear_reuse_history();
        ctx
    }

    /// Get reference to the local context
    pub(crate) fn local_context(&self) -> std::cell::Ref<'_, LocalContext> {
        self.ctx.borrow()
    }

    /// Enable type checking cache.
    pub(crate) fn enable_type_cache(&mut self) {
        let env_hash = self.compute_env_hash();
        let mode_hash = self.compute_mode_hash();
        *self.type_cache.borrow_mut() = Some(crate::cache::TypeCheckCache::with_hashes(
            env_hash, mode_hash,
        ));
    }

    /// Disable type checking cache.
    pub(crate) fn disable_type_cache(&mut self) {
        *self.type_cache.borrow_mut() = None;
    }

    #[must_use]
    pub(crate) fn whnf_core_cache_entries(&self) -> usize {
        self.whnf_core_cache.borrow().len()
    }
    /// Part of #1360.
    #[must_use]
    pub(crate) fn args_failure_cache_entries(&self) -> usize {
        self.args_failure_cache.borrow().len()
    }
    #[must_use]
    pub(crate) fn proj_type_cache_entries(&self) -> usize {
        self.proj_type_cache.borrow().len()
    }
    #[must_use]
    pub(crate) fn equiv_manager_entries(&self) -> usize {
        self.equiv_manager.borrow().len()
    }
    /// Part of #3210.
    #[must_use]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn unfold_cache_entries(&self) -> usize {
        self.unfold_cache.borrow().len()
    }

    /// Get the current maximum cache entries threshold.
    #[must_use]
    pub(crate) fn max_cache_entries(&self) -> usize {
        self.max_cache_entries
    }

    /// Set the trace collector for Phase 4 self-verification.
    pub(crate) fn set_trace_collector(
        &mut self,
        collector: Option<crate::cert::SharedTraceCollector>,
    ) {
        self.trace_collector = collector;
    }

    /// Get a reference to the current trace collector, if any.
    pub(crate) fn trace_collector(&self) -> Option<&crate::cert::SharedTraceCollector> {
        self.trace_collector.as_ref()
    }
}
