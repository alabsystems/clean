// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Weak-head normal form (WHNF) reduction.
//!
//! Contains a single parameterized WHNF core (`whnf_core_inner`) that replaces
//! three near-identical implementations (`whnf_core`, `whnf_core_no_delta`,
//! `whnf_with_transparency_inner`). See #1481 for consolidation rationale.
//!
//! Entry points:
//! - `whnf` — full WHNF with delta reduction (cached)
//! - `whnf_core_no_delta` — WHNF without constant unfolding
//! - `whnf_with_transparency` — WHNF with transparency mode control
//! - `reduce_proj_with_mode` — shared projection reduction helper parameterized by `WhnfMode`

use crate::env::TransparencyMode;
use crate::expr::{stack_safe, Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;
#[cfg(test)]
use std::cell::Cell;

#[cfg(test)]
thread_local! {
    static WHNF_IMPL_CALL_COUNT: Cell<u64> = const { Cell::new(0) };
}

/// Controls how WHNF reduction handles delta (constant unfolding) and projection.
///
/// Consolidates the three prior WHNF implementations into a single parameterized
/// core function. Each variant preserves the exact semantics of its predecessor.
///
/// Lean 4 reference: `type_checker.cpp` `whnf_core(e, use_delta, cheap_proj)`
#[derive(Clone, Copy)]
pub(super) enum WhnfMode {
    /// Full delta at Default transparency.
    /// Projection recursion goes through `whnf_impl` (cached).
    /// Previously: `whnf_core`.
    Full,
    /// No delta reduction with cheap projection recursion.
    /// Used by `is_def_eq_core` Phase 1 and `lazy_delta_reduction`.
    /// Previously: `whnf_core_no_delta(_, cheap_proj=true)`.
    NoDeltaCheapProj,
    /// No delta reduction with full no-delta projection recursion.
    /// Used by `is_def_eq_core` Phase 5.
    /// Previously: `whnf_core_no_delta(_, cheap_proj=false)`.
    NoDeltaFullProj,
    /// Delta at caller-specified transparency.
    /// Previously: `whnf_with_transparency_inner`.
    WithTransparency(TransparencyMode),
}

/// Outcome of one head-reduction step in the [`TypeChecker::whnf_core_inner`]
/// trampoline: either the term is already in WHNF (`Done`) or it head-reduced to
/// a new term that must be reduced further (`Continue`). Returning this from a
/// borrow-confined helper lets the loop rebind its current term without growing
/// the native stack (the #20 deep-recheck iterative-WHNF fix).
enum WhnfStepResult {
    /// Term is in weak-head normal form; stop and return it.
    Done(Expr),
    /// Term head-reduced; continue the trampoline on this new term.
    Continue(Expr),
}

impl WhnfMode {
    /// Whether iota/quotient reduction should use full WHNF (including delta) on the
    /// recursor major premise and quotient lift argument.
    ///
    /// Lean 4 reference: `type_checker.cpp:340` — `reduce_recursor` passes:
    ///   `cheap_rec ? whnf_core(e, cheap_rec, cheap_proj) : whnf(e)`
    ///
    /// clean's NoDelta modes correspond to Lean 4's `whnf_core(e, cheap_rec=false,
    /// cheap_proj=true/false)`, NOT `cheap_rec=true`. With `cheap_rec=false`, the
    /// major premise gets **full whnf** (including delta). Only the hypothetical
    /// `cheap_rec=true` mode (not currently used in clean) would restrict the major
    /// premise to no-delta WHNF.
    ///
    /// Similarly, Lean 4's `quot_reduce_rec` (line 335) always uses full `whnf`,
    /// regardless of `cheap_rec`.
    ///
    /// See #1484 for the parity analysis.
    fn use_delta_for_iota(self) -> bool {
        // All current modes use full whnf on the major premise.
        // A future CheapRec mode would return false here.
        true
    }
}

impl<'env> TypeChecker<'env> {
    #[cfg(test)]
    pub(super) fn reset_whnf_impl_call_count_for_tests(&self) {
        WHNF_IMPL_CALL_COUNT.with(|count| count.set(0));
    }

    #[cfg(test)]
    pub(super) fn whnf_impl_call_count_for_tests(&self) -> u64 {
        WHNF_IMPL_CALL_COUNT.with(Cell::get)
    }

    /// Compute weak-head normal form
    ///
    /// WHNF reduces an expression to a form where the head is not a reducible redex.
    /// This includes beta reduction (for lambdas), delta reduction (for definitions),
    /// zeta reduction (for let bindings), and iota reduction (for recursors).
    ///
    /// # Contract
    ///
    /// REQUIRES: All FVars in `e` are defined in `self.ctx`
    /// REQUIRES: All Consts in `e` are defined in `self.env`
    ///
    /// ENSURES: Result is in weak-head normal form (no head redex)
    /// ENSURES: `is_def_eq(e, result)` holds (definitional equality preserved)
    /// ENSURES: `whnf(result) == result` (idempotent - verified in debug builds)
    /// ENSURES: Terminates for well-typed input (recursion bounded by expr structure)
    ///
    /// # Properties
    ///
    /// - **Idempotent**: `whnf(whnf(e)) == whnf(e)` (enforced by debug assertion)
    /// - **Meaning-preserving**: `is_def_eq(e, whnf(e))` for all well-typed `e`
    pub fn whnf(&self, e: &Expr) -> Expr {
        // No stack_safe here — whnf_impl already wraps its inner call
        // in stack_safe, and all recursive paths go through whnf_impl.
        self.whnf_impl(e)
    }

    /// Implementation of WHNF (called via stacker::maybe_grow).
    ///
    /// Every recursive call goes through `stack_safe` to prevent stack overflow
    /// on deeply nested expressions. See #1455.
    pub(super) fn whnf_impl(&self, e: &Expr) -> Expr {
        // Lean 4 parity: skip cache/whnf_core for kinds that are already in WHNF.
        // Reference: type_checker.cpp:639-656 — whnf() returns immediately for
        // BVar, Sort, MVar, Pi, Lit, Lambda, and non-let FVar.
        // This avoids cache lookup overhead for the ~40% of whnf calls on
        // already-normal expressions (Pi chains in telescopes, literal types).
        // Part of #3210.
        //
        // The heartbeat tick comes AFTER these early returns — Lean parity:
        // `check_system` runs only when whnf does real work, never on the
        // already-normal early returns above it. Ticking before the match
        // burned ~65% of the 2M budget on no-op calls (1.3M of the
        // Lean.Omega.tidy_sat ticks were Pi-type early returns from quick
        // inference) — the 2026-06-12 kernel performance-parity fix.
        match &e.kind {
            ExprKind::Sort(_)
            | ExprKind::Pi(..)
            | ExprKind::Lam(..)
            | ExprKind::Lit(_)
            | ExprKind::BVar(_) => return e.clone(),
            ExprKind::FVar(id) => {
                // Only skip for non-let FVars (FVars without a value in context).
                // Let-FVars need zeta reduction.
                let is_let = self
                    .ctx
                    .borrow()
                    .get(*id)
                    .and_then(|d| d.value.clone())
                    .is_some();
                if !is_let {
                    return e.clone();
                }
            }
            _ => {}
        }

        // Lean parity: a whnf CACHE HIT is O(1) no-op work, so `check_system`
        // must NOT tick on it (Lean checks its whnf cache before entering
        // `whnf_core`/`check_system`). Ticking before the cache check burned the
        // deterministic heartbeat on the MILLIONS of cache-hit re-visits that a
        // super-linear def-eq traversal of a carrier proof performs — e.g.
        // `Init.Data.Char.Ordinal` `_proof_*`: ~2M whnf calls but only ~6K real
        // reductions (measured via `reduction-stats`), the entire PERF class.
        // Peek here and return the hit WITHOUT ticking; only genuine
        // cache-missing work below consumes budget. VERDICT-NEUTRAL: returns the
        // identical cached value, only changes tick accounting (a resource
        // bound — can never accept a non-def-eq term, only avoid a spurious
        // timeout on cheap repeated lookups).
        if let Some(cached) = self.whnf_cache.borrow_mut().get(e) {
            return cached;
        }

        self.inc_heartbeat();
        // Early bail: if heartbeat counter is exhausted, return unreduced.
        // This is sound — returning a less-reduced expression preserves
        // definitional equality. The heartbeat error will surface at the
        // next `tick_heartbeat()` call in `infer_type`.
        if self.heartbeat_exhausted() {
            return e.clone();
        }

        #[cfg(test)]
        WHNF_IMPL_CALL_COUNT.with(|count| count.set(count.get().saturating_add(1)));
        stack_safe(|| self.whnf_inner(e))
    }

    /// Inner WHNF implementation with caching and the outer delta loop.
    ///
    /// Matches Lean 4's `whnf()` structure (type_checker.cpp:659-681):
    /// ```text
    /// while (true) {
    ///     t1 = whnf_core(t);           // beta/iota/zeta/proj, NO delta
    ///     if (reduce_native(t1)) ...   // try native reducer
    ///     else if (reduce_nat(t1)) ... // try nat arithmetic
    ///     else if (unfold_definition(t1)) { t = *next; } // delta + loop
    ///     else { return t1; }          // done
    /// }
    /// ```
    ///
    /// This loop structure ensures `reduce_nat` and `reduce_native` fire after
    /// every delta step, not just on the initial expression. Without this,
    /// chains like `HPow.hPow → instHPow → instPowNat → Nat.pow` require
    /// multiple delta steps before `reduce_nat` sees `Nat.pow(2, 32)`, and
    /// each intermediate step wastes heartbeat budget. Part of #3210.
    fn whnf_inner(&self, e: &Expr) -> Expr {
        // Check cache first (borrow_mut for SlidingCache promotion on hit)
        if let Some(cached) = self.whnf_cache.borrow_mut().get(e) {
            #[cfg(feature = "debug-whnf")]
            eprintln!("[whnf_impl] cache hit: {:?}", e);
            #[cfg(feature = "reduction-stats")]
            crate::tc::reduction_stats::record_whnf_cache(true, None);
            return cached;
        }
        #[cfg(feature = "reduction-stats")]
        {
            let head = e.get_app_fn();
            let head_name = match head.kind() {
                ExprKind::Const(name, _) => Some(name),
                _ => None,
            };
            crate::tc::reduction_stats::record_whnf_cache(false, head_name);
        }

        #[cfg(feature = "debug-whnf")]
        eprintln!("[whnf_impl] start: {:?}", e);

        let result = self.whnf_outer_loop(e);

        #[cfg(feature = "debug-whnf")]
        if &result != e {
            eprintln!("[whnf_impl] reduced to: {:?}", result);
        }

        // Idempotency check: WHNF applied twice must yield the same result.
        // Gated behind "debug-whnf" feature (not debug_assertions) because the
        // redundant whnf_core call doubles WHNF cost for every test invocation.
        // See #1389.
        #[cfg(feature = "debug-whnf")]
        {
            let result2 = self.whnf_outer_loop(&result);
            assert!(
                result == result2,
                "WHNF not idempotent!\nInput: {e:?}\nFirst WHNF: {result:?}\nSecond WHNF: {result2:?}"
            );
        }

        // Cache all WHNF results including identity — prevents O(n^2+) re-traversal
        // on stuck app chains (axiom/opaque head). Matches Lean 4. See #1584.
        // Sliding window eviction retains hot entries across trim cycles (#2410).
        {
            let mut cache = self.whnf_cache.borrow_mut();
            cache.trim_if_needed(self.max_cache_entries);
            cache.insert(e.clone(), result.clone());
        }

        result
    }

    /// Core WHNF implementation — full delta at Default transparency.
    ///
    /// Delegates to the shared `whnf_core_inner` with `WhnfMode::Full`.
    #[cfg(test)]
    pub(super) fn whnf_core(&self, e: &Expr) -> Expr {
        self.whnf_core_inner(e, WhnfMode::Full)
    }

    /// Elaboration-time reducibility gate (gap-sweep bricks B14 + B15).
    ///
    /// Returns `true` when the head constant `name` must NOT delta-unfold at the
    /// active transparency, matching MetaM's `canUnfold`. Returns `false` (never
    /// blocks) when the opt-in `honor_reducibility` flag is off, so the trusted
    /// kernel path stays transparency-blind and bit-identical.
    ///
    /// Per-mode policy (only consulted when `honor_reducibility` is on):
    /// - `All`: never blocks (everything unfolds, incl. `@[irreducible]`).
    /// - `Default`/`Instances` (B14): only `@[irreducible]` is gated;
    ///   `Regular`/`@[reducible]`/theorem heads keep their pre-B14 unfolding, so
    ///   ordinary def-eq/WHNF completeness is preserved.
    /// - `Reducible` (B15 — simp/`withReducible`): only `@[reducible]`
    ///   (abbreviation) heads unfold; `Regular` (semireducible), `@[irreducible]`,
    ///   and `Opaque` (theorem) heads stay folded. This is the transparency
    ///   `simp` uses when matching lemma LHSs and closing reflexivity goals, so a
    ///   bare `def f := e` (semireducible) is opaque to simp — `f = e := by simp`
    ///   reports "no progress" instead of silently unfolding `f`.
    ///
    /// Strictly narrowing: the only new blocking is at `Reducible` transparency,
    /// which no pre-B15 path uses.
    pub(in crate::tc) fn reducibility_gate_blocks(&self, name: &Name) -> bool {
        if !self.honors_reducibility() {
            return false;
        }
        match self.transparency() {
            TransparencyMode::All => false,
            TransparencyMode::Reducible => self
                .env
                .get_const(name)
                .is_some_and(|info| !info.reducibility.should_unfold(TransparencyMode::Reducible)),
            // Default / Instances: preserve the B14 behavior exactly (Irreducible
            // only) so the existing honor-reducibility callers are unchanged.
            TransparencyMode::Default | TransparencyMode::Instances => self
                .env
                .get_const(name)
                .is_some_and(|info| info.reducibility == crate::env::Reducibility::Irreducible),
        }
    }

    /// Partial WHNF without delta reduction, parameterized by projection mode.
    ///
    /// Performs beta, zeta, iota, quotient, and projection reduction but skips
    /// direct constant unfolding (`ExprKind::Const` returns as-is).
    ///
    /// - `cheap_proj=true`: Projection reduction uses this same no-delta WHNF on
    ///   struct expressions. Matches Lean 4 `whnf_core(e, false, true)`.
    ///   Used by `is_def_eq_core` Phase 1 and `lazy_delta_reduction`.
    /// - `cheap_proj=false`: Projection reduction uses this same no-delta WHNF
    ///   (with `cheap_proj=false`) on struct expressions. Matches Lean 4
    ///   `whnf_core(e, false, false)` without `unfold_definition`.
    ///   Used by `is_def_eq_core` Phase 5.
    pub(super) fn whnf_core_no_delta(&self, e: &Expr, cheap_proj: bool) -> Expr {
        // Cache read is unconditional — matches Lean 4 m_whnf_core behavior.
        // Cheap-mode calls benefit from full-mode cached results since full
        // reduction is strictly more reduced (safe to reuse). Part of #1768.
        if let Some(cached) = self.whnf_core_cache.borrow_mut().get(e) {
            return cached;
        }

        let mode = if cheap_proj {
            WhnfMode::NoDeltaCheapProj
        } else {
            WhnfMode::NoDeltaFullProj
        };
        let result = stack_safe(|| self.whnf_core_inner(e, mode));

        // Cache write only when cheap_proj=false (full projection mode) —
        // matches Lean 4 `!cheap_rec && !cheap_proj` guard. clean always
        // uses cheap_rec=false, so only cheap_proj matters.
        if !cheap_proj {
            let mut cache = self.whnf_core_cache.borrow_mut();
            cache.trim_if_needed(self.max_cache_entries);
            cache.insert(e.clone(), result.clone());
        }

        result
    }

    /// Reduce to weak head normal form with transparency control.
    ///
    /// This is the **elaboration-style** WHNF entry point. Unlike the kernel
    /// type-checker's [`whnf`](Self::whnf) — which always unfolds every
    /// definition/theorem that has a value (only `Opaque` is blocked) so that
    /// definitional equality stays *complete* — this variant honors the Lean 4
    /// reducibility hints (`@[reducible]`/`@[semireducible]`/`@[irreducible]`)
    /// bridged from `.olean`, which are an elaboration-time transparency
    /// concern, NOT a kernel-soundness property:
    /// - `Reducible`: only unfold `@[reducible]` definitions
    /// - `Instances`: reducible + typeclass instances
    /// - `Default`: most definitions except `@[irreducible]`
    /// - `All`: everything including `@[irreducible]` (matches kernel `whnf`)
    ///
    /// Use this for elaborator def-eq / unification and tactic rule matching
    /// (e.g. aesop, simp), where `@[irreducible]` defs should stay folded. The
    /// kernel's final type-checking def-eq must keep using [`whnf`](Self::whnf)
    /// (full delta) so it never incompletely rejects a valid proof.
    ///
    /// # Contract
    ///
    /// REQUIRES: All FVars in `e` are defined in `self.ctx`
    /// REQUIRES: All Consts in `e` are defined in `self.env`
    ///
    /// ENSURES: Result is in weak-head normal form (no head redex respecting `mode`)
    /// ENSURES: `is_def_eq(e, result)` holds (definitional equality preserved)
    /// ENSURES: Only unfolds definitions permitted by `mode`
    pub fn whnf_with_transparency(&self, e: &Expr, mode: TransparencyMode) -> Expr {
        // No stack_safe here — whnf_recurse (called by whnf_core_inner) already
        // wraps WithTransparency recursion in stack_safe.
        self.whnf_with_transparency_impl(e, mode)
    }

    /// Implementation of whnf_with_transparency.
    ///
    /// Callers (`whnf_with_transparency`, `whnf_recurse`) wrap this in `stack_safe`.
    /// Direct callers from reduction functions are already within a stack_safe boundary.
    pub(super) fn whnf_with_transparency_impl(&self, e: &Expr, mode: TransparencyMode) -> Expr {
        self.whnf_core_inner(e, WhnfMode::WithTransparency(mode))
    }

    /// Unified WHNF core replacing three near-identical match blocks. See #1481.
    pub(super) fn whnf_core_inner(&self, e: &Expr, mode: WhnfMode) -> Expr {
        // ITERATIVE WHNF TRAMPOLINE (#20 deep-recheck).
        //
        // The tail-position continuations of head reduction — `return
        // self.whnf_recurse(&reduced, mode)` after a beta/iota/delta/zeta/native
        // step — used to RE-ENTER `whnf_core_inner` via native (stacker-grown)
        // recursion. For a tail-recursive computational fold like the resolution
        // checker `checkRefutes3` (a `List.rec` over the refutation steps whose
        // cons case tail-calls the recursive `ih` once `checkStep3` succeeds),
        // that built O(steps) native frames and stack-overflowed past ~6.7k steps
        // (the live add@32 / eq@32 obligations are 9.7k–11.2k steps).
        //
        // This loop trampolines those tail continuations: a head-reduction step
        // rebinds the local `t` and `continue`s instead of recursing. SUB-term
        // reductions (the application head `f0`, projection inner, etc.) stay
        // recursive — their depth is bounded by term STRUCTURE, not by fold
        // length. The reduction RESULT is bit-identical (same WHNF fixpoint); this
        // is a pure evaluation-strategy change with ZERO soundness effect.
        let mut t_owned: Expr;
        let mut t: &Expr = e;
        loop {
            let step = match &t.kind {
                ExprKind::App(..) => {
                    let e = t;
                    // Pre-check: try Nat/native reduction on the full expression BEFORE
                    // delta-unfolding the function head. Functions like Nat.add/mul/pow
                    // have definition bodies (Regular reducibility), so WHNF would unfold
                    // them to lambdas and beta-reduce recursively. For Nat.pow(2, 32),
                    // that means ~2^33 iota reduction steps through Nat.rec. The pre-check
                    // gives O(1) reduction on literal arguments instead.
                    //
                    // Only fire when the head is a visible Const (not yet reduced).
                    // Reference: Lean 4 type_checker.cpp reduce_nat / reduce_native —
                    // these fire in the App else-branch when the head stays as Const
                    // (i.e., NoDelta mode). In Full mode, the head unfolds to a lambda,
                    // making reduce_nat/reduce_native unreachable. This pre-check closes
                    // that gap. Part of #3134.
                    // Resolve the spine head once and reuse it below (`e` is not
                    // mutated in between), instead of walking the application spine a
                    // second time at the `whnf_recurse(f0, ..)` call.
                    let f0 = e.get_app_fn();
                    if let ExprKind::Const(name, _) = f0.kind() {
                        // Encoded Glue / unglue redex (Const/App over reserved
                        // heads). Cubical-only: classical envs short-circuit on the
                        // single mode compare and never run the name checks, so the
                        // hot path is unaffected. The reduction is keyed on the
                        // reserved `Glue`/`unglue` names + arity and is stuck by
                        // default, so it only ever rewrites genuine encodings.
                        let glue = if self.mode.has_cubical_layer() {
                            // Cubical layer (Cubical, or Directed via the 2LTT
                            // bridge): encoded Glue/unglue, an interval-connection
                            // redex (I.min/I.max/I.neg), OR the Σ-iota
                            // (Sigma.elim … (Sigma.mk …)). All are keyed on reserved
                            // heads + arity and stuck by default, so they only ever
                            // rewrite genuine encodings.
                            let cube = self
                                .try_glue_reduction(e, name, mode)
                                .or_else(|| self.try_interval_connection_reduction(e, name, mode))
                                .or_else(|| self.try_sigma_reduction(e, name, mode));
                            // Additionally, in Directed mode try the directed (Rung
                            // 2) redexes over reserved `Dir.*` heads: the order
                            // decision `Dir.le i j` and the extension/hom eliminator
                            // `Dir.homApp` (β + boundary). These stay Directed-only
                            // (NOT in plain Cubical mode), keyed on the reserved
                            // heads + arity, stuck by default — cleanly separate from
                            // the cubical machinery (different heads). The cubical
                            // reductions cannot fire on `Dir.*` heads and vice versa,
                            // so the `.or_else` order is immaterial.
                            if cube.is_some() {
                                cube
                            } else if self.mode == crate::mode::CleanMode::Directed {
                                self.try_directed_reduction(e, name, mode)
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        if let Some(reduced) = glue {
                            WhnfStepResult::Continue(reduced)
                        } else if let Some(reduced) = self.reduce_nat(e) {
                            WhnfStepResult::Continue(reduced)
                        } else if let Some(reduced) = self.reduce_native(e) {
                            WhnfStepResult::Continue(reduced)
                        } else if self.native_nat_binop_grind_stuck(name, e) {
                            // PERF-CLASS GUARD (carrier tower). `reduce_nat` just
                            // declined (an operand is symbolic) but the recursion
                            // count is a large closed literal: delta-unfolding this
                            // native Nat op would iota-grind `Nat.rec` Θ(count)
                            // steps (e.g. `Nat.sub m 2^31`). Leave it STUCK — the
                            // stuck form is def-eq to the unfolded form, so this
                            // strictly narrows reduction (never a wrong ACCEPT) and
                            // matches Lean, whose def-eq never forces this unary
                            // unfolding. See `native_nat_binop_grind_stuck`.
                            WhnfStepResult::Done(t.clone())
                        } else {
                            #[cfg(feature = "reduction-stats")]
                            crate::tc::reduction_stats::record_binop_unfold(name, e);
                            Self::beta_or_iota_step(self, e, f0, mode)
                        }
                    } else {
                        Self::beta_or_iota_step(self, e, f0, mode)
                    }
                }
                ExprKind::Let(_, _, val, body, _) => {
                    WhnfStepResult::Continue(body.instantiate(val))
                }
                ExprKind::Const(name, levels) => {
                    // Delta-unfold the head constant, then loop (tail continuation),
                    // matching the old `whnf_reduce_const` -> `whnf_recurse` tail call
                    // without growing the native stack.
                    match mode {
                        WhnfMode::NoDeltaCheapProj | WhnfMode::NoDeltaFullProj => {
                            WhnfStepResult::Done(t.clone())
                        }
                        WhnfMode::Full => {
                            // B14 elaboration-time gate: an `@[irreducible]` head
                            // stays folded when the opt-in flag is on (elaborator/
                            // unifier). Off by default → transparency-blind kernel
                            // path unchanged.
                            if self.reducibility_gate_blocks(name) {
                                WhnfStepResult::Done(t.clone())
                            } else {
                                match self.unfold_definition_cached(t) {
                                    Some(val) => WhnfStepResult::Continue(val),
                                    None => WhnfStepResult::Done(t.clone()),
                                }
                            }
                        }
                        WhnfMode::WithTransparency(tm) => {
                            match self.env.unfold_with_transparency(name, levels, tm) {
                                Some(val) => WhnfStepResult::Continue(val),
                                None => WhnfStepResult::Done(t.clone()),
                            }
                        }
                    }
                }
                ExprKind::FVar(id) => {
                    let val_opt = self.ctx.borrow().get(*id).and_then(|d| d.value.clone());
                    match val_opt {
                        Some(val) => WhnfStepResult::Continue(val),
                        None => WhnfStepResult::Done(t.clone()),
                    }
                }
                ExprKind::Proj(struct_name, idx, expr) => {
                    WhnfStepResult::Done(self.whnf_reduce_proj(struct_name, *idx, expr, mode))
                }
                ExprKind::MData(_, inner) => WhnfStepResult::Continue(inner.as_ref().clone()),
                // Cubical path-beta: `(<i> e) @ r` head-reduces to `e[r/i]`.
                // The interval binder shares the ordinary de Bruijn space (see
                // `infer_cubical.rs`, which opens it via `open_bvar` and
                // instantiates endpoints with `instantiate`), so the reduction
                // is exactly `body.instantiate(arg)` — no separate interval
                // substitution machinery. Stuck (Done) when the path head does
                // not reduce to a literal path-lam (e.g. a neutral variable),
                // matching how the kernel leaves typed eliminations stuck in
                // untyped WHNF.
                ExprKind::CubicalPathApp { path, arg } => {
                    match self.try_path_beta_step(path, arg, mode) {
                        Some(reduced) => WhnfStepResult::Continue(reduced),
                        None => WhnfStepResult::Done(t.clone()),
                    }
                }
                // Kan generalized coercion: `coe (λ i. A) r s base` reduces per
                // the type-family line `A` (degenerate `r ≡ s`, constant family,
                // Pi). Interval-dependent Sigma/Path and neutral heads stay
                // stuck. See `reduction/kan.rs`.
                ExprKind::CubicalCoe { .. } => match self.try_coe_reduction(t, mode) {
                    Some(reduced) => WhnfStepResult::Continue(reduced),
                    None => WhnfStepResult::Done(t.clone()),
                },
                // Kan transport delegates to `coe^{i0→i1}` (in `reduction/kan.rs`);
                // fires only when the coercion makes progress, else stays stuck.
                ExprKind::CubicalTransp { .. } => match self.try_transp_reduction(t, mode) {
                    Some(reduced) => WhnfStepResult::Continue(reduced),
                    None => WhnfStepResult::Done(t.clone()),
                },
                // Kan homogeneous composition: fires the total-cofibration rule
                // (`hcomp {A} {⊤} u base ↝ u i1`); other cofibrations stay stuck.
                ExprKind::CubicalHComp { .. } => match self.try_hcomp_reduction(t, mode) {
                    Some(reduced) => WhnfStepResult::Continue(reduced),
                    None => WhnfStepResult::Done(t.clone()),
                },
                _ => WhnfStepResult::Done(t.clone()),
            };
            match step {
                WhnfStepResult::Done(result) => return result,
                WhnfStepResult::Continue(next) => {
                    t_owned = next;
                    t = &t_owned;
                }
            }
        }
    }

    /// One path-beta head-reduction step for `CubicalPathApp { path, arg }`.
    ///
    /// WHNFs the `path` head; if it reduces to a literal `CubicalPathLam`, the
    /// path application `(<i> body) @ arg` reduces to `body[arg/i]`, which is
    /// exactly `body.instantiate(arg)` because the path-lambda's interval binder
    /// occupies the ordinary de Bruijn slot 0 of `body`. Returns `None` (stuck)
    /// for a neutral path head; endpoint reduction of a neutral path (`p @ i0`)
    /// needs the path's type and is therefore deferred to the typed/Kan-aware
    /// conversion layer rather than untyped WHNF.
    fn try_path_beta_step(&self, path: &Expr, arg: &Expr, mode: WhnfMode) -> Option<Expr> {
        let path_whnf = self.whnf_recurse(path, mode);
        if let ExprKind::CubicalPathLam { body } = path_whnf.kind() {
            Some(body.instantiate(arg))
        } else {
            None
        }
    }

    /// One beta-or-iota head-reduction step for an `App` whose Nat/native
    /// pre-check did not fire. Factored out of [`Self::whnf_core_inner`]'s loop
    /// body so the spine-arg borrows are confined to this call and released
    /// before the trampoline rebinds its current term. Returns the next term to
    /// continue reducing, or the stuck WHNF.
    fn beta_or_iota_step(&self, e: &Expr, f0: &Expr, mode: WhnfMode) -> WhnfStepResult {
        // Multi-argument beta reduction (Lean 4 parity).
        //
        // Instead of recursively entering whnf_core_inner for each App layer
        // (which costs O(N) recursive calls for N-argument applications), we:
        // 1. Collect ALL arguments into a flat buffer
        // 2. WHNF just the head function
        // 3. Peel off as many lambdas as possible, matching with args
        // 4. Instantiate all matched args at once via instantiate_rev
        //
        // Reference: Lean 4 type_checker.cpp:443-471
        // Part of #3210.
        let f = self.whnf_recurse(f0, mode);
        if f.is_lam() {
            // Collect the spine args only in the branches that consume them.
            // The dominant stuck case below (`f == *f0`) never reads `args`,
            // so this avoids an O(spine) walk + SmallVec collect per WHNF on
            // every head-normal application. `e` is unchanged ⇒ identical args.
            let args = e.get_app_args();
            // Count how many nested lambdas we can consume
            let num_args = args.len();
            let mut body = &f;
            let mut m = 0usize;
            while let ExprKind::Lam(_, _, inner_body) = &body.kind {
                m += 1;
                if m >= num_args {
                    break;
                }
                body = inner_body;
            }
            // body is now the innermost lambda body, m = number of lambdas consumed
            // Extract the actual body (unwrap the last Lam)
            let inner_body = if let ExprKind::Lam(_, _, b) = &body.kind {
                b.as_ref()
            } else {
                // m was incremented past available lambdas — shouldn't happen
                // but handle gracefully
                body
            };

            // Build the substitution values: args[num_args-m .. num_args] in reverse
            // BVar(0) = args[num_args - m] (first consumed arg)
            // BVar(m-1) = args[num_args - 1] (last consumed arg)
            // But actually: we consumed the FIRST m args (args[0..m]).
            // The lambda telescope is: λ x₀. λ x₁. ... λ xₘ₋₁. body
            // args[0] corresponds to x₀ = BVar(m-1) in body
            // args[1] corresponds to x₁ = BVar(m-2) in body
            // args[m-1] corresponds to xₘ₋₁ = BVar(0) in body
            // So vals[i] = args[m-1-i] for BVar(i)
            let mut vals: smallvec::SmallVec<[Expr; 8]> = smallvec::SmallVec::with_capacity(m);
            for i in 0..m {
                vals.push(args[m - 1 - i].clone());
            }

            let mut reduced = inner_body.instantiate_rev(&vals);

            // Apply remaining args (if any) that weren't consumed by lambdas
            for arg in &args[m..] {
                reduced = Expr::app(reduced, (*arg).clone());
            }

            // PERF-CLASS GUARD (carrier tower) — projection-spine bypass.
            // If this head-unfold+beta just materialized a native-Nat grind
            // recursor `Nat.rec (fun _ => Nat) <symbolic> (succ/pred-seed)
            // <large-closed-literal>` — e.g. `Nat.add (UInt32.toNat (Char.val
            // c)) (UInt32.toNat ('A'.val - 'a'.val))` reached via the
            // `HAdd.hAdd` instance projection, which the head-keyed
            // `native_nat_binop_grind_stuck` pre-check cannot see — leave the
            // pre-beta application STUCK instead of grinding Θ(count) unary
            // `Nat.rec` steps. Sound: the stuck app is def-eq to the ι-normal
            // form, so this strictly narrows reduction (never a wrong ACCEPT)
            // and matches Lean's stuck-`@[extern]` `Nat.add`. Both sides of the
            // congruent carrier comparison are left in the same stuck form, so
            // def-eq closes them structurally. See
            // `native_nat_grind_recursor_stuck`.
            if self.native_nat_grind_recursor_stuck(&reduced) {
                return WhnfStepResult::Done(e.clone());
            }

            WhnfStepResult::Continue(reduced)
        } else {
            // Head didn't reduce to a lambda — rebuild App and try iota/quot/nat/native
            let app_with_whnf = if f == *f0 {
                e.clone()
            } else {
                // Rebuild application with reduced head (args needed only here).
                let args = e.get_app_args();
                let mut result = f;
                for arg in &args {
                    result = Expr::app(result, (*arg).clone());
                }
                result
            };
            let use_delta = mode.use_delta_for_iota();
            if let Some(reduced) = self.try_iota_reduction(&app_with_whnf, use_delta) {
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.try_quot_reduction(&app_with_whnf, use_delta) {
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.reduce_nat(&app_with_whnf) {
                // Nat literal arithmetic reduction (Lean 4: type_checker.cpp reduce_nat).
                // Must come after iota/quot since those handle constructor-form Nats.
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.reduce_int(&app_with_whnf) {
                // Arbitrary-precision Int add/sub/mul (operands WHNF'd first).
                // See reduction::int — closes the Rat.le cross-product blowup.
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.reduce_native(&app_with_whnf) {
                // Native reducer fast-path (Lean 4: type_checker.cpp reduce_native).
                WhnfStepResult::Continue(reduced)
            } else {
                WhnfStepResult::Done(app_with_whnf)
            }
        }
    }
}
