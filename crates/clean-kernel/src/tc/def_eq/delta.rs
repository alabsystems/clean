// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::expr::{Expr, LevelVec};
use crate::name::Name;
use crate::tc::def_eq::DefEqCacheKey;
use crate::tc::TypeChecker;
use std::cmp::Ordering;

/// Result of a single lazy delta reduction step.
///
/// Reference: Lean 4 `type_checker.h:72` `reduction_status` enum.
///
/// Used by `lazy_delta_reduction_step` to communicate progress to its callers:
/// `lazy_delta_reduction` (the full loop with Nat/native hooks) and
/// `lazy_delta_proj_reduction` (the projection-specific loop).
enum ReductionStatus {
    /// Made progress (unfolded something), continue looping.
    Continue,
    /// Definitively equal (same-head argument-wise match succeeded).
    DefEqual,
    /// Neither side is delta-reducible; delta is exhausted.
    DefUnknown,
    /// Definitively not equal (`quick_is_def_eq` returned `Some(false)`).
    /// Callers may still try fallback paths (e.g., `reduce_proj_core`).
    DefDiff,
}

impl<'env> TypeChecker<'env> {
    /// Lazy delta reduction loop for definitional equality (#1421).
    ///
    /// Unfolds definitions one at a time using height-based ordering, checking equality
    /// after each unfold. Returns `Ok(true/false)` when equality is determined, or
    /// `Err((t, s))` with the final partially-reduced expressions when no more delta
    /// reduction is possible.
    ///
    /// At the top of each loop iteration, checks Nat-specific optimizations before
    /// attempting delta reduction (matching Lean 4 type_checker.cpp:975-1001):
    /// 1. `is_def_eq_offset` — structural Nat successor peeling
    /// 2. `reduce_nat` — closed Nat arithmetic evaluation (only when no free variables)
    ///
    /// Returning the final expressions is critical: the caller needs them for structural
    /// comparison. Lean 4 achieves this by passing `t_n`/`s_n` by mutable reference
    /// (type_checker.cpp:1094); we return them explicitly.
    ///
    /// Reference: Lean 4 kernel type_checker.cpp:975 `lazy_delta_reduction`
    ///
    /// # Termination
    ///
    /// Each loop iteration must unfold at least one definition (delta step) or
    /// a projection via `try_unfold_proj_app`. The number of unfoldable
    /// definitions is finite, so the loop terminates for well-typed input.
    /// However, adversarial .olean files could potentially violate this
    /// assumption, so we enforce a hard iteration cap (see #1773).
    #[allow(clippy::result_large_err)] // Hot path: boxing (Expr,Expr) adds allocation overhead for no benefit
    pub(in crate::tc) fn lazy_delta_reduction(
        &self,
        a: &Expr,
        b: &Expr,
    ) -> Result<bool, (Expr, Expr)> {
        /// Maximum iterations before we conservatively return "not def-eq".
        /// Each iteration unfolds at least one definition, so 10,000 is far
        /// beyond any legitimate .olean workload (Mathlib peaks ~200 per call).
        const MAX_LAZY_DELTA_ITERATIONS: u32 = 10_000;

        let mut t = a.clone();
        let mut s = b.clone();

        let mut iterations = 0u32;

        loop {
            iterations += 1;
            #[cfg(feature = "reduction-stats")]
            crate::tc::reduction_stats::record_delta_loop_iter();
            if iterations > MAX_LAZY_DELTA_ITERATIONS {
                // Conservative: treat as not definitionally equal.
                // This prevents non-termination from adversarial inputs
                // while being safe (false negatives don't compromise soundness).
                return Ok(false);
            }
            // Nat-specific fast paths (Lean 4 type_checker.cpp:977-986).
            // These run before each delta reduction step. These hooks are
            // specific to the outer loop — `lazy_delta_proj_reduction` does
            // NOT call them (matching Lean 4's separation).

            // 1. Structural Nat successor peeling: 0 =?= 0, succ(a) =?= succ(b) → a =?= b
            if let Some(result) = self.is_def_eq_offset(&t, &s) {
                return Ok(result);
            }

            // 2. Closed Nat arithmetic reduction (only when no free variables,
            // OR when eager_reduce is active — Lean 4: type_checker.cpp:978).
            if (!t.has_fvar_quick() && !s.has_fvar_quick()) || self.eager_reduce.get() {
                if let Some(t_v) = self.reduce_nat(&t) {
                    return Ok(self.is_def_eq_impl(&t_v, &s));
                }
                if let Some(s_v) = self.reduce_nat(&s) {
                    return Ok(self.is_def_eq_impl(&t, &s_v));
                }
            }

            // 3. Native reduction hook (Lean 4 type_checker.cpp:988-991).
            // Unlike reduce_nat, this has NO fvar guard — native implementations
            // can handle any well-typed input. Currently a no-op placeholder since
            // clean does not yet support @[implemented_by]/@[extern] native reducers.
            if let Some(t_v) = self.reduce_native(&t) {
                return Ok(self.is_def_eq_impl(&t_v, &s));
            }
            if let Some(s_v) = self.reduce_native(&s) {
                return Ok(self.is_def_eq_impl(&t, &s_v));
            }

            // 4. Monadic reduction hook (Track Q). A monad-class head
            // (`Bind.bind`/`Pure.pure` over a concrete `Except`/`StateT`/`ExceptT`,
            // or the transformer binds) is an axiom: it cannot delta-unfold, so
            // `lazy_delta_step` below treats `Pure.pure …` vs `Except.ok …` as two
            // distinct stuck consts and reports DefUnknown — even though
            // `Pure.pure (Except ε) α a` IS `Except.ok ε α a` and a do-block's
            // trailing `pure x` / lane-fold bind must converge. `try_monad_reduce`
            // performs exactly those instance-unfolding rewrites; firing it here
            // (symmetrically, like the Nat/native hooks) lets the reduced side
            // re-enter def-eq. Only fires when the rewrite makes progress
            // (`reduced != side`); the kernel re-checks the produced term.
            if let Some(t_v) = self.try_monad_reduce(&t) {
                if t_v != t {
                    return Ok(self.is_def_eq_impl(&t_v, &s));
                }
            }
            if let Some(s_v) = self.try_monad_reduce(&s) {
                if s_v != s {
                    return Ok(self.is_def_eq_impl(&t, &s_v));
                }
            }

            // Perform one delta reduction step.
            // Lean 4 type_checker.cpp:993-1008 maps:
            //   Continue   → loop, DefEqual → l_true,
            //   DefUnknown → l_undef (structural comparison),
            //   DefDiff    → l_false (definitively not equal).
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[lazy_delta] iter {}: t = {}, s = {}", iterations, t, s);
            match self.lazy_delta_reduction_step(&mut t, &mut s) {
                ReductionStatus::Continue => {
                    #[cfg(feature = "debug-def-eq")]
                    eprintln!("[lazy_delta] step => Continue");
                }
                ReductionStatus::DefEqual => {
                    #[cfg(feature = "debug-def-eq")]
                    eprintln!("[lazy_delta] step => DefEqual");
                    return Ok(true);
                }
                ReductionStatus::DefUnknown => {
                    #[cfg(feature = "debug-def-eq")]
                    eprintln!(
                        "[lazy_delta] step => DefUnknown (exhausted): t = {}, s = {}",
                        t, s
                    );
                    return Err((t, s));
                }
                ReductionStatus::DefDiff => {
                    #[cfg(feature = "debug-def-eq")]
                    eprintln!("[lazy_delta] step => DefDiff");
                    return Ok(false);
                }
            }
        }
    }

    fn lazy_delta_reduction_step(&self, t: &mut Expr, s: &mut Expr) -> ReductionStatus {
        let status = match (self.get_delta_const(t), self.get_delta_const(s)) {
            (Some(t_const), Some(s_const)) => {
                #[cfg(feature = "debug-def-eq")]
                eprintln!(
                    "[lazy_delta_step] both delta: t_head = {}, s_head = {}",
                    t_const.0, s_const.0
                );
                self.lazy_delta_step_both(t, s, t_const, s_const)
            }
            (Some((t_name, t_levels, _)), None) => {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[lazy_delta_step] left only: t_head = {}", t_name);
                self.lazy_delta_step_left_only(t, s, t_name, t_levels)
            }
            (None, Some((s_name, s_levels, _))) => {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[lazy_delta_step] right only: s_head = {}", s_name);
                self.lazy_delta_step_right_only(t, s, s_name, s_levels)
            }
            (None, None) => {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[lazy_delta_step] no delta consts");
                self.lazy_delta_step_no_consts(t, s)
            }
        };
        if matches!(status, ReductionStatus::Continue) {
            return self.finish_lazy_delta_reduction_step(t, s);
        }
        status
    }

    fn lazy_delta_step_both(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        t_const: (Name, LevelVec, crate::env::Reducibility),
        s_const: (Name, LevelVec, crate::env::Reducibility),
    ) -> ReductionStatus {
        let (t_name, t_levels, t_red) = t_const;
        let (s_name, s_levels, s_red) = s_const;
        match t_red.compare(&s_red) {
            Ordering::Less => {
                if self.try_unfold_const_in_place(t, &t_name, &t_levels, self.transparency)
                    || self.try_unfold_const_in_place(s, &s_name, &s_levels, self.transparency)
                {
                    ReductionStatus::Continue
                } else {
                    ReductionStatus::DefUnknown
                }
            }
            Ordering::Greater => {
                if self.try_unfold_const_in_place(s, &s_name, &s_levels, self.transparency)
                    || self.try_unfold_const_in_place(t, &t_name, &t_levels, self.transparency)
                {
                    ReductionStatus::Continue
                } else {
                    ReductionStatus::DefUnknown
                }
            }
            Ordering::Equal => {
                self.lazy_delta_step_equal(t, s, (t_name, t_levels, t_red), (s_name, s_levels))
            }
        }
    }

    fn lazy_delta_step_equal(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        t_const: (Name, LevelVec, crate::env::Reducibility),
        s_const: (Name, LevelVec),
    ) -> ReductionStatus {
        let (t_name, t_levels, t_red) = t_const;
        let (s_name, s_levels) = s_const;
        // Same-head args-first fast path. Lean 4 (type_checker.cpp:917-931)
        // gates the attempt on `d_t->get_hints().is_regular()`. Clean widens
        // the gate to `Reducible` heads as well — a DELIBERATE, documented
        // divergence (designs/2026-07-15-lazy-delta-ordering-parity.md,
        // STEP 4, evidence-gated by STEP 0):
        //
        // - Lean's hints are source-faithful, so its Regular-only gate only
        //   skips genuine `abbrev`s (cheap unfolds). Clean OVER-ASSIGNS
        //   `Reducible`: the prelude seeds mark class definitions like
        //   `Nat.lt` `is_reducible: true` (env/order_le_lt.rs:429) where
        //   Lean's olean hint is `Regular`, and the olean importer
        //   force-promotes every projection-bodied definition (`LT.lt`,
        //   `HAdd.hAdd`, `UInt32.toBitVec`, …) to `Reducible`
        //   (clean-olean import/convert.rs:170-176).
        // - Under the Regular-only gate those heads NEVER got the args
        //   attempt. Step-0 witness (full Nat-seed-suppression combo):
        //   `[EXTEQ d=2] Nat.lt t_red=Reducible s_red=Reducible gate=false
        //   verdict=SKIPPED(gate: non-Regular head)` (same for LT.lt at
        //   d=1; 13 same-head pairs gate-skipped pre-grind, 0 cache hits,
        //   0 heartbeat taint) — so both sides delta-unfolded into genuine
        //   `Nat.rec`/brecOn bodies and launched a Θ(literal) iota grind on
        //   major = 4294967264 that congruence closes at depth 1-2. Where
        //   the gate DID admit a pair (`Nat.add`, Regular(0)==Regular(0),
        //   depth 3) the args attempt returned TRUE on this term family.
        //
        // SOUNDNESS (TRUE-early only): `DefEqual` is returned only when both
        // heads are the SAME constant with level-wise-equal instantiations
        // and every argument pair passes the UNCHANGED `is_def_eq_impl` —
        // any accept is inside the congruence closure of the existing
        // acceptance relation. Failure is cached and falls through to the
        // byte-identical unfold-both path below (pinned by
        // `test_delta_ordering_constant_function_fallback_must_accept`).
        //
        // Same name ⇒ same `ConstantInfo` ⇒ same hint on both sides (both
        // classifications come from the same env lookup in
        // `get_delta_const`), so gating on `t_red` covers both sides; a
        // mixed Regular/Reducible SAME-NAME pair cannot exist. `Irreducible`
        // heads keep the skip (no evidence they need the attempt), and
        // `Opaque` never reaches here (excluded by `get_delta_const`).
        //
        // The deeper fix is a seed/import hint-fidelity sweep (store Lean's
        // actual ReducibilityHints), after which this gate can narrow back
        // to Regular-only — design doc open question 5.
        if t_name == s_name
            && matches!(
                t_red,
                crate::env::Reducibility::Regular(_) | crate::env::Reducibility::Reducible
            )
        {
            // Lean 4 optimization (type_checker.cpp:924-930): skip argument
            // comparison if a previous attempt with the same pair already failed.
            if !self.args_failed_before(t, s) {
                if self.is_def_eq_args_only(t, s) {
                    return ReductionStatus::DefEqual;
                }
                self.cache_args_failure(t, s);
            }
        }
        let t_changed = self.try_unfold_const_in_place(t, &t_name, &t_levels, self.transparency);
        let s_changed = self.try_unfold_const_in_place(s, &s_name, &s_levels, self.transparency);
        if t_changed || s_changed {
            ReductionStatus::Continue
        } else {
            ReductionStatus::DefUnknown
        }
    }

    fn lazy_delta_step_left_only(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        t_name: Name,
        t_levels: LevelVec,
    ) -> ReductionStatus {
        if let Some(s_new) = self.try_unfold_proj_app(s) {
            *s = s_new;
            return ReductionStatus::Continue;
        }
        if self.try_unfold_const_in_place(t, &t_name, &t_levels, self.transparency) {
            ReductionStatus::Continue
        } else {
            ReductionStatus::DefUnknown
        }
    }

    fn lazy_delta_step_right_only(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        s_name: Name,
        s_levels: LevelVec,
    ) -> ReductionStatus {
        if let Some(t_new) = self.try_unfold_proj_app(t) {
            *t = t_new;
            return ReductionStatus::Continue;
        }
        if self.try_unfold_const_in_place(s, &s_name, &s_levels, self.transparency) {
            ReductionStatus::Continue
        } else {
            ReductionStatus::DefUnknown
        }
    }

    /// Lean 4 parity (type_checker.cpp:888-889): when neither side has a
    /// delta-reducible head, return `DefUnknown` immediately. Lean 4 does NOT
    /// attempt `try_unfold_proj_app` in this case — projection unfolding is
    /// only tried in the asymmetric cases (one side has delta, the other
    /// doesn't). Trying it here caused over-reduction that could leave the
    /// two sides in incompatible forms. Part of #3134.
    fn lazy_delta_step_no_consts(&self, _t: &mut Expr, _s: &mut Expr) -> ReductionStatus {
        ReductionStatus::DefUnknown
    }

    /// Finish a lazy delta reduction step by checking for easy equality.
    ///
    /// Reference: Lean 4 type_checker.cpp:935 `lazy_delta_reduction_step`.
    /// After each delta unfold, Lean 4 checks only structural equality and
    /// `quick_is_def_eq` — NOT proof irrelevance. Proof irrelevance is
    /// checked once before entering the delta loop (`is_def_eq_core` Phase 1.5,
    /// line 333 in mod.rs) and again after exiting (via recursive `is_def_eq_impl`
    /// calls in structural comparison). Checking it inside the loop adds
    /// `infer_type` overhead on every delta step with no soundness benefit.
    ///
    /// Fix for #3229: removed `is_def_eq_proof_irrel` call that was here.
    fn finish_lazy_delta_reduction_step(&self, t: &Expr, s: &Expr) -> ReductionStatus {
        if *t == *s {
            return ReductionStatus::DefEqual;
        }
        match self.quick_is_def_eq(t, s) {
            Some(true) => return ReductionStatus::DefEqual,
            Some(false) => return ReductionStatus::DefDiff,
            None => {}
        }
        ReductionStatus::Continue
    }

    /// Lazy delta reduction for projection comparison.
    ///
    /// Reference: Lean 4 type_checker.cpp:1010-1027 `lazy_delta_proj_reduction`.
    ///
    /// When comparing `Proj(_, i, a) =?= Proj(_, i, b)`, runs the lazy delta
    /// reduction loop on the inner struct expressions `a` and `b`. Unlike the
    /// full `lazy_delta_reduction`, this calls `lazy_delta_reduction_step`
    /// directly (no Nat/native hooks), matching Lean 4's structure.
    ///
    /// On `DefUnknown` or `DefDiff` (delta exhausted or proved structurally
    /// different), tries to extract field `idx` from both sides via
    /// `reduce_proj_core`. Falls back to `is_def_eq_core` on the delta-reduced
    /// inner expressions.
    pub(in crate::tc) fn lazy_delta_proj_reduction(
        &self,
        t_c: &Expr,
        s_c: &Expr,
        idx: u32,
    ) -> bool {
        /// Safety cap for the projection delta loop (same rationale as
        /// `MAX_LAZY_DELTA_ITERATIONS` in `lazy_delta_reduction`). #1773.
        const MAX_PROJ_DELTA_ITERATIONS: u32 = 10_000;

        let mut t = t_c.clone();
        let mut s = s_c.clone();
        let mut iterations = 0u32;

        loop {
            iterations += 1;
            if iterations > MAX_PROJ_DELTA_ITERATIONS {
                return false; // Conservative: not def-eq
            }

            match self.lazy_delta_reduction_step(&mut t, &mut s) {
                ReductionStatus::Continue => {} // Keep looping
                ReductionStatus::DefEqual => return true,
                ReductionStatus::DefUnknown | ReductionStatus::DefDiff => {
                    // Delta exhausted or proved structurally different.
                    // Try extracting projection fields from the delta-reduced
                    // inner expressions before giving up.
                    // Lean 4 type_checker.cpp:1017-1024
                    if let Some(t_field) = self.reduce_proj_core(&t, idx) {
                        if let Some(s_field) = self.reduce_proj_core(&s, idx) {
                            return self.is_def_eq_impl(&t_field, &s_field);
                        }
                    }
                    // Fall back to comparing the inner expressions directly.
                    return self.is_def_eq_impl(&t, &s);
                }
            }
        }
    }

    /// Check if argument comparison for (t, s) previously failed.
    ///
    /// Uses the `args_failure_cache` SlidingCache to detect pairs whose
    /// `is_def_eq_args_only` already returned false in a prior delta step.
    ///
    /// Reference: Lean 4 `type_checker.cpp:847-855` `failed_before`.
    /// Part of #1360.
    fn args_failed_before(&self, t: &Expr, s: &Expr) -> bool {
        let key = DefEqCacheKey::new(t, s, self.transparency);
        self.args_failure_cache.borrow_mut().get(&key).is_some()
    }

    /// Record that argument comparison for (t, s) failed.
    ///
    /// Inserts into the `args_failure_cache` SlidingCache. Uses the same
    /// `max_cache_entries` threshold as other TC caches for sliding window
    /// eviction.
    ///
    /// Reference: Lean 4 `type_checker.cpp:857-863` `cache_failure`.
    /// Part of #1360.
    fn cache_args_failure(&self, t: &Expr, s: &Expr) {
        let key = DefEqCacheKey::new(t, s, self.transparency);
        let mut cache = self.args_failure_cache.borrow_mut();
        cache.trim_if_needed(self.max_cache_entries);
        cache.insert(key, ());
    }
}
