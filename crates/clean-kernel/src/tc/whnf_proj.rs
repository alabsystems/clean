// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WHNF helper methods: projection reduction, outer delta loop, and dispatch.
//!
//! Extracted from `whnf.rs` to stay under the 500-line file-size limit.
//! Contains `reduce_proj_with_mode`, `whnf_recurse`, `whnf_outer_loop`,
//! and `try_unfold_definition`.
//!
//! Part of #3210.

use crate::expr::{stack_safe, Expr, ExprKind};
use crate::name::Name;
use crate::tc::reduction::string_lit_to_constructor;
use crate::tc::whnf::WhnfMode;
use crate::tc::TypeChecker;
use std::sync::Arc;

impl<'env> TypeChecker<'env> {
    /// Projection reduction dispatch for `ExprKind::Proj`.
    pub(super) fn whnf_reduce_proj(
        &self,
        struct_name: &Name,
        idx: u32,
        expr: &Expr,
        mode: WhnfMode,
    ) -> Expr {
        self.reduce_proj_with_mode(struct_name, idx, expr, mode)
    }

    /// Dispatch recursive WHNF call based on mode.
    ///
    /// - `Full`: recurse through `whnf_impl` (includes caching layer)
    /// - `NoDelta*`: check `whnf_core_cache` then recurse (matches Lean 4 m_whnf_core)
    /// - `WithTransparency`: recurse through `whnf_with_transparency_impl` (stack_safe)
    #[inline]
    pub(super) fn whnf_recurse(&self, e: &Expr, mode: WhnfMode) -> Expr {
        match mode {
            WhnfMode::Full => self.whnf_impl(e),
            WhnfMode::NoDeltaCheapProj | WhnfMode::NoDeltaFullProj => {
                // Check whnf_core_cache before recursing (#1768).
                if let Some(cached) = self.whnf_core_cache.borrow_mut().get(e) {
                    return cached;
                }
                let result = stack_safe(|| self.whnf_core_inner(e, mode));
                // Store only in full-proj mode (Lean 4: !cheap_rec && !cheap_proj).
                if matches!(mode, WhnfMode::NoDeltaFullProj) {
                    let mut cache = self.whnf_core_cache.borrow_mut();
                    cache.trim_if_needed(self.max_cache_entries);
                    cache.insert(e.clone(), result.clone());
                }
                result
            }
            WhnfMode::WithTransparency(tm) => {
                stack_safe(|| self.whnf_with_transparency_impl(e, tm))
            }
        }
    }

    /// Shared projection reduction for all WHNF modes.
    ///
    /// Mirrors Lean 4's `reduce_proj` (type_checker.cpp:375-386):
    /// - When `cheap_proj=true` (NoDeltaCheapProj): uses `whnf_core` (no delta)
    ///   on the inner expression.
    /// - When `cheap_proj=false` (NoDeltaFullProj, Full): uses full `whnf()`
    ///   (including delta) on the inner expression. This is critical because
    ///   the projection needs to see the constructor form, which requires
    ///   delta-unfolding instance constants like `instHAddNat` to their
    ///   `HAdd.mk Nat.add` values.
    ///
    /// Part of #3210.
    fn reduce_proj_with_mode(
        &self,
        struct_name: &Name,
        idx: u32,
        expr: &Expr,
        mode: WhnfMode,
    ) -> Expr {
        // Lean 4 reduce_proj (type_checker.cpp:382-385):
        //   if (cheap_proj) c = whnf_core(proj_expr, cheap_rec, cheap_proj);
        //   else            c = whnf(proj_expr);
        //
        // NoDeltaCheapProj → whnf_core (no delta)
        // NoDeltaFullProj  → whnf (full delta) — critical for instance unfolding
        // Full             → whnf (full delta via whnf_impl)
        // WithTransparency → whnf with transparency (stack_safe path)
        let proj_whnf = match mode {
            WhnfMode::NoDeltaCheapProj => {
                // Cheap projection: no delta on inner expression
                self.whnf_recurse(expr, mode)
            }
            WhnfMode::NoDeltaFullProj | WhnfMode::Full => {
                // Full projection: use full WHNF (including delta) on inner expression
                // This matches Lean 4's `whnf(proj_expr(e))` for cheap_proj=false
                self.whnf_impl(expr)
            }
            WhnfMode::WithTransparency(tm) => {
                stack_safe(|| self.whnf_with_transparency_impl(expr, tm))
            }
        };

        let proj_whnf = match &proj_whnf.kind {
            ExprKind::Lit(crate::expr::Literal::String(s)) => {
                let expanded = string_lit_to_constructor(s);
                // String literal expansion produces `String.ofList (List.cons ...)` which
                // requires delta reduction to reach the `String.mk` constructor form
                // needed for projection extraction. Use full WHNF for all modes —
                // including NoDeltaCheapProj — because the expansion is an internal
                // lowering step, not a user-visible delta unfold.
                //
                // Without this, `Proj(String, 0, "hello")` stays stuck in cheap
                // projection mode since `String.ofList` never unfolds to `String.mk`.
                // Part of #3234.
                match mode {
                    WhnfMode::WithTransparency(tm) => {
                        stack_safe(|| self.whnf_with_transparency_impl(&expanded, tm))
                    }
                    _ => self.whnf_impl(&expanded),
                }
            }
            _ => proj_whnf,
        };

        let head = proj_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(ctor_val) = self.env.get_constructor(ctor_name) {
                // Lean 4 parity: reduce_proj_core does NOT check that the
                // constructor's inductive name matches the Proj's struct name.
                // This is critical for type aliases: if `Substring` is an
                // abbreviation for `Substring.Raw`, a Proj("Substring", 0, e)
                // where e WHNFs to `Substring.Raw.mk(...)` must still reduce.
                // Lean 4 type_checker.cpp:358-373 — only checks is_constructor
                // and field index bounds, not the struct name.
                // Part of #3209.
                let field_idx = (ctor_val.num_params as usize).saturating_add(idx as usize);
                let args = proj_whnf.get_app_args();
                if let Some(reduced) = args.get(field_idx) {
                    // Re-enter WHNF on the extracted field
                    return self.whnf_recurse(reduced, mode);
                }
            }
        }

        Expr::proj(struct_name.clone(), idx, proj_whnf)
    }

    /// Lean 4-style outer WHNF loop with a lazy monad stage:
    /// whnf_core (no-delta) -> reduce_native -> reduce_nat -> try_monad_reduce
    /// -> unfold_definition -> repeat.
    ///
    /// Gives reduce_nat/reduce_native a chance to fire after every delta step.
    /// Reference: Lean 4 type_checker.cpp:659-681.
    ///
    /// Optimization beyond Lean 4: after delta-unfolding produces a new intermediate
    /// expression, we check the WHNF cache (`whnf_cache`, Lean 4's `m_whnf`) before
    /// re-entering the loop. This short-circuits chains like
    /// `HPow.hPow -> instHPow -> instPowNat -> Nat.pow` when an intermediate form
    /// (e.g., `instPowNat args...`) was already fully WHNF'd in a prior call.
    /// Part of #3210.
    pub(super) fn whnf_outer_loop(&self, e: &Expr) -> Expr {
        let mut t = e.clone();
        loop {
            if self.heartbeat_exhausted() {
                return t;
            }
            let t1 = self.whnf_core_inner(&t, WhnfMode::NoDeltaFullProj);

            if let Some(reduced) = self.reduce_native(&t1) {
                let mut cache = self.whnf_cache.borrow_mut();
                cache.trim_if_needed(self.max_cache_entries);
                cache.insert(e.clone(), reduced.clone());
                return reduced;
            }

            if let Some(reduced) = self.reduce_nat(&t1) {
                let mut cache = self.whnf_cache.borrow_mut();
                cache.trim_if_needed(self.max_cache_entries);
                cache.insert(e.clone(), reduced.clone());
                return reduced;
            }

            // Lazy monadic reduction: short-circuit bind chains for StateT,
            // ExceptT, and abstract Bind.bind before delta-unfolding the
            // full bind definition (which materializes O(2^N) paths).
            // Part of #3401.
            if let Some(reduced) = self.try_monad_reduce(&t1) {
                if reduced == t1 {
                    return reduced;
                }
                if let Some(cached) = self.whnf_cache.borrow_mut().get(&reduced) {
                    return cached;
                }
                t = reduced;
                continue;
            }

            if let Some(unfolded) = self.try_unfold_definition(&t1) {
                self.inc_heartbeat();
                // Check whnf_cache for the intermediate expression after delta
                // unfolding. If this expression was already fully WHNF'd in a
                // prior call, we can skip the remaining loop iterations entirely.
                // This is an optimization beyond Lean 4, which only checks
                // m_whnf at the top of whnf(). Part of #3210.
                if let Some(cached) = self.whnf_cache.borrow_mut().get(&unfolded) {
                    return cached;
                }
                t = unfolded;
                continue;
            }

            return t1;
        }
    }

    /// Try to unfold the head constant of an expression (delta reduction).
    ///
    /// For `App(App(...App(Const(name, levels), a1), ...), an)`, unfolds `Const(name, levels)`
    /// to its definition value and reconstructs the application via flat arg collection.
    ///
    /// Reference: Lean 4 type_checker.cpp:521-532 `unfold_definition_core`.
    /// Part of #3208, Part of #3209, Part of #3210.
    pub(super) fn try_unfold_definition(&self, e: &Expr) -> Option<Expr> {
        // Cubical path application `p @ r` whose path `p` is a delta-defined redex
        // (e.g. `intLoop n = MyZ.rec … n`): unfold the path head here, in the outer
        // delta loop. The inner `whnf_core` runs NoDelta, so it can only path-beta a
        // *literal* path-lam; and the outer loop's `get_app_fn` of a `CubicalPathApp`
        // is the path-app node, not a `Const`, so a delta-defined path would never
        // expose its path-lam. Recursing on `path` unfolds its head (one delta step),
        // after which `whnf_core` can iota/path-beta it. This is the path-application
        // analogue of unfolding an ordinary application's function head — definitional
        // unfolding, hence type-preserving and sound. Returns `None` (no change) when
        // the path head is not a definition (a neutral variable, a literal path-lam),
        // leaving the term stuck exactly as before.
        if let ExprKind::CubicalPathApp { path, arg } = &e.kind {
            let unfolded_path = self.try_unfold_definition(path)?;
            return Some(Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(unfolded_path),
                arg: arg.clone(),
            }));
        }
        let head = e.get_app_fn();
        if let ExprKind::Const(name, _) = &head.kind {
            // B14 elaboration-time gate: this is the top-level `whnf` delta path
            // (`whnf_outer_loop` runs a NoDelta core, then delta-unfolds here).
            // When the opt-in `honor_reducibility` flag is on (elaborator/
            // unifier), an `@[irreducible]` head stays folded at a non-`All`
            // transparency — matching MetaM `canUnfold` at `.default`. Off by
            // default → transparency-blind kernel path unchanged.
            if self.reducibility_gate_blocks(name) {
                return None;
            }
            // BARE guarded-binop deferral — closes the bare-Const guard bypass
            // (the ToInt/GrindInstances omega-frame grind class).
            //
            // A BARE `Nat.add`/`Nat.sub`/`Nat.mul`/`Nat.pow` Const reaches this
            // outer-loop delta site when the op is exposed WITHOUT its operands:
            // the instance-projection field extraction (`reduce_proj_with_mode`
            // above pulls `Nat.mul` out of `Mul.mk Nat.mul`) returns the bare op
            // as the whole core-WHNF result, typically while `beta_or_iota_step`
            // is whnf-ing an application HEAD whose spine args are waiting one
            // frame up. Eagerly unfolding here hands that caller the raw
            // recursor-seed LAMBDA, which beta-receives the args DIRECTLY into a
            // materialized `Nat.rec`/`brecOn` tower — so a closed
            // `Nat.mul <lit> <lit>` at 2^31/2^63 scale grinds Θ(count) unary
            // iota steps without a 2-arg `Nat.mul` app ever existing for the
            // App-arm `reduce_nat` accelerator or the
            // `native_nat_binop_grind_stuck` guard to key on.
            //
            // Declining the BARE unfold lets the caller re-form the full
            // `Nat.mul a b` app (`beta_or_iota_step`'s non-lambda rebuild),
            // where `reduce_nat` computes the closed case in binary (BigNat)
            // and the existing binop guard sticks the mixed large-count case.
            // Lean-parity: Lean's kernel whnf loop runs `reduce_nat` BEFORE
            // `unfold_definition` on every iteration and its `whnf_core` never
            // delta-unfolds heads, so these certificates always reduce in
            // binary via reduce_nat's extern acceleration, never through a
            // materialized tower (type_checker.cpp:576-585, 604-633).
            //
            // SOUNDNESS: a pure deferral — never changes acceptance. The folded
            // Const is definitionally equal to its unfolding, and the unfold
            // still happens wherever genuinely demanded: the APPLIED form takes
            // the `e.is_app()` branch below (args re-attached before the unfold
            // decision); def-eq's lazy delta unfolds via
            // `unfold_definition_cached` directly (delta_helpers.rs:87); a
            // direct `whnf_core` of a bare Const unfolds via the Full-mode
            // Const arm (whnf.rs). Acceleration produces the identical literal
            // the unary walk would (`reduce_nat` is the already-certified
            // path), and deferral strictly narrows WHERE reduction happens,
            // never WHAT is accepted. The result is a WHNF fixpoint
            // (`whnf(bare op) == bare op`), so whnf idempotency is preserved.
            if !e.is_app() && Self::is_guarded_nat_binop_name(name) {
                #[cfg(feature = "reduction-stats")]
                crate::tc::reduction_stats::record_binop_bare_defer(name);
                return None;
            }
            // APPLIED guarded-binop grind guard at the unfold COMMIT point —
            // the LAST unguarded delta lane for these heads (the ToInt
            // 2M-heartbeat residual, traced 2026-07-15).
            //
            // `whnf_core_inner`'s App arm already leaves a mixed-operand
            // `Nat.add a <closed count >= 512>` STUCK via
            // `native_nat_binop_grind_stuck` (whnf.rs), and def-eq's lazy
            // delta declines it via the same guard in `get_delta_const`
            // (delta_helpers.rs) — but this outer-loop site then unfolded the
            // identical application unconditionally, overriding the core
            // arm's verdict on every full `whnf_impl`. The unfold
            // beta-materializes the imported brecOn below-tower (motive
            // `fun n => PProd ((fun _ => Nat → Nat) n) (Nat.below … n)`,
            // which the `fun _ => Nat`-keyed recursor guard deliberately does
            // not match) and walks Θ(count) unary iota steps — live-traced as
            // `Nat.add fvar 2^31` launched from the Clean-only
            // `reduce_int → get_nat_bignat_whnf` extraction probes inside the
            // Init/GrindInstances/ToInt omega frames, where the probe's
            // literal extraction is doomed regardless (an fvar-bearing term
            // never yields a literal): the guard converts a Θ(2^31)
            // heartbeat-exhausting walk into the identical O(1) `None`.
            //
            // SOUNDNESS: identical to the certified guard it applies —
            // the stuck application is definitionally equal to its unfolded
            // form, so declining strictly NARROWS reduction (never a wrong
            // ACCEPT), and this site only aligns the outer loop with the
            // already-pinned core-arm/lazy-delta verdicts. Closed-closed
            // applications never reach here (`reduce_nat` computes them in
            // binary one stage earlier in `whnf_outer_loop`); symbolic-count
            // applications are untouched (the guard's count probe returns
            // `None`, so they still unfold). Result is a WHNF fixpoint
            // (core arm and outer loop now agree), preserving idempotency.
            if e.is_app() && self.native_nat_binop_grind_stuck(name, e) {
                return None;
            }
            let value = self.unfold_definition_cached(head)?;
            if e.is_app() {
                let args = e.get_app_args();
                let mut result = value;
                for arg in &args {
                    result = Expr::app(result, (*arg).clone());
                }
                Some(result)
            } else {
                Some(value)
            }
        } else {
            None
        }
    }

    /// Cached constant definition unfolding.
    ///
    /// Matches Lean 4's `m_unfold` cache (`type_checker.h:31`): maps a Const
    /// expression to its unfolded definition value (with universe levels
    /// substituted). Avoids repeating `instantiate_level_params_direct` when
    /// the same `Const(name, levels)` is encountered multiple times during
    /// type checking.
    ///
    /// Only caches successful unfolds (Some). Failed unfolds (None — axioms,
    /// opaque constants) are not cached since the env lookup is cheap.
    ///
    /// Part of #3210.
    pub(super) fn unfold_definition_cached(&self, const_expr: &Expr) -> Option<Expr> {
        // Check cache first
        if let Some(cached) = self.unfold_cache.borrow_mut().get(const_expr) {
            #[cfg(feature = "reduction-stats")]
            if let ExprKind::Const(name, _) = &const_expr.kind {
                crate::tc::reduction_stats::record_unfold(name, true);
            }
            return Some(cached);
        }

        let ExprKind::Const(name, levels) = &const_expr.kind else {
            return None;
        };

        let value = self.env.unfold_definition(name, levels)?;
        #[cfg(feature = "reduction-stats")]
        crate::tc::reduction_stats::record_unfold(name, false);
        // GRIND TRACE: a nat-binop DEFINITION being delta-unfolded to its
        // recursor seed. NOTE: `const_expr` here is always the bare head
        // Const, so this fires for APPLIED unfolds too (try_unfold_definition
        // app branch, lazy delta) — it does not by itself prove a bare-Const
        // bypass. The bare eager-unfold path in `try_unfold_definition` is
        // closed by the guarded-binop deferral there; residual events here are
        // the legitimate applied/explicit-delta unfolds.
        #[cfg(feature = "reduction-stats")]
        crate::tc::reduction_stats::record_binop_def_unfold(name);

        // Cache the result
        {
            let mut cache = self.unfold_cache.borrow_mut();
            cache.trim_if_needed(self.max_cache_entries);
            cache.insert(const_expr.clone(), value.clone());
        }

        Some(value)
    }
}
