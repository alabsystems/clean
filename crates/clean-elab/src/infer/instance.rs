// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance resolution for type classes
//!
//! This module implements typeclass instance resolution for the elaborator.
//! It provides tabled resolution with caching and supports:
//! - Local instance-implicit binders (`[inst : T]` in scope)
//! - Global instances from the instance table
//! - Out-parameter and semi-out-parameter handling
//! - Recursive instance resolution for dependent instances
//!
//! ## Architecture
//!
//! Instance resolution methods are implemented as an `impl` block on `ElabCtx`.
//! This keeps the instance logic cleanly separated while still having full
//! access to the elaboration context.
//!
//! ## Resolution Algorithm
//!
//! 1. Check local instance-implicit binders first (stack-based search)
//! 2. Check global instances from the instance table (priority order)
//! 3. For each candidate, apply implicit parameters and unify
//! 4. Two-phase unification handles out-parameters correctly

use super::ElabCtx;
use crate::stack_safe;
use crate::unify::{MetaId, MetaState, Unifier, UnifyResult};
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, FVarId, Level, Name};
use std::collections::{HashMap, HashSet};

/// Cap on the ∀-telescope a LOCAL instance binder may be opened under by
/// [`ElabCtx::resolve_local_instance_telescoped`]. `DecidableEq α` needs 2.
/// The cap exists so a pathological local type cannot turn a failure path into
/// an unbounded walk; a local needing more binders than this is refused, never
/// truncated.
const MAX_LOCAL_TELESCOPE: usize = 8;

/// Cap on the ∀-telescope a Pi-shaped GOAL may be opened under by
/// [`ElabCtx::resolve_pi_goal_by_abstraction`]. `DecidableEq α` needs 2. Same
/// contract as [`MAX_LOCAL_TELESCOPE`]: a goal needing more binders than this
/// is refused, never truncated — a truncated telescope would build a lambda of
/// the wrong arity.
const MAX_GOAL_TELESCOPE: usize = 8;

/// Instance resolution methods for ElabCtx
impl<'a> ElabCtx<'a> {
    /// Clear the instance resolution cache
    ///
    /// This should be called when the metavariable context changes significantly
    /// (e.g., after solving metavariables that might affect cached results).
    pub fn clear_instance_cache(&mut self) {
        self.instance_cache.clear();
    }

    /// Get instance cache statistics for debugging/profiling
    pub fn instance_cache_stats(&self) -> (usize, usize) {
        (self.instance_cache.len(), self.instance_cache.capacity())
    }

    /// Push a local instance-implicit binder for nested instance resolution.
    /// When elaborating `[inst : TC R]` where TC has nested instance dependencies,
    /// this allows the inner instance resolution to find `inst` as a local instance.
    pub(super) fn push_local_instance(&mut self, fvar: FVarId, ty: Expr) {
        // The cache key contains only the normalized goal, not the active local
        // instance stack.  A result cached before this push must not mask the
        // newly shadowing local instance.
        self.instance_cache.clear();
        self.local_instances.push((fvar, ty));
    }

    /// Pop a local instance-implicit binder.
    pub(super) fn pop_local_instance(&mut self) {
        if self.local_instances.pop().is_some() {
            // A ground-goal cache entry may be the FVar belonging to the local
            // instance just removed.  Returning it after the pop would create an
            // out-of-scope term, so invalidate at the scope mutation primitive.
            self.instance_cache.clear();
        }
    }

    /// Try to resolve an instance for a type class goal
    ///
    /// For example, given type `Add Nat`, this will search for a registered
    /// instance that implements `Add Nat`.
    ///
    /// Returns Some(instance_expr) if found, None otherwise.
    pub fn resolve_instance(&mut self, goal_ty: &Expr) -> Option<Expr> {
        // `strict` propagates the open-input postpone from the TOP-LEVEL goal's
        // class to every SUB-goal the search generates, which is what Lean gets
        // for free from `withNewMCtxDepth` (`Lean/Meta/SynthInstance.lean`:
        // the whole search runs at a deeper metavariable-context depth, so the
        // caller's metavariables are not assignable ANYWHERE inside it).
        //
        // Clean's phase-1 postpone (below) was one hop deep — it consulted only
        // the class of the goal immediately in front of it — and the grab it
        // refuses LAUNDERS through a sub-goal. Measured shape
        // (`tests_instance_open_carrier_postpone.rs`): a polymorphic bridge
        // `{a} → [C a] → Inhabited a` PASSES the one-hop guard, because its
        // conclusion argument is itself a bare metavariable and flex/flex
        // unification is legitimately deferred, not a wrong grab. Its `[C ?a]`
        // sub-goal is then in class `C`, which the allowlist does not name, so
        // THERE a concrete `C Decoy` candidate is committed and `?a := Decoy`.
        // The bare `default` came back as a term at that carrier and the
        // declaration failed against the type the author wrote
        // ("expected FVar(..), got Const(..)").
        //
        // Deliberately keyed on the TOP-LEVEL class only, and deliberately ONE
        // pass. A search whose root goal is outside
        // `is_input_only_postpone_class` — `OfNat ?a 5`, `HAdd ?a ?b ?g`,
        // `Monad ?m`, everything Clean resolves by grabbing where real Lean
        // applies `@[default_instance]` — is byte-identical to before, at every
        // depth, and pays nothing.
        //
        // A wider design was written and RETRACTED, for a structural reason
        // worth recording: arming the postpone for every class and recovering
        // the grabby classes with a SECOND, unguarded search. Instance
        // resolution is not idempotent across two searches. Candidate
        // universe-level unification pins level parameters in the
        // DECLARATION-WIDE, Name-keyed union-find (`add_level_constraint`,
        // see the freshening comment in the candidate loop below), which
        // `metas.pop_scope()` does NOT undo — so a candidate REJECTED in pass 1
        // can leave the goal's level parameter pinned to its own fresh
        // parameter and make pass 2's genuine candidate fail on a level
        // conflict. Propagating one flag through one search has no such
        // exposure.
        //
        // LOCAL instance binders are never guarded, at any depth. A local
        // `[inst : C t]` is a hypothesis of the declaration being elaborated,
        // so matching it can only produce a carrier already named in its binder
        // list — evidence, not invention. That is also what REPAIRS the
        // laundering case rather than merely refusing it: with the global grab
        // refused, the bridge's `[C ?a]` sub-goal reaches the local `[C a]`
        // binder and pins the carrier CORRECTLY.
        let strict = crate::instances::extract_class_app(&self.metas.instantiate(goal_ty))
            .is_some_and(|(n, _)| is_input_only_postpone_class(&n));
        let mut goal_path = Vec::new();
        self.resolve_instance_with_depth(goal_ty, 0, &mut goal_path, strict)
    }

    /// Depth- and cycle-bounded recursive entry point.
    ///
    /// Search bounding (the recursive TC search must terminate — no tabled
    /// search yet, this is a depth-capped DFS with cycle detection):
    /// - `depth` caps the sub-goal recursion at `MAX_DEPTH`;
    /// - `goal_path` holds the normalized cache keys of the goals on the
    ///   ACTIVE DFS path. Re-encountering a goal with the same normalized
    ///   shape (metavariable ids are canonicalized by
    ///   [`Self::normalize_for_cache`], so `MonadLiftT Id ?a` and
    ///   `MonadLiftT Id ?b` coincide) means a candidate is reproducing its
    ///   own goal as a sub-goal — the divergent regress a transitivity
    ///   instance can generate — so that branch fails and the search moves
    ///   to the next candidate. Lean's `SynthInstance.lean` reaches the same
    ///   effect by TABLING such goals (one generator node per normalized
    ///   goal); a full tabled search is a later increment.
    fn resolve_instance_with_depth(
        &mut self,
        goal_ty: &Expr,
        depth: usize,
        goal_path: &mut Vec<String>,
        strict: bool,
    ) -> Option<Expr> {
        use crate::instances::extract_class_app;

        const MAX_DEPTH: usize = 32;
        if depth > MAX_DEPTH {
            return None;
        }

        // Prefer the un-whnf'd head when the goal is ALREADY a registered class
        // application. `whnf` would otherwise unfold a `def`-based class such as
        // `DecidableEq T` (= `(a b : T) → Decidable (Eq a b)`) to its underlying
        // Pi, losing the `DecidableEq` head so `extract_class_app` returns `None`
        // and resolution fails. Inductive/structure classes (`Add`, `Ring`, …)
        // are unaffected — they don't reduce, so pre- and post-whnf heads agree.
        let goal_inst = self.metas.instantiate(goal_ty);
        let goal_ty =
            if extract_class_app(&goal_inst).is_some_and(|(n, _)| self.instances.is_class(&n)) {
                goal_inst.clone()
            } else {
                let w = self.whnf(&goal_inst);
                self.metas.instantiate(&w)
            };

        // Generate cache key for this goal
        // We normalize the goal type so that structurally similar goals
        // (differing only in metavariable IDs) map to the same key.
        let cache_key = self.normalize_for_cache(&goal_ty);

        // Check cache for previously resolved instance
        // Note: We only use cached results if the goal is ground (no metavariables)
        // because metavariable-containing goals might resolve differently depending
        // on how those metavariables get solved later.
        let goal_is_ground = !self.has_metavars(&goal_ty);
        if goal_is_ground {
            if let Some(cached) = self.instance_cache.get(&cache_key) {
                return Some(cached.clone());
            }
        }

        // Cycle detection: same normalized goal already on the active path.
        //
        // Keyed on a SEPARATE, more aggressively normalized key than `cache_key`.
        // `cache_key` is computed from the goal above with the head deliberately
        // left un-whnf'd (to preserve `def`-based class heads such as
        // `DecidableEq`), so a self-wrapping instance produces a goal chain
        // `OfNat Nat 0` -> `OfNat (Id Nat) 0` -> `OfNat (Id (Id Nat)) 0` -> …
        // whose members are all definitionally equal but SYNTACTICALLY distinct.
        // The cycle check therefore never fired: resolution ran to `MAX_DEPTH`,
        // bottomed out on the genuine instance, and unwound into a 31-wrapper
        // tower that was then accepted as the answer (the literal `0` in
        // `n + 0` elaborated to 12,470 characters of `Id.instOfNat`).
        //
        // Normalizing the class ARGUMENTS collapses that chain to one key so the
        // check fires on the second level. The head is untouched, so no
        // `def`-based class head is lost, and `cache_key` keeps its existing
        // meaning for the instance cache — a stricter cycle key can only reject
        // paths that were already non-terminating.
        let cycle_key = self.cycle_detection_key(&goal_ty, &cache_key);
        if goal_path.contains(&cycle_key) {
            return None;
        }
        goal_path.push(cycle_key);
        let mut result = self.resolve_instance_candidates(
            &goal_ty,
            &cache_key,
            goal_is_ground,
            depth,
            goal_path,
            strict,
        );
        // FRONTIER STAGE I-1, the candidate side. Runs ONLY on a search that
        // has already returned `None`, which is the whole safety argument: no
        // resolution that succeeded before this change can take a different
        // answer after it, because the fallback is never consulted while an
        // answer exists. See `resolve_local_instance_telescoped`.
        if result.is_none() {
            result = self.resolve_local_instance_telescoped(&goal_inst, &goal_ty);
            // FRONTIER STAGE I-2, the GOAL side. Same safety argument, one rung
            // further out: consulted only after the primary search AND the
            // candidate-side match have both returned `None`, so it can add
            // resolutions and never change one. See
            // `resolve_pi_goal_by_abstraction`.
            //
            // `depth == 0`: the abstraction answers only the ELABORATOR's own
            // goal, never a candidate's `[inst]` sub-goal. Without this a
            // candidate like `instD : [(x : Nat) → C Nat] → D Nat` gets its
            // sub-goal answered by the goal-side telescope and `D Nat`
            // resolves — and the `decEq` bridge's `DecidableEq α` delegation
            // would silently change the TERM of goals that already resolve.
            // The boundary was documented by
            // `test_goal_side_is_not_applied_to_an_internal_subgoal` on the
            // day the stage landed (0c907dd23), but the guard itself never
            // was — the test was born red (measured 2026-08-28).
            if result.is_none() && depth == 0 {
                result = self.resolve_pi_goal_by_abstraction(
                    &goal_ty,
                    goal_is_ground,
                    depth,
                    goal_path,
                    strict,
                );
            }
            if goal_is_ground {
                if let Some(found) = &result {
                    self.instance_cache.insert(cache_key, found.clone());
                }
            }
        }
        goal_path.pop();
        result
    }

    /// Candidate-side telescope for LOCAL instance binders — the half of
    /// Lean's `Lean/Class.lean:isClass?` that Clean was missing.
    ///
    /// # The gap
    ///
    /// `DecidableEq α` is a `def`, not a `class`:
    /// `DecidableEq α := (a b : α) → Decidable (a = b)`. Two consequences,
    /// both measured (`tests/fixtures/source_frontier/p08,p11`, and 34 of the
    /// 53 `instance synthesis` entries of the 2026-08-25 five-file
    /// source-elaboration measurement):
    ///
    /// 1. The primary local-instance loop whnf's each local's type before
    ///    matching it. For `[inst : DecidableEq α]` that yields a Pi,
    ///    `extract_class_app` yields `None`, and the binder is passed over
    ///    silently — so even the *syntactically identical* goal `DecidableEq α`
    ///    cannot be answered by the binder that literally has that type.
    /// 2. `is_class` is a plain lookup over names registered by the `class`
    ///    keyword, so the `def`-based alias closes the door a second time.
    ///
    /// # What this adds
    ///
    /// Three matches, in order, all against locals only:
    ///
    /// - **(A) alias head.** The goal *as handed in* (`goal_pre_whnf`) against
    ///   each local's type *as bound*, with no normalisation on either side.
    ///   A local whose declared type unifies with the goal's declared type is
    ///   evidence for it whatever the head reduces to. Answers `DecidableEq α`
    ///   from `[DecidableEq α]`, which is also what lets the existing
    ///   `Decidable (@Eq α a b)` bridge (which delegates to `DecidableEq α`)
    ///   stop dying one level down.
    /// - **(C) whole normalised type**, for a **Pi-shaped** goal with no class
    ///   application at all — the alias the *caller* already unfolded. Unify
    ///   goal and local outright; the term is the binder. The Pi restriction
    ///   is a safety property, not tidiness — see the comment at the match.
    /// - **(B) ∀-telescope.** The normalised goal against each local's
    ///   normalised type opened under its ∀-telescope: binders become
    ///   metavariables, the conclusion's class app is matched against the
    ///   goal, and the term returned is `inst a b …` rather than the bare
    ///   `inst`. This is Lean registering `[inst : DecidableEq α]` as an
    ///   instance *of class `Decidable`, with binders*.
    ///
    /// # Why it cannot admit a wrong candidate
    ///
    /// - It is consulted only after the primary search returned `None`
    ///   (see the call site), so it can add resolutions and never change one.
    /// - It matches LOCALS only. A local `[inst : C t]` is a hypothesis of the
    ///   declaration being elaborated, so its carrier is already named in the
    ///   binder list — evidence, not invention (the same argument
    ///   `resolve_instance` makes for leaving the local loop unguarded).
    /// - Unification is per-candidate scoped: a local whose conclusion does not
    ///   unify with the goal is rolled back and skipped, so a `[DecidableEq α]`
    ///   in scope is NOT grabbed for a `Decidable (b = b)` goal at a different
    ///   carrier (pinned: `p20_wrong_carrier_refused_MUST_FAIL`).
    /// - Every telescope metavariable must end DETERMINED by the goal — the
    ///   same hygiene check the global candidate loop applies — so a binder the
    ///   goal does not pin fails the candidate instead of leaking an
    ///   unassigned metavariable into the emitted term (pinned:
    ///   `p22_undetermined_binder_refused_MUST_FAIL`).
    /// - The emitted term is kernel-re-checked exactly as before. Zero TCB.
    fn resolve_local_instance_telescoped(
        &mut self,
        goal_pre_whnf: &Expr,
        goal_norm: &Expr,
    ) -> Option<Expr> {
        use crate::instances::extract_class_app;

        // Hot path: no local instance binders in scope — the common case for
        // non-generic code — costs one `len()`.
        if self.local_instances.is_empty() {
            return None;
        }

        // (A) alias head ↔ alias head, no `whnf` on either side.
        if let Some((goal_class, goal_args)) = extract_class_app(goal_pre_whnf) {
            for i in (0..self.local_instances.len()).rev() {
                let (fvar, local_ty) = self.local_instances[i].clone();
                let local_ty_inst = self.metas.instantiate(&local_ty);
                let Some((local_class, local_args)) = extract_class_app(&local_ty_inst) else {
                    continue;
                };
                if local_class != goal_class || local_args.len() != goal_args.len() {
                    continue;
                }
                self.metas.push_scope();
                let unified = local_args
                    .iter()
                    .zip(goal_args.iter())
                    .all(|(l, g)| self.try_unify(l, g));
                if unified {
                    self.metas.commit();
                    return Some(Expr::fvar(fvar));
                }
                self.metas.pop_scope();
            }
        }

        // (C) The goal has NO class application at all — which today means the
        // primary search bailed on its very first line
        // (`extract_class_app_with_levels(&goal_ty)?`) and did no work
        // whatsoever, so nothing here can interfere with anything. This is the
        // `def`-based alias the CALLER already normalised into its Pi:
        // `elab_app.rs`'s two `resolve_instance` call sites whnf the goal
        // before handing it over, so a `[DecidableEq α]` argument arrives as
        // `(x y : α) → Decidable (Eq α x y)` and the un-whnf'd head that (A)
        // matches on is gone before the search starts.
        //
        // Match it the only way that is still available: unify the WHOLE
        // normalised goal against each local's WHOLE normalised type. A local
        // whose type unifies with the goal type inhabits the goal — the term
        // is the binder itself, no telescope is opened and no lambda is
        // synthesized. (Synthesizing `fun a b => …` for a Pi goal with no
        // matching local is the separate goal-side increment; it is what still
        // buys `DecidableEq Nat` from a global `Nat.decEq`, which no local can
        // supply.)
        //
        // RESTRICTED TO A Pi-SHAPED GOAL, and that restriction is load-bearing
        // rather than tidy. Unifying a WHOLE goal is the one match here that
        // can SOLVE the goal expression instead of matching it: handed a goal
        // that is still a bare metavariable, `try_unify` would cheerfully
        // assign `?goal := <the first local's type>` and hand back that local —
        // inventing the class rather than finding evidence for it, which is
        // exactly the wrong-candidate failure this stage must not create. (A)
        // and (B) cannot do that: both require a rigid `Const` head on the
        // goal before they look at anything. A δ-unfolded class alias is
        // always a Pi, so nothing this match exists for is lost.
        let Some((goal_class, goal_args)) = extract_class_app(goal_norm) else {
            if !matches!(goal_norm.kind(), ExprKind::Pi(..)) {
                return None;
            }
            for i in (0..self.local_instances.len()).rev() {
                let (fvar, local_ty) = self.local_instances[i].clone();
                let local_ty_norm = self.whnf(&self.metas.instantiate(&local_ty));
                self.metas.push_scope();
                if self.try_unify(&local_ty_norm, goal_norm) {
                    self.metas.commit();
                    return Some(Expr::fvar(fvar));
                }
                self.metas.pop_scope();
            }
            return None;
        };

        // (B) telescoped local: match the CONCLUSION of the local's
        // ∀-telescope, and return the local APPLIED to the arguments the goal
        // determined.
        for i in (0..self.local_instances.len()).rev() {
            let (fvar, local_ty) = self.local_instances[i].clone();
            let local_ty_norm = self.whnf(&self.metas.instantiate(&local_ty));
            // A local that is NOT Pi-shaped after normalisation is exactly what
            // the primary loop already tried; re-trying it here would be dead
            // work and a second chance at the same answer.
            if !matches!(local_ty_norm.kind(), ExprKind::Pi(..)) {
                continue;
            }

            self.metas.push_scope();
            let mut cursor = local_ty_norm;
            let mut tele_args: Vec<Expr> = Vec::new();
            let mut opened = true;
            while let ExprKind::Pi(bi, arg_ty, body) = cursor.kind() {
                let info = bi.info;
                let arg_ty = arg_ty.as_ref().clone();
                let body = body.as_ref().clone();
                // Deliberately narrow: an `[inst]` binder inside a LOCAL's own
                // telescope would need a nested sub-goal search to fill, which
                // is a separate increment with its own termination argument.
                // Refuse the candidate instead of guessing.
                if tele_args.len() >= MAX_LOCAL_TELESCOPE || info == BinderInfo::InstImplicit {
                    opened = false;
                    break;
                }
                let arg_ty_inst = self.metas.instantiate(&arg_ty);
                let meta = self.fresh_meta(arg_ty_inst);
                let next = body.instantiate(&meta);
                tele_args.push(meta);
                cursor = self.whnf(&self.metas.instantiate(&next));
            }
            if !opened || tele_args.is_empty() {
                self.metas.pop_scope();
                continue;
            }

            let Some((concl_class, concl_args)) = extract_class_app(&cursor) else {
                self.metas.pop_scope();
                continue;
            };
            if concl_class != goal_class || concl_args.len() != goal_args.len() {
                self.metas.pop_scope();
                continue;
            }
            let unified = concl_args
                .iter()
                .zip(goal_args.iter())
                .all(|(c, g)| self.try_unify(c, g));
            if !unified {
                self.metas.pop_scope();
                continue;
            }

            // Candidate hygiene, verbatim in spirit from the global candidate
            // loop: a telescope binder the goal does not determine is not
            // evidence for the goal, and returning it would leak an unassigned
            // metavariable (a tagged FVar) into the declaration, surfacing far
            // away as the kernel's "Declaration contains free variables".
            let goal_metas = self.collect_meta_fvars(&self.metas.instantiate(goal_norm));
            let undetermined = tele_args.iter().any(|meta_arg| {
                let solved = self.metas.instantiate(meta_arg);
                has_meta_fvar_outside(&solved, &goal_metas)
            });
            if undetermined {
                self.metas.pop_scope();
                continue;
            }

            self.metas.commit();
            let applied = Expr::apps(Expr::fvar(fvar), tele_args);
            let result = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&applied));
            return Some(result);
        }

        None
    }

    /// GOAL-side telescope: solve a Pi-shaped instance goal by *building* the
    /// function rather than finding it.
    ///
    /// # The residue this closes
    ///
    /// [`Self::resolve_local_instance_telescoped`] matches a `def`-based class
    /// alias against LOCAL binders, which answers every goal whose carrier is
    /// itself a binder of the declaration being elaborated. It cannot answer a
    /// goal that has to be *constructed*: at a concrete carrier there is no
    /// local to match, and the answer is a lambda.
    ///
    /// `def callee {α} [DecidableEq α] (a : α) : Nat := 0` applied at `Nat`
    /// raises the instance goal `DecidableEq Nat`, which `elab_app` δ-unfolds
    /// before the search ever sees it, so what arrives is
    /// `(n n1 : Nat) → Decidable (Eq Nat n n1)`. `extract_class_app_with_levels`
    /// returns `None` on a Pi and `resolve_instance_candidates` bails on its
    /// first line — the entire candidate search, local and global, is skipped.
    /// Yet the Pi's BODY, `Decidable (Eq Nat n n1)`, resolves from the global
    /// table today. What is missing is only the abstraction.
    ///
    /// So: open the goal's ∀-telescope over fresh locals, resolve the
    /// conclusion as an ordinary instance goal, and re-abstract the locals into
    /// lambdas — `fun n n1 => Nat.decEq n n1`. (Pinned: probe
    /// `p18_goal_side_constructed`, which carries its own in-file control
    /// showing the body was always solvable, and `p24`, which removes the
    /// hand-written `Decidable`/`Eq` bridge from the picture entirely and adds
    /// a DEPENDENT telescope.)
    ///
    /// # Why it cannot admit a wrong candidate
    ///
    /// - It is consulted only after the primary search and the candidate-side
    ///   match have both returned `None` (see the call site), so it can add
    ///   resolutions and never change one.
    /// - **Ground goals only.** A goal still carrying metavariables is refused
    ///   outright. Solving the conclusion under the telescope can assign one of
    ///   the goal's OWN metavariables to a term mentioning a telescope local,
    ///   which would escape the moment the telescope closes — abstraction fixes
    ///   the returned term, not the caller's metavariable context. Refusing the
    ///   whole shape is the only check that covers that hazard completely; the
    ///   δ-unfolded alias goals this exists for are ground (their carrier was
    ///   pinned before the instance goal was raised).
    /// - **No `[inst]` binder in the goal telescope.** Such a binder would have
    ///   to enter scope as a local instance for the conclusion's own search, a
    ///   separate increment with its own argument. Refused, never guessed.
    /// - The conclusion must be a rigid class application before anything is
    ///   attempted, so a Pi ending in a metavariable or a `Sort` never starts a
    ///   search.
    /// - Candidate hygiene, verbatim from the two loops above: the emitted term
    ///   may not carry a metavariable the goal does not determine.
    /// - The emitted term is kernel-re-checked exactly as before. Zero TCB.
    fn resolve_pi_goal_by_abstraction(
        &mut self,
        goal_norm: &Expr,
        goal_is_ground: bool,
        depth: usize,
        goal_path: &mut Vec<String>,
        strict: bool,
    ) -> Option<Expr> {
        use crate::instances::extract_class_app;

        if !goal_is_ground || !matches!(goal_norm.kind(), ExprKind::Pi(..)) {
            return None;
        }
        let goal_metas = self.collect_meta_fvars(&self.metas.instantiate(goal_norm));

        // Open the telescope over fresh LOCALS (not metavariables): the
        // conclusion must be solved for an arbitrary argument, exactly as the
        // lambda we are about to build promises.
        let mut binders: Vec<(BinderData, Expr, FVarId)> = Vec::new();
        let mut cursor = self.metas.instantiate(goal_norm);
        let mut opened = true;
        while let ExprKind::Pi(bd, arg_ty, body) = cursor.kind() {
            let bd = *bd;
            if binders.len() >= MAX_GOAL_TELESCOPE || bd.info == BinderInfo::InstImplicit {
                opened = false;
                break;
            }
            let arg_ty = arg_ty.as_ref().clone();
            let body = body.as_ref().clone();
            let arg_ty = self.metas.instantiate(&arg_ty);
            let fvar = self.fresh_fvar();
            self.push_local_with_fvar(format!("_goaltele.{}", fvar.as_u64()), fvar, arg_ty.clone());
            cursor = body.instantiate(&Expr::fvar(fvar));
            binders.push((bd, arg_ty, fvar));
        }

        let mut result = None;
        if opened && !binders.is_empty() {
            let concl = self.metas.instantiate(&cursor);
            if extract_class_app(&concl).is_some() {
                self.metas.push_scope();
                if let Some(found) =
                    self.resolve_instance_with_depth(&concl, depth + 1, goal_path, strict)
                {
                    // Instantiate BEFORE abstracting: a solved metavariable
                    // standing for a telescope local must become that local so
                    // `abstract_fvar` can see and bind it.
                    let mut term = self.metas.instantiate(&found);
                    for (bd, ty, fvar) in binders.iter().rev() {
                        // The binder type is abstracted by the OUTER iterations:
                        // `abstract_fvar` walks the whole expression, binder
                        // types included, so a dependent telescope
                        // (`(x : α) → (y : β x) → …`) comes out correct.
                        let ty = self.metas.instantiate(ty);
                        term = Expr::lam(*bd, ty, term.abstract_fvar(*fvar));
                    }
                    let term = self
                        .metas
                        .instantiate_levels(&self.metas.instantiate(&term));
                    if has_meta_fvar_outside(&term, &goal_metas) {
                        self.metas.pop_scope();
                    } else {
                        self.metas.commit();
                        result = Some(term);
                    }
                } else {
                    self.metas.pop_scope();
                }
            }
        }

        for _ in 0..binders.len() {
            self.pop_local();
        }
        result
    }

    /// Candidate search for an already-normalized goal (split from
    /// [`Self::resolve_instance_with_depth`], which owns bounding, caching,
    /// and the goal-path bookkeeping).
    fn resolve_instance_candidates(
        &mut self,
        goal_ty: &Expr,
        cache_key: &str,
        goal_is_ground: bool,
        depth: usize,
        goal_path: &mut Vec<String>,
        strict: bool,
    ) -> Option<Expr> {
        use crate::instances::extract_class_app;

        // Extract the class name and arguments from the goal type
        let (class_name, goal_levels, goal_args) =
            crate::instances::extract_class_app_with_levels(goal_ty)?;

        // decEq bridge: `Decidable (@Eq α a b)` is inhabited by `DecidableEq α`
        // applied to `a b`, since `DecidableEq α` is definitionally
        // `(a b : α) → Decidable (a = b)`. The lean4-core prelude ships no
        // standalone `Decidable` *instance* for this, so instance search never
        // finds it — `Decidable (a = b)` in a `resolve_instance` context (a
        // `[Decidable (a=b)]` binder, a dependent `if h : a = b`, the decide lane's
        // `eval_decide`) fails. Bridge it explicitly: resolve `DecidableEq α` and
        // apply it. Weakening-only — adds resolutions, never changes an existing
        // one; the kernel re-checks the emitted `(decEqInst a b)` term.
        if class_name.to_string() == "Decidable" && goal_args.len() == 1 {
            let eq_app = self.whnf(&self.metas.instantiate(&goal_args[0]));
            let eq_fn = eq_app.get_app_fn();
            if let ExprKind::Const(eq_name, eq_levels) = eq_fn.kind() {
                let eq_args = eq_app.get_app_args();
                if eq_name.to_string() == "Eq" && eq_args.len() == 3 {
                    let alpha = eq_args[0].clone();
                    let a = eq_args[1].clone();
                    let b = eq_args[2].clone();
                    let dec_eq_goal = Expr::app(
                        Expr::const_(Name::from_string("DecidableEq"), eq_levels.to_vec()),
                        alpha,
                    );
                    if let Some(inst) =
                        self.resolve_instance_with_depth(&dec_eq_goal, depth + 1, goal_path, strict)
                    {
                        let applied = Expr::apps(inst, [a, b]);
                        let result = self
                            .metas
                            .instantiate_levels(&self.metas.instantiate(&applied));
                        if goal_is_ground {
                            self.instance_cache
                                .insert(cache_key.to_string(), result.clone());
                        }
                        return Some(result);
                    }
                }
            }
        }

        // Check local instance-implicit binders in reverse (index-based to avoid O(N) Vec alloc).
        let num_local = self.local_instances.len();
        for i in (0..num_local).rev() {
            let (fvar, local_ty) = self.local_instances[i].clone();
            let local_ty_inst = self.metas.instantiate(&local_ty);
            let local_ty_norm = self.whnf(&local_ty_inst);

            if let Some((local_class, local_args)) = extract_class_app(&local_ty_norm) {
                if local_class == class_name && local_args.len() == goal_args.len() {
                    // Try to unify the local instance arguments with the goal arguments
                    self.metas.push_scope();
                    let mut unified = true;

                    for (local_arg, goal_arg) in local_args.iter().zip(goal_args.iter()) {
                        if !self.try_unify(local_arg, goal_arg) {
                            unified = false;
                            break;
                        }
                    }

                    if unified {
                        // Local instance matches - commit scope and return the fvar reference
                        self.metas.commit();
                        let result = Expr::fvar(fvar);

                        if goal_is_ground {
                            self.instance_cache
                                .insert(cache_key.to_string(), result.clone());
                        }

                        return Some(result);
                    } else {
                        // Restore metavariable state on failed unification
                        self.metas.pop_scope();
                    }
                }
            }
        }

        // Check if this is a registered type class
        if !self.instances.is_class(&class_name) {
            return None;
        }

        // Get out-parameter and semi-out-parameter indices for this class
        let (out_params, semi_out_params): (Vec<usize>, Vec<usize>) = self
            .instances
            .get_class(&class_name)
            .map(|info| (info.out_params.clone(), info.semi_out_params.clone()))
            .unwrap_or_default();

        // Note: semiOutParams are treated like regular parameters during unification
        // (they participate in Phase 1 bidirectional unification), but instances
        // promise to always fill them with concrete values. The only difference
        // from regular params is this "promise" - useful for tooling/error messages.

        // Whether an undetermined bare-metavar INPUT position of THIS class goal
        // must trigger Lean-style postponement in phase-1 unification below.
        // Gated to input-only classes with no out-params (see
        // `is_input_only_postpone_class`), so it provably cannot alter
        // arithmetic / heterogeneous out-param resolution — OR to any goal
        // reached from such a root (`strict`, see `resolve_instance`), which is
        // the hop the one-hop form was missing.
        let postpone_undetermined_inputs = strict || is_input_only_postpone_class(&class_name);

        // B99: Lean's `@[default_instance]` defaulting. When the goal still
        // has an OPEN (bare unassigned metavariable) INPUT position — no
        // use-site has pinned the carrier — real Lean does not run the plain
        // instance search: it POSTPONES the goal and, if nothing ever pins
        // it, applies the registered DEFAULT instances for the class in
        // priority order (`Lean/Elab/DefaultInstance`). Clean's eager search
        // instead let table order pick the carrier (the r82
        // `instprio_default_instance_mvar` silent-wrong: 3 provable where
        // Lean's defaulting proves 4). When the class HAS user-registered
        // default instances, restrict the candidate set to exactly those
        // (highest default-priority first, most recent within a tier) and —
        // if none applies — fail LOUD (return None) rather than falling back
        // to the ordering-chosen grab. Classes without default instances
        // keep the pre-existing eager search unchanged.
        let default_order = if self.default_instances.is_empty() {
            // No user `@[default_instance]` in this file — the common case;
            // skip the open-input scan entirely (hot path unchanged).
            None
        } else {
            let stuck_open_input = goal_args.iter().enumerate().any(|(idx, arg)| {
                !out_params.contains(&idx)
                    && !semi_out_params.contains(&idx)
                    && bare_unassigned_meta(&self.metas, &self.metas.instantiate(arg)).is_some()
            });
            if stuck_open_input {
                self.default_instance_order(&class_name)
            } else {
                None
            }
        };
        let defaulting = default_order.is_some();

        // Try each instance in priority order; within a priority tier, order by
        // head-symbol compatibility with the goal (Lean-faithful; see
        // `candidate_order`).
        let order = default_order.unwrap_or_else(|| self.candidate_order(&class_name, &goal_args));
        for inst_idx in order {
            let inst = self.instances.get_instances(&class_name)[inst_idx].clone();
            // Push scope for backtracking on failure
            self.metas.push_scope();

            // Freshen the candidate's universe-level parameters. The stored
            // instance term/type carry the instance CONSTANT's declared
            // level-param names verbatim (e.g. Lean-core `instHAdd.{u_1}` —
            // `{α : Type u_1} → [Add α] → HAdd α α α`). Unifying that raw type
            // against the goal below pins those NAMES in the declaration-wide,
            // Name-keyed level union-find (`add_level_constraint`), where they
            // collide with (a) the elaborator's own fresh params —
            // `fresh_universe_param()` also generates `u_1`, `u_2`, … — and
            // (b) the same-named declared params of every other polymorphic
            // instance used in the same declaration. Observed failure mode:
            // resolving `instHAdd` for a `Nat`-typed `k + 1` committed
            // `u_1 := Zero`; the statement's own fresh `u_1` (an `Eq` at a
            // `Type`-valued carrier, needing `Succ Zero`) then failed with
            // "universe level conflict: Zero vs Succ(Zero)" (the trust-ir
            // data-loop bridge blocker). Substituting a fresh param per
            // declared name — exactly what Lean does when it instantiates a
            // candidate's universe metavariables — makes unification pin
            // per-candidate names that cannot alias anything else.
            let mut raw_level_params: Vec<Name> = Vec::new();
            crate::level_params::collect_level_params_from_expr(&inst.type_, &mut raw_level_params);
            crate::level_params::collect_level_params_from_expr(&inst.expr, &mut raw_level_params);
            let (inst_type_fresh, inst_expr_fresh) = if raw_level_params.is_empty() {
                (inst.type_.clone(), inst.expr.clone())
            } else {
                let level_subst: Vec<(Name, Level)> = raw_level_params
                    .iter()
                    .map(|n| (n.clone(), self.fresh_universe_param()))
                    .collect();
                (
                    inst.type_.instantiate_level_params(&level_subst),
                    inst.expr.instantiate_level_params(&level_subst),
                )
            };

            // The instance expression and type (may contain implicit binders).
            // As with the goal above, keep the instance type un-whnf'd when it is
            // already a registered-class application (e.g. a concrete
            // `instColorDecidableEq : DecidableEq Color`); whnf would unfold the
            // `DecidableEq` head to its Pi and the post-strip class would read as
            // `Decidable`, mismatching the `DecidableEq` goal. Pi-headed instances
            // (the `decEq` bridge `{α} → [DecidableEq α] → …`) still whnf so their
            // implicit/instance binders get stripped below.
            let mut inst_expr = inst_expr_fresh;
            let mut inst_type = if extract_class_app(&inst_type_fresh)
                .is_some_and(|(n, _)| self.instances.is_class(&n))
            {
                inst_type_fresh
            } else {
                self.whnf(&inst_type_fresh)
            };
            // Pending `[inst]` sub-goals as (telescope binder index, meta,
            // binder type at strip time). The binder index keys the sub-goal
            // into the instance's synthesization order below.
            let mut pending_inst_args: Vec<(usize, Expr, Expr)> = Vec::new();
            // Every metavariable allocated for THIS candidate's binders, kept
            // for the determinedness check below (see "candidate hygiene").
            let mut binder_metas: Vec<Expr> = Vec::new();

            // Apply implicit parameters in the instance type (including dependent instances)
            while let ExprKind::Pi(bi, arg_ty, body_ty) = inst_type.kind() {
                let binder_idx = binder_metas.len();
                let instantiated_arg_ty = self.metas.instantiate(arg_ty);

                let arg = match bi.info {
                    BinderInfo::InstImplicit => {
                        // Defer dependent instance resolution until after the
                        // candidate result has unified with the target. This
                        // lets inputs such as `R` in
                        // `{R} -> [Semiring R] -> Semiring (F R)` be inferred
                        // from the requested `Semiring (F T)` before resolving
                        // `[Semiring R]`.
                        let meta = self.fresh_meta(instantiated_arg_ty.clone());
                        pending_inst_args.push((binder_idx, meta.clone(), instantiated_arg_ty));
                        meta
                    }
                    // For other binders, create a metavariable to be solved by unification
                    _ => self.fresh_meta(instantiated_arg_ty.clone()),
                };
                binder_metas.push(arg.clone());

                // Apply the argument to the instance expression and type
                inst_expr = self.apply_instance_arg(inst_expr, &arg);
                inst_type = self.whnf(&self.metas.instantiate(&body_ty.instantiate(&arg)));
            }

            // Extract class name and args from instance type after applying implicit binders
            if let Some((inst_class, inst_levels, inst_args)) =
                crate::instances::extract_class_app_with_levels(&inst_type)
            {
                if inst_class != class_name {
                    self.metas.pop_scope();
                    continue;
                }

                // Unify the CLASS CONSTANT's universe levels, not just its
                // arguments. A class whose level does not appear in any
                // argument — `HasEquiv.{u,v} (α : Sort u)`, where `v` lives
                // only in the `Equiv` field — otherwise leaves that level an
                // unsolved metavariable in the goal (`HasEquiv {1, ?v} Nat`)
                // that argument unification can never pin, and synthesis
                // fails even though the candidate matches. The candidate's
                // levels are freshened above, so this only ever SOLVES goal
                // metavariables or rejects a genuinely level-mismatched
                // candidate; the produced term is kernel-rechecked.
                if inst_levels.len() == goal_levels.len() {
                    let mut levels_ok = true;
                    for (inst_lvl, goal_lvl) in inst_levels.iter().zip(goal_levels.iter()) {
                        // Level unification touches no free variable: an
                        // empty context is the exact closure of its inputs.
                        let ctx = self.demand_local_ctx(&[]);
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        if !matches!(
                            unifier.unify_levels(inst_lvl, goal_lvl),
                            UnifyResult::Success
                        ) {
                            levels_ok = false;
                            break;
                        }
                    }
                    if !levels_ok {
                        self.metas.pop_scope();
                        continue;
                    }
                }

                // Try to unify the instance arguments with the goal arguments
                if inst_args.len() != goal_args.len() {
                    self.metas.pop_scope();
                    continue;
                }

                // Two-phase unification for out-parameters:
                // Phase 1: Unify non-out-parameters first (these must match)
                let mut unified = true;
                for (idx, (inst_arg, goal_arg)) in
                    inst_args.iter().zip(goal_args.iter()).enumerate()
                {
                    if !out_params.contains(&idx) {
                        // Lean-style POSTPONEMENT of an undetermined INPUT.
                        //
                        // For a non-out-param (INPUT) argument of an input-only
                        // class, the GOAL must determine the argument — never the
                        // candidate. If the goal's arg is still a BARE UNASSIGNED
                        // metavariable and the candidate's arg is RIGID/concrete,
                        // the `try_unify` below would assign `?goalInput :=
                        // <candidate concrete>`, letting the FIRST candidate tried
                        // backfill the input and grabbing a WRONG instance (a
                        // decoy `Decidable SomeProp` seized for a `Decidable ?a`
                        // goal). Lean's `synthInstance` instead POSTPONES a goal
                        // whose input positions are still metavariables and retries
                        // once the surrounding term pins them. Reject this
                        // candidate so the whole search returns None (postpone)
                        // rather than committing garbage.
                        //
                        // Restricted to input-only classes with no out-params (the
                        // `postpone_undetermined_inputs` allowlist) or to any
                        // goal reached from such a root (`strict`): out-param /
                        // heterogeneous arithmetic classes (HAdd/HMod/…) never
                        // reach here for their out positions — phase 1 skips
                        // out-params — so this cannot alter their resolution. A
                        // FLEXIBLE candidate arg (itself a bare metavar) is NOT
                        // rejected: flex/flex unification is legitimately
                        // deferred, not a wrong grab.
                        //
                        // NOTE this is the GLOBAL-candidate loop only. The
                        // local-instance loop above is deliberately unguarded at
                        // every depth: a local `[inst : C t]` binder is a
                        // hypothesis of the declaration being elaborated, and
                        // pinning the carrier from it is evidence rather than
                        // invention — see `resolve_instance`.
                        //
                        // Suppressed while DEFAULTING (B99): a default
                        // instance's entire purpose is to pin an open input,
                        // so the undetermined-input rejection must not veto
                        // it.
                        if postpone_undetermined_inputs && !defaulting {
                            let goal_arg_inst = self.metas.instantiate(goal_arg);
                            if bare_unassigned_meta(&self.metas, &goal_arg_inst).is_some() {
                                let inst_arg_inst = self.metas.instantiate(inst_arg);
                                if bare_unassigned_meta(&self.metas, &inst_arg_inst).is_none() {
                                    unified = false;
                                    break;
                                }
                            }
                        }
                        // Non-out-parameter: must unify
                        if !self.try_unify(inst_arg, goal_arg) {
                            unified = false;
                            break;
                        }
                    }
                }

                if !unified {
                    self.metas.pop_scope();
                    continue;
                }

                // Phase 2: Unify out-parameters (these can be inferred from the instance)
                for (idx, (inst_arg, goal_arg)) in
                    inst_args.iter().zip(goal_args.iter()).enumerate()
                {
                    if out_params.contains(&idx) {
                        // Out-parameter: try to unify, direction is instance -> goal
                        if !self.try_unify(inst_arg, goal_arg) {
                            unified = false;
                            break;
                        }
                    }
                }

                if unified {
                    // Synthesize the candidate's `[inst]` sub-goals in the
                    // instance's synthesization order (Lean's
                    // `InstanceEntry.synthOrder`, consumed verbatim by
                    // `getSubgoals` in `Lean/Meta/SynthInstance.lean:337`),
                    // NOT in binder order: a sub-goal's solution pins
                    // metavariables (e.g. the middle monad `n` of
                    // `instMonadLiftTOfMonadLift : (m n o) → [MonadLift n o] →
                    // [MonadLiftT m n] → MonadLiftT m o`) that later sub-goals
                    // consume — assignments propagate through the shared meta
                    // state via the re-instantiation before each recursion.
                    // Imported instances carry Lean's persisted order;
                    // hand-registered ones get the Lean-style default
                    // (`super::synth_order`, out-param-driven port of
                    // `computeSynthOrder`, `Lean/Meta/Instances.lean:145-229`).
                    let scheduled = self.schedule_pending_subgoals(&inst, &pending_inst_args);
                    let mut resolved_pending = true;
                    for pos in scheduled {
                        let (_, meta_arg, arg_ty) = pending_inst_args[pos].clone();
                        let arg_ty = self.metas.instantiate(&arg_ty);
                        let Some(resolved) =
                            self.resolve_instance_with_depth(&arg_ty, depth + 1, goal_path, strict)
                        else {
                            resolved_pending = false;
                            break;
                        };
                        let ExprKind::FVar(fvar) = meta_arg.kind() else {
                            resolved_pending = false;
                            break;
                        };
                        let Some(meta_id) = MetaState::from_fvar(*fvar) else {
                            resolved_pending = false;
                            break;
                        };
                        if !self.metas.assign(meta_id, resolved) {
                            resolved_pending = false;
                            break;
                        }
                    }
                    if !resolved_pending {
                        self.metas.pop_scope();
                        continue;
                    }

                    // Candidate hygiene: every metavariable allocated for THIS
                    // candidate's binders must end the search DETERMINED — either
                    // assigned (by unification with the goal or by the pending
                    // instance resolution above) or unified into the goal itself
                    // (the unifier may orient `goal-meta := candidate-meta`, in
                    // which case the meta legitimately survives as part of the
                    // caller's goal and is solved later by the caller). A
                    // candidate that "succeeds" while leaving a binder hole the
                    // goal does not determine is NOT evidence for the goal: the
                    // classic shape is a constructor or hypothesis-taking
                    // definition registered as an instance (`Decidable.isFalse
                    // {p} (h : ¬p) : Decidable p` from an `.olean` import — its
                    // `¬p` proof binder unifies with nothing and can never be
                    // synthesized). Lean's `synthInstance` likewise fails a
                    // candidate with unassigned mvars. Returning such a term
                    // used to leak the unassigned metavariable (encoded as a
                    // tagged FVar) into the elaborated declaration, surfacing
                    // far from the cause as the kernel's fail-closed
                    // "Declaration contains free variables" rejection (the
                    // trust-ir bridge blocker on `if rhs ≥ Int.ofNat width …`
                    // guards). Reject the candidate and let the search continue
                    // to a genuinely applicable instance — weakening-only for
                    // accepts: any candidate rejected here could only have
                    // produced a kernel-rejected term.
                    let goal_metas = self.collect_meta_fvars(&self.metas.instantiate(goal_ty));
                    let undetermined = binder_metas.iter().any(|meta_arg| {
                        let solved = self.metas.instantiate(meta_arg);
                        has_meta_fvar_outside(&solved, &goal_metas)
                    });
                    if undetermined {
                        self.metas.pop_scope();
                        continue;
                    }

                    // Commit scope - instance resolution succeeded
                    self.metas.commit();
                    // Apply any metavariable substitutions and return the instance
                    let result = self.metas.instantiate(&inst_expr);
                    // Also apply universe level constraints (#152: instance resolution
                    // must substitute concrete levels for typeclass universe params)
                    let result = self.metas.instantiate_levels(&result);

                    // Cache the result if the goal was ground
                    if goal_is_ground {
                        self.instance_cache
                            .insert(cache_key.to_string(), result.clone());
                    }

                    return Some(result);
                }
            }

            // Unification failed, restore metavariable state
            self.metas.pop_scope();
        }

        None
    }

    /// Lean-faithful candidate order for a class goal — a discrimination-tree
    /// approximation over the priority-sorted instance list.
    ///
    /// Real Lean's `synthInstance` looks candidates up in a discrimination tree
    /// keyed with reducible-only whnf: an instance whose conclusion argument has
    /// a RIGID head constant different from the goal's (e.g. `OfNat (Id ?α) ?n`
    /// against `OfNat Int 0`) is never even considered — it could only match by
    /// unfolding a non-reducible definition. Clean's unifier, by contrast,
    /// happily delta-unfolds `Id`, so such a wrapper candidate placed early
    /// self-matched its own recursive subgoal until the depth limit and buried
    /// the genuine instance under 30+ redundant wrappers (`Id.instOfNat` around
    /// `instOfNat` — the `(0 : Int)` literal-shape divergence of the trust-ir
    /// Lean↔Clean bridge). Within each priority tier this orders candidates by:
    ///
    /// 1. no rigid head-constant mismatch before any mismatch (mismatched
    ///    candidates are DEMOTED, not skipped: clean environments occasionally
    ///    rely on delta matching, so completeness is preserved — a demoted
    ///    candidate is still tried when nothing compatible resolves);
    /// 2. more exact head-constant matches first (real Lean reaches the same
    ///    choice via most-recently-declared-first search order, which the
    ///    import lane's alphabetical registration cannot reproduce);
    /// 3. original (registration) order as the stable tiebreaker.
    ///
    /// Priority still dominates everything, exactly as before.
    fn candidate_order(&self, class_name: &Name, goal_args: &[Expr]) -> Vec<usize> {
        use crate::instances::extract_class_app;

        // Rigid head constant of an expression, if any. `None` = flexible
        // (metavariable, bound variable, sort, lambda, …) — matches anything.
        fn rigid_head(e: &Expr) -> Option<Name> {
            match e.get_app_fn().kind() {
                ExprKind::Const(n, _) => Some(n.clone()),
                _ => None,
            }
        }

        let instances = self.instances.get_instances(class_name);
        let goal_heads: Vec<Option<Name>> = goal_args
            .iter()
            .map(|a| rigid_head(&self.metas.instantiate(a)))
            .collect();

        let mut order: Vec<(
            std::cmp::Reverse<u32>,
            bool,
            std::cmp::Reverse<usize>,
            usize,
        )> = Vec::with_capacity(instances.len());
        for (idx, inst) in instances.iter().enumerate() {
            // Scope visibility (B99): a `local instance` whose section has
            // ended, or a `scoped instance` whose namespace is neither
            // current nor opened, is NOT a candidate at all.
            if !self.instance_visible(&inst.name) {
                continue;
            }
            // Structural conclusion of the instance type: strip leading Pis,
            // then read the class application. Bound variables left in the
            // conclusion are flexible for head scoring, which is all we need.
            let mut conclusion = &inst.type_;
            while let ExprKind::Pi(_, _, body) = conclusion.kind() {
                conclusion = body;
            }
            let (mut mismatch, mut exact) = (false, 0usize);
            if let Some((inst_class, inst_args)) = extract_class_app(conclusion) {
                if inst_class == *class_name && inst_args.len() == goal_heads.len() {
                    for (inst_arg, goal_head) in inst_args.iter().zip(goal_heads.iter()) {
                        if let (Some(ih), Some(gh)) = (rigid_head(inst_arg), goal_head.as_ref()) {
                            if ih == *gh {
                                exact += 1;
                            } else {
                                mismatch = true;
                            }
                        }
                    }
                }
            }
            order.push((
                std::cmp::Reverse(inst.priority),
                mismatch,
                std::cmp::Reverse(exact),
                idx,
            ));
        }
        order.sort();
        order.into_iter().map(|(_, _, _, idx)| idx).collect()
    }

    /// Whether an instance is visible for resolution under the current
    /// scope state (B99).
    ///
    /// - `local instance`s whose declaring section/namespace block has ended
    ///   are in `hidden_instances` and never visible again.
    /// - `scoped instance`s are visible only while their declaring namespace
    ///   is ACTIVE: it is the current namespace (or an ancestor of it), or it
    ///   appears in `namespace_state.open_namespaces()` (populated by simple
    ///   `open Foo` / `open Foo in …`, with scope rollback). Explicit opens
    ///   (`open Foo (x)`) do NOT activate scoped instances — matching Lean,
    ///   where only `activateScoped` on simple opens/namespace entry does.
    ///
    /// Everything else (the overwhelmingly common case) is visible; both maps
    /// default to empty, so resolution is unchanged unless a `local`/`scoped`
    /// instance modifier was actually used.
    fn instance_visible(&self, name: &Name) -> bool {
        if self.hidden_instances.contains(name) {
            return false;
        }
        match self.scoped_instances.get(name) {
            None => true,
            Some(ns) => {
                if self.namespace_state.open_namespaces().contains(ns) {
                    return true;
                }
                let current = self.namespace_state.current_namespace();
                if current == ns {
                    return true;
                }
                // Inside a descendant namespace of the declaring one.
                let current_str = current.to_string();
                let ns_prefix = format!("{ns}.");
                current_str.starts_with(&ns_prefix)
            }
        }
    }

    /// Candidate order for Lean's `@[default_instance]` DEFAULTING of a goal
    /// with an open input (B99): indices into `get_instances(class_name)`
    /// restricted to the class's registered default instances, ordered by
    /// default-instance priority (highest first) and most-recent declaration
    /// within a tier. Returns `None` when the class has no default instances
    /// (caller falls back to the plain search); `Some(vec![])` when defaults
    /// exist but none is currently visible/resolvable — the caller's loop
    /// then fails LOUD instead of grabbing an ordering-chosen carrier.
    fn default_instance_order(&self, class_name: &Name) -> Option<Vec<usize>> {
        let entries = self.default_instances.get(class_name)?;
        if entries.is_empty() {
            return None;
        }
        let instances = self.instances.get_instances(class_name);
        let mut order: Vec<(std::cmp::Reverse<u32>, std::cmp::Reverse<usize>, usize)> = Vec::new();
        for (decl_pos, (name, priority)) in entries.iter().enumerate() {
            if !self.instance_visible(name) {
                continue;
            }
            if let Some(idx) = instances.iter().position(|i| i.name == *name) {
                order.push((
                    std::cmp::Reverse(*priority),
                    std::cmp::Reverse(decl_pos),
                    idx,
                ));
            }
        }
        order.sort();
        order.dedup_by_key(|entry| entry.2);
        Some(order.into_iter().map(|entry| entry.2).collect())
    }

    /// Apply an argument to an instance expression, performing a simple
    /// beta-reduction when the expression is a lambda.
    fn apply_instance_arg(&self, func: Expr, arg: &Expr) -> Expr {
        match func.kind() {
            ExprKind::Lam(_, _, body) => body.instantiate(arg),
            _ => Expr::app(func, arg.clone()),
        }
    }

    /// Try to unify two expressions, returning true on success
    pub(super) fn try_unify(&mut self, e1: &Expr, e2: &Expr) -> bool {
        // MEASURED: this is the per-candidate hot path of instance resolution
        // (94.5% / 94.7% of two profiles of `Mathlib/Logic/Basic` were the
        // full-context rebuild here, once per candidate, after every other
        // sink had been removed). The unifier can only reach free variables
        // of `e1`/`e2` — raw (the metavariables it will look up) and
        // instantiated (what those metavariables already stand for) — and of
        // the declarations those transitively mention, so the demand-driven
        // closure is observationally the same context at a cost proportional
        // to the two terms instead of to every metavariable of the
        // declaration (see `demand_local_ctx`).
        let e1_inst = self.metas.instantiate(e1);
        let e2_inst = self.metas.instantiate(e2);
        let ctx = self.demand_local_ctx(&[e1, e2, &e1_inst, &e2_inst]);
        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
        matches!(unifier.unify(e1, e2), UnifyResult::Success)
    }

    /// Order the candidate's pending `[inst]` sub-goals for synthesis.
    ///
    /// Returns positions into `pending` (each exactly once). The primary
    /// source is the instance's persisted `synthOrder` (decoded from the
    /// `.olean`'s `Lean.Meta.instanceExtension`; binder indices per
    /// `Lean/Meta/Instances.lean:46-60`); instances without one — the
    /// hand-registered prelude lane — get the Lean-style default computed
    /// from the instance type (`super::synth_order::default_synth_order`,
    /// port of `computeSynthOrder`). Defensive by construction: order
    /// entries that name no pending sub-goal (stale index, non-inst binder)
    /// are ignored, and pending sub-goals the order misses are appended in
    /// binder order — every sub-goal is synthesized exactly once, so a
    /// malformed order can only affect scheduling, never drop a sub-goal
    /// (no silent under-constraining) or panic.
    fn schedule_pending_subgoals(
        &self,
        inst: &crate::instances::InstanceInfo,
        pending: &[(usize, Expr, Expr)],
    ) -> Vec<usize> {
        if pending.len() <= 1 {
            return (0..pending.len()).collect();
        }
        let order_src: Vec<usize> = match &inst.synth_order {
            Some(order) => order.clone(),
            None => super::synth_order::default_synth_order(&self.instances, &inst.type_),
        };
        let mut scheduled: Vec<usize> = Vec::with_capacity(pending.len());
        for binder_idx in order_src {
            if let Some(pos) = pending.iter().position(|(idx, _, _)| *idx == binder_idx) {
                if !scheduled.contains(&pos) {
                    scheduled.push(pos);
                }
            }
        }
        for pos in 0..pending.len() {
            if !scheduled.contains(&pos) {
                scheduled.push(pos);
            }
        }
        scheduled
    }

    /// Check if an expression contains any metavariables.
    ///
    /// DAG-aware iterative walk (measured: the previous `ExprVisitor`
    /// tree-recursion was path-exponential on the Arc-shared DAGs the
    /// sharing-preserving `MetaState::instantiate` produces — third profiled
    /// hot site of the trust-clean `dataloop_composed_wall_reproducer`).
    /// Meta-encoded FVars are found via the O(1) cached `has_fvar` prune +
    /// pointer-identity visited set; Const level lists are checked with the
    /// same structural `level_has_metavars` as before (constant-false today
    /// — `Level` has no metavariable variant, matching the kernel's own
    /// `level_has_mvar` — the match is kept for compile-time safety on
    /// future variants, so the fvar-flag prune loses nothing).
    pub(super) fn has_metavars(&self, e: &Expr) -> bool {
        /// Check if a level contains any metavariables (universe level params).
        fn level_has_metavars(l: &Level) -> bool {
            match l {
                Level::Zero | Level::Param(_) => false,
                Level::Succ(l) => level_has_metavars(l),
                Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                    level_has_metavars(l1) || level_has_metavars(l2)
                }
            }
        }

        let mut visited: HashSet<*const Expr> = HashSet::new();
        let mut stack: Vec<&Expr> = vec![e];
        while let Some(cur) = stack.pop() {
            if !cur.has_fvar_quick() && !cur.has_level_mvar_quick() {
                continue;
            }
            if !visited.insert(cur as *const Expr) {
                continue;
            }
            match cur.kind() {
                ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some() => {
                    return true;
                }
                ExprKind::Const(_, levels) if levels.iter().any(level_has_metavars) => {
                    return true;
                }
                _ => {}
            }
            crate::unify::push_expr_children(cur, &mut stack);
        }
        false
    }

    /// Collect the meta-encoded FVar ids (expression metavariables) occurring
    /// in `e`. Companion to [`Self::has_metavars`], used by the candidate
    /// hygiene check in instance resolution to decide whether a candidate's
    /// residual metavariables are the goal's own (allowed — solved later by the
    /// caller) or freshly leaked binder holes (rejected). DAG-aware for the
    /// same measured reason as [`Self::has_metavars`].
    fn collect_meta_fvars(&self, e: &Expr) -> HashSet<FVarId> {
        let mut out: HashSet<FVarId> = HashSet::new();
        let mut visited: HashSet<*const Expr> = HashSet::new();
        let mut stack: Vec<&Expr> = vec![e];
        while let Some(cur) = stack.pop() {
            if !cur.has_fvar_quick() {
                continue;
            }
            if !visited.insert(cur as *const Expr) {
                continue;
            }
            if let ExprKind::FVar(id) = cur.kind() {
                if MetaState::from_fvar(*id).is_some() {
                    out.insert(*id);
                }
            }
            crate::unify::push_expr_children(cur, &mut stack);
        }
        out
    }

    /// Normalize an expression for use as a cache key.
    ///
    /// This replaces metavariables with synthetic placeholders so that
    /// structurally similar goals (differing only in metavariable IDs)
    /// map to the same cache key.
    ///
    /// For example, `Add ?m1` and `Add ?m2` both normalize to `Add ?_0`.
    /// Key used for instance-search cycle detection.
    ///
    /// Same as [`Self::normalize_for_cache`], except each class ARGUMENT is
    /// weak-head normalized first, so goals that differ only by a reducible
    /// wrapper (`OfNat Nat 0` vs `OfNat (Id Nat) 0`) share a key. The class head
    /// is left exactly as-is, so `def`-based class heads are preserved.
    ///
    /// Falls back to `cache_key` when the goal is not a class application, which
    /// keeps the previous behaviour for every non-class goal.
    fn cycle_detection_key(&mut self, goal_ty: &Expr, cache_key: &str) -> String {
        use crate::instances::extract_class_app;

        let Some((class_name, args)) = extract_class_app(goal_ty) else {
            return cache_key.to_string();
        };
        let mut key = String::from("cyc:");
        key.push_str(&class_name.to_string());
        for arg in &args {
            let arg = self.metas.instantiate(arg);
            let reduced = self.whnf(&arg);
            let reduced = self.metas.instantiate(&reduced);
            key.push('|');
            key.push_str(&self.normalize_for_cache(&reduced));
        }
        key
    }

    pub(super) fn normalize_for_cache(&self, e: &Expr) -> String {
        let mut meta_map: HashMap<u64, usize> = HashMap::new();
        let mut next_id = 0;

        fn normalize_expr(
            e: &Expr,
            meta_map: &mut HashMap<u64, usize>,
            next_id: &mut usize,
        ) -> String {
            stack_safe(|| match e.kind() {
                ExprKind::BVar(idx) => format!("#{idx}"),
                ExprKind::FVar(fvar) => {
                    // Check if this is a metavariable (has high-bit tag)
                    if let Some(meta_id) = MetaState::from_fvar(*fvar) {
                        // Normalize metavariable IDs
                        let norm_id = *meta_map.entry(meta_id.0).or_insert_with(|| {
                            let id = *next_id;
                            *next_id += 1;
                            id
                        });
                        format!("?_{norm_id}")
                    } else {
                        // Regular free variable
                        format!("@{}", fvar.as_u64())
                    }
                }
                ExprKind::Sort(lvl) => format!("Sort({})", normalize_level(lvl, meta_map, next_id)),
                ExprKind::Const(name, levels) => {
                    let lvls: Vec<_> = levels
                        .iter()
                        .map(|l| normalize_level(l, meta_map, next_id))
                        .collect();
                    if lvls.is_empty() {
                        format!("C:{name}")
                    } else {
                        format!("C:{}.[{}]", name, lvls.join(","))
                    }
                }
                ExprKind::App(f, arg) => {
                    format!(
                        "({} {})",
                        normalize_expr(f, meta_map, next_id),
                        normalize_expr(arg, meta_map, next_id)
                    )
                }
                ExprKind::Lam(bi, ty, body) => {
                    format!(
                        "(λ{:?} {} → {})",
                        bi,
                        normalize_expr(ty, meta_map, next_id),
                        normalize_expr(body, meta_map, next_id)
                    )
                }
                ExprKind::Pi(bi, ty, body) => {
                    format!(
                        "(Π{:?} {} → {})",
                        bi,
                        normalize_expr(ty, meta_map, next_id),
                        normalize_expr(body, meta_map, next_id)
                    )
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    format!(
                        "(let {} := {} in {})",
                        normalize_expr(ty, meta_map, next_id),
                        normalize_expr(val, meta_map, next_id),
                        normalize_expr(body, meta_map, next_id)
                    )
                }
                ExprKind::Lit(lit) => format!("{lit:?}"),
                ExprKind::Proj(name, idx, e) => {
                    format!("{}.{}:{}", normalize_expr(e, meta_map, next_id), name, idx)
                }
                ExprKind::MData(_, inner) => {
                    // MData wraps another expression with metadata; normalize the inner
                    normalize_expr(inner, meta_map, next_id)
                }
                ExprKind::Squash(inner) => {
                    format!("Squash({})", normalize_expr(inner, meta_map, next_id))
                }
                ExprKind::CubicalPath { ty, left, right } => {
                    format!(
                        "Path({},{},{})",
                        normalize_expr(ty, meta_map, next_id),
                        normalize_expr(left, meta_map, next_id),
                        normalize_expr(right, meta_map, next_id)
                    )
                }
                ExprKind::CubicalPathLam { body } => {
                    format!("PathLam({})", normalize_expr(body, meta_map, next_id))
                }
                ExprKind::CubicalPathApp { path, arg } => {
                    format!(
                        "PathApp({},{})",
                        normalize_expr(path, meta_map, next_id),
                        normalize_expr(arg, meta_map, next_id)
                    )
                }
                ExprKind::CubicalHComp { ty, phi, u, base } => {
                    format!(
                        "HComp({},{},{},{})",
                        normalize_expr(ty, meta_map, next_id),
                        normalize_expr(phi, meta_map, next_id),
                        normalize_expr(u, meta_map, next_id),
                        normalize_expr(base, meta_map, next_id)
                    )
                }
                ExprKind::CubicalTransp { ty, phi, base } => {
                    format!(
                        "Transp({},{},{})",
                        normalize_expr(ty, meta_map, next_id),
                        normalize_expr(phi, meta_map, next_id),
                        normalize_expr(base, meta_map, next_id)
                    )
                }
                ExprKind::CubicalCoe { ty, r, s, base } => {
                    format!(
                        "Coe({},{},{},{})",
                        normalize_expr(ty, meta_map, next_id),
                        normalize_expr(r, meta_map, next_id),
                        normalize_expr(s, meta_map, next_id),
                        normalize_expr(base, meta_map, next_id)
                    )
                }
                ExprKind::ZFCSet(set_expr) => normalize_zfc_set_expr(set_expr, meta_map, next_id),
                ExprKind::ZFCMem { element, set } => {
                    format!(
                        "ZFCMem({},{})",
                        normalize_expr(element, meta_map, next_id),
                        normalize_expr(set, meta_map, next_id)
                    )
                }
                ExprKind::ZFCComprehension { domain, pred } => {
                    format!(
                        "ZFCComp({},{})",
                        normalize_expr(domain, meta_map, next_id),
                        normalize_expr(pred, meta_map, next_id)
                    )
                }
                // Leaf nodes
                ExprKind::CubicalInterval => "CubicalI".to_string(),
                ExprKind::CubicalI0 => "I0".to_string(),
                ExprKind::CubicalI1 => "I1".to_string(),
                ExprKind::SProp => "SProp".to_string(),
            })
        }

        fn normalize_level(
            l: &Level,
            _meta_map: &mut HashMap<u64, usize>,
            _next_id: &mut usize,
        ) -> String {
            // For levels, we use a simpler approach - just convert to string
            // Universe level metavariables are less common in instance resolution
            format!("{l:?}")
        }

        fn normalize_zfc_set_expr(
            set_expr: &ZFCSetExpr,
            meta_map: &mut HashMap<u64, usize>,
            next_id: &mut usize,
        ) -> String {
            stack_safe(|| match set_expr {
                ZFCSetExpr::Empty => "ZFCEmpty".to_string(),
                ZFCSetExpr::Infinity => "ZFCInf".to_string(),
                ZFCSetExpr::Singleton(e) => {
                    format!("ZFC{{{}}}", normalize_expr(e, meta_map, next_id))
                }
                ZFCSetExpr::Pair(a, b) => {
                    format!(
                        "ZFC{{{},{}}}",
                        normalize_expr(a, meta_map, next_id),
                        normalize_expr(b, meta_map, next_id)
                    )
                }
                ZFCSetExpr::Union(e) => {
                    format!("ZFCUnion({})", normalize_expr(e, meta_map, next_id))
                }
                ZFCSetExpr::PowerSet(e) => {
                    format!("ZFCPow({})", normalize_expr(e, meta_map, next_id))
                }
                ZFCSetExpr::Separation { set, pred } => {
                    format!(
                        "ZFCSep({},{})",
                        normalize_expr(set, meta_map, next_id),
                        normalize_expr(pred, meta_map, next_id)
                    )
                }
                ZFCSetExpr::Replacement { set, func } => {
                    format!(
                        "ZFCRep({},{})",
                        normalize_expr(set, meta_map, next_id),
                        normalize_expr(func, meta_map, next_id)
                    )
                }
                ZFCSetExpr::Choice(e) => {
                    format!("ZFCChoice({})", normalize_expr(e, meta_map, next_id))
                }
            })
        }

        normalize_expr(e, &mut meta_map, &mut next_id)
    }
}

/// True iff `class_name` is an input-only type class whose undetermined
/// bare-metavar INPUT arguments must trigger Lean-style postponement in
/// phase-1 instance unification.
///
/// Every class here has NO out-parameters, so ALL of its arguments are inputs
/// the GOAL must determine — never a candidate. Deliberately narrow
/// (`Decidable`, `DecidableEq`, `Inhabited`, `BEq`): it provably cannot alter
/// resolution of arithmetic / heterogeneous out-param classes
/// (`HAdd`/`HMod`/`HMul`/…), whose out positions never enter phase-1
/// unification (they are handled in phase 2) — so the postpone can only ever
/// touch input positions of these listed input-only classes. Lean reaches the
/// same effect uniformly via `synthInstance` mvar-postponement; the allowlist
/// is Clean's conservative staging, not a semantic distinction.
///
/// This predicate is consulted TWICE per search, and the difference matters:
/// once on the TOP-LEVEL goal, where a hit makes the whole search `strict`
/// (see [`ElabCtx::resolve_instance`]); and once per goal, so a goal in one of
/// these classes still postpones even when it was reached from a root that is
/// not.
fn is_input_only_postpone_class(class_name: &Name) -> bool {
    matches!(
        class_name.to_string().as_str(),
        "Decidable" | "DecidableEq" | "Inhabited" | "BEq"
    )
}

/// Return the metavariable id iff `e` is a BARE unassigned metavariable — a
/// meta-encoded FVar with no assignment in `metas`. Caller instantiates `e`
/// first, so a residual meta-FVar is genuinely unassigned; the `is_assigned`
/// guard is belt-and-suspenders. Used by the phase-1 postpone check to detect
/// an undetermined input position.
fn bare_unassigned_meta(metas: &MetaState, e: &Expr) -> Option<MetaId> {
    if let ExprKind::FVar(id) = e.kind() {
        if let Some(meta_id) = MetaState::from_fvar(*id) {
            if !metas.is_assigned(meta_id) {
                return Some(meta_id);
            }
        }
    }
    None
}

/// True iff `e` contains a meta-encoded FVar that is NOT in `allowed`.
///
/// Short-circuiting companion to `ElabCtx::collect_meta_fvars` for the
/// candidate-hygiene check: `allowed` holds the goal's own metavariables, so a
/// hit means the candidate leaked a binder hole the goal does not determine.
fn has_meta_fvar_outside(e: &Expr, allowed: &HashSet<FVarId>) -> bool {
    // DAG-aware iterative walk — same measured rationale as
    // `ElabCtx::has_metavars` (tree recursion is path-exponential on the
    // Arc-shared DAGs sharing-preserving instantiation produces).
    let mut visited: HashSet<*const Expr> = HashSet::new();
    let mut stack: Vec<&Expr> = vec![e];
    while let Some(cur) = stack.pop() {
        if !cur.has_fvar_quick() {
            continue;
        }
        if !visited.insert(cur as *const Expr) {
            continue;
        }
        if let ExprKind::FVar(id) = cur.kind() {
            if MetaState::from_fvar(*id).is_some() && !allowed.contains(id) {
                return true;
            }
        }
        crate::unify::push_expr_children(cur, &mut stack);
    }
    false
}
