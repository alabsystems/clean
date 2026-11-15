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

/// The instance state an `open … in` changed, to put back when its scope
/// ends ([`ElabCtx::restore_instance_state`]).
pub(crate) struct SavedInstanceState {
    view: crate::instance_store::InstanceView,
    hidden: HashSet<Name>,
    buckets: Vec<(Name, Vec<crate::instances::InstanceInfo>)>,
}

pub(super) mod alias_search;
mod binder_types;
mod locals_first;

/// Cap on the ∀-telescope a LOCAL instance binder may be opened under by
/// [`ElabCtx::resolve_local_instance_telescoped`]. `DecidableEq α` needs 2.
/// The cap exists so a pathological local type cannot turn a failure path into
/// an unbounded walk; a local needing more binders than this is refused, never
/// truncated.
const MAX_LOCAL_TELESCOPE: usize = 8;

/// Candidate attempts one top-level instance query may spend, summed over
/// every depth (see `ElabCtx::instance_search_steps`). Lean's
/// `synthInstance.maxSize` default is 128 table entries and its tabled
/// resolution never re-solves a subgoal; Clean's search is a backtracking
/// DFS, so the same problem costs more attempts here. 4096 leaves every
/// Mathlib resolution the pinned slice performs untouched (measured: the
/// five files re-run at exactly their counts) and bounds the exponential
/// failing case to well under a second.
const INSTANCE_SEARCH_BUDGET: usize = 4096;

/// Cap on the ∀-telescope a Pi-shaped GOAL may be opened under by
/// [`ElabCtx::resolve_pi_goal_by_abstraction`]. `DecidableEq α` needs 2. Same
/// contract as [`MAX_LOCAL_TELESCOPE`]: a goal needing more binders than this
/// is refused, never truncated — a truncated telescope would build a lambda of
/// the wrong arity.
const MAX_GOAL_TELESCOPE: usize = 8;

/// Instance resolution methods for ElabCtx
/// `CLEAN_INSTANCE_TRACE=1` prints one line per candidate the search tries
/// and why it was rejected (class head, universe levels, arity, argument
/// unification) — the switch that localized both the
/// `Classical.decidable_of_decidable_not` loop and the greedy `max` level
/// commitment behind `Compl (α → Prop)`. Off by default; the closure keeps
/// the render off the hot path.
fn inst_trace(line: impl FnOnce() -> String) {
    if std::env::var_os("CLEAN_INSTANCE_TRACE").is_some() {
        eprintln!("[inst] {}", line());
    }
}

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

    /// Whether a binder being brought into scope is a LOCAL INSTANCE.
    ///
    /// Lean's rule (`Lean.Meta.withNewLocalInstances`, keyed on `isClass?` of
    /// the local's TYPE): any local whose type is a class is a local instance,
    /// whatever its binder annotation — `[inst : C α]`, `{_ : C α}`,
    /// `{inst : C α}` and `(h : C α)` alike. Until 2026-09-10 Clean pushed
    /// only the instance-implicit spelling, so
    ///
    /// ```text
    /// def viaImplicit {α : Type u} {_ : Cls α} : α := Cls.x
    /// ```
    ///
    /// failed `failed to synthesize instance Cls for goal Cls fvar#0` with the
    /// instance sitting in the local context. Mathlib writes the implicit
    /// spelling routinely — `Mathlib/Logic/Unique.lean`'s
    /// `uniqueElim_default {_ : Unique ι}` and `uniqueElim_const` are two of
    /// the pinned slice's failures. Measured against the pinned `lean`
    /// v4.30.0-rc2: all four spellings accepted
    /// (`tests/fixtures/source_frontier/p28_class_typed_local_is_an_instance.lean`).
    ///
    /// The class test reads the CONCLUSION of a Pi telescope without opening
    /// it (a head test needs no fresh locals), so `(h : ∀ i, C (π i))` counts
    /// too — stage I-1's telescoped-local match already knows how to APPLY such
    /// a local; this is what lets it see one that was not written `[…]`.
    ///
    /// A REDUCIBLE ALIAS of a class counts too ([`Self::head_is_class`]):
    /// `(h : DecidableLE α)`, and above all the class FIELD
    /// `toDecidableLE : DecidableLE α` that Mathlib's `LinearOrder` declares
    /// and then uses two fields later (`min := fun a b => if a ≤ b then a else
    /// b`). The telescoped local match (stage I-1 (B)) already knows how to
    /// apply such a local; it only had to be allowed to see it.
    pub(super) fn binder_is_local_instance(&mut self, info: BinderInfo, ty: &Expr) -> bool {
        if info == BinderInfo::InstImplicit {
            return true;
        }
        let ty = self.metas.instantiate(ty);
        let mut concl = &ty;
        while let ExprKind::Pi(_, _, body) = concl.kind() {
            concl = body.as_ref();
        }
        crate::instances::extract_class_app(concl)
            .is_some_and(|(head, _)| self.head_is_class(&head))
    }

    /// Whether a type headed by the constant `head` is a class the way Lean's
    /// `isClass?` reads one (`Lean/Meta/Basic.lean`): `isClassQuick?` answers
    /// for a registered class, and for any other DEFINITION defers to
    /// `isClassExpensive?`, which is `withReducible do
    /// forallTelescopeReducing type … isClassApp?` — so a reducible alias whose
    /// telescope concludes in a class (`DecidableEq`, `DecidableLE`,
    /// `DecidablePred`, a user `abbrev`) is a class type whether or not an
    /// instance has been filed under it yet.
    ///
    /// Syntactic and bounded ([`crate::instance_alias::class_alias`]); it
    /// decides which locals the resolver may TRY, never what it accepts.
    pub(super) fn head_is_class(&self, head: &Name) -> bool {
        self.instances.is_class(head)
            || crate::instance_alias::class_alias(self.env, head, |n| self.instances.is_class(n))
                .is_some()
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
        // One budget per TOP-LEVEL query (see `instance_search_steps`);
        // every sub-goal below draws on it.
        self.instance_search_steps = 0;
        self.failed_local_subgoals.clear();
        // A STUCK verdict belongs to THIS query only (see
        // `instance_search_stuck`).
        self.instance_search_stuck = false;
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
        // One pass: an input-only root or premise makes its whole premise
        // subtree strict. A defaulting operator may therefore choose its own
        // default, while its ShiftLeft/ShiftRight premise cannot invent the
        // carrier from a concrete global instance.
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
        let guarded = self.open_input_metas_to_guard(goal_ty);
        if guarded.is_empty() {
            return self.resolve_instance_with_depth(goal_ty, 0, &mut goal_path, strict);
        }
        // An answer that INVENTS a carrier for an open input is no answer.
        // Lean's `synthInstance` cannot assign the caller's metavariables
        // (`withNewMCtxDepth`), so `Tag ?α` with instances `Tag Nat` and
        // `Tag Int` is stuck until the term pins `?α`; Clean's search took
        // the most recent candidate and pinned `?α := Int`. Measured: with
        // `let f := fun k j => Tag.tag (j : Int) + Tag.tag k; f 5 7`, the
        // `Tag ?α` of `k` became `Tag Int` before `5` was seen, and
        // `m = 212` was accepted by `rfl` (Lean 4.8.0: `k : Nat`, 112); an
        // open `Neg ?α` took `Float` and `(fun k => -k + 0) 5 : Int` was
        // refused. So such a search is rolled back and reported STUCK,
        // which queues the goal for the drain at the call sites
        // (`record_postponed_stuck_instance`); one nothing ever grounds fails
        // closed. An answer that pins nothing (a parametric instance), pins
        // an open input only to the declaration's own locals (a local
        // instance binder, which is evidence), stands. A pin to a constant
        // the goal already names is invented all the same: with `Tg Int Nat`
        // declared before `Tg Int Int`, the goal `Tg Int ?β` names `Int`, and
        // exempting that pin let the latest instance answer (`let f := fun k
        // => Tg.tg (α := Int) k; f 5` was accepted at 105; Lean 4.8.0: 5).
        self.metas.push_scope();
        let result = self.resolve_instance_with_depth(goal_ty, 0, &mut goal_path, strict);
        if result.is_some()
            && guarded
                .iter()
                .any(|m| self.meta_pinned_to_invented_carrier(*m))
        {
            self.metas.pop_scope();
            self.instance_search_stuck = true;
            return None;
        }
        self.metas.commit();
        result
    }

    /// Whether the environment records a `@[default_instance]` for one of
    /// `class_name`'s instances.
    fn class_has_env_default_instance(&self, class_name: &Name) -> bool {
        self.instances
            .get_instances(class_name)
            .iter()
            .any(|inst| self.env.is_default_instance(&inst.name))
    }

    /// The unassigned metavariables of an instance goal's INPUT positions
    /// that a search must not pin to an invented carrier (see
    /// [`Self::resolve_instance`]). Empty for a class whose open goal Lean
    /// resolves by `@[default_instance]` and Clean by its search (`OfNat`,
    /// `OfScientific`, the `Pow` family, the heterogeneous operators), for the
    /// `binop_lazy%` classes (`is_lazy_binop_class`), for a class with a user
    /// default instance (B99 defaults it), and for the monad family (already
    /// reported stuck).
    fn open_input_metas_to_guard(&self, goal_ty: &Expr) -> Vec<FVarId> {
        let goal = self.metas.instantiate(goal_ty);
        let Some((class_name, args)) = crate::instances::extract_class_app(&goal) else {
            return Vec::new();
        };
        if is_default_instance_carrier_class(&class_name)
            || is_hetero_binop_default_instance_class(&class_name)
            || is_lazy_binop_class(&class_name)
            || is_monad_family_class(&class_name)
            || self
                .default_instances
                .get(&class_name)
                .is_some_and(|entries| !entries.is_empty())
            || self.class_has_env_default_instance(&class_name)
        {
            return Vec::new();
        }
        let Some(info) = self.instances.get_class(&class_name) else {
            return Vec::new();
        };
        let mut guarded: Vec<FVarId> = Vec::new();
        for (idx, arg) in args.iter().enumerate() {
            if info.out_params.contains(&idx) || info.semi_out_params.contains(&idx) {
                continue;
            }
            for fvar in self.collect_meta_fvars(arg) {
                let unassigned =
                    MetaState::from_fvar(fvar).is_some_and(|m| !self.metas.is_assigned(m));
                if unassigned && !guarded.contains(&fvar) {
                    guarded.push(fvar);
                }
            }
        }
        guarded
    }

    /// Whether a search assigned the metavariable `meta` a value naming any
    /// constant: a carrier taken from a global instance, not one a local
    /// hypothesis supplied (a pin to locals alone names none).
    fn meta_pinned_to_invented_carrier(&self, meta: FVarId) -> bool {
        let value = self.metas.instantiate(&Expr::fvar(meta));
        if bare_unassigned_meta(&self.metas, &value).is_some() {
            return false;
        }
        mentions_constant(&value)
    }

    /// Unify one LOCAL instance binder's class levels and arguments with the
    /// goal's, inside a metavariable scope this method PUSHES.
    ///
    /// The caller commits the scope on `true` and pops it on `false`; it is
    /// left pushed either way so an ambiguity scan can inspect what the match
    /// grounded before deciding.
    ///
    /// The levels used to be skipped: `[inst : HasEquiv.{u,?v} α]` answered
    /// `HasEquiv.{u,?v'} α` without linking `?v` and `?v'`, so an instance of
    /// a class whose universe only the value fixes (`HasEquiv.{u, v}`,
    /// `Equiv : α → α → Sort v`) applied the projection at `?v'` to a local at
    /// `?v` and the kernel refused it ("differ in universe levels: {u, ?u_3}
    /// vs {u, ?u_1}": `Mathlib/Data/Subtype.lean`'s
    /// `instance [HasEquiv α] (p) : HasEquiv (Subtype p)` and the five rows
    /// using it, measured 2026-09-11).
    fn try_match_local_instance(
        &mut self,
        local_levels: &[Level],
        local_args: &[Expr],
        goal_levels: &[Level],
        goal_args: &[Expr],
    ) -> bool {
        self.metas.push_scope();
        if local_levels.len() == goal_levels.len() {
            for (local_lvl, goal_lvl) in local_levels.iter().zip(goal_levels.iter()) {
                let ctx = self.demand_local_ctx(&[]);
                let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                if !matches!(
                    unifier.unify_levels(local_lvl, goal_lvl),
                    UnifyResult::Success
                ) {
                    return false;
                }
            }
        }
        // `.instances` transparency, as for a global candidate (G47): a local
        // `[inst : Foo Nat]` is not a `Foo (Wrap Nat)` for a semireducible
        // `def Wrap α := α` (pinned Lean 4.8.0: "failed to synthesize").
        for (local_arg, goal_arg) in local_args.iter().zip(goal_args.iter()) {
            if !self.try_unify_instances(local_arg, goal_arg) {
                return false;
            }
        }
        true
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
        let goal_inst = self.fold_identity_monad(&self.metas.instantiate(goal_ty));
        let goal_ty =
            if extract_class_app(&goal_inst).is_some_and(|(n, _)| self.instances.is_class(&n)) {
                goal_inst.clone()
            } else {
                let w = self.whnf(&goal_inst);
                self.metas.instantiate(&w)
            };

        // An input-only premise owns the same no-invented-carrier rule as a
        // root query, including its own premise subtree. In particular the
        // default HShift bridge must not invent its still-unknown carrier by
        // choosing a concrete ShiftLeft/ShiftRight dictionary below it.
        let strict = strict
            || extract_class_app(&goal_ty)
                .is_some_and(|(name, _)| is_input_only_postpone_class(&name));

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
            // THE `depth == 0` RESTRICTION WAS LIFTED 2026-09-16, deliberately
            // and with its cost measured. It read: the abstraction answers only
            // the ELABORATOR's own goal, never a candidate's `[inst]` sub-goal,
            // because a candidate like `instD : [(x : Nat) → C Nat] → D Nat`
            // would then resolve and the `decEq` bridge's `DecidableEq α`
            // delegation could silently change the TERM of goals that already
            // resolve.
            //
            // What that guard also did was refuse `Pi.hasLe`'s premise. A
            // candidate's `[inst]` premise is exactly where `∀ i, LE (π i)`
            // shows up, so the restriction closed the goal-side telescope to
            // the one shape Mathlib needs it for, and
            // `Mathlib/Order/Basic.lean` lost five declarations to it:
            // `le_of_strongLT`, `strongLT_of_strongLT_of_le` and
            // `le_update_iff` directly, plus `StrongLT.le` and
            // `StrongLT.trans_le` as `alias` cascades. Lifting it recovers all
            // five by name and leaves zero `failed to synthesize instance
            // LE ((x ...` errors in that file (65/206 -> 70/206, measured on a
            // corpus whose decl_count for that file equals the armed one).
            //
            // WHY THE HAZARD DOES NOT FOLLOW. The abstraction is still reached
            // only after the primary search AND the candidate-side telescope
            // have both returned `None` — the `result.is_none()` chain above is
            // unchanged — so it can only ADD a resolution where there was none.
            // It cannot replace a term that already resolves, at any depth.
            // What it can do is make a CANDIDATE succeed that used to fail, so
            // a parent goal could select a different candidate; that is the
            // real residual risk, and it is pinned rather than argued:
            // `test_goal_side_abstraction_only_adds_never_replaces` asserts an
            // already-resolving goal keeps its exact term, and
            // `test_goal_side_is_applied_to_an_internal_subgoal` pins the new
            // behaviour beside it. Full-crate evidence:
            // reports/source-frontier/2026-09-16-depth-gate-lift-probe.json.
            //
            // The local source-elab lane lifted the same guard independently at
            // 3fe8d1f59 (2026-09-10; Lean's `SynthInstance.tryResolve` opens every
            // sub-goal's telescope at any depth); the same test pins the BUILT TERM
            // (`instD (fun x => instCNat)`), and fixture `p27` pins `Pi.hasLe`.
            if result.is_none() {
                result = self.resolve_pi_goal_by_abstraction(
                    &goal_ty,
                    goal_is_ground,
                    depth,
                    goal_path,
                    strict,
                );
            }
            // FRONTIER STAGE I-3: an ALIAS goal (`DecidableEq α`,
            // `DecidablePred p`, `DecidableLE α`) kept un-whnf'd above because
            // its head is a registered class, opened the way Lean opens EVERY
            // goal. Same safety argument as I-1/I-2: consulted only after
            // everything else returned `None`. See
            // `resolve_alias_goal_by_opening`.
            if result.is_none() {
                result = self.resolve_alias_goal_by_opening(&goal_ty, depth, goal_path, strict);
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
    ///   (The primary search itself now tries every local in one
    ///   most-recent-first pass, `∀`-typed and reducible-alias locals
    ///   included, `Self::try_local_instance`, opening them at reducible
    ///   transparency only.)
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

        // A STUCK goal is stuck for every match, not only the one that
        // reported it. The primary loop refuses an ambiguous open-carrier goal
        // precisely so the carrier is chosen by the surrounding term; arm (A)
        // below matches locals the same way and would re-make that choice one
        // line later, which is how the refusal was defeated when it first
        // landed (the `Pre fvar#1` line reappeared in the trace immediately
        // under the AMBIGUOUS one). Lean's `isDefEqStuckEx` leaves the whole
        // `synthInstance` stuck for the same reason.
        if self.instance_search_stuck {
            return None;
        }

        // (A) alias head ↔ alias head, no `whnf` on either side.
        // A local instance matches on class NAME, class LEVELS and class
        // ARGUMENTS. The levels used to be skipped: `[inst : HasEquiv.{u,?v}
        // α]` answered the goal `HasEquiv.{u,?v'} α` without ever linking
        // `?v` and `?v'`, so an instance of a class whose universe only the
        // value fixes (`HasEquiv.{u, v}`, `Equiv : α → α → Sort v`) reached
        // the kernel with the projection at `?v'` applied to a local at
        // `?v` — "differ in universe levels: {u, ?u_3} vs {u, ?u_1}"
        // (`Mathlib/Data/Subtype.lean`'s `instance [HasEquiv α] (p) :
        // HasEquiv (Subtype p)` and the five rows using it, 2026-09-11).
        if let Some((goal_class, goal_levels, goal_args)) =
            crate::instances::extract_class_app_with_levels(goal_pre_whnf)
        {
            for i in (0..self.local_instances.len()).rev() {
                let (fvar, local_ty) = self.local_instances[i].clone();
                let local_ty_inst = self.metas.instantiate(&local_ty);
                let Some((local_class, local_levels, local_args)) =
                    crate::instances::extract_class_app_with_levels(&local_ty_inst)
                else {
                    continue;
                };
                if local_class != goal_class || local_args.len() != goal_args.len() {
                    continue;
                }
                self.metas.push_scope();
                let levels_ok = local_levels.len() != goal_levels.len()
                    || local_levels.iter().zip(goal_levels.iter()).all(|(l, g)| {
                        let ctx = self.demand_local_ctx(&[]);
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        matches!(unifier.unify_levels(l, g), UnifyResult::Success)
                    });
                let unified = levels_ok
                    && local_args
                        .iter()
                        .zip(goal_args.iter())
                        .all(|(l, g)| self.try_unify_instances(l, g));
                inst_trace(|| {
                    format!(
                        "local {} : {} for goal {} → levels_ok={levels_ok} unified={unified}",
                        fvar.as_u64(),
                        crate::error_render::term(&local_ty_inst),
                        crate::error_render::term(goal_pre_whnf)
                    )
                });
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
                if self.try_unify_instances(&local_ty_norm, goal_norm) {
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
                .all(|(c, g)| self.try_unify_instances(c, g));
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
            self.push_local_with_fvar(
                clean_parser::SurfaceName::from_name(
                    Name::anon().str("_goaltele").num(fvar.as_u64()),
                ),
                fvar,
                arg_ty.clone(),
            );
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

        // Check local instance-implicit binders, most recent first.
        //
        // A local `[inst : C t]` is a hypothesis of the declaration being
        // elaborated, so matching it against a GROUND goal can only produce a
        // carrier already named in its binder list — evidence, not invention,
        // and the first match wins exactly as it always did.
        //
        // AMBIGUITY, measured 2026-09-21. When the goal still carries a
        // metavariable in a non-out-param input position, a "match" is a
        // CHOICE of carrier, and reverse order made it the most recently
        // pushed binder's. With two order instances in scope
        // (`[Preorder α] [Preorder β]`, `[Decidable a] [Decidable b]` — the
        // shape of every failing row) `le_rfl`'s `[Preorder ?α]` took `β` and
        // the declaration died on "fvar mismatch: fvar#3 vs fvar#2"
        // (`Mathlib/Order/Basic.lean`: `le_imp_le_iff_lt_imp_lt`,
        // `lt_iff_lt_of_le_iff_le'`, `lt_iff_lt_of_le_iff_le`,
        // `Prod.mk_le_mk_iff_right`, and `Logic/Basic`'s anonymous
        // `Decidable (Xor' a b)`).
        //
        // Lean cannot make that choice at all: `SynthInstance` runs under
        // `withNewMCtxDepth` with `isDefEqStuckEx := true`
        // (`Lean/Meta/SynthInstance.lean:874-894`), so the caller's
        // metavariables are not assignable anywhere inside the search and a
        // match that needs one is STUCK — `trySynthInstance` returns `.undef`
        // and the instance metavariable is POSTPONED
        // (`Lean/Elab/Term/TermElabM.lean:1195-1237`), to be retried once the
        // surrounding term has pinned the carrier.
        //
        // Clean cannot adopt that wholesale — its postponement queue is
        // drained at a handful of sites, so a goal postponed on a path that
        // reaches none of them never comes back (the measurement that narrowed
        // the top-level open-input refusal to `DecidableEq`: refusing
        // `Decidable ?p` cost `peirce`, refusing `Inhabited ?α` cost
        // `Unique.default_eq`). So the refusal here is keyed on AMBIGUITY, the
        // half that is never evidence: every local of the class is tried, and
        // the goal is reported stuck only when two of them ground the goal
        // DIFFERENTLY. One matching local — which is the laundering repair the
        // unguarded loop exists for, and every single-binder declaration —
        // still matches, at the same carrier, with no second pass.
        //
        // `depth == 0` ONLY, for the same reason the top-level open-input
        // refusal carries that restriction: the postponement queue is the
        // other half of this fix, and only the ELABORATOR's own goal has a
        // caller that can queue it. A sub-goal generated by a candidate keeps
        // the pre-existing behaviour, so no candidate's search can start
        // failing — and a stuck verdict cannot leak sideways into the next
        // candidate's own local matches.
        let num_local = self.local_instances.len();
        // Ambiguity needs TWO locals of the class. With one or none the scan
        // below cannot change any answer, so it is skipped outright and the
        // single-binder path — every declaration that carries one `[C α]` —
        // stays byte-identical to before, matching and committing in one pass.
        // That matters beyond speed: a local match unifies class LEVELS into
        // the `Name`-keyed union-find, which is declaration-wide and shared by
        // every candidate (see the freshening note in `resolve_instance`), so
        // a scan pass that is never needed is a second pass over that state
        // that is never needed either.
        //
        // CORRECTION, checked 2026-09-21: that state IS rolled back. Every
        // mutation records an `UndoRecord::Level{Parent,Concrete,Bound}`
        // (`unify/meta_state/levels.rs`, restored in `undo.rs`), so a scan
        // that pops its scope leaks nothing and the reason to skip it is cost
        // alone. An earlier draft of this comment said `pop_scope` does NOT
        // undo it; read that way, a reader would take the two-locals guard for
        // a correctness barrier it is not.
        //
        // The cost is REAL but not measurable here, and the A/B is recorded so
        // nobody re-runs it: the count is computed before the `depth == 0`
        // test, so it whnfs every local on the way to every goal at every
        // depth. Making it lazy (`.nth(1)` behind `depth == 0`) moved neither
        // the `instance` filter (14.67/14.61/14.55 s eager vs
        // 14.56/14.67/14.49 s lazy) nor `lean4_corpus_tests`
        // (42.16/42.43 s vs 43.05/42.83 s), so it was measured and NOT landed.
        // A single-trial reading across a rebuild had said 20%; it was a
        // build-state artifact.
        let class_local_count = self
            .local_instances
            .iter()
            .filter(|(_, local_ty)| {
                let inst = self.metas.instantiate(local_ty);
                extract_class_app(&self.whnf(&inst)).is_some_and(|(n, _)| n == class_name)
            })
            .count();
        let goal_has_open_input = depth == 0 && class_local_count >= 2 && {
            let (outs, semis) = self
                .instances
                .get_class(&class_name)
                .map(|info| (info.out_params.clone(), info.semi_out_params.clone()))
                .unwrap_or_default();
            goal_args.iter().enumerate().any(|(idx, arg)| {
                !outs.contains(&idx) && !semis.contains(&idx) && {
                    let arg = self.metas.instantiate(arg);
                    self.has_metavars(&arg)
                }
            })
        };
        // `(index, fvar, the goal as this local grounds it)` for the most
        // recent matching local; `Some` only while the goal has an open input.
        let mut first_open_match: Option<(usize, FVarId, Expr)> = None;
        let mut ambiguous = false;
        // Whether some local other than a plain application of the goal's
        // class was passed over (the open-goal ambiguity scan below does not
        // take such locals); `resolve_locals_first` then tries them all.
        let mut passed_over_a_local = false;
        for i in (0..num_local).rev() {
            let (fvar, local_ty) = self.local_instances[i].clone();
            let local_ty_inst = self.metas.instantiate(&local_ty);
            let local_ty_norm = self.whnf(&local_ty_inst);

            // A `∀`-typed or alias-typed local (or one of an alias goal's
            // unfolding) is tried HERE, at its own place in the
            // most-recent-first order, as Lean's `getInstances` tries every
            // local in one pass (`locals_first.rs`).
            let plain = crate::instances::extract_class_app_with_levels(&local_ty_norm).filter(
                |(local_class, _, local_args)| {
                    local_class == &class_name && local_args.len() == goal_args.len()
                },
            );
            let Some((_, local_levels, local_args)) = plain else {
                if first_open_match.is_some() {
                    passed_over_a_local = true;
                    continue;
                }
                let mut sub = locals_first::SubSearch {
                    depth,
                    goal_path: &mut *goal_path,
                    strict,
                };
                if let Some(found) = self.try_local_instance(i, goal_ty, &mut sub) {
                    if goal_is_ground {
                        self.instance_cache
                            .insert(cache_key.to_string(), found.clone());
                    }
                    return Some(found);
                }
                continue;
            };
            let unified =
                self.try_match_local_instance(&local_levels, &local_args, &goal_levels, &goal_args);
            inst_trace(|| {
                format!(
                    "local {} : {} for goal {} → unified={unified}",
                    fvar.as_u64(),
                    crate::error_render::term(&local_ty_norm),
                    crate::error_render::term(goal_ty)
                )
            });
            if !unified {
                // Restore metavariable state on failed unification
                self.metas.pop_scope();
                continue;
            }

            if !goal_has_open_input {
                // Nothing of the goal was invented: commit and return.
                self.metas.commit();
                let result = Expr::fvar(fvar);
                if goal_is_ground {
                    self.instance_cache
                        .insert(cache_key.to_string(), result.clone());
                }
                return Some(result);
            }

            // Open goal: record HOW this local grounds it and keep looking, so
            // a second, differing local is seen before anything is committed.
            let grounded = self.metas.instantiate(goal_ty);
            self.metas.pop_scope();
            if let Some((_, _, first)) = &first_open_match {
                if *first != grounded {
                    ambiguous = true;
                    break;
                }
            } else {
                first_open_match = Some((i, fvar, grounded));
            }
        }

        if ambiguous {
            inst_trace(|| {
                format!(
                    "local instances are AMBIGUOUS for the open goal {} → stuck (postponed)",
                    crate::error_render::term(goal_ty)
                )
            });
            // Lean's "typeclass instance problem is stuck": the caller records
            // the instance metavariable and re-resolves it once the
            // surrounding term grounds the carrier.
            self.instance_search_stuck = true;
            return None;
        }

        if let Some((i, fvar, _)) = first_open_match {
            let (_, local_ty) = self.local_instances[i].clone();
            let local_ty_inst = self.metas.instantiate(&local_ty);
            let local_ty_norm = self.whnf(&local_ty_inst);
            if let Some((_, local_levels, local_args)) =
                crate::instances::extract_class_app_with_levels(&local_ty_norm)
            {
                if self.try_match_local_instance(
                    &local_levels,
                    &local_args,
                    &goal_levels,
                    &goal_args,
                ) {
                    self.metas.commit();
                    let result = Expr::fvar(fvar);
                    if goal_is_ground {
                        self.instance_cache
                            .insert(cache_key.to_string(), result.clone());
                    }
                    return Some(result);
                }
                self.metas.pop_scope();
            }
        }

        // The locals the open-goal ambiguity scan passed over, before the
        // bridge and every global candidate (`resolve_locals_first`).
        if passed_over_a_local {
            let mut sub = locals_first::SubSearch {
                depth,
                goal_path: &mut *goal_path,
                strict,
            };
            if let Some(local) = self.resolve_locals_first(goal_ty, &mut sub) {
                if goal_is_ground {
                    self.instance_cache
                        .insert(cache_key.to_string(), local.clone());
                }
                return Some(local);
            }
        }

        // decEq bridge: `Decidable (@Eq α a b)` is inhabited by `DecidableEq α`
        // applied to `a b`, since `DecidableEq α` is definitionally
        // `(a b : α) → Decidable (a = b)`. The lean4-core prelude ships no
        // standalone `Decidable` *instance* for this, so instance search never
        // finds it — `Decidable (a = b)` in a `resolve_instance` context (a
        // `[Decidable (a=b)]` binder, a dependent `if h : a = b`, the decide lane's
        // `eval_decide`) fails. Bridge it explicitly: resolve `DecidableEq α` and
        // apply it; the kernel re-checks the emitted `(decEqInst a b)` term.
        // NOT weakening-only: it runs before the class's own global
        // candidates, so a later or higher-priority user `instance : Decidable
        // (a = b)` loses to it where Lean orders the two by priority and then
        // recency (DECISIONS R127 (l), pinned in `decide_lean_order_e2e.rs`).
        //
        // `dec_eq_bridged` records that the bridge SEARCHED `DecidableEq α` for
        // this goal, so the alias admission below does not walk that same
        // bucket a second time.
        //
        // AFTER the local instances (Lean's `getInstances` appends the locals
        // last and `synthInstance` tries them first, at every sub-goal), and
        // the proposition is normalized at INSTANCE transparency, which is
        // where Lean's search matches: a semireducible `def P n : Prop := n =
        // 1` stays folded and `Decidable (P 1)` fails to synthesize (pinned
        // v4.30.0-rc2), an `abbrev` unfolds to the equation (DECISIONS R127).
        let mut dec_eq_bridged = false;
        if class_name.to_string() == "Decidable" && goal_args.len() == 1 {
            let eq_app = self.whnf_instances(&self.metas.instantiate(&goal_args[0]));
            let eq_fn = eq_app.get_app_fn();
            if let ExprKind::Const(eq_name, eq_levels) = eq_fn.kind() {
                let eq_args = eq_app.get_app_args();
                if eq_name.to_string() == "Eq" && eq_args.len() == 3 {
                    dec_eq_bridged = true;
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
        let default_order = if self.default_instances.is_empty()
            && !self.class_has_env_default_instance(&class_name)
        {
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
                let order = self.default_instance_order(&class_name);
                if order.is_none() && depth == 0 && self.user_default_priority_floor.is_some() {
                    // The scope's default pass, and every default of this
                    // class is at or below the numerals' tier: it applies
                    // after them, so the goal keeps waiting.
                    self.instance_search_stuck = true;
                    return None;
                }
                order
            } else {
                None
            }
        };
        let defaulting = default_order.is_some();
        if defaulting && depth == 0 && self.defer_user_defaults > 0 {
            // Inside a Lean-order alternative the default waits, as in Lean:
            // the goal is stuck and queued for the scope's default pass.
            self.deferred_user_default_goals += 1;
            self.instance_search_stuck = true;
            return None;
        }
        if defaulting {
            self.user_default_instance_answers += 1;
        }

        // Lean's heterogeneous-operator refusal (see
        // `is_hetero_binop_default_instance_class` for the measured message).
        // A goal EVERY one of whose type arguments is still a bare unassigned
        // metavariable carries no evidence at all: `candidate_order` ties on
        // priority and head-match, so registration order alone picks the
        // carrier. Postpone it instead — the caller records the instance
        // metavariable and
        // `ElabCtx::retry_postponed_open_carrier_instances` re-resolves it
        // once a sibling argument grounds one of the slots, which is Lean's
        // own order (the `instHAdd` bridge collapses the slots, then the
        // low-priority `instOfNatNat` defaults what is left).
        //
        // Deliberately narrow, four ways. `!defaulting`: placed BELOW the B99
        // block on purpose, so this refusal can never pre-empt a registered
        // `@[default_instance]`. That guard is INERT today — measured
        // 2026-09-16, `default_order` does not fire for these classes at all
        // (an `@[default_instance] instHAddSec : HAdd Sec Sec Sec` LOSES to a
        // later plain `instHAddSec2`, HEAD answering `Sec2` where Lean answers
        // `Sec`) — and is written so that repairing B99 for them cannot be
        // silently defeated here. `depth == 0`: a sub-goal generated by
        // another candidate keeps the
        // pre-existing behaviour, so no candidate's search can start failing.
        // ALL arguments open: one determined argument is evidence and already
        // steers `candidate_order` (`HAdd ?b Nat ?g` picks `instHAddNat`
        // today, and still does). This class family only: nothing else
        // changes. LOCAL instance binders are matched ABOVE this point and are
        // never postponed, for the reason `resolve_instance` gives — a
        // hypothesis of the declaration is evidence, not invention.
        //
        // THE SAME REFUSAL FOR AN INPUT-ONLY CLASS (`DecidableEq ?α`,
        // `Decidable ?p`, `Inhabited ?α`, `BEq ?α`), measured 2026-09-20. The
        // per-argument-pair check below rejects a candidate whose own argument
        // is CONCRETE, which is why it never fired here: every parametric
        // candidate meets an open goal flex/flex and is admitted, and its own
        // sub-goals then invent the carrier. `Function.ne_update_self_iff` /
        // `update_ne_self_iff` / `update_eq_self` (Mathlib/Logic/Function/Basic)
        // took `decidableEq_of_subsingleton ?α (instSubsingleton ?α)` for the
        // `[DecidableEq ?α]` slot of `eq_update_self_iff`, which forces `?α` to
        // be a `Subsingleton`, and the section's own `[DecidableEq α]` local
        // could then never unify with it — "Type mismatch: expected f ≠ update
        // f a b ↔ …, got ¬?f = update ?α ?β (decidableEq_of_subsingleton …) …".
        // The postponement queue is the second half (`record_postponed_open_
        // carrier_instance`): once the surrounding term grounds the carrier the
        // goal is re-resolved, and one that never grounds fails closed, which
        // is what Lean's "typeclass instance problem is stuck" is.
        let all_inputs_open = !goal_args.is_empty()
            && goal_args.iter().enumerate().all(|(idx, arg)| {
                out_params.contains(&idx)
                    || semi_out_params.contains(&idx)
                    || bare_unassigned_meta(&self.metas, &self.metas.instantiate(arg)).is_some()
            })
            && goal_args
                .iter()
                .enumerate()
                .any(|(idx, _)| !out_params.contains(&idx) && !semi_out_params.contains(&idx));
        //
        // NARROWED TO `DecidableEq` after measuring the wider form, and the
        // measurement is the argument. Clean's postponement queue is drained
        // at three sites only (`retry_postponed_open_carrier_instances`), so a
        // goal postponed on a path that reaches none of them does not come
        // back: refusing `Decidable ?p` cost `peirce` (and `Classical.by
        // Contradiction'` behind it) "failed to synthesize instance Decidable
        // fvar#0", and refusing `Inhabited ?α` cost `Unique.default_eq` /
        // `Unique.exists_iff`, whose `Inhabited.default` stopped being applied
        // to its implicits at all. Those two answer an open goal with a
        // PARAMETRIC instance (`Unique.instInhabited ?α ?u`) that pins nothing,
        // which unification then fills correctly — legitimate, and what Lean
        // reaches after its own postponement. `DecidableEq` is where an
        // alias-filed candidate pins the carrier through its own premise
        // (`decidableEq_of_subsingleton` forces a `Subsingleton`), so it is the
        // one class measured to need the refusal. Widening this needs the
        // queue drained wherever an instance-implicit slot is filled, not a
        // bigger allowlist.
        if !defaulting
            && depth == 0
            && all_inputs_open
            && (is_hetero_binop_default_instance_class(&class_name)
                || class_name == Name::from_string("DecidableEq"))
        {
            return None;
        }
        // THE MONAD FAMILY, 2026-09-28. `Pure ?m` / `Bind ?m` / `Monad ?m`
        // with the monad still open carries no evidence: every candidate
        // (`Applicative.toPure`, `instMonadOption`, `StateT.instMonad`, …)
        // meets it flex/flex, so registration order would pick the monad.
        // Until 2026-09-28 these goals never arose — the do lowering used
        // instance-less axioms (which proved `False`) — and now every lowered
        // `pure`/`bind` asks one. Lean reports the goal stuck and postpones
        // it; so does this, and `instance_search_stuck` lets the caller queue
        // it (`resolve_deferred_instances_postponing_stuck`).
        if !defaulting && depth == 0 && all_inputs_open && is_monad_family_class(&class_name) {
            self.instance_search_stuck = true;
            return None;
        }

        // Try each instance in priority order; within a priority tier, order by
        // head-symbol compatibility with the goal (Lean-faithful; see
        // `candidate_order`).
        //
        // Candidates filed under an ALIAS of this class (`LinearOrder.toDecidableLT`,
        // filed under `DecidableLT`, for `Decidable (a < b)`) join the order by
        // priority — Lean's instance index keys them by the class their
        // reducible telescope concludes in (`Lean/Meta/Instances.lean`
        // `mkInstanceKey`), so they compete with this class's own instances.
        // Measured: `min_def_lt`, `max_def_lt`, `LinearOrder.lift` on
        // `Mathlib/Order/Basic.lean` failed `Decidable (a < b)` /
        // `Decidable (f x ≤ f y)` with `LinearOrder.toDecidableLT/LE` never
        // tried. Not while DEFAULTING, whose candidate set is fixed.
        let order: Vec<(Name, usize)> = match default_order {
            Some(order) => order
                .into_iter()
                .map(|idx| (class_name.clone(), idx))
                .collect(),
            None => {
                let own = self.candidate_order(&class_name, &goal_args);
                let aliased = self.alias_candidate_order(&class_name, &goal_args, dec_eq_bridged);
                self.merge_candidate_orders(&class_name, own, aliased)
            }
        };
        for (bucket, inst_idx) in order {
            // The per-query budget (see `ElabCtx::instance_search_steps`): a
            // search that has already tried this many candidates across all
            // depths is a failing search over recursive instances, and Lean
            // would have given up on it too (`synthInstance.maxSize`,
            // heartbeats). Stopping here can only turn a search that would
            // have FAILED after exponential work into one that fails now; a
            // search that succeeds within the budget is untouched.
            if self.instance_search_steps >= INSTANCE_SEARCH_BUDGET {
                return None;
            }
            self.instance_search_steps += 1;
            let inst = self.instances.get_instances(&bucket)[inst_idx].clone();
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
            // The candidate's own fresh level parameters (see the deferred
            // class-level pairs below).
            let mut candidate_level_names: Vec<Name> = Vec::new();
            let (inst_type_fresh, inst_expr_fresh) = if raw_level_params.is_empty() {
                (inst.type_.clone(), inst.expr.clone())
            } else {
                let level_subst: Vec<(Name, Level)> = raw_level_params
                    .iter()
                    .map(|n| (n.clone(), self.fresh_universe_param()))
                    .collect();
                candidate_level_names.extend(level_subst.iter().filter_map(|(_, l)| match l {
                    Level::Param(name) => Some(name.clone()),
                    _ => None,
                }));
                (
                    inst.type_.instantiate_level_params(&level_subst),
                    inst.expr.instantiate_level_params(&level_subst),
                )
            };

            // The instance expression and type (may contain implicit binders).
            // Normalise with `whnf` so binders get stripped, EXCEPT where the
            // type is already an application of the GOAL's class: whnf would
            // unfold an alias head (`DecidableEq Color` to its Pi) and the
            // post-strip class would read as `Decidable`, mismatching the
            // `DecidableEq` goal.
            //
            // The stop is keyed on the goal's class, not on "any registered
            // class", and it is applied after EVERY binder below, not only to
            // the bare type. Lean compares the two telescopes at the same depth
            // (`SynthInstance.lean` `tryResolve`: the goal's
            // `forallTelescopeReducing` body against `getSubgoals`' body);
            // Clean keeps an alias goal at the alias, so the candidate must
            // stop there too. The old rule stopped only a binder-free type, so
            // a PARAMETRIC alias instance — `Option.instDecidableEq : [DecidableEq
            // α] → DecidableEq (Option α)` — was stripped straight through its
            // conclusion to `Decidable (?a = ?b)` and rejected on
            // `class head Decidable ≠ DecidableEq` for the very goal it is filed
            // under (`Mathlib/Logic/Function/Basic.lean`: `Option.rec_update`,
            // `curry_update`, `uncurry_update_update`). And an alias-filed
            // candidate tried for a FINAL-class goal (`MyLO.decLT : DecidableLT α`
            // for `Decidable (a < b)`) must be unfolded, not kept.
            let stops_at_goal_class =
                |e: &Expr| extract_class_app(e).is_some_and(|(n, _)| n == class_name);
            let mut inst_expr = inst_expr_fresh;
            let mut inst_type = if stops_at_goal_class(&inst_type_fresh) {
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

                // Apply the argument to the instance expression and type.
                //
                // The class-application guard applied to `inst_type_fresh` above
                // has to hold HERE TOO, and for exactly the same reason: a
                // reducible class abbreviation whnf's to a Pi, and this loop's
                // own condition is "is it a Pi", so the extra binders get
                // stripped as if they were the candidate's and the post-loop
                // head reads as the UNFOLDED class. Measured 2026-09-20 with
                // `CLEAN_INSTANCE_TRACE=1`: the parametric
                // `instDecidableEqList : {α} → [DecidableEq α] → DecidableEq
                // (List α)` was rejected with "class head Decidable ≠
                // DecidableEq" — its conclusion `DecidableEq (List ?α)` unfolded
                // to `(a b : List ?α) → Decidable (Eq a b)`, whose two binders
                // this loop then consumed. The pre-loop guard did not cover it
                // because it inspects the instance's FULL Pi-headed type, not
                // the body left after the binders are stripped. Concrete
                // instances (`instColorDecidableEq : DecidableEq Color`) never
                // enter the loop at all, which is why only the parametric shape
                // was affected.
                inst_expr = self.apply_instance_arg(inst_expr, &arg);
                // Merge note (2026-09-21): integrate/2026-09-20 fixed this same
                // spot independently, stopping at ANY registered class
                // (`self.instances.is_class(&n)`) rather than at the goal's
                // class. Main's rule is kept because it is strictly the correct
                // one and the comment above says why: an alias-filed candidate
                // tried for a FINAL-class goal — `MyLO.decLT : DecidableLT α`
                // against `Decidable (a < b)` — MUST be unfolded, and an
                // any-class stop would park it at `DecidableLT` and reject the
                // goal it is meant to answer. The two rules agree on the case
                // integ was fixing (`instDecidableEqList`), because there the
                // class reached IS the goal's.
                let body = self.metas.instantiate(&body_ty.instantiate(&arg));
                inst_type = if stops_at_goal_class(&body) {
                    body
                } else {
                    self.whnf(&body)
                };
            }

            // Extract class name and args from instance type after applying implicit binders
            if let Some((inst_class, inst_levels, inst_args)) =
                crate::instances::extract_class_app_with_levels(&inst_type)
            {
                if inst_class != class_name {
                    inst_trace(|| format!("{}: class head {inst_class} ≠ {class_name}", inst.name));
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
                // A level pair that does not unify YET because it still
                // mentions one of THIS candidate's undetermined level
                // parameters is retried once the arguments are unified, as
                // Lean's `isLevelDefEq` postpones a constraint it cannot
                // decide: `Except.instMonad.{u, u_1} : Monad.{u_1, max u_1 u}
                // (Except.{u, u_1} ε)` meets the goal `Monad.{1, 1}
                // (Except.{0, 1} ε)` with `max 1 ?u =?= 1`, which only the
                // argument `Except.{?u, 1} =?= Except.{0, 1}` decides (G32).
                // A determined mismatch rejects the candidate at once, and a
                // deferred pair that still fails rejects it after.
                let mut deferred_levels: Vec<(Level, Level)> = Vec::new();
                if inst_levels.len() == goal_levels.len() {
                    let mut levels_ok = true;
                    for (inst_lvl, goal_lvl) in inst_levels.iter().zip(goal_levels.iter()) {
                        // Level unification touches no free variable: an
                        // empty context is the exact closure of its inputs.
                        let unified_now = {
                            let ctx = self.demand_local_ctx(&[]);
                            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                            matches!(
                                unifier.unify_levels(inst_lvl, goal_lvl),
                                UnifyResult::Success
                            )
                        };
                        if !unified_now {
                            let now = self.metas.instantiate_level(inst_lvl);
                            if level_mentions_any(&now, &candidate_level_names) {
                                deferred_levels.push((inst_lvl.clone(), goal_lvl.clone()));
                            } else {
                                levels_ok = false;
                                break;
                            }
                        }
                    }
                    if !levels_ok {
                        inst_trace(|| {
                            format!(
                                "{}: universe levels {:?} vs goal {:?}",
                                inst.name, inst_levels, goal_levels
                            )
                        });
                        self.metas.pop_scope();
                        continue;
                    }
                }

                // Try to unify the instance arguments with the goal arguments
                if inst_args.len() != goal_args.len() {
                    inst_trace(|| format!("{}: class arity mismatch", inst.name));
                    self.metas.pop_scope();
                    continue;
                }

                // Two-phase unification for out-parameters:
                // Phase 1: Unify non-out-parameters first (these must match)
                let mut failed_pair: Option<(Expr, Expr)> = None;
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
                        // Non-out-parameter: must unify — at Lean's
                        // `.instances` transparency (G47), so a semireducible
                        // `def` in the goal is not seen through.
                        if !self.try_unify_instances(inst_arg, goal_arg) {
                            failed_pair = Some((inst_arg.clone(), goal_arg.clone()));
                            unified = false;
                            break;
                        }
                    }
                }

                if !unified {
                    if std::env::var_os("CLEAN_INSTANCE_TRACE").is_some() {
                        let detail = failed_pair
                            .as_ref()
                            .map(|(a, b)| self.unify_verdict_for_trace(a, b))
                            .unwrap_or_default();
                        eprintln!(
                            "[inst] {}: arguments do not unify with goal {}: {detail}",
                            inst.name,
                            crate::error_render::term(goal_ty)
                        );
                    }
                    self.metas.pop_scope();
                    continue;
                }

                // Phase 2: Unify out-parameters (these can be inferred from the instance)
                for (idx, (inst_arg, goal_arg)) in
                    inst_args.iter().zip(goal_args.iter()).enumerate()
                {
                    if out_params.contains(&idx) {
                        // Out-parameter: try to unify, direction is instance -> goal
                        // (`.instances` transparency, as above).
                        if !self.try_unify_instances(inst_arg, goal_arg) {
                            unified = false;
                            break;
                        }
                    }
                }

                // The postponed class-level pairs, now that the arguments
                // have pinned what they can.
                if unified {
                    for (inst_lvl, goal_lvl) in &deferred_levels {
                        let ctx = self.demand_local_ctx(&[]);
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        if !matches!(
                            unifier.unify_levels(inst_lvl, goal_lvl),
                            UnifyResult::Success
                        ) {
                            inst_trace(|| {
                                format!(
                                    "{}: universe levels {:?} vs goal {:?}",
                                    inst.name, inst_levels, goal_levels
                                )
                            });
                            unified = false;
                            break;
                        }
                    }
                }

                if unified {
                    // Binders the goal fixed only through the TYPE of another
                    // binder (`{α} [self : C α]` against a goal that names
                    // `self` but not `α`): Lean's `checkTypesAndAssign`.
                    self.determine_binders_from_assignment_types(&binder_metas);
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
                        let ExprKind::FVar(fvar) = meta_arg.kind() else {
                            resolved_pending = false;
                            break;
                        };
                        let Some(meta_id) = MetaState::from_fvar(*fvar) else {
                            resolved_pending = false;
                            break;
                        };
                        // A sub-goal the conclusion's unification (or an
                        // earlier sub-goal) already ASSIGNED needs no search:
                        // Lean's `consume` drops it (`SynthInstance.lean`:
                        // "Filter out subgoals that have already been assigned
                        // when solving typing constraints"). The `[self :
                        // LinearOrder α]` of `LinearOrder.toDecidableLT` is the
                        // shape: the goal `Decidable (@LT.lt α (…inst…) a b)`
                        // fixes it through the `LT` instance, and `assign`
                        // below then refused the second write and rejected the
                        // candidate. The value is the goal's own, unified in,
                        // and the kernel re-checks the term.
                        if self.metas.is_assigned(meta_id) {
                            continue;
                        }
                        let arg_ty = self.metas.instantiate(&arg_ty);
                        let Some(resolved) =
                            self.resolve_instance_with_depth(&arg_ty, depth + 1, goal_path, strict)
                        else {
                            inst_trace(|| {
                                format!(
                                    "{}: sub-goal {} unresolved",
                                    inst.name,
                                    crate::error_render::term(&arg_ty)
                                )
                            });
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
                        inst_trace(|| format!("{}: a binder is left undetermined", inst.name));
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
    /// With the module's instance state injected
    /// ([`Self::set_instance_view`]) that state alone decides: an instance is
    /// a candidate exactly when it is in the current state's tree and not
    /// erased (Lean's `getInstances`).
    ///
    /// Without it (a context built with no `FileContext`):
    /// - `local instance`s are in `hidden_instances` and never visible.
    /// - `scoped instance`s are visible only while their declaring namespace
    ///   is ACTIVE: it is the current namespace (or an ancestor of it), or it
    ///   was activated by a simple `open Foo` / `open Foo in …` (with scope
    ///   rollback). Explicit opens (`open Foo (x)`) do NOT activate scoped
    ///   instances — matching Lean, where only `activateScoped` on simple
    ///   opens/namespace entry does.
    ///
    /// Either way, inside a `classical` tactic scope the `Classical`-scoped
    /// instances — `Classical.propDecidable`, priority low — are available,
    /// as the `classical` tactic adds that instance for the rest of its
    /// block.
    fn instance_visible(&self, name: &Name) -> bool {
        let classical = || {
            self.classical_tactic_scope > 0
                && self
                    .scoped_instances
                    .get(name)
                    .is_some_and(|ns| ns.to_string() == "Classical")
        };
        if let Some(view) = &self.instance_view {
            return view.in_force(name) || (classical() && !view.erased.contains(name));
        }
        if self.hidden_instances.contains(name) {
            return false;
        }
        match self.scoped_instances.get(name) {
            None => true,
            Some(ns) => self.namespace_state.is_scope_active(ns) || classical(),
        }
    }

    /// Lean's `activateScoped` for `namespaces`, each just activated by an
    /// `open … in` inside this declaration (`open N in e`, `open N in cmd`):
    /// on this context's instance state, which adds each namespace's scoped
    /// entries in order (in place where the state already holds the
    /// instance, pushed as the newest where it does not) unless it is
    /// already active. Returns what [`Self::restore_instance_state`] puts
    /// back when that scope ends (Lean's `popScope`). Without an injected
    /// instance state the `scoped_instances` gating follows the namespace
    /// state by itself, and nothing needs restoring.
    pub(crate) fn activate_scoped_instances_here(
        &mut self,
        namespaces: &[Name],
    ) -> Option<SavedInstanceState> {
        let env = self.env;
        let view = self.instance_view.as_mut()?;
        let saved_view = view.clone();
        let mut changed = Vec::new();
        for ns in namespaces {
            changed.extend(view.activate(env, ns));
        }
        let buckets = self.instances.snapshot_buckets(&changed);
        let hidden = std::mem::replace(&mut self.hidden_instances, view.hidden());
        self.instances
            .apply_instance_entries(&changed, &view.overrides, env);
        Some(SavedInstanceState {
            view: saved_view,
            hidden,
            buckets,
        })
    }

    /// Put back the instance state [`Self::activate_scoped_instances_here`]
    /// saved.
    pub(crate) fn restore_instance_state(&mut self, saved: Option<SavedInstanceState>) {
        if let Some(saved) = saved {
            self.instance_view = Some(saved.view);
            self.hidden_instances = saved.hidden;
            self.instances.restore_buckets(saved.buckets);
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
        let instances = self.instances.get_instances(class_name);
        // Without a file context (`elaborate_decl_and_register`), the table is
        // empty but the environment still records each `@[default_instance]`
        // (`decl_attributes`): those entries, at Lean's default priority, in
        // registration order.
        let declared = self.default_instances.get(class_name);
        // Native prelude defaults remain candidates when a file also declares
        // defaults for the class. A file entry supplies its recorded priority
        // and declaration order; do not duplicate it through the environment.
        let mut entries: Vec<(Name, u32)> = instances
            .iter()
            .filter(|inst| self.env.is_default_instance(&inst.name))
            .filter(|inst| {
                !declared.is_some_and(|entries| entries.iter().any(|(name, _)| *name == inst.name))
            })
            .map(|inst| (inst.name.clone(), 1000))
            .collect();
        if let Some(declared) = declared {
            entries.extend(declared.iter().cloned());
        }
        if entries.is_empty() {
            return None;
        }
        let mut order: Vec<(std::cmp::Reverse<u32>, std::cmp::Reverse<usize>, usize)> = Vec::new();
        for (decl_pos, (name, priority)) in entries.iter().enumerate() {
            if !self.instance_visible(name) {
                continue;
            }
            if self
                .user_default_priority_floor
                .is_some_and(|floor| *priority <= floor)
            {
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
        if order.is_empty() && self.user_default_priority_floor.is_some() {
            return None;
        }
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
    /// The unifier's verdict on `e1 =?= e2`, rendered — for
    /// `CLEAN_INSTANCE_TRACE` only. Runs inside its own metavariable scope
    /// and rolls it back, so tracing never changes what the search assigns.
    fn unify_verdict_for_trace(&mut self, e1: &Expr, e2: &Expr) -> String {
        self.metas.push_scope();
        let e1_inst = self.metas.instantiate(e1);
        let e2_inst = self.metas.instantiate(e2);
        let ctx = self.demand_local_ctx(&[e1, e2, &e1_inst, &e2_inst]);
        let verdict = {
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            format!("{:?}", unifier.unify(e1, e2))
        };
        self.metas.pop_scope();
        format!(
            "{} =?= {} → {verdict}",
            crate::error_render::term(&e1_inst),
            crate::error_render::term(&e2_inst)
        )
    }

    /// [`Self::try_unify`] at Lean's `.instances` transparency
    /// (`Lean/Meta/SynthInstance.lean` runs the whole search there): only
    /// `@[reducible]` constants and registered instances unfold. Used to match
    /// a GLOBAL instance candidate's class arguments against the goal's (G47:
    /// `def M a := Option a` must not make `instMonadOption` a `Monad M`).
    pub(super) fn try_unify_instances(&mut self, e1: &Expr, e2: &Expr) -> bool {
        let e1_inst = self.metas.instantiate(e1);
        let e2_inst = self.metas.instantiate(e2);
        let ctx = self.demand_local_ctx(&[e1, e2, &e1_inst, &e2_inst]);
        let mut unifier = Unifier::with_env_instances(&mut self.metas, self.env, ctx);
        matches!(unifier.unify(e1, e2), UnifyResult::Success)
    }

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
    pub(super) fn collect_meta_fvars(&self, e: &Expr) -> HashSet<FVarId> {
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
    /// weak-head normalized first at `.instances` transparency, so goals that
    /// differ only by a wrapper candidate matching can see through (an
    /// `abbrev`/`@[reducible]` alias) share a key. The class head is left
    /// exactly as-is, so `def`-based class heads are preserved.
    ///
    /// The transparency MUST equal the one candidate matching uses (G47,
    /// ledger (117)): a self-wrapping tower can only form through an unfolding
    /// matching performs, so this key still collapses it, while a goal behind a
    /// SEMIREDUCIBLE wrapper (`C (Wrap Nat)` with `def Wrap α := α`) stays
    /// distinct from its subgoal `C Nat`. At default transparency the two
    /// collided and `instance [C α] : C (Wrap α)` was cut off as a cycle —
    /// Mathlib's `OrderDual`/`Multiplicative` idiom, which Lean accepts.
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
            let reduced = self.whnf_instances(&arg);
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

/// Whether a constant occurs in `e`.
fn mentions_constant(e: &Expr) -> bool {
    let mut visited: HashSet<*const Expr> = HashSet::new();
    let mut stack: Vec<&Expr> = vec![e];
    while let Some(cur) = stack.pop() {
        if !visited.insert(cur as *const Expr) {
            continue;
        }
        if matches!(cur.kind(), ExprKind::Const(..)) {
            return true;
        }
        crate::unify::push_expr_children(cur, &mut stack);
    }
    false
}

/// True iff Lean elaborates `class_name`'s notation with `binop_lazy%`
/// (`<|>`, `>>`), which unifies the operands' types before the instance is
/// synthesized: `HOrElse (Option ?α) (Option Nat) _` has `?α := Nat` from
/// that unification in Lean, not from a choice of instance. Clean's search
/// reaches the same pin through the homogeneous instance
/// (`instHOrElseOption : HOrElse (Option u) (Option u) (Option u)`).
fn is_lazy_binop_class(class_name: &Name) -> bool {
    matches!(class_name.to_string().as_str(), "HOrElse" | "HAndThen")
}

/// True iff Lean resolves an open goal of `class_name` through a core
/// `@[default_instance]` (`instOfNatNat`, `instPowNat`, `instHPow`, …) and
/// Clean's eager search stands in for that defaulting.
fn is_default_instance_carrier_class(class_name: &Name) -> bool {
    matches!(
        class_name.to_string().as_str(),
        "OfNat" | "OfScientific" | "Pow" | "NatPow" | "HPow"
    )
}

/// True iff `class_name` is an input-only type class whose undetermined
/// bare-metavar INPUT arguments must trigger Lean-style postponement in
/// phase-1 instance unification.
///
/// Every class here has NO out-parameters, so ALL of its arguments are inputs
/// the GOAL must determine — never a candidate. Deliberately narrow
/// (`Decidable`, `DecidableEq`, `Inhabited`, `BEq`, `ShiftLeft`, `ShiftRight`):
/// the guard touches input positions of these classes and their premise
/// subtrees. Heterogeneous operators can still select a default bridge, but
/// its homogeneous premise must not invent an undetermined carrier. Lean reaches the
/// same effect uniformly via `synthInstance` mvar-postponement; the allowlist
/// is Clean's conservative staging, not a semantic distinction.
///
/// The root consults this predicate and each recursive goal extends `strict`
/// for its subtree. An input-only premise therefore has the same protection
/// when reached from a defaulting operator as when queried directly.
fn is_input_only_postpone_class(class_name: &Name) -> bool {
    matches!(
        class_name.to_string().as_str(),
        "Decidable" | "DecidableEq" | "Inhabited" | "BEq" | "ShiftLeft" | "ShiftRight"
    )
}

impl ElabCtx<'_> {
    /// Re-fold the identity monad in a monad-family goal: `Monad (fun α => α)`
    /// becomes `Monad Id.{u}`.
    ///
    /// The unifier solves `?m Nat =?= Nat` — the shape `Id.run (x : ?m Nat)`
    /// reaches once the semireducible `Id` alias has been unfolded on the
    /// other side — with the higher-order pattern `?m := fun α => α`, which no
    /// instance names: every monad instance is filed under a constant carrier
    /// (`Id.instMonad : Monad Id`). `Id` is DEFINED as that lambda
    /// (`Id := fun α => α`), so the two goals are definitionally equal and an
    /// instance of one is an instance of the other; the kernel re-checks the
    /// emitted term against the unfolded goal. Only a goal of a monad-family
    /// class (`is_monad_family_class`) is touched, and only an argument that
    /// is exactly the identity lambda over `Type u`.
    fn fold_identity_monad(&self, goal: &Expr) -> Expr {
        let Some((class_name, args)) = crate::instances::extract_class_app(goal) else {
            return goal.clone();
        };
        if !is_monad_family_class(&class_name)
            || self.env.get_const(&Name::from_string("Id")).is_none()
        {
            return goal.clone();
        }
        let mut changed = false;
        let new_args: Vec<Expr> = args
            .iter()
            .map(|arg| match arg.kind() {
                ExprKind::Lam(_, dom, body) if matches!(body.kind(), ExprKind::BVar(0)) => {
                    match dom.kind() {
                        ExprKind::Sort(Level::Succ(u)) => {
                            changed = true;
                            Expr::const_(Name::from_string("Id"), vec![u.as_ref().clone()])
                        }
                        _ => arg.clone(),
                    }
                }
                _ => arg.clone(),
            })
            .collect();
        if !changed {
            return goal.clone();
        }
        Expr::apps(goal.get_app_fn().clone(), new_args)
    }
}

/// True iff `class_name` is one of the classes of Lean's monad hierarchy,
/// whose only input is the monad (or, for `MonadExcept`, the monad beside an
/// out-param error type). A goal of one of these with the monad still open is
/// stuck, never searched (see the refusal in `resolve_instance_candidates`).
pub(in crate::infer) fn is_monad_family_class(class_name: &Name) -> bool {
    matches!(
        class_name.to_string().as_str(),
        "Pure"
            | "Bind"
            | "Functor"
            | "Seq"
            | "SeqLeft"
            | "SeqRight"
            | "Applicative"
            | "Monad"
            | "MonadExcept"
    )
}

/// True iff `class_name` is one of Lean core's HETEROGENEOUS operator classes
/// whose only `@[default_instance]` is the homogeneous bridge —
/// `@[default_instance] instHAdd [Add α] : HAdd α α α` and its siblings.
///
/// Lean REFUSES to run instance search for such a goal while its type
/// arguments still contain metavariables. Measured verbatim on the pinned
/// v4.30.0-rc2 binary, `def f := fun a b => a + b`:
///
/// ```text
/// error: typeclass instance problem is stuck
///   HAdd ?m.13 (?m.14 a) (?m.15 a b)
/// Note: Lean will not try to resolve this typeclass instance problem because
/// the first and second type arguments to `HAdd` contain metavariables.
/// ```
///
/// Clean had no such refusal, so a goal with NOTHING determined fell through
/// to [`ElabCtx::candidate_order`], where every candidate ties on
/// priority/head-match and registration order decides — most-recent-first, and
/// the last `HAdd` instance the prelude registers is `instHAddUInt64`
/// (`clean-kernel/src/env/data_types_uint.rs::init_uint_arith`, the
/// `["UInt8","UInt16","UInt32","UInt64"] x [HAdd, ...]` loop, run after
/// `init_nat_hadd_inst`'s `instHAddNat`). Measured 2026-09-16 at HEAD with
/// `clean check`: `def a1 := List.foldl (· + ·) 0 [1, 2, 3]` gave
/// `a1 : UInt64`, where the pinned `lean` v4.30.0-rc2 gives `a1 : Nat`.
///
/// The only caller sits BELOW the B99 `@[default_instance]` block and is
/// guarded on `!defaulting`, so this refusal can never pre-empt a registered
/// default. That guard is INERT today and is written for the future:
/// measured 2026-09-16 at HEAD, with `@[default_instance] instance
/// instHAddSec : HAdd Sec Sec Sec` followed by a PLAIN `instance
/// instHAddSec2 : HAdd Sec2 Sec2 Sec2`, `def usesDefault := fun a b => a + b`
/// answered `Sec2 -> Sec2 -> Sec2` — the most-recent registration, where Lean
/// v4.30.0-rc2 answers `Sec`. So `default_order` does not fire for these
/// classes at all and `defaulting` is false at every one of these calls. The
/// guard is here so that repairing B99 for them cannot be silently defeated by
/// this refusal. Pinned by
/// `test_default_instance_on_a_hetero_class_is_refused_not_grabbed`.
pub(in crate::infer) fn is_hetero_binop_default_instance_class(class_name: &Name) -> bool {
    matches!(
        class_name.to_string().as_str(),
        "HAdd"
            | "HSub"
            | "HMul"
            | "HDiv"
            | "HMod"
            | "HAnd"
            | "HOr"
            | "HXor"
            | "HAppend"
            | "HPow"
            | "HShiftLeft"
            | "HShiftRight"
    )
}

/// True iff this class's arguments may all be collapsed onto one carrier when
/// its goal is drained.
///
/// `instHAdd [Add α] : HAdd α α α` and its arithmetic/bitwise/append siblings
/// force all three equal, so all three are linked. `HPow` genuinely does not —
/// `instHPow [Pow α β] : HPow α β α` keeps an independent exponent type — so
/// only `α` and the result `γ` are linked there.
///
/// `HShiftLeft`/`HShiftRight` are excluded too, and that is Clean's split
/// rather than Lean's: Lean's `instance [ShiftLeft α] : HShiftLeft α α α` IS
/// homogeneous, but Clean's own `binop%` desugaring keeps the shift amount in
/// an independent slot (`ElabCtx::hetero_binop_homogenize_slots`'s
/// `homogeneous` field), and this predicate follows Clean so the two passes
/// cannot disagree. Linking fewer arguments can only leave a goal postponed;
/// it can never assign a wrong carrier.
///
/// A bare numeral shift is defaulted by resolving its actual dictionary in
/// `ElabCtx::resolve_shift_numeral_instance`, before the lower-priority Nat
/// numeral default. No unconditional homogeneous shift join is made here.
pub(in crate::infer) fn hetero_binop_links_all_arguments(class_name: &Name) -> bool {
    !matches!(
        class_name.to_string().as_str(),
        "HPow" | "HShiftLeft" | "HShiftRight"
    )
}

/// Return the metavariable id iff `e` is a BARE unassigned metavariable — a
/// meta-encoded FVar with no assignment in `metas`. Caller instantiates `e`
/// first, so a residual meta-FVar is genuinely unassigned; the `is_assigned`
/// guard is belt-and-suspenders. Used by the phase-1 postpone check to detect
/// an undetermined input position.
pub(in crate::infer) fn bare_unassigned_meta(metas: &MetaState, e: &Expr) -> Option<MetaId> {
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

/// Whether `level` mentions a parameter named in `names`.
fn level_mentions_any(level: &Level, names: &[Name]) -> bool {
    match level {
        Level::Zero => false,
        Level::Succ(inner) => level_mentions_any(inner, names),
        Level::Max(a, b) | Level::IMax(a, b) => {
            level_mentions_any(a, names) || level_mentions_any(b, names)
        }
        Level::Param(name) => names.contains(name),
    }
}
