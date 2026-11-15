// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two halves of Lean's `processAssignment` that [`Unifier::unify_meta`]
//! used to lack: the `ctxApprox` arm of `CheckAssignment.checkMVar` and
//! `checkTypesAndAssign` (`Lean/Meta/ExprDefEq.lean:457-472`, `:856-890`).
//!
//! Both were measured on the source-elaboration slice
//! (`Mathlib/Logic/Function/Basic.lean`, `Mathlib/Logic/Basic.lean`): nine rows,
//! pinned by `crate::tests_pkg4_unifier`.

use std::collections::HashSet;

use clean_kernel::{ExprKind, FVarId};

use super::super::meta_id::{MetaId, MetaKind};
use super::super::meta_state::MetaState;
use super::pattern::{collect_unassigned_metas, find_escaping_fvar, find_scope_widening_meta};
use super::{Unifier, UnifyResult};
use clean_kernel::Expr;

/// Nesting bound for [`Unifier::check_types_before_assign`]. A metavariable's
/// type is a type, whose own metavariables are typed by sorts, so a genuine
/// chain is two or three deep; the bound only stops a pathological cycle
/// through ill-formed metavariable types from recursing without end. Hitting
/// it skips the check, which is the historical behaviour.
const MAX_CHECK_TYPES_DEPTH: u32 = 8;

impl Unifier<'_> {
    /// Lean's `ctxApprox` for a bare assignment `?m := other`
    /// (`CheckAssignment.checkMVar`, `Lean/Meta/ExprDefEq.lean:856-890`,
    /// enabled for elaboration at `Lean/Elab/Config.lean:62`).
    ///
    /// `other` mentions an unassigned metavariable `?n` created in a WIDER
    /// context than `?m`'s (`allowed`): a binder's type `?T` is an outer
    /// metavariable, and the binder's body minted `?n` for an implicit
    /// argument. `?m := other` would let `?n` capture a local `?m` cannot see
    /// once `?n` is solved, so Clean used to return `Stuck`, reported as
    /// `Cannot infer type` (`LeftInverse`'s implicits against `∃ g`'s binder
    /// type; `extend`'s `γ` against `fun g ↦`'s). Lean instead restricts `?n`
    /// to `?m`'s context and assigns. Clean's local scope is a list read only
    /// by scope checks, so the restriction is done IN PLACE
    /// (`MetaState::restrict_locals`) rather than through Lean's fresh
    /// `?n := ?n'`; the two are the same constraint on `?n`.
    ///
    /// Refused — returning `false` with nothing changed, so the caller keeps
    /// its `Stuck` — exactly where Lean throws, plus two places where Clean's
    /// representation differs from Lean's:
    ///
    /// * `?n` is not [`MetaKind::Natural`] (Lean: `isSyntheticOpaque`; Clean
    ///   applies it to every metavariable not minted as natural, see
    ///   [`MetaKind`]);
    /// * `?m`'s context is not contained in `?n`'s (Lean: `isSubPrefixOf`);
    /// * `?n`'s type, after the same restriction of ITS metavariables,
    ///   mentions a local `?m` cannot see (Lean: `check mvarDecl.type` throws
    ///   `outOfScopeFVar`);
    /// * a local `?n` would lose is not LIVE in the unifier's context. Lean
    ///   never meets a raw metavariable whose extra locals were already
    ///   abstracted — `mkLambdaFVars` rewrites it to `?n' x` through
    ///   `elimMVarDeps` — while Clean's `fun x => ?n` keeps `?n` raw. Narrowing
    ///   such a `?n` would forbid it from ever using the bound `x`, a loss Lean
    ///   does not take, so only locals of the binder being elaborated right
    ///   now (the rows' shape) may be dropped;
    /// * `other` is itself a bare metavariable: the caller then assigns in the
    ///   reverse direction, which is Lean's preference for `?m =?= ?n` too.
    ///
    /// Soundness: narrowing only REMOVES locals a metavariable may be solved
    /// with, and is undo-tracked, so a rolled-back attempt restores it. The
    /// kernel re-checks every declaration.
    pub(super) fn approximate_context(
        &mut self,
        target: MetaId,
        allowed: &HashSet<FVarId>,
        other: &Expr,
    ) -> bool {
        if self.as_meta(other).is_some() || !self.has_whnf() {
            return false;
        }
        self.metas.push_scope();
        let mut visiting = HashSet::new();
        let narrowed = self.narrow_widening_metas(other, target, allowed, &mut visiting)
            && find_scope_widening_meta(&self.metas.instantiate(other), allowed, self.metas)
                .is_none();
        if narrowed {
            self.metas.commit();
        } else {
            self.metas.pop_scope();
        }
        narrowed
    }

    /// Narrow every scope-widening metavariable of `expr` to `allowed`,
    /// depth-first through their types (Lean's `check mvarDecl.type`).
    fn narrow_widening_metas(
        &mut self,
        expr: &Expr,
        target: MetaId,
        allowed: &HashSet<FVarId>,
        visiting: &mut HashSet<MetaId>,
    ) -> bool {
        let mut nested = collect_unassigned_metas(expr, self.metas);
        nested.sort_unstable();
        nested.dedup();
        for meta_id in nested {
            if meta_id == target {
                return false;
            }
            let Some(meta) = self.metas.get(meta_id) else {
                continue;
            };
            let own: HashSet<FVarId> = meta.locals.iter().map(|(_, fvar, _)| *fvar).collect();
            if own.is_subset(allowed) {
                continue;
            }
            let (kind, raw_ty) = (meta.kind, meta.ty.clone());
            // Lean's `isSubPrefixOf`: `?m`'s context must be contained in `?n`'s.
            if kind != MetaKind::Natural
                || !allowed.is_subset(&own)
                || !own
                    .difference(allowed)
                    .all(|fvar| self.is_live_local(*fvar))
                || !visiting.insert(meta_id)
            {
                return false;
            }
            let ty = self.metas.instantiate(&raw_ty);
            if find_escaping_fvar(&ty, allowed).is_some()
                || !self.narrow_widening_metas(&ty, target, allowed, visiting)
                || !self.metas.restrict_locals(meta_id, allowed)
            {
                return false;
            }
        }
        true
    }

    /// Whether `fvar` is a local of the context this unifier was built over
    /// (the elaborator's current locals), as opposed to a local that was
    /// already abstracted out of the term being unified.
    fn is_live_local(&self, fvar: FVarId) -> bool {
        self.tc_cache
            .borrow()
            .as_ref()
            .is_some_and(|tc| tc.local_context().get(fvar).is_some())
    }

    /// Lean's `checkTypesAndAssign` (`Lean/Meta/ExprDefEq.lean:457-472`):
    /// before `?m := value`, unify `?m`'s type with `value`'s.
    ///
    /// Measured motivation: a type implicit that occurs ONLY in the type of
    /// another metavariable was never solved. Applying
    /// `ce3 {α β} {f : α → β} {g : β → α} (h : ∀ x, f (g x) = x)` to an `h`
    /// solves `?f := f` and `?g := g` structurally, and `?α` occurs in neither
    /// side of any constraint — only in `?f : ?α → ?β` — so the declaration
    /// died `unsolved metavariables` (`Function.LeftInverse.surjective`,
    /// `RightInverse.injective`, `leftInverse_iff_comp`, `rightInverse_iff_comp`,
    /// `RightInverse.comp`).
    ///
    /// Two deliberate narrowings of Lean's rule, each keeping a behaviour that
    /// already existed:
    ///
    /// * it runs only when `?m`'s type still mentions an unassigned
    ///   metavariable (a ground type has nothing to solve, and this keeps the
    ///   hot path free), and never for a `Sort`-typed `?m`, whose arm in
    ///   `unify_meta` already constrains the level with cumulativity
    ///   (`?T : Type := P : Prop` is accepted there and must stay accepted);
    /// * a type unification that does not SUCCEED is rolled back and the
    ///   assignment proceeds as before, where Lean would refuse it. Clean's
    ///   unifier is weaker than Lean's (no lazy delta; the lenient Bool/Prop
    ///   bridge), and a refusal here would turn each of those weaknesses into a
    ///   new failure. This adds solutions and removes none; the kernel
    ///   re-checks every declaration, so a type-incorrect assignment still
    ///   fails closed.
    pub(super) fn check_types_before_assign(&mut self, meta_id: MetaId, value: &Expr) {
        let depth = self.check_types_depth.get();
        if depth >= MAX_CHECK_TYPES_DEPTH {
            return;
        }
        let Some(meta) = self.metas.get(meta_id) else {
            return;
        };
        let raw_ty = meta.ty.clone();
        // Cheapest-first: a ground `?x : Nat` exits on the metadata bit.
        if !raw_ty.has_fvar_quick() || !Self::expr_mentions_meta(&raw_ty) {
            return;
        }
        let meta_ty = self.metas.instantiate(&raw_ty);
        if matches!(meta_ty.kind(), ExprKind::Sort(_))
            || collect_unassigned_metas(&meta_ty, self.metas).is_empty()
        {
            return;
        }
        let value_ty = {
            let tc_cache = self.tc_cache.borrow();
            let Some(tc) = tc_cache.as_ref() else {
                return;
            };
            match tc.infer_type(value) {
                Ok(ty) => ty,
                // `value` mentions a metavariable minted after this unifier's
                // context was built: nothing to compare against.
                Err(_) => return,
            }
        };
        let value_ty = self.metas.instantiate(&value_ty);
        // Unifying the types must not be able to solve `?m` itself, or the
        // assignment that follows would find it taken.
        if collect_unassigned_metas(&value_ty, self.metas).contains(&meta_id) {
            return;
        }
        self.check_types_depth.set(depth + 1);
        self.metas.push_scope();
        if matches!(self.unify(&meta_ty, &value_ty), UnifyResult::Success) {
            self.metas.commit();
        } else {
            self.metas.pop_scope();
        }
        self.check_types_depth.set(depth);
    }

    /// Whether `e` mentions any elaborator metavariable (encoded as high-bit
    /// FVars). Iterative DAG walk via [`crate::unify::meta_state::push_expr_children`];
    /// used by the type-guarded head-projection check in [`Self::unify_meta`]
    /// and by [`Self::check_types_before_assign`].
    pub(super) fn expr_mentions_meta(e: &Expr) -> bool {
        let mut stack: Vec<&Expr> = vec![e];
        while let Some(cur) = stack.pop() {
            if let ExprKind::FVar(id) = cur.kind() {
                if MetaState::from_fvar(*id).is_some() {
                    return true;
                }
            }
            crate::unify::meta_state::push_expr_children(cur, &mut stack);
        }
        false
    }
}
