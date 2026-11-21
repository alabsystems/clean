// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Postponing an un-annotated lambda argument whose body is stuck on its own
//! open binder type (G28, ledger class (98)).
//!
//! `ps.foldl (fun acc p => acc.bump p) m` with no expected type: `List.foldl`'s
//! `f : α → β → α` slot is elaborated before `init : α` pins `α`, so `acc`'s
//! type is the open `?α` when `acc.bump` is reached. Lean does not fail there:
//! `resolveLValLoop` (`Lean/Elab/App.lean`) runs `tryPostponeIfMVar eType` on a
//! field-notation receiver whose type is a metavariable, the postponement is
//! caught at the enclosing `elabTerm`, and the stuck subterm is resumed by
//! `synthesizeSyntheticMVars` once the later argument `m` has solved `?α`.
//!
//! Clean has no per-subterm postponement, so it postpones the WHOLE lambda
//! argument, and only in exactly the situation Lean postpones in:
//!
//! 1. the argument is an un-annotated `fun` (at least one binder without a
//!    type) whose slot type still carries metavariables;
//! 2. it was elaborated EAGERLY first, exactly as before, and that failed;
//! 3. either field notation needs an unknown receiver type or a relative
//!    constructor pattern needs an unknown scrutinee type. The head must
//!    still be an unassigned metavariable. A miss in a known type does not
//!    trigger a retry.
//!
//! Then the whole application is re-elaborated with that argument deferred:
//! a placeholder metavariable stands in its slot, the remaining arguments and
//! the expected result type pin the slot, and the lambda is elaborated in the
//! drain the `by`-block deferral already uses (`elab_app.rs`). If the retry
//! fails too, the ORIGINAL error is returned, so an application that failed
//! before fails with the same message; one that succeeded before never reaches
//! this path. The term is kernel-checked like every other, so this can turn a
//! refusal into an acceptance only where the deferred elaboration type-checks.
//!
//! Retries nest (a deferred lambda can contain an application that defers its
//! own lambda), so their depth is capped at [`MAX_RETRY_DEPTH`].

use super::*;

/// Nesting cap on whole-application retries; each level at most doubles the
/// elaboration of a failing application.
const MAX_RETRY_DEPTH: u32 = 4;

/// Lambda postponement and the shared field-notation watch used by arrows.
#[derive(Debug, Default)]
pub(crate) struct LambdaPostponeState {
    /// How many eager lambda or arrow-domain attempts are in flight; field notation records a
    /// meta-typed receiver only while this is non-zero.
    watch: u32,
    /// Field notation met a receiver whose type head is an unassigned
    /// metavariable since the innermost watch began.
    stuck: bool,
    /// Current nesting depth of whole-application retries.
    retry_depth: u32,
    /// One-shot: argument indices the NEXT `elab_app_inner` call defers.
    /// Consumed at its entry, so nested applications never see it.
    defer_next_app: Vec<usize>,
}

/// Saved state of the enclosing watch, restored by
/// [`ElabCtx::end_field_notation_watch`].
pub(super) struct FieldNotationWatch {
    outer_stuck: bool,
}

impl ElabCtx<'_> {
    /// Is `e` (through parentheses) a `fun` with at least one un-annotated
    /// binder, or a `fun | …` pattern lambda (whose binders carry no types)?
    pub(super) fn is_unascribed_lambda_arg(e: &SurfaceExpr) -> bool {
        match e {
            SurfaceExpr::Paren(_, inner) => Self::is_unascribed_lambda_arg(inner),
            SurfaceExpr::Lambda(_, binders, _) => binders.iter().any(|b| b.ty.is_none()),
            SurfaceExpr::PatternMatchLambda(..) => true,
            _ => false,
        }
    }

    /// Take the one-shot set of argument indices this application defers.
    pub(super) fn take_deferred_lambda_args(&mut self) -> Vec<usize> {
        std::mem::take(&mut self.lambda_postpone.defer_next_app)
    }

    /// Watch an eager lambda or arrow-domain attempt for field notation whose
    /// receiver has an unassigned metavariable type.
    pub(super) fn begin_field_notation_watch(&mut self) -> FieldNotationWatch {
        let outer_stuck = std::mem::replace(&mut self.lambda_postpone.stuck, false);
        self.lambda_postpone.watch += 1;
        FieldNotationWatch { outer_stuck }
    }

    /// End the watch begun by [`Self::begin_field_notation_watch`]; returns whether
    /// this attempt met a meta-typed receiver. The enclosing watch keeps
    /// seeing it too: a stuck nested attempt is visible to its caller.
    pub(super) fn end_field_notation_watch(&mut self, watch: FieldNotationWatch) -> bool {
        self.lambda_postpone.watch = self.lambda_postpone.watch.saturating_sub(1);
        let stuck = self.lambda_postpone.stuck;
        self.lambda_postpone.stuck = watch.outer_stuck || stuck;
        stuck
    }

    /// Record, during a watched attempt, field notation whose receiver type
    /// has an unassigned metavariable at its head (Lean's
    /// `tryPostponeIfMVar eType` in `resolveLValLoop`). Read-only otherwise.
    pub(super) fn note_field_notation_receiver(&mut self, receiver: &Expr) {
        if self.lambda_postpone.watch == 0 || self.lambda_postpone.stuck {
            return;
        }
        let Ok(ty) = self.infer_type(receiver) else {
            return;
        };
        self.note_unassigned_expected_type(&ty);
    }

    /// Both a projection receiver and a relative constructor are resolved
    /// from the type of their subject. A later application argument can
    /// determine that type after eager elaboration of the lambda has failed.
    pub(in crate::infer) fn note_unassigned_expected_type(&mut self, ty: &Expr) {
        if self.lambda_postpone.watch == 0 || self.lambda_postpone.stuck {
            return;
        }
        let ty = self.whnf(&self.metas.instantiate(ty));
        let head_is_open_meta = matches!(ty.get_app_fn().kind(),
            ExprKind::FVar(id) if MetaState::from_fvar(*id)
                .is_some_and(|m| self.metas.get_assignment(m).is_none()));
        if head_is_open_meta {
            self.lambda_postpone.stuck = true;
        }
    }

    /// Solve a slot that is still a BARE unassigned metavariable with the
    /// argument's type as written, when whnf would change that type's head (a
    /// `def` alias such as `VM := Nat → Option Nat`). Lean's `?α =?= VM`
    /// assigns `VM`; assigning the unfolded Pi instead hides the alias from
    /// field notation on a later binder of that type (G28: `ps.foldl (fun acc
    /// p => acc.set p.1 p.2) m` with `m : VM`). Returns whether it assigned;
    /// on `false` nothing changed and the caller unifies the whnf forms as
    /// before.
    pub(super) fn assign_bare_slot_folded(&mut self, arg_type: &Expr, slot: &Expr) -> bool {
        let slot = self.metas.instantiate(slot);
        if instance::bare_unassigned_meta(&self.metas, &slot).is_none()
            || instance::bare_unassigned_meta(&self.metas, arg_type).is_some()
            || !matches!(arg_type.get_app_fn().kind(), ExprKind::Const(..))
        {
            return false;
        }
        let unfolded = self.whnf(arg_type);
        if unfolded.get_app_fn() == arg_type.get_app_fn() {
            return false;
        }
        self.metas.push_scope();
        if self.try_unify(&slot, arg_type) {
            self.metas.commit();
            true
        } else {
            self.metas.pop_scope();
            false
        }
    }

    /// May the application retry with one more lambda deferred?
    pub(super) fn lambda_retry_allowed(&self) -> bool {
        self.lambda_postpone.retry_depth < MAX_RETRY_DEPTH
    }

    /// Re-elaborate `func args` with the arguments at `defer` postponed; on
    /// failure, return `original` (the error of the eager attempt).
    pub(super) fn elab_app_retry_deferring_lambdas(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
        defer: Vec<usize>,
        original: ElabError,
    ) -> Result<Expr, ElabError> {
        self.lambda_postpone.defer_next_app = defer;
        self.lambda_postpone.retry_depth += 1;
        let result = self.elab_app_inner(func, args);
        self.lambda_postpone.retry_depth -= 1;
        // Defensive: `elab_app_inner` consumed it at entry.
        self.lambda_postpone.defer_next_app.clear();
        result.map_err(|_| original)
    }
}

#[cfg(test)]
#[path = "elab_app_postpone_lambda_tests.rs"]
mod tests;
