// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implicit-lambda introduction — Lean's `elabImplicitLambda`.
//!
//! When a term is elaborated against an expected type whose leading binder is
//! implicit or instance-implicit, Lean does not unify the term with the `Pi`:
//! it WRAPS the term, introducing a fresh local per non-explicit binder,
//! elaborating the term against the instantiated body and `mkLambdaFVars`-ing
//! the locals back (`Lean/Elab/Term/TermElabM.lean`: `blockImplicitLambda`
//! :1684, `useImplicitLambda` :1711, `elabImplicitLambda` :1774, dispatched
//! once per term at :1806).
//!
//! Clean built implicit lambdas only when the surface term was itself a `fun`,
//! and decided it PER SURFACE BINDER inside `elab_lambda`. Both halves are
//! wrong in a way this module fixes together:
//!
//! * a non-`fun` term was unified directly with the `Pi`, so
//!   `Function.Injective.preorder f .rfl .rfl` (`Mathlib/Order/Basic.lean`
//!   `Preorder.lift` / `PartialOrder.lift`, whose slots are
//!   `∀ {x y}, f x ≤ f y ↔ x ≤ y`) left its `{x y}` as metavariables nothing
//!   constrains;
//! * re-testing at every binder let an EXPLICIT surface binder facing an
//!   implicit expected binder insert a synthetic one and recurse with the
//!   surface binder unconsumed, which left the remaining body with NO expected
//!   type (`Mathlib/Logic/Basic.lean` `eq_iff_eq_cancel_left` /
//!   `_right`). Lean's `propagateExpectedType` (`Lean/Elab/Binders.lean`:410,
//!   the arm `| .forallE _ d b _ =>` at :416) peels exactly one `forallE` per
//!   user binder and IGNORES its binder info, which is why Lean accepts
//!   `fun h a => …` there and REJECTS
//!   `fun n x => x : Nat → {α : Type} → α → α` — measured both ways against
//!   the pinned v4.30.0-rc2 binary.
//!
//! The trigger and the loop are deliberately different, as they are in Lean:
//! only an implicit / instance-implicit FIRST binder triggers the wrap
//! (`useImplicitLambda`, :1718-1720 — a strict-implicit `⦃x⦄` does not), but
//! once triggered the loop consumes every binder that is not explicit
//! (:1779-1786), strict-implicit included.

use super::*;
use crate::stack_safe;
use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, FVarId, Name};

/// One binder introduced by the wrap, in the order it was pushed.
struct ImplicitBinder {
    data: BinderData,
    fvar: FVarId,
    domain: Expr,
    is_local_instance: bool,
}

impl<'a> ElabCtx<'a> {
    /// Lean's `blockImplicitLambda` (`TermElabM.lean`:1684-1688): the surface
    /// shapes that never get an implicit lambda.
    ///
    /// `noImplicitLambda%` has no Clean spelling. Parentheses are pure
    /// grouping, so the test is made on the unwrapped node — `(by tac)` and
    /// `(fun {α} x => …)` block exactly as their bare forms do.
    fn blocks_implicit_lambda(surface: &SurfaceExpr) -> bool {
        // `@e` / `@f a` (`isExplicit` / `isExplicitApp`).
        if Self::surface_is_explicit_app(surface) {
            return true;
        }
        match Self::unwrap_surface_parens(surface) {
            // `_` (`isHole`) and `?x` (`isSyntheticHole`).
            SurfaceExpr::Hole(_) | SurfaceExpr::NamedHole(..) => true,
            // `by …` (`isTacticBlock`).
            SurfaceExpr::ByTactic(..) => true,
            // `(e : T)` (`isTypeAscription`) — the INNER term is elaborated
            // against `T` by `elab_ascription` and wraps there if it should.
            SurfaceExpr::Ascription(..) => true,
            // `fun {α} x => …` (`isLambdaWithImplicit`): the user is binding
            // the implicit position themselves. A `match` never blocks, even
            // when every alternative binds it: `isLambdaWithImplicit` reads
            // one syntax node (see `binds_implicit_position_itself`).
            SurfaceExpr::Lambda(..) | SurfaceExpr::PatternMatchLambda(..) => {
                Self::binds_implicit_position_itself(surface)
            }
            _ => false,
        }
    }

    /// The "binds the implicit position itself" half of
    /// [`Self::blocks_implicit_lambda`].
    ///
    /// A `fun` with an implicit or instance-implicit binder. Lean's test names
    /// exactly two binder kinds — `Lean.Parser.Term.implicitBinder` and
    /// `Lean.Parser.Term.instBinder` (`TermElabM.lean`:1648-1651) — so a
    /// STRICT-implicit `⦃β⦄` binder does NOT block, and `fun ⦃β⦄ x => x : {α :
    /// Type} → α → α` is WRAPPED and then rejected (`fun ⦃β⦄ x => x has type
    /// ⦃β : α✝⦄ → ?m → ?m but is expected to have type α✝ → α✝`, measured on
    /// the pinned v4.30.0-rc2 binary). Blocking on every non-explicit binder
    /// instead let that term bind `⦃β⦄` to the expected `{α}` and be ACCEPTED
    /// — a term Lean refuses.
    ///
    /// A `match` does NOT bind it, even when every alternative is a `fun {α}
    /// …`. `isLambdaWithImplicit` reads one syntax node and does not look
    /// through `match`, so Lean wraps such a `match`, elaborates each `fun {α}
    /// …` alternative against the REMAINING type `α✝ → …`, and refuses the
    /// declaration (`fun {A} x => acc has type {A : Type} → A → Nat … but is
    /// expected to have type A✝ → Nat`, pinned lean v4.30.0-rc2). Clean
    /// declined the wrap for that shape from bb3b6ffe6 until 2026-10-02 and
    /// accepted it, a deliberate superset of Lean. Decision D2 (2026-10-02,
    /// `docs/DECISIONS.md`): Clean never accepts what Lean rejects, so the
    /// `match` takes Lean's route and the spelling is refused, here and in
    /// `refuse_alternative_binding_wrapped_implicit` for a recursive body.
    fn binds_implicit_position_itself(surface: &SurfaceExpr) -> bool {
        match Self::unwrap_surface_parens(surface) {
            SurfaceExpr::Lambda(_, binders, _) | SurfaceExpr::PatternMatchLambda(_, binders, _) => {
                binders.iter().any(|b| {
                    matches!(
                        convert_binder_info(b.info),
                        BinderInfo::Implicit | BinderInfo::InstImplicit
                    )
                })
            }
            _ => false,
        }
    }

    /// Does any alternative of this `match` (through nested `match`es in
    /// alternative position and parentheses) bind the implicit position
    /// itself, in the sense of [`Self::binds_implicit_position_itself`]?
    fn some_alternative_binds_implicit_position(surface: &SurfaceExpr) -> bool {
        match Self::unwrap_surface_parens(surface) {
            SurfaceExpr::Match(_, _, _, arms) => arms
                .iter()
                .any(|arm| Self::some_alternative_binds_implicit_position(&arm.body)),
            other => Self::binds_implicit_position_itself(other),
        }
    }

    /// The recursive-`match` definition body inserts the implicit lambda in
    /// each alternative rather than around the `match` (see the call site in
    /// [`Self::elab_def_value_maybe_implicit_lambda`]). That placement is
    /// Clean's, forced by where it lowers structural recursion; Lean wraps the
    /// whole body, so every alternative faces the type that REMAINS after the
    /// leading implicit binders, and an alternative that binds one of them
    /// itself (`| k => fun {A} (x : A) => …`) is a type mismatch in Lean.
    /// Refuse it here so the per-alternative placement accepts nothing Lean's
    /// placement rejects (decision D2, 2026-10-02, `docs/DECISIONS.md`).
    fn refuse_alternative_binding_wrapped_implicit(
        &mut self,
        val: &SurfaceExpr,
        expected: &Expr,
    ) -> Result<(), ElabError> {
        if self.explicit_mode || !Self::some_alternative_binds_implicit_position(val) {
            return Ok(());
        }
        let expected = self.whnf(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(expected)),
        );
        let ExprKind::Pi(bd, _, _) = expected.kind() else {
            return Ok(());
        };
        if !matches!(bd.info, BinderInfo::Implicit | BinderInfo::InstImplicit) {
            return Ok(());
        }
        Err(ElabError::TypeMismatch {
            expected: "the type that remains after Lean's implicit lambda around the whole \
                       `match` (its leading implicit binders are already introduced)"
                .to_string(),
            actual: "an alternative `fun` that binds a leading implicit binder itself, \
                     which pinned Lean refuses"
                .to_string(),
        })
    }

    /// Lean's `isLocalIdent?` escape (`TermElabM.lean`:1721-1745): a local
    /// whose type is still a metavariable is NOT wrapped — Lean postpones
    /// instead, because wrapping would commit the local to a function type the
    /// expected type has not yet earned.
    fn implicit_lambda_escape_local_ident(&self, surface: &SurfaceExpr) -> bool {
        let SurfaceExpr::Ident(_, name) = Self::unwrap_surface_parens(surface) else {
            return false;
        };
        let Some((_, ty)) = self.lookup_local(name) else {
            return false;
        };
        let ty = self.metas.instantiate(ty);
        matches!(ty.kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some())
    }

    /// Lean's `useImplicitLambda` (`TermElabM.lean`:1711-1746): should this
    /// term be wrapped against this expected type?
    ///
    /// Only an `Implicit` / `InstImplicit` FIRST binder triggers. A
    /// strict-implicit `⦃x⦄` does not — Lean's own remark — even though the
    /// loop below consumes one once something else has triggered.
    pub(super) fn use_implicit_lambda(&mut self, surface: &SurfaceExpr, expected: &Expr) -> bool {
        // `@` governs the binders, so it blocks the wrap exactly as the
        // surface `@` spelling does.
        if self.explicit_mode {
            return false;
        }
        if Self::blocks_implicit_lambda(surface) {
            return false;
        }
        let expected = self.whnf(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(expected)),
        );
        let ExprKind::Pi(bd, _, _) = expected.kind() else {
            return false;
        };
        if !matches!(bd.info, BinderInfo::Implicit | BinderInfo::InstImplicit) {
            return false;
        }
        !self.implicit_lambda_escape_local_ident(surface)
    }

    /// Lean's `elabImplicitLambda` (`TermElabM.lean`:1774-1789).
    ///
    /// Introduces one inaccessible local per LEADING non-explicit binder of
    /// `expected`, elaborates `surface` against what remains, and abstracts the
    /// locals back with their recorded binder info. The synthetic names carry
    /// the inaccessible dagger, so no source identifier in `surface` can
    /// resolve to one (capture-free), and `add_decl` re-checks the closed
    /// lambda — this can only fill binders the expected type already fixes.
    ///
    /// Terminates: each step strips one `Pi` layer off a finite type, and the
    /// recursive `elaborate_with_expected_type` below cannot re-trigger because
    /// the remaining type no longer leads with a non-explicit binder.
    pub(super) fn elab_implicit_lambda(
        &mut self,
        surface: &SurfaceExpr,
        expected: &Expr,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            let (pushed, remaining) = self.open_implicit_lambda_binders(expected);
            let inner = self.elaborate_with_expected_type(surface, Some(remaining));
            // The locals are popped BEFORE `?`: an elaboration error here is
            // routinely RECOVERED (the speculative definition-body lane, the
            // application retries), and a local — or worse, a local INSTANCE —
            // left on the context would then be visible to the retry that runs
            // next in the same `ElabCtx`. The deleted per-binder code in
            // `elab_core` popped before propagating for the same reason.
            self.pop_implicit_lambda_binders(&pushed);
            let inner = inner?;
            Ok(self.abstract_implicit_lambda_binders(pushed, inner))
        })
    }

    /// Push a local for every leading non-explicit binder of `expected` and
    /// return them with the type that remains.
    ///
    /// Shared with `elab_lambda`, which needs the same introduction but then
    /// continues with its own surface binder list rather than re-entering the
    /// term elaborator. Two copies of a binder-introduction rule would drift.
    fn open_implicit_lambda_binders(&mut self, expected: &Expr) -> (Vec<ImplicitBinder>, Expr) {
        // A well-formed expected type has a finite telescope and this loop
        // strips one `Pi` per step. The bound only keeps a type whose `whnf`
        // keeps producing non-explicit binders — which nothing here proves
        // impossible, and which the deleted per-binder code could not reach
        // because it was bounded by the SURFACE binder list — from hanging the
        // elaborator instead of failing it. Stopping early leaves binders
        // unconsumed, so the term is refused by the type check that follows;
        // it can never accept more. The same reasoning as `resolve_instance`'s
        // candidate budget.
        const MAX_INTRODUCED_BINDERS: usize = 1024;
        let mut pushed = Vec::new();
        let mut ty = self.whnf(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(expected)),
        );
        let display_names = self
            .term_info_capture
            .as_ref()
            .and_then(|_| self.named_arg_slots_of_surface_forall(&ty));
        while let ExprKind::Pi(bd, domain, codomain) = ty.kind() {
            if pushed.len() >= MAX_INTRODUCED_BINDERS {
                break;
            }
            // Lean's loop consumes every binder that is not EXPLICIT — a
            // strict-implicit `⦃x⦄` included, even though one does not trigger
            // the wrap (`elabImplicitLambda`, `TermElabM.lean`:1779-1786).
            if bd.info == BinderInfo::Default {
                break;
            }
            let data = *bd;
            let domain = self
                .metas
                .instantiate_levels(&self.metas.instantiate(domain));
            let codomain = codomain.as_ref().clone();
            let fvar = self.push_local(
                SurfaceName::from_name(Name::anon().str("✝implicit")),
                domain.clone(),
            );
            if let Some((Some(name), _)) = display_names
                .as_ref()
                .and_then(|names| names.get(pushed.len()))
            {
                self.term_local_display_names.insert(
                    fvar,
                    SurfaceName::from_name(Name::anon().str(format!("{name}✝"))),
                );
            }
            // Lean's implicit lambda introduces the local with the binder's
            // own info, which a captured `let rec` keeps.
            self.note_let_rec_binder(fvar, data.info);
            self.locals.set_binder_info(fvar, data);
            let is_local_instance = self.binder_is_local_instance(data.info, &domain);
            if is_local_instance {
                self.push_local_instance(fvar, domain.clone());
            }
            pushed.push(ImplicitBinder {
                data,
                fvar,
                domain,
                is_local_instance,
            });
            let next = codomain.instantiate(&Expr::fvar(fvar));
            ty = self.whnf(
                &self
                    .metas
                    .instantiate_levels(&self.metas.instantiate(&next)),
            );
        }
        (pushed, ty)
    }

    /// Pop the locals `open_implicit_lambda_binders` pushed, innermost first.
    ///
    /// Separate from the abstraction below so it can run on the ERROR path as
    /// well: every caller pops before propagating an elaboration failure.
    fn pop_implicit_lambda_binders(&mut self, pushed: &[ImplicitBinder]) {
        for binder in pushed.iter().rev() {
            self.term_local_display_names.remove(&binder.fvar);
            if binder.is_local_instance {
                self.pop_local_instance();
            }
            self.pop_local();
        }
    }

    /// Abstract the popped locals back over `inner`, innermost first.
    fn abstract_implicit_lambda_binders(
        &mut self,
        pushed: Vec<ImplicitBinder>,
        inner: Expr,
    ) -> Expr {
        // SOUNDNESS: instantiate assigned metavars/levels before abstracting,
        // for the reason `elab_lambda` records at its own abstraction — an
        // assignment mentioning one of these fvars would otherwise leave a
        // loose fvar in the closed lambda.
        let mut result = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&inner));
        for binder in pushed.into_iter().rev() {
            let domain = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&binder.domain));
            let abstracted = result.abstract_fvar(binder.fvar);
            result = Expr::lam(binder.data, domain, abstracted);
        }
        result
    }

    /// The `elab_lambda` half: wrap a `fun` term whose expected type leads with
    /// a non-explicit binder, then hand the surface binder list to
    /// `elab_lambda` against what remains.
    ///
    /// Decided ONCE for the term, never per binder — that is the whole of the
    /// `eq_iff_eq_cancel_left` class. `elab_lambda`'s ordinary path then peels
    /// one `Pi` per surface binder regardless of its binder info, which is
    /// `propagateExpectedType`'s rule.
    pub(super) fn elab_lambda_with_implicit_wrap(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
        expected: &Expr,
    ) -> Result<Expr, ElabError> {
        self.with_implicit_lambda_binders(expected, |this, remaining| {
            this.current_expected_type = Some(remaining);
            this.elab_lambda(binders, body)
        })
    }

    /// Take the implicit-lambda decision at the DEFINITION-BODY entry, then
    /// run `elab` against whatever expected type survives it.
    ///
    /// `elab_def_body` does not route through `elaborate_with_expected_type`
    /// — the chokepoint where this decision is taken for every other term —
    /// and `elaborate`'s own `Lambda` / `PatternMatchLambda` bypasses take it
    /// only for a `fun`. So a NON-`fun` body facing a declared type whose
    /// leading binder is implicit was never wrapped, and
    /// `theorem t : ∀ {a : Nat}, PP a := pp _`, `def d : {α : Type} → Nat := 0`
    /// and `def d : {α : Type} → Nat := base` were all refused where the pinned
    /// v4.30.0-rc2 binary accepts them (Lean's `elabTermEnsuringType` runs the
    /// ordinary `elabTerm` dispatch, `Term/TermElabM.lean`:1806).
    ///
    /// A `fun` is excluded here — `elaborate`'s own bypass already decides it
    /// and that route stays byte-for-byte unchanged.
    pub(super) fn elab_def_value_maybe_implicit_lambda<F>(
        &mut self,
        val: &SurfaceExpr,
        ty_expr: &Expr,
        type_was_written: bool,
        elab: F,
    ) -> Result<Expr, ElabError>
    where
        F: FnOnce(&mut Self, Expr) -> Result<Expr, ElabError>,
    {
        // No written type means no EXPECTED type: Lean introduces implicit
        // lambdas inside `elabTermEnsuringType`, so there is nothing to wrap
        // against, and `ty_expr` here is a metavariable the VALUE solves. See
        // the call site for the `alias` measurement that this restriction is.
        if !type_was_written {
            return elab(self, ty_expr.clone());
        }
        // `elaborate`'s own bypasses decide these two, and those routes are
        // measured green; taking the decision twice would only add a second
        // rule that can drift.
        //
        // The bare `PatternMatchLambda` exclusion is NOT a gap in this
        // decision — measured 2026-09-20. Wrapping it here DOES introduce the
        // binders (the refusal moves to `expected MyL fvar#0 → Nat, got Nat`,
        // naming the introduced `α✝`), and the class still does not close,
        // because what refuses it is `elab_pattern_lambda`'s curried peel, not
        // the wrap. The discriminators are pinned in
        // `tests_implicit_lambda_term`: the ARGUMENT-position and
        // parenthesised spellings of the identical term both pass through this
        // very machinery.
        if matches!(
            val,
            SurfaceExpr::Lambda(..) | SurfaceExpr::PatternMatchLambda(..)
        ) {
            return elab(self, ty_expr.clone());
        }
        // A RECURSIVE definition whose body is a `match`: the implicit
        // lambda is inserted in each alternative instead of around the
        // `match`. The scrutinee cannot mention the inaccessible `✝implicit`
        // locals, so `fun {A} => match n with | p => e` and `match n with | p
        // => fun {A} => e` are the same function; but Clean lowers structural
        // recursion AT the match (where Lean's `brecOn` covers the whole
        // body), so only the second shape keeps `{A}` in the match's motive
        // and makes each induction hypothesis the whole function. Wrapped
        // around the match, `{A}` was a local bound outside it, and the
        // recursion check rightly refused a minor reading it
        // (`structural_recursion_prefix_params::
        // recursive_function_results_insert_implicit_binders_lean_spelling`,
        // `def f (acc n : Nat) : {A : Type} → A → Nat := match n with …`,
        // which Lean accepts).
        if self.recursive_def_ctx.is_some()
            && matches!(Self::unwrap_surface_parens(val), SurfaceExpr::Match(..))
        {
            self.refuse_alternative_binding_wrapped_implicit(val, ty_expr)?;
            return elab(self, ty_expr.clone());
        }
        let instantiated = self
            .metas
            .instantiate_levels(&self.metas.instantiate(ty_expr));
        if !self.use_implicit_lambda(val, &instantiated) {
            return elab(self, ty_expr.clone());
        }
        self.with_implicit_lambda_binders(&instantiated, elab)
    }

    /// Introduce the expected type's leading non-explicit binders, run `elab`
    /// against what remains, and abstract them back — restoring
    /// `current_expected_type` and popping the locals on BOTH paths.
    fn with_implicit_lambda_binders<F>(
        &mut self,
        expected: &Expr,
        elab: F,
    ) -> Result<Expr, ElabError>
    where
        F: FnOnce(&mut Self, Expr) -> Result<Expr, ElabError>,
    {
        stack_safe(|| {
            let prev_expected = self.current_expected_type.clone();
            let (pushed, remaining) = self.open_implicit_lambda_binders(expected);
            let inner = elab(self, remaining);
            self.current_expected_type = prev_expected;
            self.pop_implicit_lambda_binders(&pushed);
            let inner = inner?;
            Ok(self.abstract_implicit_lambda_binders(pushed, inner))
        })
    }
}
