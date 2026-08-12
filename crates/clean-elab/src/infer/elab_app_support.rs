// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Application elaboration support: bidirectional type checking, named argument
//! resolution, and Nat-to-Real coercion retry.
//!
//! Split from `elab_app.rs` (#307). These methods are called from the core
//! application elaboration loop but are self-contained algorithms.

use super::*;
use crate::stack_safe;

impl<'a> ElabCtx<'a> {
    /// Check if a binder info requires implicit argument insertion
    pub(in crate::infer) fn is_implicit_binder(bi: impl Into<BinderData>) -> bool {
        let info = bi.into().info;
        matches!(
            info,
            BinderInfo::Implicit | BinderInfo::StrictImplicit | BinderInfo::InstImplicit
        )
    }

    /// Count the number of explicit (non-implicit) binders in a function type.
    /// This is used to decide whether user-provided args should fill implicit slots.
    pub(in crate::infer) fn count_explicit_binders(ty: &Expr) -> usize {
        let mut count = 0;
        let mut current = ty.clone();
        while let ExprKind::Pi(bi, _, body) = current.kind() {
            if !Self::is_implicit_binder(*bi) {
                count += 1;
            }
            current = body.as_ref().clone();
        }
        count
    }

    /// If `ty` is an explicit `optParam α default` parameter type, return its
    /// default value (the second argument of the `optParam` application).
    ///
    /// In Lean a parameter with a default value `(x : α := v)` is encoded in the
    /// kernel/`.olean` as a parameter whose *type* is literally
    /// `optParam α v` where
    /// `@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α`.
    /// When an explicit argument at that position is omitted, the elaborator
    /// supplies `v`. We detect the `optParam` head structurally (head constant
    /// named `optParam`, applied to exactly the carrier and the default) so the
    /// behavior fires for *imported* declarations that ship no clean-side
    /// default-argument metadata — only the raw `optParam` parameter type.
    ///
    /// `autoParam α tac` (tactic-synthesized defaults) is intentionally *not*
    /// handled here: filling it requires running the named tactic, which the
    /// elaborator does not yet drive at application sites. Returning `None` for
    /// `autoParam` leaves such a parameter unfilled (the existing behavior).
    pub(in crate::infer) fn opt_param_default(ty: &Expr) -> Option<Expr> {
        let head = ty.get_app_fn();
        let ExprKind::Const(name, _) = head.kind() else {
            return None;
        };
        if name.last_component().as_deref() != Some("optParam") {
            return None;
        }
        // `optParam` takes exactly two arguments: the carrier and the default.
        let args: Vec<&Expr> = ty.get_app_args().into_iter().collect();
        if args.len() != 2 {
            return None;
        }
        Some(args[1].clone())
    }

    /// Insert default values for any leading *explicit* `optParam` parameters in
    /// `val`'s type that have no further argument to fill them.
    ///
    /// Returns the (possibly extended) value together with its remaining type.
    /// Walks the Pi telescope of `val`'s type, and for each leading explicit
    /// binder whose domain is `optParam α default`, applies `val` to `default`
    /// and continues. Stops at the first binder that is implicit (those are
    /// handled by [`Self::insert_implicit_args`]) or whose domain is not an
    /// `optParam`. This mirrors Lean 4's default-argument insertion in
    /// `elabApp`, and crucially keys off the raw `optParam` parameter type so it
    /// works for imported declarations with no clean-side metadata.
    pub(in crate::infer) fn insert_opt_param_defaults(
        &mut self,
        val: Expr,
        val_type: &Expr,
    ) -> (Expr, Expr) {
        let mut result = val;
        let mut ty = self.whnf(&self.metas.instantiate(val_type));
        while let ExprKind::Pi(bi, arg_ty, body_ty) = ty.kind() {
            // Implicit binders are not default-argument positions, and a
            // non-`optParam` explicit binder is a genuinely required argument.
            if Self::is_implicit_binder(*bi) {
                break;
            }
            let arg_ty_inst = self.metas.instantiate(arg_ty);
            let Some(default) = Self::opt_param_default(&arg_ty_inst) else {
                break;
            };
            result = Expr::app(result, default.clone());
            ty = self.whnf(&self.metas.instantiate(&body_ty.instantiate(&default)));
        }
        (result, ty)
    }

    /// Apply a value to implicit arguments to match an expected type.
    ///
    /// This implements bidirectional type checking: when we have an expected type
    /// and the value's type is a function with implicit arguments, we apply the
    /// value to those arguments to get a value of the expected type.
    ///
    /// For example, `sorry : {α : Sort u} → α` with expected type `Nat`:
    /// - Infer type of sorry: `{α : Sort u} → α`
    /// - Apply sorry to Nat: `sorry Nat : Nat`
    ///
    /// This is essential for theorem/definition bodies where the value is a
    /// polymorphic constant like `sorry` that needs to be instantiated at
    /// the expected type.
    ///
    /// # Contract
    ///
    /// ENSURES: Result has all solved metavariables instantiated
    /// ENSURES: Result has all solved level constraints substituted (instantiate_levels applied)
    /// Whether `ty1` already satisfies `ty2` closely enough that
    /// [`Self::apply_implicit_to_expected_type`] should stop consuming
    /// leading implicit binders / accept a computed instantiation as-is.
    ///
    /// Trust: a raw `unifier.unify(ty1, ty2)` success is NOT sufficient for
    /// this decision. Pi/Lam unification deliberately ignores `BinderInfo`
    /// now (Brick P1, `unify/unifier/unify_expr.rs` + `unify_ext.rs` —
    /// Lean's `isDefEq` and Clean's own kernel defeq never compare binder
    /// info either), so it can structurally unify `ty1`'s LEADING
    /// IMPLICIT-class Pi telescope directly against an unrelated
    /// EXPLICIT-binder (or otherwise mismatched) `ty2` — e.g. importing
    /// `Except.ok : {ε:Type u1} → {α:Type u2} → α → Except ε α` as the bare
    /// `f` argument of `congrArg : {α:Sort u} → {β:Sort v} → (f : α → β) →
    /// …`. Before Brick P1, `unify(Pi(Implicit,ε,_), Pi(Default,_,_))`
    /// hard-failed on the outer binder-info mismatch, forcing every one of
    /// this function's call sites to fall through and properly insert fresh
    /// metavariables for `ε`/`α`. Now it structurally unifies straight
    /// through — pinning congrArg's OWN fresh `α`/`β` to Except.ok's
    /// *implicit parameter types* instead of to `Int`/`Except SemError Int`
    /// — which produced a bogus TYPE-valued `Eq` and "level mismatch: Zero
    /// vs Succ(u)" (the trust-ir bridge PRELUDE_SRC regression, `congrArg
    /// Except.ok (wrap_eq_self …)`).
    ///
    /// Lean itself only keeps a value polymorphic when the expected type is
    /// *also* headed by a matching implicit-class Pi (e.g. assigning one
    /// still-polymorphic value to an implicit-Pi-typed slot) — so restore
    /// that binder-info-sensitive gate here, for every "is this already a
    /// match" decision in this file, without reintroducing binder-info
    /// comparison into the general Pi/Lam unifier (which must stay
    /// Lean/kernel-parity for Brick P1's own higher-kinded-head cases). Only
    /// the outermost, already-fully-formed Pi shapes are compared — an
    /// unresolved expected-type metavariable (whnf leaves it opaque, not a
    /// Pi) is untouched, so the pre-existing Miller-pattern "keep
    /// polymorphic when expected is open" behavior is unaffected. Returns
    /// the full [`UnifyResult`] (not just success/fail) so callers that
    /// branch on `Stuck` vs `Failure` keep that distinction: a detected
    /// mismatch reports `Failure`, exactly what the pre-Brick-P1 unifier
    /// itself returned for a binder-info-mismatched Pi/Pi comparison.
    fn direct_type_match(&mut self, ty1: &Expr, ty2: &Expr) -> UnifyResult {
        let binder_info_mismatch = matches!(
            (self.whnf(ty1).kind(), self.whnf(&self.metas.instantiate(ty2)).kind()),
            (ExprKind::Pi(bi1, _, _), ExprKind::Pi(bi2, _, _)) if bi1 != bi2
        );
        if binder_info_mismatch {
            return UnifyResult::Failure(
                "binder info mismatch (implicit-arg insertion gate)".to_string(),
            );
        }
        let ctx = self.build_local_ctx();
        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
        unifier.unify(ty1, ty2)
    }

    pub(in crate::infer) fn apply_implicit_to_expected_type(
        &mut self,
        val: &Expr,
        expected_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            // Infer type of the value; failures must propagate so callers do not accept
            // ill-typed terms as if elaboration succeeded.
            let val_ty = self.infer_type(val)?;

            // Nested-aux → container pre-coercion (Track U). When the value's
            // type is a bare nested-inductive aux mirror (`Value._List`) and the
            // expected slot is still an *open metavar* (`?α`) — the shape of a
            // type-class type-param the operands are supposed to pin, e.g. the
            // `?α` of `HAppend ?α ?β ?γ` for `xs ++ ys` over `.sequence`-bound
            // lists — the direct unify below would pin `?α := Value._List`. No
            // `HAppend Value._List …` / `Append Value._List` instance exists, so
            // instance resolution then leaves the instance metavar unsolved and
            // the assembled term leaks a free variable. Coerce the value to its
            // real container (`@Value._List.toContainer val : List Value`) first
            // so the open slot pins to `List Value` and the ordinary `List`
            // instances resolve. The coercion's own def-eq guard unifies its
            // `List Value` codomain with the open `?α`, pinning it. SOUNDNESS: the
            // produced term is the kernel-checked `toContainer` conversion; if the
            // expected slot is not an open metavar (a concrete aux-typed position,
            // e.g. a constructor field that genuinely wants `Value._List`) the
            // guard below is skipped and the prior direct-match behavior is kept
            // verbatim.
            {
                let val_ty_w = self.whnf(&self.metas.instantiate(&val_ty));
                let expected_inst = self.metas.instantiate(expected_ty);
                let expected_is_open_meta = matches!(
                    expected_inst.kind(),
                    ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some()
                );
                if expected_is_open_meta && matches!(val_ty_w.kind(), ExprKind::Const(_, _)) {
                    if let Some(coerced) =
                        self.try_coerce_nested_aux_to_container(val, &val_ty_w, &expected_inst)
                    {
                        let result = self.metas.instantiate(&coerced);
                        return Ok(self.metas.instantiate_levels(&result));
                    }
                }
            }

            // Bare polymorphic constant against an OPEN expected metavariable
            // (B06, sweep row classes_instances/p20): for `some Zz.z` the
            // argument `Zz.z : {α : Type} → [Zz α] → α` is elaborated against
            // the element-type metavar `?β`. The direct match below would
            // happily assign `?β := {α} → [Zz α] → α` — the RAW projection
            // type — instead of inserting the implicit/instance arguments.
            // Lean inserts implicit args for an identifier in non-`@` position
            // and only then unifies with the expected type (lean4
            // `src/Lean/Elab/App.lean`, `elabAppArgs` with no explicit args).
            // Try the deferred-insertion path first: insert `{α}`/`[inst]`
            // metavariables, unify the RESULT type with the expected metavar,
            // then resolve the deferred instance goals. Fully speculative: on
            // any failure the scope is popped and the legacy direct-match
            // behavior is preserved verbatim (and the kernel re-checks
            // whatever term is produced, so this can never accept more).
            if !self.explicit_mode {
                let expected_inst = self.metas.instantiate(expected_ty);
                let expected_is_open_meta = matches!(
                    expected_inst.kind(),
                    ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some()
                );
                let val_ty_whnf = self.whnf(&val_ty);
                let leads_with_implicit = matches!(
                    val_ty_whnf.kind(),
                    ExprKind::Pi(bi, _, _) if Self::is_implicit_binder(*bi)
                );
                if expected_is_open_meta && leads_with_implicit {
                    self.metas.push_scope();
                    let (inserted, inserted_ty, pending) =
                        self.insert_implicit_args_deferring_instances(val.clone(), &val_ty_whnf);
                    let unified = {
                        let inserted_ty_whnf = self.whnf(&self.metas.instantiate(&inserted_ty));
                        let ctx = self.build_local_ctx();
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        matches!(
                            unifier.unify(&inserted_ty_whnf, &expected_inst),
                            UnifyResult::Success
                        )
                    };
                    if unified && self.resolve_deferred_instances(&pending) {
                        self.metas.commit();
                        let result = self.metas.instantiate(&inserted);
                        return Ok(self.metas.instantiate_levels(&result));
                    }
                    self.metas.pop_scope();
                }
            }

            // Avoid consuming leading implicits when the value already
            // matches the expected type. See `direct_type_match` for why
            // this can no longer be a raw `unify()` call.
            let direct_match = matches!(
                self.direct_type_match(&val_ty, expected_ty),
                UnifyResult::Success
            );
            if direct_match {
                let result = self.metas.instantiate(val);
                return Ok(self.metas.instantiate_levels(&result));
            }

            // Default-argument (`optParam`) insertion: when the value's type
            // begins with an explicit `optParam α default` parameter and the
            // expected type is the result *after* those parameters, supply the
            // defaults. This fires for imported declarations whose parameter
            // type is literally `optParam …` and which ship no clean-side
            // default metadata. Attempt speculatively so an unrelated mismatch
            // leaves no partial state behind for the implicit-insertion lane.
            {
                let val_ty_whnf = self.whnf(&val_ty);
                let leads_with_opt_param = matches!(
                    val_ty_whnf.kind(),
                    ExprKind::Pi(bi, arg_ty, _)
                        if !Self::is_implicit_binder(*bi)
                            && Self::opt_param_default(&self.metas.instantiate(arg_ty)).is_some()
                );
                if leads_with_opt_param {
                    self.metas.push_scope();
                    let (defaulted, defaulted_ty) =
                        self.insert_opt_param_defaults(val.clone(), &val_ty_whnf);
                    // After supplying defaults the remaining type may still carry
                    // leading implicits (e.g. an `optParam` before an instance
                    // binder); reuse the implicit/expected-type machinery to close
                    // the gap and unify with the expected type.
                    let matched = {
                        let defaulted_ty_whnf = self.whnf(&self.metas.instantiate(&defaulted_ty));
                        matches!(
                            self.direct_type_match(&defaulted_ty_whnf, expected_ty),
                            UnifyResult::Success
                        )
                    };
                    if matched {
                        self.metas.commit();
                        let result = self.metas.instantiate(&defaulted);
                        return Ok(self.metas.instantiate_levels(&result));
                    }
                    // Defaults did not by themselves reach the expected type; let
                    // the recursive call handle any remaining implicit binders.
                    let still_pi = matches!(defaulted_ty.kind(), ExprKind::Pi(..));
                    if still_pi {
                        self.metas.commit();
                        let defaulted = self.metas.instantiate(&defaulted);
                        return self.apply_implicit_to_expected_type(&defaulted, expected_ty);
                    }
                    self.metas.pop_scope();
                }
            }

            // Check if value type is a function with implicit arguments
            let val_ty_whnf = self.whnf(&val_ty);
            match val_ty_whnf.kind() {
                ExprKind::Pi(bi, arg_ty, body_ty) if Self::is_implicit_binder(*bi) => {
                    // Check if the argument type is a Sort (type parameter)
                    // This catches `sorry : {α : Sort u} → α` pattern
                    let arg_ty_whnf = self.whnf(&self.metas.instantiate(arg_ty));

                    let is_type_arg = matches!(arg_ty_whnf.kind(), ExprKind::Sort(_));

                    if is_type_arg {
                        // Check if the body type is just BVar(0) (the implicit IS the return type)
                        // e.g., sorry : {α : Sort u} → α has body = BVar(0)
                        // For these cases, we can directly apply expected_ty as the argument
                        //
                        // For types like MyOption.none : {α : Type} → MyOption α,
                        // body = App(MyOption, BVar(0)), so we can't directly apply expected_ty.
                        // Instead, use a metavariable and let unification solve it.
                        let body_is_direct_return = matches!(body_ty.kind(), ExprKind::BVar(0));

                        // Issue #169 (gated on body_is_direct_return): pin the domain level only
                        // when the implicit type-arg IS the return type (`sorry : {α} → α`). For
                        // `rfl`/`Eq.refl` the expected type is the Eq *proposition* (Sort 0), so
                        // pinning u := 0 is wrong and poisons the later `Eq.{u}` unification —
                        // leave it for the final return-type unification to solve from the value.
                        if body_is_direct_return {
                            if let ExprKind::Sort(domain_level) = arg_ty_whnf.kind() {
                                if let Ok(expected_ty_ty) = self.infer_type(expected_ty) {
                                    let expected_ty_ty_whnf = self.whnf(&expected_ty_ty);
                                    if let ExprKind::Sort(actual_level) = expected_ty_ty_whnf.kind()
                                    {
                                        let ctx = self.build_local_ctx();
                                        let mut u =
                                            Unifier::with_env(&mut self.metas, self.env, ctx);
                                        let _ = u.unify(
                                            &Expr::sort(domain_level.clone()),
                                            &Expr::sort(actual_level.clone()),
                                        );
                                    }
                                }
                            }
                        }

                        if body_is_direct_return {
                            // Direct return case: apply the value to the expected type
                            let result = Expr::app(val.clone(), expected_ty.clone());

                            // The body type should now be `expected_ty` after instantiation
                            let result_ty = body_ty.instantiate(expected_ty);
                            let result_ty_whnf = self.whnf(&self.metas.instantiate(&result_ty));

                            // Unify the result type with the expected type
                            let unify_result = self.direct_type_match(&result_ty_whnf, expected_ty);
                            match unify_result {
                                UnifyResult::Success => {
                                    // Check if there are more implicit args to handle
                                    // (consistent with the #252 fix in the else branch)
                                    let result_ty = self.metas.instantiate(&result_ty);
                                    let result_ty_whnf = self.whnf(&result_ty);
                                    if matches!(result_ty_whnf.kind(), ExprKind::Pi(bi, _, _) if Self::is_implicit_binder(*bi))
                                    {
                                        // More implicits - recurse
                                        self.apply_implicit_to_expected_type(&result, expected_ty)
                                    } else {
                                        // Apply level instantiation before returning
                                        let result = self.metas.instantiate(&result);
                                        Ok(self.metas.instantiate_levels(&result))
                                    }
                                }
                                UnifyResult::Stuck => {
                                    // Stuck means unification could not determine correctness.
                                    // Treat as error for soundness, consistent with elab_app_inner.
                                    Err(ElabError::CannotInfer)
                                }
                                UnifyResult::Failure(_) => {
                                    // Unification failed - maybe there are more implicit args
                                    // Recursively apply to handle nested implicits
                                    self.apply_implicit_to_expected_type(&result, expected_ty)
                                }
                            }
                        } else {
                            // Issue #252: Type parameter case (e.g., MyOption.none)
                            // Use metavariable and unification to solve the type parameter
                            let meta = self.fresh_meta(arg_ty_whnf.clone());
                            let result = Expr::app(val.clone(), meta.clone());
                            let result_ty = body_ty.instantiate(&meta);
                            let result_ty_whnf = self.whnf(&self.metas.instantiate(&result_ty));

                            // Unify to solve the metavariable
                            let unify_result = self.direct_type_match(&result_ty_whnf, expected_ty);
                            match unify_result {
                                UnifyResult::Success => {
                                    // Instantiate the result with solved metavariables
                                    let result = self.metas.instantiate(&result);
                                    // Check if there are more implicit args to handle
                                    let result_ty = self.metas.instantiate(&result_ty);
                                    let result_ty_whnf = self.whnf(&result_ty);
                                    if matches!(result_ty_whnf.kind(), ExprKind::Pi(bi, _, _) if Self::is_implicit_binder(*bi))
                                    {
                                        // More implicits - recurse
                                        self.apply_implicit_to_expected_type(&result, expected_ty)
                                    } else {
                                        // Apply level instantiation before returning
                                        Ok(self.metas.instantiate_levels(&result))
                                    }
                                }
                                UnifyResult::Stuck => {
                                    // Stuck means unification could not determine correctness.
                                    // Treat as error for soundness, consistent with elab_app_inner.
                                    Err(ElabError::CannotInfer)
                                }
                                UnifyResult::Failure(_) => {
                                    // Unification failed - try recursive handling
                                    let result = self.metas.instantiate(&result);
                                    self.apply_implicit_to_expected_type(&result, expected_ty)
                                }
                            }
                        }
                    } else {
                        // Not a type argument (e.g., `m : Type → Type` in StateT.get).
                        // Insert metavariables for all remaining implicit arguments,
                        // then unify the result type with the expected type to solve
                        // both the metavariables and any universe level constraints.
                        //
                        // Without this unification, universe params like u_13 in
                        // `StateT.get.{u_9, u_13}` remain unsolved when the expected
                        // type comes from an abbrev like `MySem MyState` that reduces
                        // to `StateT.{0, 0} MyState (Except.{0} MyError) MyState`.
                        // Part of #3396.
                        //
                        // Defer instance-implicit binders so the expected type pins
                        // any carrier metavariables *before* typeclass resolution
                        // runs. For a class method like
                        // `Pick.chosen : {α} → [Pick α] → α`, eager resolution would
                        // resolve `[Pick ?α]` against an unconstrained `?α` and grab
                        // whichever `Pick` instance is registered first; unifying the
                        // result type `?α` with the expected type first solves
                        // `?α := <carrier>` so the correct instance is selected. This
                        // matches Lean 4's postponement of typeclass resolution.
                        let expected_whnf = self.whnf(&self.metas.instantiate(expected_ty));

                        // Try the deferred path in a speculative scope so a failure to
                        // resolve every instance this way leaves no partial metavariable
                        // assignments behind for the eager fallback.
                        self.metas.push_scope();
                        let (deferred_result, deferred_ty, pending) = self
                            .insert_implicit_args_deferring_instances(val.clone(), &val_ty_whnf);
                        let deferred_ty_whnf = self.whnf(&self.metas.instantiate(&deferred_ty));
                        {
                            let ctx = self.build_local_ctx();
                            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                            let _ = unifier.unify(&deferred_ty_whnf, &expected_whnf);
                        }
                        if self.resolve_deferred_instances(&pending) {
                            self.metas.commit();
                            let result = self.metas.instantiate(&deferred_result);
                            return Ok(self.metas.instantiate_levels(&result));
                        }
                        self.metas.pop_scope();

                        // Fall back to eager insertion so behavior is never worse than
                        // before this refinement (the original #3396 path).
                        let (result, result_ty) =
                            self.insert_implicit_args(val.clone(), &val_ty_whnf);
                        let result_ty_inst = self.metas.instantiate(&result_ty);
                        let result_ty_whnf = self.whnf(&result_ty_inst);
                        {
                            let ctx = self.build_local_ctx();
                            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                            let _ = unifier.unify(&result_ty_whnf, &expected_whnf);
                        }
                        let result = self.metas.instantiate(&result);
                        Ok(self.metas.instantiate_levels(&result))
                    }
                }
                _ => {
                    // Val's type does not lead with an implicit binder, so there
                    // is nothing to *insert*. But the type may still carry
                    // unsolved metavariables that only the expected type can pin
                    // — e.g. `MonadExcept.throw e` elaborates to
                    // `@throw ?ε ?m ?α e` whose type is the application
                    // `?m ?α` (the explicit arg `e` solved only `?ε`). The
                    // higher-order carrier `?m` and result `?α` are determined by
                    // the expected codomain (`StateT MyState (Except MyError) α`).
                    // Without unifying here, `?m`/`?α` leak to the kernel as free
                    // variables ("contains free variables"). Mirror the
                    // expected-type unification the constructor / `Option.some`
                    // path already performs (elab_app.rs:146 and :308) so the
                    // metavars get solved. The kernel re-checks the instantiated
                    // term, so this only fills metavars the expected type already
                    // forces — it cannot weaken the kernel check. Unify
                    // speculatively so an unrelated mismatch leaves the prior
                    // (unchanged-return) behavior intact.
                    // Unify against the *folded* expected type. When the val type
                    // is a flex application `?m ?α` (head is an unsolved metavar —
                    // e.g. the carrier monad of `MonadExcept.throw`), the eager
                    // leading WHNF in the ordinary `unify` would unfold the rigid
                    // expected `StateT σ (Except ε) α` into its `Pi` body, giving
                    // `App(?m, ?α) =?= Pi(...)` — a shape mismatch that leaves
                    // `?m`/`?α` unsolved (they then leak to the kernel as free
                    // variables). `unify_no_initial_whnf` keeps the folded
                    // application so the structural App rule pairs `?m` with the
                    // partial application and `?α` with the final argument. The
                    // kernel re-checks the instantiated term, so this only fills
                    // metavars the expected type already determines.
                    let val_ty_inst = self.metas.instantiate(&val_ty);
                    let expected_inst = self.metas.instantiate(expected_ty);
                    {
                        let ctx = self.build_local_ctx();
                        let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                        let _ = unifier.unify_no_initial_whnf(&val_ty_inst, &expected_inst);
                    }
                    // Apply level instantiation to ensure any solved level constraints are substituted
                    let result = self.metas.instantiate(val);
                    Ok(self.metas.instantiate_levels(&result))
                }
            }
        })
    }

    /// When an expected type is present, allow user-provided arguments to fill
    /// leading implicit binders if they elaborate cleanly at those binder types.
    ///
    /// This covers recursor-style applications like `PEmpty.rec (fun _ => Nat)`,
    /// where the surface argument targets an implicit motive binder.
    /// For recursor constants, also try this without an expected type because
    /// motives are commonly supplied explicitly despite being implicit (#796).
    pub(in crate::infer) fn try_consume_leading_implicit_args(
        &mut self,
        func_expr: Expr,
        func_type: Expr,
        args: &[SurfaceArg],
    ) -> Result<(Expr, Expr, usize), ElabError> {
        if self.explicit_mode {
            return Ok((func_expr, func_type, 0));
        }

        // With an expected type, always try consumption. Without one, only try
        // for recursor constants whose leading implicit is the motive.
        if self.current_expected_type.is_none() {
            let is_recursor = match func_expr.kind() {
                ExprKind::Const(name, _) => self.env.get_recursor(name).is_some(),
                _ => false,
            };
            if !is_recursor {
                return Ok((func_expr, func_type, 0));
            }
        }

        let mut result = func_expr;
        let mut current_type = self.whnf(&func_type);
        let mut consumed = 0;

        while let Some(arg) = args.get(consumed) {
            let (arg_ty, body_ty) = match current_type.kind() {
                ExprKind::Pi(bi, arg_ty, body_ty) if Self::is_implicit_binder(*bi) => {
                    (arg_ty.as_ref().clone(), body_ty.as_ref().clone())
                }
                _ => break,
            };

            let expected_arg_ty = self.metas.instantiate(&arg_ty);
            // Ordinary sort-valued type parameters such as `{α : Type u}` in
            // `List.cons` should stay in the implicit-insertion lane.
            let expected_arg_ty_whnf = self.whnf(&expected_arg_ty);
            if matches!(expected_arg_ty_whnf.kind(), ExprKind::Sort(_)) {
                break;
            }
            self.metas.push_scope();
            let attempt: Result<Expr, ElabError> = (|| {
                let arg_expr =
                    self.elaborate_with_expected_type(&arg.expr, Some(expected_arg_ty.clone()))?;
                self.enforce_expr_type(&arg_expr, &expected_arg_ty)?;
                Ok(arg_expr)
            })();

            match attempt {
                Ok(arg_expr) => {
                    self.metas.commit();
                    let arg_expr = self.metas.instantiate(&arg_expr);
                    let arg_expr = self.metas.instantiate_levels(&arg_expr);
                    result = Expr::app(result, arg_expr.clone());
                    current_type =
                        self.whnf(&self.metas.instantiate(&body_ty.instantiate(&arg_expr)));
                    consumed += 1;
                }
                Err(_) => {
                    self.metas.pop_scope();
                    break;
                }
            }
        }

        Ok((result, current_type, consumed))
    }

    /// Resolve named arguments by reordering them to match parameter positions
    /// (#1230, rebuilt for B01 — GAP_SWEEP_2026-07-09).
    ///
    /// Lean ground truth (lean4 `src/Lean/Elab/App.lean`, `ElabAppArgs`):
    /// a named argument binds the binder with that exact name — searching the
    /// remaining explicit AND implicit binders — and the positional arguments
    /// fill the remaining *explicit* binders in order. Unknown names and
    /// double-filled binders are hard errors.
    ///
    /// Binder names come from, in order:
    /// 1. the environment's parameter-name registry (surface `def`/`theorem`/
    ///    `axiom`/`opaque` declarations, registered with binder kinds), or
    /// 2. for a constructor, the parent inductive's structure-field table
    ///    (`num_params` unnamed parameter slots followed by the named fields),
    ///    with binder kinds read off the constructor's declared Pi telescope.
    ///
    /// When neither source knows the head's binder names the call FAILS LOUDLY
    /// ([`ElabError::NamedArgBindingFailed`]). The pre-B01 fallback silently
    /// bound named arguments positionally, which certified swapped structure
    /// fields (`Point.mk (y := 2) (x := 1)` elaborated as `Point.mk 2 1`).
    ///
    /// Descoped LOUD (never silent): Lean additionally eta-expands earlier
    /// unfilled explicit binders into a lambda (`f (y := 2)` becomes
    /// `fun x => f x 2`); Clean fills such slots with `_` holes, so a hole the
    /// later elaboration cannot solve fails the declaration instead of
    /// abstracting over it.
    pub(in crate::infer) fn resolve_named_args(
        &self,
        func_expr: &Expr,
        args: &[SurfaceArg],
    ) -> Result<Vec<SurfaceArg>, ElabError> {
        let named_arg_err = |name: &str, reason: String| ElabError::NamedArgBindingFailed {
            func: match func_expr.kind() {
                ExprKind::Const(n, _) => n.to_string(),
                _ => "<non-constant function head>".to_string(),
            },
            name: name.to_string(),
            reason,
        };
        // The caller only routes here when at least one arg is named.
        let first_named = args
            .iter()
            .find_map(|a| a.name.as_deref())
            .unwrap_or("<unnamed>");

        // Extract the function name to look up parameter names.
        let func_name = match func_expr.kind() {
            ExprKind::Const(name, _) => name.clone(),
            _ => {
                // Named args on a non-constant head (fvar/lambda/projection):
                // binder names are not recorded for these. LOUD descope —
                // never bind a named argument positionally.
                return Err(named_arg_err(
                    first_named,
                    "named arguments require a function head whose binder names \
                     are known (a declared constant or a constructor)"
                        .to_string(),
                ));
            }
        };

        // Binder slots in declaration order: (name if known, kind if known).
        let slots: Vec<(Option<String>, Option<BinderInfo>)> =
            if let Some(param_names) = self.env.get_param_names(&func_name) {
                // Kinds are recorded by `set_param_infos` (surface decls). A
                // names-only legacy registration has no kinds row; treat every
                // slot as explicit — exactly the pre-B01 positional-fill behavior.
                let kinds = self.env.get_param_binder_infos(&func_name);
                param_names
                    .iter()
                    .enumerate()
                    .map(|(i, n)| {
                        (
                            Some(n.clone()),
                            kinds
                                .and_then(|k| k.get(i).copied())
                                .or(Some(BinderInfo::Default)),
                        )
                    })
                    .collect()
            } else if let Some(ctor) = self.env.get_constructor(&func_name) {
                // Constructor: `num_params` leading parameter slots (unnamed —
                // only reachable as holes) followed by `num_fields` field slots
                // named by the structure-field table. Binder kinds are read off
                // the constructor's declared type telescope, which lists exactly
                // params-then-fields (kernel `ConstructorVal`).
                let num_params = ctor.num_params as usize;
                let num_fields = ctor.num_fields as usize;
                let field_names = self
                    .env
                    .get_structure_field_names(&ctor.inductive_name)
                    .filter(|f| f.len() == num_fields)
                    .ok_or_else(|| {
                        named_arg_err(
                            first_named,
                            format!(
                                "constructor `{func_name}` has no recorded field names \
                             (non-structure inductive constructors are a LOUD descope; \
                             pass the arguments positionally)"
                            ),
                        )
                    })?;
                let kinds = Self::pi_telescope_binder_infos(&ctor.type_, num_params + num_fields);
                (0..num_params + num_fields)
                    .map(|i| {
                        let name = i
                            .checked_sub(num_params)
                            .map(|fi| field_names[fi].to_string());
                        (name, kinds.get(i).copied())
                    })
                    .collect()
            } else if let Some(rec) = self.env.get_recursor(&func_name).cloned() {
                // Recursor / casesOn family: derive binder names from the
                // recursor layout, exactly as Lean names them — inductive
                // params (unnamed holes), `motive` (or `motive_1..motive_n`
                // for a mutual block), one minor per constructor named by the
                // constructor's SHORT name (Lean: `Nat.rec (motive := M)
                // (zero := z) (succ := s) t`), indices (unnamed), and the
                // major premise `t`. Slot ORDER follows the recursor's declared
                // `arg_order` (mirrors the top-level lowering and
                // `wrap_with_nested_ctor_caseson`): `MajorAfterMotive`
                // (casesOn) = params, motives, indices, major, minors;
                // `MajorAfterMinors` (rec) = params, motives, minors, indices,
                // major. Binder kinds are read off the recursor's stored Pi
                // telescope, so an implicit `motive` stays implicit. This arm
                // only fires where the call previously failed LOUD
                // (NamedArgBindingFailed) — pure widening, no behavior change
                // for any head that already resolved.
                let np = rec.num_params as usize;
                let nm = rec.num_motives as usize;
                let nmin = rec.num_minors as usize;
                let nidx = rec.num_indices as usize;
                let total = np + nm + nmin + nidx + 1;

                let mut names: Vec<Option<String>> = Vec::with_capacity(total);
                names.extend(std::iter::repeat_with(|| None).take(np));
                if nm == 1 {
                    names.push(Some("motive".to_string()));
                } else {
                    names.extend((1..=nm).map(|i| Some(format!("motive_{i}"))));
                }
                let minor_names = (0..nmin).map(|i| {
                    rec.rules.get(i).map(|r| {
                        let full = r.constructor_name.to_string();
                        full.rsplit('.').next().unwrap_or(&full).to_string()
                    })
                });
                match rec.arg_order {
                    clean_kernel::RecursorArgOrder::MajorAfterMotive => {
                        names.extend(std::iter::repeat_with(|| None).take(nidx));
                        names.push(Some("t".to_string()));
                        names.extend(minor_names);
                    }
                    clean_kernel::RecursorArgOrder::MajorAfterMinors => {
                        names.extend(minor_names);
                        names.extend(std::iter::repeat_with(|| None).take(nidx));
                        names.push(Some("t".to_string()));
                    }
                }
                let kinds = Self::pi_telescope_binder_infos(&rec.type_, total);
                names
                    .into_iter()
                    .enumerate()
                    .map(|(i, n)| (n, kinds.get(i).copied()))
                    .collect()
            } else {
                return Err(named_arg_err(
                    first_named,
                    format!(
                        "no binder names are recorded for `{func_name}` \
                     (LOUD descope; pass the arguments positionally)"
                    ),
                ));
            };

        // Place named args into the binder slot with that exact name (first
        // unfilled match, explicit or implicit); queue positional args.
        let mut positioned: Vec<Option<SurfaceArg>> = vec![None; slots.len()];
        let mut positional_queue: Vec<&SurfaceArg> = Vec::new();

        for arg in args {
            if let Some(ref name) = arg.name {
                let pos = slots
                    .iter()
                    .enumerate()
                    .position(|(i, (n, _))| n.as_deref() == Some(name) && positioned[i].is_none());
                match pos {
                    Some(pos) => {
                        positioned[pos] = Some(SurfaceArg::positional(arg.expr.clone()));
                    }
                    None if slots
                        .iter()
                        .any(|(n, _)| n.as_deref() == Some(name.as_str())) =>
                    {
                        return Err(named_arg_err(
                            name,
                            "binder already bound by an earlier named argument".to_string(),
                        ));
                    }
                    None => {
                        let known: Vec<&str> =
                            slots.iter().filter_map(|(n, _)| n.as_deref()).collect();
                        return Err(named_arg_err(
                            name,
                            format!("unknown named argument; known: {}", known.join(", ")),
                        ));
                    }
                }
            } else {
                positional_queue.push(arg);
            }
        }

        // Positional args fill the remaining EXPLICIT binders in order (Lean
        // `ElabAppArgs`). Slots with unknown kind are treated as explicit.
        // Under `@` every binder is consumed positionally, so positionals fill
        // ANY unfilled slot in declaration order (`@two Nat 1 (B := Nat) 2`).
        let mut pos_iter = positional_queue.into_iter();
        for (i, slot) in positioned.iter_mut().enumerate() {
            let explicit =
                self.explicit_mode || matches!(slots[i].1, Some(BinderInfo::Default) | None);
            if slot.is_none() && explicit {
                if let Some(arg) = pos_iter.next() {
                    *slot = Some(arg.clone());
                }
            }
        }

        // Build final arg list: only include slots up to the last provided arg.
        // Trailing None slots (unprovided params) are omitted.
        let mut result = Vec::new();
        let last_filled = positioned.iter().rposition(|s| s.is_some());
        if let Some(last) = last_filled {
            for slot in positioned.into_iter().take(last + 1) {
                result.push(slot.unwrap_or_else(|| {
                    // Create a hole expression for skipped parameters
                    SurfaceArg::positional(SurfaceExpr::Hole(clean_parser::Span::dummy()))
                }));
            }
        }

        // Append remaining positional args beyond the named param range
        for arg in pos_iter {
            result.push(arg.clone());
        }

        Ok(result)
    }

    /// Binder kinds of the leading `limit` Pi binders of a declared type.
    ///
    /// Purely syntactic walk (no reduction): kernel constructor types are
    /// stored as explicit Pi telescopes of params-then-fields, so the walk is
    /// exact for the B01 constructor lane. Returns fewer entries when the
    /// telescope is shorter than `limit`.
    fn pi_telescope_binder_infos(ty: &Expr, limit: usize) -> Vec<BinderInfo> {
        let mut infos = Vec::with_capacity(limit);
        let mut current = ty;
        while infos.len() < limit {
            match current.kind() {
                ExprKind::Pi(bd, _, body) => {
                    infos.push(bd.info);
                    current = body.as_ref();
                }
                _ => break,
            }
        }
        infos
    }

    /// Re-elaborate a function application with Nat literals coerced to Real.
    ///
    /// This is called when we detect that a Nat literal constrained a type parameter
    /// to Nat, but a later argument has type Real. We retry with the literal coerced.
    ///
    /// # Contract
    ///
    /// ENSURES: Result has all solved metavariables instantiated
    /// ENSURES: Result has all solved level constraints substituted (instantiate_levels applied)
    pub(in crate::infer) fn elab_app_with_real_coercion(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        // Elaborate the function
        let func_expr = self.elaborate(func)?;
        let func_type = self.infer_type(&func_expr)?;

        // Insert leading implicit arguments
        let (mut result, mut current_type) = self.insert_implicit_args(func_expr, &func_type);

        // Process each explicit argument, coercing Nat literals to Real
        for (idx, arg) in args.iter().enumerate() {
            current_type = self.whnf(&current_type);

            let type_info = match current_type.kind() {
                ExprKind::Pi(bi, arg_ty, body_ty) => {
                    Some((*bi, arg_ty.as_ref().clone(), body_ty.as_ref().clone()))
                }
                _ => None,
            };

            if let Some((_bi, expected_arg_ty, _body_ty)) = type_info {
                let local_arg_ty = expected_arg_ty;

                // Elaborate argument with expected type context
                let expected_arg_ty = self.metas.instantiate(&local_arg_ty);
                let arg_expr =
                    self.elaborate_with_expected_type(&arg.expr, Some(expected_arg_ty.clone()))?;
                let arg_type = self.infer_type(&arg_expr)?;
                let arg_type = self.metas.instantiate(&arg_type);
                let arg_type = self.whnf(&arg_type);

                let expected_arg_ty = self.whnf(&expected_arg_ty);

                // If this is a Nat literal, coerce it to Real and unify with expected type
                let final_arg = if Self::is_nat_literal(&arg_expr) {
                    let coerced = Expr::app(
                        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
                        arg_expr.clone(),
                    );
                    let coerced_ty = self.infer_type(&coerced)?;
                    let coerced_ty = self.metas.instantiate(&coerced_ty);
                    let coerced_ty = self.whnf(&coerced_ty);
                    let ctx = self.build_local_ctx();
                    let ur = Unifier::with_env(&mut self.metas, self.env, ctx)
                        .unify(&coerced_ty, &expected_arg_ty);
                    match ur {
                        UnifyResult::Success => coerced,
                        UnifyResult::Failure(msg) => {
                            return Err(ElabError::TypeMismatch {
                                expected: format!("{expected_arg_ty:?}"),
                                actual: msg,
                            });
                        }
                        UnifyResult::Stuck => return Err(ElabError::CannotInfer),
                    }
                } else {
                    let ctx = self.build_local_ctx();
                    let ur = Unifier::with_env(&mut self.metas, self.env, ctx)
                        .unify(&arg_type, &expected_arg_ty);
                    match ur {
                        UnifyResult::Success => arg_expr.clone(),
                        UnifyResult::Failure(msg) => {
                            if let Some(coerced) =
                                self.try_coerce(&arg_expr, &arg_type, &expected_arg_ty)
                            {
                                coerced
                            } else {
                                return Err(ElabError::TypeMismatch {
                                    expected: format!("{expected_arg_ty:?}"),
                                    actual: msg,
                                });
                            }
                        }
                        UnifyResult::Stuck => {
                            return Err(ElabError::CannotInfer);
                        }
                    }
                };

                // Update type before consuming final_arg
                current_type = if let ExprKind::Pi(_, _, body) = current_type.kind() {
                    self.metas.instantiate(&body.instantiate(&final_arg))
                } else {
                    current_type.clone()
                };

                // Build the application (consuming final_arg)
                result = Expr::app(result, final_arg);

                let (new_result, new_type) = self.insert_implicit_args(result, &current_type);
                result = new_result;
                current_type = new_type;
            } else {
                // Function type is exhausted (not a Pi) but arguments remain.
                // Return an error instead of silently applying (#1720).
                return Err(ElabError::TooManyArguments {
                    func_type: format!("{current_type:?}"),
                    remaining_args: args.len() - idx,
                });
            }
        }

        let result = self.metas.instantiate(&result);
        Ok(self.metas.instantiate_levels(&result))
    }

    /// Re-elaborate a function application with Nat literals coerced to `Int`.
    ///
    /// Mirror of [`elab_app_with_real_coercion`] for `Int`: called when a Nat
    /// literal at an EARLIER argument position solved a shared type metavar to
    /// `Nat` (e.g. operand-0 of `0 ≤ a`), but a LATER argument is `Int`. We retry
    /// with the literal coerced via `Int.ofNat`, so `0 ≤ (a : Int)` elaborates as
    /// `LE.le (Int.ofNat 0) a` instead of mismatching `Nat` vs `Int`.
    pub(in crate::infer) fn elab_app_with_int_coercion(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        let func_expr = self.elaborate(func)?;
        let func_type = self.infer_type(&func_expr)?;
        // DEFER class-instance args: a homogeneous class-binop (`LE.le`/`LT.lt`)
        // inserts `[LE ?α]` BEFORE the operands; resolving it eagerly against the
        // unconstrained `?α` picks `instLENat` and pins `?α := Nat`, defeating the
        // literal→`Int.ofNat` coercion below. Collect the instance metavars and
        // resolve them only AFTER the operand loop pins `?α := Int`.
        let (mut result, mut current_type, mut pending) =
            self.insert_implicit_args_deferring_instances(func_expr, &func_type);

        for (idx, arg) in args.iter().enumerate() {
            current_type = self.whnf(&current_type);
            let type_info = match current_type.kind() {
                ExprKind::Pi(bi, arg_ty, body_ty) => {
                    Some((*bi, arg_ty.as_ref().clone(), body_ty.as_ref().clone()))
                }
                _ => None,
            };
            if let Some((_bi, expected_arg_ty, _body_ty)) = type_info {
                let expected_arg_ty = self.metas.instantiate(&expected_arg_ty);

                let final_arg = if let SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) = &arg.expr {
                    // Coerce the bare literal to `Int.ofNat n` WITHOUT first
                    // elaborating it against the expected type. For a homogeneous
                    // binop (`LE.le`/`Eq : α → α → …`) both operands share the SAME
                    // type metavar `?α`; elaborating `0` against `?α` would solve
                    // `?α := Nat` and defeat the very coercion this path exists for.
                    // Unifying `Int` against `?α` instead pins the carrier to `Int`.
                    let coerced = Expr::app(
                        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                        Expr::nat_lit(*n),
                    );
                    let coerced_ty = self.infer_type(&coerced)?;
                    let coerced_ty = self.metas.instantiate(&coerced_ty);
                    let coerced_ty = self.whnf(&coerced_ty);
                    let expected_w = self.whnf(&expected_arg_ty);
                    let ctx = self.build_local_ctx();
                    let ur = Unifier::with_env(&mut self.metas, self.env, ctx)
                        .unify(&coerced_ty, &expected_w);
                    match ur {
                        UnifyResult::Success => coerced,
                        UnifyResult::Failure(msg) => {
                            return Err(ElabError::TypeMismatch {
                                expected: format!("{expected_w:?}"),
                                actual: msg,
                            });
                        }
                        UnifyResult::Stuck => return Err(ElabError::CannotInfer),
                    }
                } else {
                    let arg_expr = self
                        .elaborate_with_expected_type(&arg.expr, Some(expected_arg_ty.clone()))?;
                    let arg_type = self.infer_type(&arg_expr)?;
                    let arg_type = self.metas.instantiate(&arg_type);
                    let arg_type = self.whnf(&arg_type);
                    let expected_w = self.whnf(&expected_arg_ty);
                    let ctx = self.build_local_ctx();
                    let ur = Unifier::with_env(&mut self.metas, self.env, ctx)
                        .unify(&arg_type, &expected_w);
                    match ur {
                        UnifyResult::Success => arg_expr.clone(),
                        UnifyResult::Failure(msg) => {
                            if let Some(coerced) =
                                self.try_coerce(&arg_expr, &arg_type, &expected_w)
                            {
                                coerced
                            } else {
                                return Err(ElabError::TypeMismatch {
                                    expected: format!("{expected_w:?}"),
                                    actual: msg,
                                });
                            }
                        }
                        UnifyResult::Stuck => return Err(ElabError::CannotInfer),
                    }
                };

                current_type = if let ExprKind::Pi(_, _, body) = current_type.kind() {
                    self.metas.instantiate(&body.instantiate(&final_arg))
                } else {
                    current_type.clone()
                };
                result = Expr::app(result, final_arg);
                let (new_result, new_type, mut new_pending) =
                    self.insert_implicit_args_deferring_instances(result, &current_type);
                result = new_result;
                current_type = new_type;
                pending.append(&mut new_pending);
            } else {
                return Err(ElabError::TooManyArguments {
                    func_type: format!("{current_type:?}"),
                    remaining_args: args.len() - idx,
                });
            }
        }

        // Resolve the deferred class-instance args now that the operands (incl.
        // the `Int.ofNat`-coerced literal) have pinned the carrier to `Int`.
        self.resolve_deferred_instances(&pending);
        let result = self.metas.instantiate(&result);
        Ok(self.metas.instantiate_levels(&result))
    }
}
