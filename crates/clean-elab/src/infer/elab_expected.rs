// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expected-type helpers shared across elaboration entry points.

use super::*;

impl<'a> ElabCtx<'a> {
    pub(super) fn elaborate_with_expected_type(
        &mut self,
        expr: &SurfaceExpr,
        expected_ty: Option<Expr>,
    ) -> Result<Expr, ElabError> {
        let prev_expected = self.current_expected_type.clone();
        self.current_expected_type = expected_ty.clone();
        let result = self.elaborate(expr);
        self.current_expected_type = prev_expected;
        match result {
            Ok(expr) => {
                if let Some(expected_ty) = expected_ty {
                    let expr = self.apply_implicit_to_expected_type(&expr, &expected_ty)?;
                    // Prop → Bool decision coercion (Track PP). This is the
                    // single central expected-type chokepoint, so applying the
                    // `decide` coercion here covers every site that elaborates
                    // a sub-expression against an expected type — match arms,
                    // `if`/`then`/`else` branches, function arguments, etc. —
                    // without patching each call individually. Only fires when
                    // the expected type is `Bool` and the elaborated term is a
                    // `Prop` (`Sort 0`), i.e. exactly the case the lenient
                    // `Prop ≈ Bool` unifier would otherwise wave through to a
                    // kernel rejection.
                    let expr = self.maybe_decide_coerce_to_bool(expr, &expected_ty);
                    // Symmetric Bool → Prop sort coercion. The chokepoint above
                    // covers the Prop → Bool direction; this covers a `Bool` term
                    // elaborated against a `Prop` expected type (e.g. a match arm
                    // `addr % size == 0` in a `Prop`-valued function), inserting
                    // `instCoeSortBoolProp` (`b ↦ b = true`) — see `try_coerce`
                    // Step 1e. Kernel-checked downstream; no-op otherwise.
                    let expr = self.maybe_coerce_bool_to_prop(expr, &expected_ty);
                    // Nested-aux → container coercion (Track U). When a match arm
                    // binds a nested-inductive field (e.g. `.sequence xs` binds
                    // `xs : Value._List`, the synthesized aux mirror) and the arm
                    // body is just that variable used where the real container
                    // `List Value` is expected (`| .sequence xs => xs`, or
                    // `some xs`), the elaborated body keeps the aux type and the
                    // kernel rejects the minor (`expected Value._List → List Value`,
                    // `got Value._List → Value._List`). This is the single central
                    // expected-type chokepoint, so routing the aux→container
                    // coercion here repairs every such arm/return site at once
                    // without per-call patches. Fires only when the body's type is
                    // a bare aux mirror with a `.toContainer` conversion and the
                    // expected type is its matching container; `try_coerce`'s
                    // kernel-checked `@<aux>.toContainer` term means a wrong
                    // insertion fails closed. No-op otherwise.
                    let expr = self.maybe_coerce_nested_aux_to_container(expr, &expected_ty);
                    // General coercion fallback (Lean `ensureHasType`): when the
                    // elaborated term's type still differs from a GROUND expected
                    // type and a registered `Coe` bridges them, insert it. This is
                    // the single central chokepoint, so it covers every
                    // expected-typed site at once — most visibly a `match` arm
                    // whose body needs coercing to the result type (`match b with |
                    // true => (1 : Nat) | false => (-1 : Int) : Int`), which the 18+
                    // per-arm elaboration sites do NOT individually coerce (unlike a
                    // `def … : Int := n`, which calls `coerce_to_expected_type`).
                    Ok(self.maybe_coerce_general(expr, &expected_ty))
                } else {
                    Ok(expr)
                }
            }
            Err(err) => Err(err),
        }
    }

    /// Insert a registered coercion when the elaborated term's type differs from
    /// a ground expected type. Conservative and no-op-by-default:
    /// - skips a non-ground (metavariable-carrying) expected type — coercing
    ///   toward an inference-position `?m` would pin the wrong type;
    /// - skips when the term already has the expected type (`is_def_eq`), so a
    ///   currently-matching site is untouched;
    /// - only fires when `try_coerce` finds a real `Coe` instance, and the
    ///   produced term is kernel-checked downstream.
    ///
    /// Because it acts only on a genuine mismatch backed by a real coercion, it
    /// can turn a currently-failing site (raw mismatch reaching the kernel) into
    /// a passing one, but cannot break a site whose types already match.
    pub(super) fn maybe_coerce_general(&mut self, expr: Expr, expected_ty: &Expr) -> Expr {
        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(expected_ty));
        if self.has_metavars(&expected) {
            return expr;
        }
        let actual = match self.infer_type(&expr) {
            Ok(t) => self.metas.instantiate_levels(&self.metas.instantiate(&t)),
            Err(_) => return expr,
        };
        if self.is_def_eq(&actual, &expected) {
            return expr;
        }
        match self.try_coerce(&expr, &actual, &expected) {
            Some(coerced) => coerced,
            None => expr,
        }
    }

    /// If `expected_ty` is `Bool` and `expr` is a decidable `Prop`, return the
    /// `@decide p inst` coercion; otherwise return `expr` unchanged.
    ///
    /// Soundness: the produced term is `@decide p inst : Bool`, kernel-checked
    /// downstream. If no `Decidable p` instance resolves (or there is no
    /// Bool-valued `decide` constant), `expr` is returned untouched, preserving
    /// prior behavior. (Track PP)
    pub(super) fn maybe_decide_coerce_to_bool(&mut self, expr: Expr, expected_ty: &Expr) -> Expr {
        let expected_whnf = self.whnf(&self.metas.instantiate(expected_ty));
        let is_bool = matches!(expected_whnf.kind(), ExprKind::Const(n, l) if l.is_empty() && n.to_string() == "Bool");
        if !is_bool {
            return expr;
        }
        let actual_ty = match self.infer_type(&expr) {
            Ok(t) => self.whnf(&self.metas.instantiate(&t)),
            Err(_) => return expr,
        };
        if !matches!(actual_ty.kind(), ExprKind::Sort(lvl) if lvl.is_zero()) {
            return expr;
        }
        // Reuse the single coercion implementation in `try_coerce` (Step 1d).
        match self.try_coerce(&expr, &actual_ty, &expected_whnf) {
            Some(coerced) => coerced,
            None => expr,
        }
    }

    /// If `expected_ty` is `Prop` and `expr` is a `Bool`, return the
    /// `instCoeSortBoolProp` coercion `@Eq Bool expr Bool.true`; otherwise return
    /// `expr` unchanged. Symmetric counterpart to `maybe_decide_coerce_to_bool`.
    ///
    /// Soundness: the produced term is `@Eq Bool expr Bool.true : Prop`, built from
    /// core constants and kernel-checked downstream. When the expected type is not
    /// `Prop` or `expr` is not `Bool`-typed, `expr` is returned untouched, so prior
    /// behavior is preserved exactly.
    pub(super) fn maybe_coerce_bool_to_prop(&mut self, expr: Expr, expected_ty: &Expr) -> Expr {
        let expected_whnf = self.whnf(&self.metas.instantiate(expected_ty));
        let is_prop = matches!(expected_whnf.kind(), ExprKind::Sort(lvl) if lvl.is_zero());
        if !is_prop {
            return expr;
        }
        let actual_ty = match self.infer_type(&expr) {
            Ok(t) => self.whnf(&self.metas.instantiate(&t)),
            Err(_) => return expr,
        };
        let is_bool = matches!(actual_ty.kind(), ExprKind::Const(n, l) if l.is_empty() && n.to_string() == "Bool");
        if !is_bool {
            return expr;
        }
        // Reuse the single coercion implementation in `try_coerce` (Step 1e).
        match self.try_coerce(&expr, &actual_ty, &expected_whnf) {
            Some(coerced) => coerced,
            None => expr,
        }
    }

    /// If `expr`'s type is a bare nested-aux mirror (`Value._List`) and
    /// `expected_ty` is its matching real container (`List Value`), return the
    /// `@<aux>.toContainer expr` coercion; otherwise return `expr` unchanged.
    ///
    /// This is the return-position counterpart of the argument-position
    /// coercion `elab_app` already performs: a match arm `| .sequence xs => xs`
    /// (or `some xs`) leaves the body at the aux type `Value._List`, which the
    /// kernel rejects against the `List Value` branch type. We only act when the
    /// actual type is a bare `Const` (aux types carry no value params) carrying a
    /// generated `.toContainer` and the expected type unifies with that
    /// conversion's codomain (`try_coerce_nested_aux_to_container` enforces both).
    ///
    /// SOUNDNESS: the produced term is the kernel-checked `@<aux>.toContainer
    /// expr`; an expected type that is not the matching container leaves
    /// `try_coerce_nested_aux_to_container` returning `None`, so `expr` is
    /// returned untouched and prior behavior is preserved exactly.
    pub(super) fn maybe_coerce_nested_aux_to_container(
        &mut self,
        expr: Expr,
        expected_ty: &Expr,
    ) -> Expr {
        let expected_whnf = self.whnf(&self.metas.instantiate(expected_ty));
        let actual_ty = match self.infer_type(&expr) {
            Ok(t) => self.whnf(&self.metas.instantiate(&t)),
            Err(_) => return expr,
        };
        // Cheap precondition: aux mirror sources are bare constants (no value
        // params/indices). Bail before the heavier coercion attempt otherwise so
        // ordinary arms pay nothing.
        if !matches!(actual_ty.kind(), ExprKind::Const(_, _)) {
            return expr;
        }
        // If the body already has the expected type there is nothing to coerce;
        // only act on a genuine aux/container mismatch.
        if self.is_def_eq(&actual_ty, &expected_whnf) {
            return expr;
        }
        match self.try_coerce_nested_aux_to_container(&expr, &actual_ty, &expected_whnf) {
            Some(coerced) => coerced,
            None => expr,
        }
    }

    /// B18 — elaborator-side `ensureHasType` at ascription / def-/theorem-body
    /// boundaries: reject a term whose type the KERNEL would also reject.
    ///
    /// Lean's `Term.ensureHasType` runs at every ascription and def-body
    /// boundary, so an ill-typed body is a LOUD elaboration error and its term
    /// is never handed to the kernel — and, critically, never laundered into a
    /// registered declaration or a synthetic `sorryAx`. Clean's elaborator is
    /// lenient (it defers final checking to the kernel's `add_decl`), so a
    /// mismatched body currently reaches the kernel as a `KernelCheckFailed`
    /// only AFTER the elaborator has already shipped (and in some paths
    /// registered) the ill-typed term. This method relocates that verdict to
    /// elaboration time.
    ///
    /// STRICTLY RELOCATION-ONLY: the check is the kernel's OWN transparency-blind
    /// def-eq — the exact verdict `add_decl` reaches — so it rejects a body if
    /// and only if the kernel would also reject it. It never newly rejects a
    /// term the kernel accepts, and it never changes the term (no coercion), so
    /// the only observable effect is `KernelCheckFailed` (kernel-deferred) →
    /// `TypeMismatch` (loud at elaboration), plus the ill-typed term never being
    /// registered.
    ///
    /// Skipped (stay lenient — the kernel re-check decides) when either type
    /// still carries an unsolved metavariable (the ground kernel verdict would
    /// be unreliable) or the body's type cannot be inferred here.
    pub(super) fn reject_body_type_mismatch(&self, val: &Expr, ty: &Expr) -> Result<(), ElabError> {
        let Ok(val_ty) = self.infer_type(val) else {
            return Ok(());
        };
        let val_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&val_ty));
        let ty = self.metas.instantiate_levels(&self.metas.instantiate(ty));
        if val_ty.has_expr_mvar_quick() || ty.has_expr_mvar_quick() {
            return Ok(());
        }
        let ctx = self.build_local_ctx();
        // Transparency-blind, complete def-eq: mirrors the kernel `add_decl`
        // re-check that would otherwise reject (or, on the synthetic-sorry
        // paths, launder) the term downstream.
        let kernel_ok =
            clean_kernel::TypeChecker::with_context(self.env, ctx).is_def_eq(&val_ty, &ty);
        if kernel_ok {
            Ok(())
        } else {
            // Readable (Display) rendering — this is a user-facing elaboration
            // error, not the kernel's internal debug dump.
            Err(ElabError::TypeMismatch {
                expected: format!("{ty}"),
                actual: format!("{val_ty}"),
            })
        }
    }

    pub(super) fn enforce_expr_type(
        &mut self,
        expr: &Expr,
        expected_ty: &Expr,
    ) -> Result<(), ElabError> {
        let actual_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&self.infer_type(expr)?));
        self.commit_pending_level_assigns();
        let expected_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(expected_ty));

        // Scope the unifier borrow so we can call try_coerce after.
        let unify_result = {
            let ctx = self.build_local_ctx();
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            unifier.unify(&actual_ty, &expected_ty)
        };
        match unify_result {
            UnifyResult::Success => Ok(()),
            UnifyResult::Failure(msg) => {
                // The metavariable-solving unifier is intentionally structural
                // and may stop at reducible aliases (`Unit` vs `PUnit.{1}`).
                // A type gate must use the kernel's complete definitional
                // equality before considering coercion or rejecting the term.
                if self.is_def_eq(&actual_ty, &expected_ty) {
                    return Ok(());
                }
                // Try type coercion before reporting TypeMismatch (#796).
                if self.try_coerce(expr, &actual_ty, &expected_ty).is_some() {
                    return Ok(());
                }
                Err(ElabError::TypeMismatch {
                    expected: format!("{expected_ty:?}"),
                    actual: format!("{actual_ty:?} ({msg})"),
                })
            }
            UnifyResult::Stuck => Err(ElabError::CannotInfer),
        }
    }

    /// Like [`enforce_expr_type`], but RETURNS the (possibly coerced) term.
    ///
    /// `enforce_expr_type` only *checks* coercibility and discards the coerced
    /// term, so callers that keep the original `expr` silently drop a coercion
    /// the kernel then rejects. This variant applies the coercion: on a
    /// type mismatch it returns the rewritten term produced by `try_coerce`
    /// (e.g. `@decide p inst : Bool` for a `Prop` used where a `Bool` is
    /// expected — Track PP). When the types already unify it returns `expr`
    /// unchanged. The kernel re-checks the returned term, so an unsound
    /// coercion still fails closed rather than passing silently. (Track PP)
    pub(super) fn coerce_to_expected_type(
        &mut self,
        expr: &Expr,
        expected_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        let actual_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&self.infer_type(expr)?));
        self.commit_pending_level_assigns();
        let expected_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(expected_ty));

        // Prop → Bool special case (Track PP): the *unifier* leniently treats
        // `Prop` ≈ `Bool` as defeq (unify/unify_expr.rs `is_bool_prop_pair`)
        // even though they are NOT kernel-defeq, on the understanding that a
        // `decide` coercion is the intended interpretation. `enforce_expr_type`
        // therefore reports Success and never coerces, so the raw `Prop` term
        // reaches the kernel, which rejects it. Here we apply the coercion
        // explicitly whenever the expected type is `Bool` and the actual type
        // is `Prop`, BEFORE consulting the lenient unifier — producing the
        // `@decide p inst` term the kernel actually accepts.
        let actual_whnf = self.whnf(&actual_ty);
        let expected_whnf = self.whnf(&expected_ty);
        let is_bool = |e: &Expr| matches!(e.kind(), ExprKind::Const(n, l) if l.is_empty() && n.to_string() == "Bool");
        let is_prop = |e: &Expr| matches!(e.kind(), ExprKind::Sort(lvl) if lvl.is_zero());
        if is_bool(&expected_whnf) && is_prop(&actual_whnf) {
            if let Some(coerced) = self.try_coerce(expr, &actual_ty, &expected_ty) {
                return Ok(coerced);
            }
            // No Decidable instance / no `decide` constant: fall through to the
            // normal path, which (via the lenient unifier) preserves the prior
            // behavior rather than newly rejecting.
        }

        // Bool → Prop special case (symmetric to the above): the lenient unifier
        // also treats `Bool` ≈ `Prop` as defeq, so without coercing here the raw
        // `Bool` term would reach the kernel against a `Prop` expected type and be
        // rejected. Apply the `instCoeSortBoolProp` coercion (`b ↦ b = true`) via
        // `try_coerce` before the lenient unifier sees the pair. The kernel
        // re-checks the produced `@Eq Bool b Bool.true`, so this fails closed.
        if is_prop(&expected_whnf) && is_bool(&actual_whnf) {
            if let Some(coerced) = self.try_coerce(expr, &actual_ty, &expected_ty) {
                return Ok(coerced);
            }
        }

        let unify_result = {
            let ctx = self.build_local_ctx();
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            unifier.unify(&actual_ty, &expected_ty)
        };
        match unify_result {
            UnifyResult::Success => Ok(expr.clone()),
            UnifyResult::Failure(msg) => {
                if let Some(coerced) = self.try_coerce(expr, &actual_ty, &expected_ty) {
                    return Ok(coerced);
                }
                Err(ElabError::TypeMismatch {
                    expected: format!("{expected_ty:?}"),
                    actual: format!("{actual_ty:?} ({msg})"),
                })
            }
            UnifyResult::Stuck => Err(ElabError::CannotInfer),
        }
    }
}
