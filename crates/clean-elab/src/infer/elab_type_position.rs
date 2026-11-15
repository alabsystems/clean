// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type positions: Lean's `elabType` → `ensureType` → `coerceToSort`.
//!
//! Lean elaborates every TYPE position — an arrow's domain and codomain, a
//! `∀`/Pi binder type and body, a `fun` binder annotation, a declaration's
//! binder types and its result type — through `Term.elabType`, which calls
//! `ensureType` and, when the term is not already a sort, `coerceToSort`. For a
//! `Bool`-valued term the `CoeSort Bool Prop` instance (`boolToSort`, unfolded
//! by `expandCoe`) turns `b` into `b = true`, so `∀ m, m != n → m != n` and
//! `(h : o != none)` are ordinary propositions (G34, ledger (104)).
//!
//! Clean coerced `Bool → Prop` only at the expected-type chokepoint
//! (`maybe_coerce_bool_to_prop`, `try_coerce` Step 1e), where the expected type
//! is the sort `Prop` — never in a type position, so these shapes were refused
//! ("expected valid type, got ExpectedSort(Bool)") or reached the kernel as a
//! `Bool` binder type. This is the one helper every type position calls.
//!
//! SOUNDNESS: the produced term is the kernel-checked `@Eq.{1} Bool b true`;
//! the coercion fires only when the term's type is, at REDUCIBLE transparency,
//! the constant `Bool`, so every other type is returned untouched.
//!
//! Reducible, not default, transparency (r4 review): Lean reaches
//! `boolToSort` through instance resolution, which sees `Bool` itself or an
//! `abbrev`/`@[reducible]` alias of it and never a semireducible
//! `def MyBool := Bool` — pinned Lean 4.8.0 refuses `(h : b)` with
//! `b : MyBool` ("type expected"). Bracketed binders use this ordinary
//! coercion too; the separate declaration/forall class annotation check is in
//! `instance_binder`. Lambdas have no such annotation check, matching Lean.

use super::*;

impl<'a> ElabCtx<'a> {
    /// `coerceToSort`, Bool arm: `b : Bool` in a type position becomes
    /// `@Eq.{1} Bool b Bool.true`. Any other term is returned unchanged
    /// (including one whose type cannot be inferred yet).
    pub(super) fn coerce_type_position(&mut self, ty: Expr) -> Expr {
        let Ok(ty_ty) = self.infer_type(&ty) else {
            return ty;
        };
        let ty_ty = self.metas.instantiate(&ty_ty);
        // A sort is the overwhelmingly common case: no whnf needed.
        if matches!(ty_ty.kind(), ExprKind::Sort(_)) {
            return ty;
        }
        let ty_ty = self.whnf_reducible(&ty_ty);
        let is_bool = matches!(
            ty_ty.kind(),
            ExprKind::Const(n, l) if l.is_empty() && n.to_string() == "Bool"
        );
        if !is_bool
            || self.env.get_const(&Name::from_string("Eq")).is_none()
            || self
                .env
                .get_const(&Name::from_string("Bool.true"))
                .is_none()
        {
            return ty;
        }
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [
                Expr::const_str("Bool"),
                self.metas.instantiate(&ty),
                Expr::const_str("Bool.true"),
            ],
        )
    }

    /// [`Self::ensure_type_expr`], with [`Self::coerce_type_position`] as its
    /// `coerceToSort` fallback: the (possibly coerced) type and its universe
    /// level. A term that is already a type is never re-inferred.
    pub(super) fn ensure_type_coerced(&mut self, ty: Expr) -> Result<(Expr, Level), ElabError> {
        match self.ensure_type_expr(&ty) {
            Ok(level) => Ok((ty, level)),
            Err(err) => {
                let coerced = self.coerce_type_position(ty.clone());
                if coerced == ty {
                    return Err(err);
                }
                let level = self.ensure_type_expr(&coerced)?;
                Ok((coerced, level))
            }
        }
    }
}
