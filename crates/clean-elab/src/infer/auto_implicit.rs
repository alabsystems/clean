// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Auto-implicit parameter handling.
//!
//! Extracted from `infer/mod.rs`. Contains methods for discovering, tracking,
//! and wrapping auto-implicit type parameters during elaboration.

use super::*;

impl<'a> ElabCtx<'a> {
    fn rebuild_auto_implicit_lookup(&mut self) {
        self.auto_implicit_lookup.clear();
        for (name, fvar, _) in &self.auto_implicits {
            self.auto_implicit_lookup
                .entry(name.clone())
                .or_insert(*fvar);
        }
    }

    fn abstract_over_auto_implicit_fvars(mut expr: Expr, outer_fvars: &[FVarId]) -> Expr {
        // Iterate FORWARD: the first fvar in the list corresponds to the outermost
        // Pi/Lambda binder (highest BVar index), and the last fvar corresponds to
        // the innermost binder (BVar(0)). Each abstract_fvar replaces the target
        // FVar with BVar(0) and shifts existing BVars up by 1, so abstracting
        // in forward order produces:
        //   first fvar  → BVar(N-1) (shifted up N-1 times by subsequent abstractions)
        //   last fvar   → BVar(0)   (never shifted)
        // which matches Pi(first, Pi(second, ... Pi(last, body))) where BVar(0) in
        // the body refers to the innermost (last) binder.
        for fvar in outer_fvars.iter() {
            expr = expr.abstract_fvar(*fvar);
        }
        expr
    }

    fn wrap_with_auto_implicits_rec(
        ty: Expr,
        val: Expr,
        auto_implicits: &[(String, FVarId, Expr)],
        outer_fvars: &[FVarId],
    ) -> (Expr, Expr) {
        let Some(((_name, fvar, implicit_ty), rest)) = auto_implicits.split_first() else {
            return (
                Self::abstract_over_auto_implicit_fvars(ty, outer_fvars),
                Self::abstract_over_auto_implicit_fvars(val, outer_fvars),
            );
        };

        let mut new_outer_fvars = outer_fvars.to_vec();
        new_outer_fvars.push(*fvar);
        let (inner_ty, inner_val) =
            Self::wrap_with_auto_implicits_rec(ty, val, rest, &new_outer_fvars);

        let binder_ty = Self::abstract_over_auto_implicit_fvars(implicit_ty.clone(), outer_fvars);
        (
            Expr::pi(BinderInfo::Implicit, binder_ty.clone(), inner_ty),
            Expr::lam(BinderInfo::Implicit, binder_ty, inner_val),
        )
    }

    fn wrap_type_with_auto_implicits_rec(
        ty: Expr,
        auto_implicits: &[(String, FVarId, Expr)],
        outer_fvars: &[FVarId],
    ) -> Expr {
        let Some(((_name, fvar, implicit_ty), rest)) = auto_implicits.split_first() else {
            return Self::abstract_over_auto_implicit_fvars(ty, outer_fvars);
        };

        let mut new_outer_fvars = outer_fvars.to_vec();
        new_outer_fvars.push(*fvar);
        let inner_ty = Self::wrap_type_with_auto_implicits_rec(ty, rest, &new_outer_fvars);
        let binder_ty = Self::abstract_over_auto_implicit_fvars(implicit_ty.clone(), outer_fvars);
        Expr::pi(BinderInfo::Implicit, binder_ty, inner_ty)
    }

    /// Check whether an identifier name is valid for auto-implicit resolution.
    ///
    /// In Lean 4 with relaxedAutoImplicit (the default):
    /// - Any alphabetic identifier can become an auto-implicit
    /// - Greek letters (α, β, etc.) and single uppercase letters (A, R, etc.)
    ///   are common auto-implicits in Mathlib
    ///
    /// Without relaxedAutoImplicit:
    /// - The identifier must be a single alphabetic character
    ///
    /// This implements relaxed auto-implicit by default since that matches Lean 4's
    /// default behavior and what most FATE-X files expect.
    pub(in crate::infer) fn is_valid_auto_implicit_name(name: &str, relaxed: bool) -> bool {
        if name.is_empty() {
            return false;
        }

        let mut chars = name.chars();
        let first_char = chars.next().expect("invariant: name is non-empty");
        if !first_char.is_alphabetic() {
            return false;
        }

        relaxed || chars.next().is_none()
    }

    /// Unwrap parentheses from a surface expression.
    /// Returns the innermost non-Paren expression.
    pub(in crate::infer) fn unwrap_surface_parens(expr: &SurfaceExpr) -> &SurfaceExpr {
        match expr {
            SurfaceExpr::Paren(_, inner) => Self::unwrap_surface_parens(inner),
            _ => expr,
        }
    }

    /// Run `f` with the term-body flag set: auto-bound implicit creation is
    /// disabled inside. Lean binds auto-implicits only while elaborating
    /// declaration *headers* (`Lean/Elab/MutualDef.lean` `elabHeaders` runs
    /// under `withAutoBoundImplicit`; `Lean/Elab/Term.lean` `mkAutoBoundImplicit`
    /// consults that flag) — a bare unknown identifier in a VALUE position
    /// (def body, theorem proof, instance field value) is always a loud
    /// `unknown identifier` error (gap sweep B03).
    pub(in crate::infer) fn with_term_body_scope<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let prev = self.in_term_body;
        self.in_term_body = true;
        let result = f(self);
        self.in_term_body = prev;
        result
    }

    /// Check if an auto-implicit with this name already exists
    pub(in crate::infer) fn has_auto_implicit(&self, name: &str) -> Option<FVarId> {
        self.auto_implicit_lookup.get(name).copied()
    }

    /// Add a new auto-implicit binding
    pub(in crate::infer) fn add_auto_implicit(&mut self, name: String, ty: Expr) -> FVarId {
        let fvar = self.fresh_fvar();
        self.auto_implicits.push((name.clone(), fvar, ty.clone()));
        self.auto_implicit_lookup
            .entry(name.clone())
            .or_insert(fvar);
        // Also add to locals so the identifier can be looked up in subsequent uses
        self.locals.push((name, fvar, ty));
        fvar
    }

    /// Take auto-implicits for finalizing a declaration
    pub(in crate::infer) fn take_auto_implicits(&mut self) -> Vec<(String, FVarId, Expr)> {
        let instantiated: Vec<_> = self
            .auto_implicits
            .iter()
            .map(|(name, fvar, ty)| {
                let ty = self.metas.instantiate(ty);
                let ty = self.metas.instantiate_levels(&ty);
                (name.clone(), *fvar, ty)
            })
            .collect();

        // Remove auto-implicits from locals as well
        let auto_fvars: std::collections::HashSet<_> = self
            .auto_implicits
            .iter()
            .map(|(_, fvar, _)| *fvar)
            .collect();
        self.locals
            .retain(|(_, fvar, _)| !auto_fvars.contains(fvar));

        self.auto_implicits.clear();
        self.auto_implicit_lookup.clear();
        instantiated
    }

    /// Return the number of active auto-implicits in scope.
    pub(in crate::infer) fn auto_implicit_count(&self) -> usize {
        self.auto_implicits.len()
    }

    /// Non-destructive snapshot of auto-implicits created after `start`.
    ///
    /// Unlike `take_auto_implicits_since`, this does NOT remove them from
    /// `self.auto_implicits` or `self.locals`, so they remain in scope for
    /// subsequent elaboration. Used to freeze the header auto-implicit packet
    /// before constructor elaboration (#2680).
    pub(in crate::infer) fn snapshot_auto_implicits_since(
        &self,
        start: usize,
    ) -> Vec<(String, FVarId, Expr)> {
        assert!(
            start <= self.auto_implicits.len(),
            "auto-implicit scope start must be within bounds"
        );
        self.auto_implicits[start..]
            .iter()
            .map(|(name, fvar, ty)| {
                let ty = self.metas.instantiate(ty);
                let ty = self.metas.instantiate_levels(&ty);
                (name.clone(), *fvar, ty)
            })
            .collect()
    }

    /// Drain auto-implicits created after `start`, leaving earlier ones in scope.
    pub(in crate::infer) fn take_auto_implicits_since(
        &mut self,
        start: usize,
    ) -> Vec<(String, FVarId, Expr)> {
        assert!(
            start <= self.auto_implicits.len(),
            "auto-implicit scope start must be within bounds"
        );

        let drained = self.auto_implicits.split_off(start);
        let instantiated: Vec<_> = drained
            .iter()
            .map(|(name, fvar, ty)| {
                let ty = self.metas.instantiate(ty);
                let ty = self.metas.instantiate_levels(&ty);
                (name.clone(), *fvar, ty)
            })
            .collect();

        let drained_fvars: std::collections::HashSet<_> =
            drained.iter().map(|(_, fvar, _)| *fvar).collect();
        self.locals
            .retain(|(_, fvar, _)| !drained_fvars.contains(fvar));
        self.rebuild_auto_implicit_lookup();

        instantiated
    }

    /// Wrap type and value expressions with auto-implicit Pi/Lambda binders (#164)
    ///
    /// Given auto-implicits [(A, fvarA, implicitTyA), (B, fvarB, implicitTyB), ...],
    /// transforms:
    ///   ty:  A → B → body_ty
    ///   val: λ(x:A) λ(y:B) body_val
    /// into:
    ///   ty:  {A : implicitTyA} → {B : implicitTyB} → A → B → body_ty
    ///   val: λ{A : implicitTyA} λ{B : implicitTyB} λ(x:A) λ(y:B) body_val
    pub(in crate::infer) fn wrap_with_auto_implicits(
        ty: Expr,
        val: Expr,
        auto_implicits: &[(String, FVarId, Expr)],
    ) -> (Expr, Expr) {
        Self::wrap_with_auto_implicits_rec(ty, val, auto_implicits, &[])
    }

    /// Wrap type expression only with auto-implicit Pi binders (#164)
    /// Used for axioms which have no value expression
    pub(in crate::infer) fn wrap_type_with_auto_implicits(
        ty: Expr,
        auto_implicits: &[(String, FVarId, Expr)],
    ) -> Expr {
        Self::wrap_type_with_auto_implicits_rec(ty, auto_implicits, &[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_auto_implicit_lookup_updates_after_drain_and_clear() {
        let env = Environment::with_prelude();
        let mut ctx = ElabCtx::new(&env);
        let sort_ty = Expr::sort(Level::zero());

        let alpha = ctx.add_auto_implicit("alpha".to_string(), sort_ty.clone());
        let beta = ctx.add_auto_implicit("beta".to_string(), sort_ty.clone());
        assert_eq!(ctx.has_auto_implicit("alpha"), Some(alpha));
        assert_eq!(ctx.has_auto_implicit("beta"), Some(beta));

        let drained = ctx.take_auto_implicits_since(1);
        assert_eq!(drained.len(), 1, "only the tail packet should drain");
        assert_eq!(drained[0].0, "beta");
        assert_eq!(ctx.auto_implicit_count(), 1);
        assert_eq!(ctx.has_auto_implicit("alpha"), Some(alpha));
        assert_eq!(ctx.has_auto_implicit("beta"), None);

        let beta_rebound = ctx.add_auto_implicit("beta".to_string(), sort_ty);
        assert_eq!(ctx.has_auto_implicit("beta"), Some(beta_rebound));

        let taken = ctx.take_auto_implicits();
        assert_eq!(taken.len(), 2, "both active auto-implicits should drain");
        assert_eq!(ctx.auto_implicit_count(), 0);
        assert_eq!(ctx.has_auto_implicit("alpha"), None);
        assert_eq!(ctx.has_auto_implicit("beta"), None);
    }
}
