// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::expr::{Expr, ExprKind};
use crate::tc::reduction::string_lit_to_constructor;
use crate::tc::TypeChecker;

impl<'env> TypeChecker<'env> {
    pub(in crate::tc::def_eq) fn is_def_eq_structural(&self, a_whnf: &Expr, b_whnf: &Expr) -> bool {
        match (a_whnf.kind(), b_whnf.kind()) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.levels_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                n1 == n2
                    && ls1.len() == ls2.len()
                    && ls1
                        .iter()
                        .zip(ls2.iter())
                        .all(|(l1, l2)| self.levels_eq(l1, l2))
            }
            (ExprKind::App(_f1, _a1), ExprKind::App(_f2, _a2)) => {
                // Branch-sharing optimization (#3402): flatten application spines
                // and compare left-to-right. When multiple case-split branches
                // share a common prefix (e.g., 49 branches with identical first
                // 4 monadic binds), the spine comparison checks the shared prefix
                // once — subsequent branches find those subexpressions in the
                // equiv_manager and def_eq_cache in O(1).
                //
                // Falls back to try_structure_eta_expansion on failure, matching
                // Lean 4 parity (type_checker.cpp:1117-1124). Part of #3134, #3402.
                if self.is_def_eq_app_spine(a_whnf, b_whnf) {
                    return true;
                }
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[structural] App spine failed, trying struct eta");
                self.try_structure_eta_expansion(a_whnf, b_whnf)
            }
            (ExprKind::Lam(..), ExprKind::Lam(..)) | (ExprKind::Pi(..), ExprKind::Pi(..)) => {
                self.is_def_eq_binding(a_whnf, b_whnf)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(s1, i1, e1), ExprKind::Proj(s2, i2, e2)) => {
                s1 == s2 && i1 == i2 && self.is_def_eq_impl(e1, e2)
            }
            (ExprKind::Lam(bd, ty, body), _) => {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[structural] eta expansion (lhs Lam)");
                self.try_eta_expansion_impl(a_whnf, b_whnf, *bd, ty, body)
            }
            (_, ExprKind::Lam(bd, ty, body)) => {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[structural] eta expansion (rhs Lam)");
                self.try_eta_expansion_impl(b_whnf, a_whnf, *bd, ty, body)
            }
            _ => {
                // Cubical mode: component-wise / path-eta comparison of cubical
                // constructs (Path, PathLam, PathApp, HComp, Transp, interval
                // endpoints). Returns `None` when neither side is a cubical
                // construct it handles, falling through to the existing
                // structure-eta fallback below.
                if let Some(result) = self.is_def_eq_cubical(a_whnf, b_whnf) {
                    return result;
                }
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[structural] struct eta fallback");
                self.try_structure_eta_expansion(a_whnf, b_whnf)
            }
        }
    }

    /// Compare two App expressions by flattening their application spines and
    /// comparing arguments left-to-right.
    ///
    /// For `f a₁ a₂ ... aₙ` vs `g b₁ b₂ ... bₘ`:
    /// 1. If n != m, return false (mismatched arities cannot be structurally equal)
    /// 2. Check `is_def_eq(f, g)` -- the function heads
    /// 3. Check `is_def_eq(aᵢ, bᵢ)` for i = 1..n, left-to-right
    ///
    /// The left-to-right ordering is the key optimization for branch sharing
    /// (#3402): when multiple case-split branches share a common prefix of
    /// identical subexpressions, the first branch comparison checks each prefix
    /// pair and records the result in the equiv_manager and def_eq_cache.
    /// Subsequent branches find these pairs as O(1) cache hits.
    ///
    /// When the branch-sharing cache is available and both sides share a Const
    /// function head (common in case splits like `semBinOp` with 49 branches),
    /// uses `branch_sharing_compare` for each argument pair. This proactively
    /// pre-caches no-delta WHNF results for subexpressions, so that later
    /// spine comparisons on different branches find the shared prefix in O(1).
    ///
    /// For semBinOp with 49 branches sharing 4 monadic binds as prefix:
    /// - Branch 1: full comparison of 4 prefix args + divergent suffix
    /// - Branches 2-49: 4 cache hits + divergent suffix comparison
    /// - Net savings: ~48 * (cost of 4 prefix args) for the shared prefix
    fn is_def_eq_app_spine(&self, a: &Expr, b: &Expr) -> bool {
        // Flatten application spines. get_app_args() returns args in
        // left-to-right order (first applied arg at index 0).
        let a_args = a.get_app_args();
        let b_args = b.get_app_args();

        // Mismatched arities: these apps can't be structurally equal.
        // Don't attempt comparison -- let the caller try eta/struct-eta.
        if a_args.len() != b_args.len() {
            return false;
        }

        // Compare function heads first (innermost function in the App chain).
        let a_head = a.get_app_fn();
        let b_head = b.get_app_fn();
        if !self.is_def_eq_impl(a_head, b_head) {
            return false;
        }

        // When the branch-sharing cache is available and both heads are the
        // same Const, use branch_sharing_compare for arguments. This pre-caches
        // no-delta WHNF results so subsequent spine comparisons (from other
        // case-split branches sharing the same function head) get O(1) cache
        // hits on the shared prefix arguments. (#3402)
        let use_branch_cache =
            self.branch_sharing_cache.is_some() && self.heads_are_same_const(a_head, b_head);

        // Compare arguments left-to-right. The left-to-right order ensures
        // shared prefix arguments (common monadic binds) are checked first,
        // populating caches for subsequent branch comparisons.
        if use_branch_cache {
            for (ai, bi) in a_args.iter().zip(b_args.iter()) {
                if !self.branch_sharing_compare(ai, bi) {
                    return false;
                }
            }
        } else {
            for (ai, bi) in a_args.iter().zip(b_args.iter()) {
                if !self.is_def_eq_impl(ai, bi) {
                    return false;
                }
            }
        }

        true
    }

    /// Check if two function heads are the same Const (same name).
    ///
    /// Used to detect case-split patterns where multiple branches share the
    /// same function head (e.g., `semBinOp` applied to different arguments).
    /// When true, spine comparison benefits from pre-caching shared prefix
    /// arguments in the branch-sharing cache.
    pub(in crate::tc) fn heads_are_same_const(&self, a_head: &Expr, b_head: &Expr) -> bool {
        if let (ExprKind::Const(n1, _), ExprKind::Const(n2, _)) = (a_head.kind(), b_head.kind()) {
            n1 == n2
        } else {
            false
        }
    }

    fn try_structure_eta_expansion(&self, a_whnf: &Expr, b_whnf: &Expr) -> bool {
        self.try_structure_eta_core(a_whnf, b_whnf) || self.try_structure_eta_core(b_whnf, a_whnf)
    }

    /// Structure eta for definitional equality — Lean 4's exact algorithm.
    ///
    /// Lean 4 parity (`type_checker.cpp:786-811` `try_eta_struct_core(t, s)`):
    /// structure eta fires ONLY when `t` is literally a saturated constructor
    /// application of a structure-like inductive. `s` (the other side, of the
    /// same structure type) is then compared FIELDWISE via projections:
    /// `Proj i s =?= t.field_i`. When neither side is a constructor
    /// application, Lean returns false and lets the outer machinery (lazy
    /// delta at the enclosing comparison) find the reduction path.
    ///
    /// The previous clean implementation eta-expanded ANY structure-typed
    /// side (fvar vs proj, proj vs proj, ...) and re-entered full def-eq on
    /// the expanded pair. That is semantically valid (structure eta is a true
    /// definitional principle) but COMPLETE-BUT-EXPONENTIAL: on
    /// nested-structure case splits the fvar/proj ping-pong regenerates
    /// fresh comparison pairs forever — `Lean.Omega.tidy_sat`'s 666k def-eq
    /// cores per 2M heartbeats with ~zero actual reduction (the 2026-06-12
    /// kernel performance-parity wall). Lean's ctor-app trigger makes the
    /// recursion structural in `t` and terminates.
    fn try_structure_eta_core(&self, t: &Expr, s: &Expr) -> bool {
        // `t` must be a saturated constructor application of a structure.
        let ExprKind::Const(head_name, _) = t.get_app_fn().kind() else {
            return false;
        };
        let Some(ctor) = self.env.get_constructor(head_name) else {
            return false;
        };
        if !self.is_structure_like(&ctor.inductive_name) {
            return false;
        }
        let num_params = ctor.num_params as usize;
        let num_fields = ctor.num_fields as usize;
        let args = t.get_app_args();
        if args.len() != num_params + num_fields {
            return false;
        }
        // `s`'s type must be the same structure.
        // Lean 4 reference: type_checker.cpp:801 uses full `infer_type`.
        // Fall back to full inference when quick fails. Part of #3134.
        let Some(s_type) = self
            .try_infer_type_quick(s)
            .or_else(|| self.infer_type_infer_only(s).ok())
        else {
            return false;
        };
        let s_type_whnf = self.whnf_impl(&s_type);
        let ExprKind::Const(s_ind, _) = s_type_whnf.get_app_fn().kind() else {
            return false;
        };
        if *s_ind != ctor.inductive_name {
            return false;
        }
        // Fieldwise: Proj i s =?= t.field_i (Lean 4 type_checker.cpp:805-809).
        (0..num_fields).all(|i| {
            let proj = Expr::proj(ctor.inductive_name.clone(), i as u32, s.clone());
            self.is_def_eq_impl(&proj, args[num_params + i])
        })
    }

    pub(in crate::tc::def_eq) fn try_string_lit_expansion(&self, t: &Expr, s: &Expr) -> bool {
        self.try_string_lit_expansion_core(t, s) || self.try_string_lit_expansion_core(s, t)
    }

    /// Try to prove `t ≡ s` when `t` is a string literal and `s` is its
    /// constructor form (Lean 4 `is_def_eq_string_lit`,
    /// type_checker.cpp:1126-1127).
    ///
    /// `t` is lowered via [`string_lit_to_constructor`] to
    /// `String.ofList (List.cons (Char.ofNat c₀) (... List.nil))` and then run
    /// through the *full* `whnf` so that:
    ///   - `String.ofList` (a reducible alias `λ d => String.mk d`) delta-unfolds
    ///     to the `String.mk` constructor, and
    ///   - the nested `List.cons` / `List.nil` / `Char.ofNat` applications are
    ///     resolved by the same reducer the kernel uses elsewhere.
    ///
    /// The fully reduced literal is then compared against `s` with the ordinary
    /// `is_def_eq` machinery. This is sound: the literal is only ever replaced
    /// by its genuine definitional unfolding, and the actual equality decision
    /// is delegated to `is_def_eq_impl` — distinct literals (`"ab"` vs `"ac"`)
    /// expand to distinct character lists and are correctly rejected.
    ///
    /// Unlike the previous implementation, this no longer requires the head of
    /// `s` to be syntactically `String.ofList`: a manually written
    /// `String.mk [Char.ofNat 97, Char.ofNat 98]`, or any other expression whose
    /// normal form is the same `String.mk` constructor, is accepted. Reducing
    /// the *literal* to constructor form and letting `is_def_eq` reduce `s` is
    /// what makes the comparison robust across def_eq contexts.
    pub(in crate::tc::def_eq) fn try_string_lit_expansion_core(&self, t: &Expr, s: &Expr) -> bool {
        let ExprKind::Lit(crate::expr::Literal::String(str_val)) = t.kind() else {
            return false;
        };
        // Two string literals are compared exactly by the `Lit == Lit` rule
        // (Phase 1 / structural). Never expand here: doing so could only ever
        // re-confirm a match the literal comparison already settled, and must
        // not be used to bridge two *distinct* literals.
        if matches!(s.kind(), ExprKind::Lit(crate::expr::Literal::String(_))) {
            return false;
        }
        // A String value in normal form is a constructor application
        // (`String.mk _` or its `String.ofList _` alias). Require `s` to be an
        // application headed by a `Const`; bvars, sorts, binders, etc. can never
        // be defeq to a string literal, so we skip the expansion work for them.
        if !s.is_app() {
            return false;
        }
        if !matches!(s.get_app_fn().kind(), ExprKind::Const(..)) {
            return false;
        }
        // Lower the literal to `String.ofList (List.cons (Char.ofNat …) …)` and
        // fully reduce it (delta-unfolding `String.ofList` to `String.mk` and
        // resolving the nested list/char applications) using the shared whnf.
        let expanded = string_lit_to_constructor(str_val);
        let expanded_whnf = self.whnf_impl(&expanded);
        self.is_def_eq_impl(&expanded_whnf, s)
    }

    pub(in crate::tc::def_eq) fn is_def_eq_unit_like(&self, t: &Expr, s: &Expr) -> bool {
        // Lean 4 reference: type_checker.cpp:1129-1130 `is_def_eq_unit_like`.
        // Fall back to full inference when quick fails. Part of #3134.
        let Some(t_type) = self
            .try_infer_type_quick(t)
            .or_else(|| self.infer_type_infer_only(t).ok())
        else {
            return false;
        };
        let t_type_whnf = self.whnf_impl(&t_type);
        let ExprKind::Const(ind_name, _) = t_type_whnf.get_app_fn().kind() else {
            return false;
        };
        if !self.is_structure_like(ind_name) {
            return false;
        }
        let Some(ind) = self.env.get_inductive(ind_name) else {
            return false;
        };
        if ind.constructor_names.is_empty() {
            return false;
        }
        let ctor_name = &ind.constructor_names[0];
        let Some(ctor) = self.env.get_constructor(ctor_name) else {
            return false;
        };
        if ctor.num_fields != 0 {
            return false;
        }
        let Some(s_type) = self
            .try_infer_type_quick(s)
            .or_else(|| self.infer_type_infer_only(s).ok())
        else {
            return false;
        };
        self.is_def_eq_impl(&t_type_whnf, &self.whnf_impl(&s_type))
    }
}
