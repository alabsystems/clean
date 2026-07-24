// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Eta expansion and structure eta for definitional equality.
//!
//! Contains:
//! - `try_eta_expansion_impl` — lambda eta (λ x. f x ≡ f)
//! - `try_eta_struct` / `expand_eta_struct` — structure eta (s ≡ S.mk s.1 s.2)
//! - `is_structure_like` / `is_constructor_app` — structure predicates
//! - `open_bvar` — bound variable opening

use crate::expr::{BinderData, Expr, ExprKind, FVarId};
use crate::name::Name;
use crate::tc::TypeChecker;

impl<'env> TypeChecker<'env> {
    /// Try eta expansion to prove equality.
    ///
    /// Eta expansion: (λ x. f x) ≡ f when x does not appear free in f.
    ///
    /// This is called when we have `Lam(bi, ty, body)` vs `other`.
    /// We check if `other : Pi(bi, ty, result_type)`, and if so,
    /// we create a lambda wrapper around `other` and compare.
    ///
    /// Reference: Lean 4 kernel type_checker.cpp `try_eta_expansion_core`
    pub(super) fn try_eta_expansion_impl(
        &self,
        lam_expr: &Expr,
        other: &Expr,
        _bd: BinderData,
        _lam_ty: &Expr,
        _lam_body: &Expr,
    ) -> bool {
        // Get the type of `other` to see if it's a function type.
        // Lean 4 reference: type_checker.cpp:780 uses full `infer_type(s)`.
        // We try quick inference first for performance, then fall back to
        // full inference if quick fails. Without this fallback, eta expansion
        // fails for expressions whose types require full inference (e.g.,
        // complex App chains, Proj results). Part of #3134.
        let Some(other_type) = self
            .try_infer_type_quick(other)
            .or_else(|| self.infer_type_infer_only(other).ok())
        else {
            return false;
        };

        let other_type_whnf = self.whnf_impl(&other_type);

        match &other_type_whnf.kind {
            ExprKind::Pi(bi, pi_domain, _) => {
                // Lean 4 parity: wrap `other` in a matching lambda and then compare
                // the two lambda expressions via is_def_eq. This goes through
                // is_def_eq_binding which opens BVars to FVars, enabling proof
                // irrelevance on sub-expressions under the binder. The old approach
                // compared bodies directly with BVars, which broke proof irrelevance
                // because infer_type cannot type-check BVars.
                // Reference: Lean 4 type_checker.cpp try_eta_expansion_core
                let new_s = Expr::lam(
                    *bi,
                    pi_domain.as_ref().clone(),
                    Expr::app(other.lift_from(0, 1), Expr::bvar(0)),
                );
                self.is_def_eq_impl(lam_expr, &new_s)
            }
            _ => false,
        }
    }

    // ============================================================================
    // Structure Eta Expansion (#573)
    // ============================================================================
    // Lean 4 supports "structure eta expansion" during definitional equality checking,
    // allowing `s = Struct.mk s.1 s.2` to hold definitionally.
    // Reference: lean4/src/kernel/inductive.cpp:98-111, inductive.h:60-73

    /// Check if an inductive is "structure-like" (single constructor, no indices, not recursive).
    /// These support eta expansion: s ≡ S.mk s.1 s.2 ... s.n
    ///
    /// Reference: Lean 4 inductive.cpp:27-32 `is_structure_like`
    pub(super) fn is_structure_like(&self, name: &Name) -> bool {
        let Some(ind) = self.env.get_inductive(name) else {
            return false;
        };
        ind.constructor_names.len() == 1 && ind.num_indices == 0 && !ind.is_recursive
    }

    /// Check if `e` is a constructor application.
    pub(super) fn is_constructor_app(&self, e: &Expr) -> bool {
        let head = e.get_app_fn();
        if let ExprKind::Const(name, _) = &head.kind {
            return self.env.get_constructor(name).is_some();
        }
        false
    }

    /// Expand e to constructor form: S.mk e.0 e.1 ... e.n
    /// `e_type` is the WHNF'd type of `e` (must be of form `S params...`)
    ///
    /// Reference: Lean 4 inductive.cpp:98-111 `expand_eta_struct`
    pub(super) fn expand_eta_struct(&self, e_type: &Expr, e: &Expr) -> Option<Expr> {
        // Get the inductive name - check head before collecting args
        let type_head = e_type.get_app_fn();

        let ExprKind::Const(ind_name, levels) = &type_head.kind else {
            return None;
        };

        // Now collect args (after confirming head is Const)
        let type_args = e_type.get_app_args();

        // Get the constructor
        let ind = self.env.get_inductive(ind_name)?;
        if ind.constructor_names.len() != 1 {
            return None;
        }
        let ctor_name = &ind.constructor_names[0];
        let ctor = self.env.get_constructor(ctor_name)?;

        // Build: ctor params... (proj 0 e) (proj 1 e) ... (proj n e)
        let mut result = Expr::const_(ctor_name.clone(), levels.clone());

        // Apply parameters (first `num_params` of type_args)
        for i in 0..ctor.num_params as usize {
            result = Expr::app(result, (*type_args.get(i)?).clone());
        }

        // Apply projections for each field
        for field_idx in 0..ctor.num_fields {
            let proj = Expr::proj(ind_name.clone(), field_idx, e.clone());
            result = Expr::app(result, proj);
        }

        Some(result)
    }

    /// Try structure eta expansion: convert `e` to `S.mk e.0 e.1 ... e.n`
    /// Called during def-eq when comparing structure values.
    ///
    /// Reference: Lean 4 inductive.h:60-73 `to_cnstr_when_structure`
    pub(super) fn try_eta_struct(&self, ind_name: &Name, e: &Expr) -> Option<Expr> {
        // Guard 1: Must be structure-like
        if !self.is_structure_like(ind_name) {
            return None;
        }

        // Guard 2: Already a constructor application - no expansion needed
        if self.is_constructor_app(e) {
            return None;
        }

        // Get the type of e.
        // Lean 4 reference: type_checker.cpp:801 uses full `infer_type`.
        // Fall back to full inference when quick fails. Part of #3134.
        let e_type_raw = self
            .try_infer_type_quick(e)
            .or_else(|| self.infer_type_infer_only(e).ok())?;
        let e_type = self.whnf_impl(&e_type_raw);

        self.try_eta_struct_core(ind_name, e, &e_type)
    }

    /// Core logic for structure eta expansion (recursor-major conversion;
    /// def-eq structure eta lives in `def_eq/structural.rs` and uses Lean's
    /// fieldwise `try_eta_struct_core` algorithm instead).
    fn try_eta_struct_core(&self, ind_name: &Name, e: &Expr, e_type_whnf: &Expr) -> Option<Expr> {
        // Guard 3: Type head must match the inductive
        let type_head = e_type_whnf.get_app_fn();
        let ExprKind::Const(type_name, _) = &type_head.kind else {
            return None;
        };
        if type_name != ind_name {
            return None;
        }

        // Guard 4: Not for Prop-typed structures (avoid duplicating proof terms).
        // Fall back to full inference when quick fails. Part of #3134.
        let type_of_type_raw = self
            .try_infer_type_quick(e_type_whnf)
            .or_else(|| self.infer_type_infer_only(e_type_whnf).ok())?;
        let type_of_type = self.whnf_impl(&type_of_type_raw);
        if type_of_type.is_prop() {
            return None;
        }

        self.expand_eta_struct(e_type_whnf, e)
    }

    /// Lift an expression by increasing all free de Bruijn indices >= cutoff by amount.
    /// Delegates to Expr::lift_from which is sharing-preserving (#1326 Phase 2b).
    #[cfg(test)]
    pub(super) fn lift_expr(&self, e: &Expr, cutoff: u32, amount: u32) -> Expr {
        e.lift_from(cutoff, amount)
    }

    /// Replace BVar(0) with FVar(id) in an expression
    pub(super) fn open_bvar(&self, e: &Expr, id: FVarId) -> Expr {
        e.instantiate(&Expr::from_kind(ExprKind::FVar(id)))
    }
}
