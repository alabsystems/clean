// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::expr::{stack_safe, Expr, ExprKind};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;
use crate::tc::TypeChecker;
use std::sync::LazyLock;

static NAME_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static NAME_STRING: LazyLock<Name> = LazyLock::new(|| Name::from_string("String"));

impl<'env> TypeChecker<'env> {
    pub(in crate::tc) fn is_def_eq_proof_irrel(&self, a: &Expr, b: &Expr) -> Option<bool> {
        // SOUNDNESS (cubical / univalent layer): definitional proof irrelevance
        // collapses *all* proofs of a `Prop` to be definitionally equal. The
        // cubical path type `Path A a b` lives in `Sort l` where `l` is `A`'s
        // level, so whenever a path family lands in `Prop` (`Sort 0`), proof
        // irrelevance would identify any two paths `p, q : Path A a b` — i.e.
        // it would derive Uniqueness of Identity Proofs (axiom K). UIP is
        // provably *inconsistent with univalence* (HoTT Book §; see
        // docs/vision/clean-univalent-directed-foundations.md §2.3). The fibrant
        // (Cubical) layer must therefore NOT use definitional proof irrelevance;
        // path equality is proof-relevant and higher-dimensional. Returning
        // `None` here only ever makes def-eq *more* conservative (it can no
        // longer conclude `a ≡ b` from "their type is a Prop"), so this is
        // strictly sound. Classical / impredicative / set-theoretic modes keep
        // proof irrelevance exactly as before.
        //
        // The Directed (Rung 2) layer is built atop the same fibrant foundation
        // (directed/simplicial HoTT extends HoTT), so it likewise must NOT use
        // definitional proof irrelevance / UIP — same soundness argument, and
        // again only ever more conservative.
        if self.mode == CleanMode::Cubical || self.mode == CleanMode::Directed {
            return None;
        }
        let ty_a = self.infer_type_quick_or_full(a)?;
        // Fast path: if ty_a is quickly known to NOT be in Prop, skip the
        // expensive type_is_proof_irrelevant check entirely. Most expressions
        // in the lazy delta loop are data terms (Nat, Bool, List, etc.) whose
        // types are in Type 0+, not Prop. This avoids redundant infer_type +
        // whnf calls on every iteration of the hot delta loop.
        if self.type_is_quickly_not_in_prop(&ty_a) {
            return None;
        }
        if !self.type_is_proof_irrelevant(&ty_a)? {
            return None;
        }
        let ty_b = self.infer_type_quick_or_full(b)?;
        Some(self.is_def_eq_impl(&ty_a, &ty_b))
    }

    #[cfg(test)]
    pub(in crate::tc) fn reset_proof_irrel_fallback_infer_count_for_tests(&self) {
        super::PROOF_IRREL_FALLBACK_INFER_COUNT.with(|count| count.set(0));
    }

    #[cfg(test)]
    pub(in crate::tc) fn proof_irrel_fallback_infer_count_for_tests(&self) -> u64 {
        super::PROOF_IRREL_FALLBACK_INFER_COUNT.with(|count| count.get())
    }

    fn infer_type_quick_or_full(&self, e: &Expr) -> Option<Expr> {
        if let Some(ty) = self.try_infer_type_quick(e) {
            return Some(ty);
        }
        #[cfg(test)]
        super::PROOF_IRREL_FALLBACK_INFER_COUNT
            .with(|count| count.set(count.get().saturating_add(1)));
        self.infer_type_infer_only(e).ok()
    }

    fn type_is_proof_irrelevant(&self, ty: &Expr) -> Option<bool> {
        let ty_whnf = self.whnf_impl(ty);
        // Quick rejection: if ty reduces to a Sort, its type is Sort(succ(l))
        // which is never Sort(0)/Prop. Skip the expensive infer_type + whnf chain.
        if matches!(ty_whnf.kind(), ExprKind::Sort(_)) {
            return Some(false);
        }
        let ty_of_ty = self.infer_type_quick_or_full(&ty_whnf)?;
        let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty);
        Some(
            matches!(ty_of_ty_whnf.kind(), ExprKind::Sort(l) if l.is_zero())
                || matches!(ty_of_ty_whnf.kind(), ExprKind::SProp),
        )
    }

    /// Cheaply determine if a type is definitely NOT in Prop.
    ///
    /// Returns `true` when we can syntactically determine that `ty` lives in
    /// `Type u` (u >= 1) or is otherwise clearly not a proposition, without
    /// any `infer_type` or `whnf` calls. Returns `false` when uncertain
    /// (the caller must fall through to the full `type_is_proof_irrelevant`).
    ///
    /// This is a pure pre-filter: returning `false` is always safe (just means
    /// "I don't know, do the full check"). Returning `true` incorrectly would
    /// be unsound (could miss proof irrelevance), so we are conservative.
    ///
    /// Key insight: most expressions in the lazy delta loop are data terms
    /// (Nat, Bool, List values, etc.) whose types are in `Type 0`, not `Prop`.
    /// Catching these cheaply avoids the expensive `whnf + infer_type + whnf`
    /// chain in `type_is_proof_irrelevant`.
    fn type_is_quickly_not_in_prop(&self, ty: &Expr) -> bool {
        match ty.kind() {
            // Sort(l) : Sort(succ(l)) — always in a Sort above Prop.
            ExprKind::Sort(_) => true,
            // Literal types: Nat and String are both in Type 0, not Prop.
            ExprKind::Const(name, levels) if levels.is_empty() => {
                *name == *NAME_NAT || *name == *NAME_STRING
            }
            _ => false,
        }
    }

    pub(in crate::tc) fn try_infer_type_quick(&self, e: &Expr) -> Option<Expr> {
        // Lean 4 parity: the kernel caches EVERY infer_type result for the
        // lifetime of the declaration check (`m_infer_type`, type_checker.h:30).
        // The proof-irrelevance check runs quick inference on both sides of
        // every is_def_eq_core pair, so without this cache each subterm of a
        // nested-rewrite proof is re-inferred once per ancestor path —
        // quadratic in term size (the Lean.Omega.tidy_sat heartbeat wall).
        // Only successful inferences are cached; a `None` falls through to
        // full inference at the call site, which has its own caching.
        if let Some(cached) = self.quick_infer_cache.borrow_mut().get(e) {
            return Some(cached);
        }
        let result = stack_safe(|| self.try_infer_type_quick_inner(e));
        debug_assert!(
            e.has_loose_bvars_quick()
                || result.as_ref().is_none_or(|ty| !ty.has_loose_bvars_quick()),
            "try_infer_type_quick returned type with escaping BVars: {:?} for closed expr: {:?}",
            result,
            e
        );
        if let Some(ref ty) = result {
            let mut cache = self.quick_infer_cache.borrow_mut();
            cache.trim_if_needed(self.max_cache_entries);
            cache.insert(e.clone(), ty.clone());
        }
        result
    }

    fn try_infer_type_quick_inner(&self, e: &Expr) -> Option<Expr> {
        match e.kind() {
            ExprKind::FVar(id) => self.ctx.borrow().get(*id).map(|d| d.type_.clone()),
            ExprKind::Const(name, levels) => self.env.instantiate_type(name, levels),
            ExprKind::Sort(l) => Some(Expr::from_kind(ExprKind::Sort(Level::succ(l.clone())))),
            ExprKind::App(f, a) => {
                let f_type = self.try_infer_type_quick(f)?;
                let f_type_whnf = self.whnf_impl(&f_type);
                match f_type_whnf.kind() {
                    ExprKind::Pi(_, _, result_type) => Some(result_type.instantiate(a)),
                    _ => None,
                }
            }
            ExprKind::Lam(bi, ty, body) => {
                let body_type = self.try_infer_type_quick(body)?;
                Some(Expr::pi(*bi, ty.as_ref().clone(), body_type))
            }
            ExprKind::Lit(lit) => Some(match lit {
                crate::expr::Literal::Nat(_) => Expr::const_(NAME_NAT.clone(), vec![]),
                crate::expr::Literal::String(_) => Expr::const_(NAME_STRING.clone(), vec![]),
            }),
            ExprKind::MData(_, inner) => self.try_infer_type_quick(inner),
            ExprKind::Squash(inner) => {
                if self.mode != CleanMode::Impredicative
                    && self.mode != CleanMode::Classical
                    && self.mode != CleanMode::SetTheoretic
                {
                    return None;
                }
                let inner_ty = self.try_infer_type_quick(inner)?;
                let inner_ty_whnf = self.whnf_impl(&inner_ty);
                if !matches!(inner_ty_whnf.kind(), ExprKind::Sort(_)) {
                    return None;
                }
                Some(Expr::from_kind(ExprKind::SProp))
            }
            ExprKind::Proj(struct_name, idx, expr) => {
                let expr_type = self.try_infer_type_quick(expr)?;
                self.infer_proj_type_from_quick(struct_name, *idx, expr, &expr_type)
            }
            _ => None,
        }
    }

    #[cfg(test)]
    pub(in crate::tc) fn is_type_in_prop(&self, ty: &Expr) -> bool {
        let ty_whnf = self.whnf_impl(ty);
        self.try_infer_type_quick(&ty_whnf).is_some_and(|ty_of_ty| {
            let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty);
            matches!(ty_of_ty_whnf.kind(), ExprKind::Sort(l) if l.is_zero())
        })
    }
}
