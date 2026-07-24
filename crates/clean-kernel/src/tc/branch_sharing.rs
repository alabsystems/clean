// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Branch-sharing WHNF cache for recursor congruence in definitional equality.
//!
//! When two `is_def_eq` inputs are applications of the same recursor, most of
//! the work is usually in the shared parameters, motive, and branch bodies.
//! This module memoizes no-delta WHNF results by expression hash so repeated
//! branch comparisons can reuse reductions of common prefixes.
//!
//! ## Prefix factoring (#3402)
//!
//! Case splits like `semBinOp` matching on two `Value` arguments (7x7 = 49
//! branches) produce minor premise lambdas whose bodies share a common prefix
//! of monadic binds before the first divergence point. The prefix-factoring
//! optimization detects this: when comparing minor premise pairs, it walks
//! into lambda bodies and compares the App-spine arguments left-to-right,
//! recording verified-equal hashes. Subsequent branch comparisons skip
//! arguments whose hashes match previously verified pairs.

use crate::expr::{Expr, ExprKind};
use crate::inductive::RecursorArgOrder;
use crate::name::Name;
use crate::tc::{TcHashMap, TypeChecker};
use std::ops::Range;

/// WHNF cache plus a set of expression pairs known to be def-eq.
///
/// BOTH maps are keyed on full `Expr` structural equality, not just cached
/// hashes. `Expr::hash` is O(1) via a cached 32-bit hash, but `Expr::eq`
/// falls back to structural comparison on hash collision, so lookups are
/// O(1) amortized AND collision-safe.
///
/// SOUNDNESS/COMPLETENESS (fix): `entries` (the no-delta WHNF memo) was
/// previously keyed on the raw 32-bit `hash_cached()` with NO structural
/// verification. On large terms (tens of thousands of subexpressions) a
/// 32-bit hash collision made `branch_sharing_whnf` return the WRONG reduced
/// expression, so `branch_sharing_compare` (and hence the same-const-head
/// arm of `is_def_eq_app_spine`) could return a wrong verdict — usually a
/// spurious `false` on genuinely def-eq arguments (completeness loss:
/// `LieDerivation.ofGradingSum._proof_4`'s `SMulCommClass` congruence), but
/// in principle a wrong `true` as well. Keying by `Expr` matches the
/// collision-safe policy of every other TC cache (`whnf_core_cache`,
/// `def_eq_cache`) and keeps the same amortized O(1) cost.
#[derive(Default)]
pub(super) struct BranchSharingCache {
    entries: TcHashMap<Expr, Expr>,
    verified_pairs: TcHashMap<(Expr, Expr), ()>,
}

impl BranchSharingCache {
    fn get(&self, key: &Expr) -> Option<Expr> {
        self.entries.get(key).cloned()
    }

    fn contains(&self, key: &Expr) -> bool {
        self.entries.contains_key(key)
    }

    fn insert(&mut self, key: Expr, value: Expr) {
        self.entries.insert(key, value);
    }

    pub(super) fn clear(&mut self) {
        self.entries.clear();
        self.verified_pairs.clear();
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    #[cfg(any(debug_assertions, test))]
    pub(super) fn verified_pair_count(&self) -> usize {
        self.verified_pairs.len()
    }

    fn is_verified_pair(&self, a: &Expr, b: &Expr) -> bool {
        // `record_verified_pair` always stores in canonical (smaller-hash-first)
        // order, so probing that same canonical key is sufficient — one lookup
        // and two clones instead of two-and-four. For distinct hashes this is
        // identical to probing both orders; the only divergence is a genuine
        // 32-bit hash collision queried in swapped order, which merely forces a
        // sound def-eq recompute (a memo miss, never a wrong verdict).
        let key = if a.hash_cached() <= b.hash_cached() {
            (a.clone(), b.clone())
        } else {
            (b.clone(), a.clone())
        };
        self.verified_pairs.contains_key(&key)
    }

    fn record_verified_pair(&mut self, a: &Expr, b: &Expr) {
        let (lhs, rhs) = if a.hash_cached() <= b.hash_cached() {
            (a.clone(), b.clone())
        } else {
            (b.clone(), a.clone())
        };
        self.verified_pairs.insert((lhs, rhs), ());
    }
}

struct RecursorApp<'a> {
    name: &'a Name,
    levels: &'a [crate::level::Level],
    arg_order: RecursorArgOrder,
    num_params: usize,
    num_indices: usize,
    num_motives: usize,
    num_minors: usize,
    args: crate::expr::AppArgs<'a>,
}

impl<'a> RecursorApp<'a> {
    fn args_before_major(&self) -> usize {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                self.num_params + self.num_motives + self.num_minors + self.num_indices
            }
            RecursorArgOrder::MajorAfterMotive => {
                self.num_params + self.num_motives + self.num_indices
            }
        }
    }

    fn required_args(&self) -> usize {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => self.args_before_major() + 1,
            RecursorArgOrder::MajorAfterMotive => self.args_before_major() + 1 + self.num_minors,
        }
    }

    fn params_range(&self) -> Range<usize> {
        0..self.num_params
    }

    fn motives_range(&self) -> Range<usize> {
        let start = self.params_range().end;
        start..start + self.num_motives
    }

    fn indices_range(&self) -> Range<usize> {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                let start = self.minors_range().end;
                start..start + self.num_indices
            }
            RecursorArgOrder::MajorAfterMotive => {
                let start = self.motives_range().end;
                start..start + self.num_indices
            }
        }
    }

    fn major_idx(&self) -> usize {
        self.args_before_major()
    }

    fn minors_range(&self) -> Range<usize> {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                let start = self.motives_range().end;
                start..start + self.num_minors
            }
            RecursorArgOrder::MajorAfterMotive => {
                let start = self.major_idx() + 1;
                start..start + self.num_minors
            }
        }
    }

    fn extras_range(&self) -> Range<usize> {
        let start = match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => self.major_idx() + 1,
            RecursorArgOrder::MajorAfterMotive => self.minors_range().end,
        };
        start..self.args.len()
    }
}

impl<'env> TypeChecker<'env> {
    /// Test-only: number of expression pairs currently in the verified-pair
    /// set. Used by regression tests to confirm the cache is being populated
    /// by comparisons that exercise the branch-sharing path.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn branch_sharing_verified_pair_count(&self) -> usize {
        self.branch_sharing_cache
            .as_ref()
            .map(|cache| cache.borrow().verified_pair_count())
            .unwrap_or(0)
    }

    fn with_branch_sharing_cache<R>(
        &self,
        f: impl FnOnce(&mut BranchSharingCache) -> R,
    ) -> Option<R> {
        let cache = self.branch_sharing_cache.as_ref()?;
        Some(f(&mut cache.borrow_mut()))
    }

    fn cache_branch_sharing_whnf(&self, expr: &Expr) {
        let Some(cache_cell) = self.branch_sharing_cache.as_ref() else {
            return;
        };

        let mut stack = vec![expr];
        while let Some(curr) = stack.pop() {
            if cache_cell.borrow().contains(curr) {
                continue;
            }

            let reduced = self.whnf_core_no_delta(curr, true);
            {
                let mut cache = cache_cell.borrow_mut();
                if cache.len() >= self.max_cache_entries {
                    cache.clear();
                }
                cache.insert(curr.clone(), reduced);
            }

            match curr.kind() {
                ExprKind::App(f, a) => {
                    stack.push(f);
                    stack.push(a);
                }
                ExprKind::Lam(_, ty, body)
                | ExprKind::Pi(_, ty, body)
                | ExprKind::Let(_, ty, _, body, _) => {
                    stack.push(ty);
                    stack.push(body);
                    if let ExprKind::Let(_, _, val, _, _) = curr.kind() {
                        stack.push(val);
                    }
                }
                ExprKind::Proj(_, _, target) | ExprKind::MData(_, target) => stack.push(target),
                ExprKind::Squash(ty) => stack.push(ty),
                ExprKind::CubicalPath { ty, left, right } => {
                    stack.push(ty);
                    stack.push(left);
                    stack.push(right);
                }
                ExprKind::CubicalPathLam { body } => stack.push(body),
                ExprKind::CubicalPathApp { path, arg } => {
                    stack.push(path);
                    stack.push(arg);
                }
                ExprKind::CubicalHComp { ty, phi, u, base } => {
                    stack.push(ty);
                    stack.push(phi);
                    stack.push(u);
                    stack.push(base);
                }
                _ => {}
            }
        }
    }

    fn branch_sharing_whnf(&self, expr: &Expr) -> Expr {
        if let Some(cached) = self
            .branch_sharing_cache
            .as_ref()
            .and_then(|cache| cache.borrow().get(expr))
        {
            return cached;
        }

        let reduced = self.whnf_core_no_delta(expr, true);
        let _ = self.with_branch_sharing_cache(|cache| {
            if cache.len() >= self.max_cache_entries {
                cache.clear();
            }
            cache.insert(expr.clone(), reduced.clone());
        });
        reduced
    }

    /// Compare two expressions using the branch-sharing WHNF cache.
    ///
    /// Pre-caches no-delta WHNF results; checks verified-pair set first for
    /// O(1) hit. Used by `try_branch_sharing_def_eq` and
    /// `is_def_eq_app_spine` (same-Const head). (#3402)
    ///
    /// SOUNDNESS (#3402 audit, 2026-04-18): (1) record-on-success only,
    /// (2) `(Expr, Expr)` keys via full `Expr::eq` — hash-collision safe,
    /// (3) per-TC scope cleared on commit/rollback, (4) context-free on
    /// closed subterms; lambda bodies gated by `compare_lambda_binder_types`.
    pub(super) fn branch_sharing_compare(&self, a: &Expr, b: &Expr) -> bool {
        // O(1) check: was this exact pair already verified in a prior branch?
        if let Some(cache_cell) = self.branch_sharing_cache.as_ref() {
            if cache_cell.borrow().is_verified_pair(a, b) {
                return true;
            }
        }

        self.cache_branch_sharing_whnf(a);
        self.cache_branch_sharing_whnf(b);

        let a_n = self.branch_sharing_whnf(a);
        let b_n = self.branch_sharing_whnf(b);
        let result = if a_n == b_n {
            true
        } else {
            self.is_def_eq_impl(&a_n, &b_n)
        };

        // Record verified pair so subsequent branches skip this comparison.
        if result {
            if let Some(cache_cell) = self.branch_sharing_cache.as_ref() {
                let mut cache = cache_cell.borrow_mut();
                cache.record_verified_pair(a, b);
            }
        }

        result
    }

    /// Compare two lambda-bodied minor premises with prefix factoring.
    ///
    /// Walks into matching lambda binders and compares bodies using the
    /// App-spine left-to-right strategy. When both bodies are applications
    /// with the same function head, compares arguments left-to-right,
    /// recording verified pairs. Subsequent calls with different lambdas
    /// that share the same prefix structure skip already-verified arguments.
    ///
    /// Falls back to `branch_sharing_compare` when the lambdas don't have
    /// matching binder structure or non-App bodies.
    pub(super) fn branch_sharing_compare_lambdas(&self, a: &Expr, b: &Expr) -> bool {
        // Peel matching lambda binders to reach the bodies.
        let (a_body, b_body) = peel_matching_lambdas(a, b);

        // If we couldn't peel any lambdas (or peeled to non-App bodies),
        // fall back to the general comparison.
        if !a_body.is_app() || !b_body.is_app() {
            return self.branch_sharing_compare(a, b);
        }

        let a_head = a_body.get_app_fn();
        let b_head = b_body.get_app_fn();

        // Only use prefix-factored comparison when both heads are the same Const.
        if !self.heads_are_same_const(a_head, b_head) {
            return self.branch_sharing_compare(a, b);
        }

        let a_args = a_body.get_app_args();
        let b_args = b_body.get_app_args();

        if a_args.len() != b_args.len() {
            return self.branch_sharing_compare(a, b);
        }

        // Compare the outer lambda structure first (binder types).
        if !self.compare_lambda_binder_types(a, b) {
            return false;
        }

        // Compare head
        if !self.branch_sharing_compare(a_head, b_head) {
            return false;
        }

        // Compare arguments left-to-right with verified-pair shortcutting.
        for (ai, bi) in a_args.iter().zip(b_args.iter()) {
            if !self.branch_sharing_compare(ai, bi) {
                return false;
            }
        }

        true
    }

    /// Compare only the binder types of two lambda chains.
    /// Returns true if the lambda binder types match (or both are non-lambdas).
    fn compare_lambda_binder_types(&self, a: &Expr, b: &Expr) -> bool {
        let mut a_cur = a;
        let mut b_cur = b;
        loop {
            match (a_cur.kind(), b_cur.kind()) {
                (ExprKind::Lam(_, ty_a, body_a), ExprKind::Lam(_, ty_b, body_b)) => {
                    if !self.branch_sharing_compare(ty_a, ty_b) {
                        return false;
                    }
                    a_cur = body_a;
                    b_cur = body_b;
                }
                _ => return true,
            }
        }
    }

    fn as_recursor_app<'a>(&self, expr: &'a Expr) -> Option<RecursorApp<'a>> {
        let ExprKind::Const(name, levels) = expr.get_app_fn().kind() else {
            return None;
        };
        let recursor = self.env.get_recursor(name)?;
        let app = RecursorApp {
            name,
            levels,
            arg_order: recursor.arg_order,
            num_params: recursor.num_params as usize,
            num_indices: recursor.num_indices as usize,
            num_motives: recursor.num_motives as usize,
            num_minors: recursor.num_minors as usize,
            args: expr.get_app_args(),
        };
        (app.args.len() >= app.required_args()).then_some(app)
    }

    fn compare_arg_range(&self, a_args: &[&Expr], b_args: &[&Expr], range: Range<usize>) -> bool {
        for idx in range {
            if !self.branch_sharing_compare(a_args[idx], b_args[idx]) {
                return false;
            }
        }
        true
    }

    /// Compare minor premise argument pairs using prefix-factored lambda
    /// comparison. Minor premises in case splits are typically lambdas whose
    /// bodies share a common monadic-bind prefix. Using the lambda-aware
    /// comparison, the first minor pair verifies the prefix and records all
    /// sub-expression pairs; subsequent minors skip verified pairs in O(1).
    fn compare_minors_range(
        &self,
        a_args: &[&Expr],
        b_args: &[&Expr],
        range: Range<usize>,
    ) -> bool {
        for idx in range {
            if !self.branch_sharing_compare_lambdas(a_args[idx], b_args[idx]) {
                return false;
            }
        }
        true
    }

    /// Compare two recursor applications using cached no-delta WHNFs for the
    /// shared parameters, motive, and minor premises.
    ///
    /// Minor premises use prefix-factored lambda comparison: the first minor
    /// pair comparison verifies and records the shared prefix, subsequent
    /// minors skip already-verified sub-expressions via the verified_pairs set.
    ///
    /// Returns `None` when either expression is not a recursor application or
    /// when their heads differ. Returns `Some(false)` on a definite mismatch.
    pub(super) fn try_branch_sharing_def_eq(&self, a: &Expr, b: &Expr) -> Option<bool> {
        let a_app = self.as_recursor_app(a)?;
        let b_app = self.as_recursor_app(b)?;

        // SOUNDNESS / completeness: this is a recursor-CONGRUENCE fast path. It may
        // only *assert equality* (`Some(true)`) when every component matches, or
        // *defer* (`None`). It must NEVER assert inequality (`Some(false)`): two
        // recursor applications whose args differ structurally can still ι-reduce
        // to definitionally-equal results — e.g. `applySubst σ1 f1` vs
        // `applySubst σ2 f2` unfold to `List.rec` applications with DIFFERENT
        // majors/minors yet reduce to the same list. Returning `Some(false)` here
        // short-circuits that ι reduction and yields a def-eq false-negative
        // (observed: kernel-checking Metamath proofs with large `applySubst`
        // terms). Deferring with `None` hands those pairs to the lazy-delta/ι path,
        // which decides correctly. This only makes `is_def_eq` MORE complete (it
        // never introduces a false positive — ι still does the real work).
        if a_app.name != b_app.name {
            return None;
        }
        if a_app.args.len() != b_app.args.len() {
            return None;
        }
        if a_app.levels.len() != b_app.levels.len() {
            return None;
        }
        if !a_app
            .levels
            .iter()
            .zip(b_app.levels.iter())
            .all(|(lhs, rhs)| self.levels_eq(lhs, rhs))
        {
            return None;
        }

        let shared_prefix_end = a_app.motives_range().end;
        if !self.compare_arg_range(&a_app.args, &b_app.args, 0..shared_prefix_end) {
            return None;
        }
        if !self.compare_arg_range(&a_app.args, &b_app.args, a_app.indices_range()) {
            return None;
        }
        if !self
            .branch_sharing_compare(a_app.args[a_app.major_idx()], b_app.args[b_app.major_idx()])
        {
            return None;
        }
        // Minor premises use lambda-aware prefix-factored comparison.
        if !self.compare_minors_range(&a_app.args, &b_app.args, a_app.minors_range()) {
            return None;
        }
        if !self.compare_arg_range(&a_app.args, &b_app.args, a_app.extras_range()) {
            return None;
        }

        Some(true)
    }
}

/// Walk into matching lambda binders and return the innermost bodies.
/// Stops when the binder structure diverges (different ExprKind, or
/// one side is a lambda while the other is not).
fn peel_matching_lambdas<'a>(a: &'a Expr, b: &'a Expr) -> (&'a Expr, &'a Expr) {
    let mut a_cur = a;
    let mut b_cur = b;
    loop {
        match (a_cur.kind(), b_cur.kind()) {
            (ExprKind::Lam(_, _, body_a), ExprKind::Lam(_, _, body_b)) => {
                a_cur = body_a;
                b_cur = body_b;
            }
            _ => return (a_cur, b_cur),
        }
    }
}
