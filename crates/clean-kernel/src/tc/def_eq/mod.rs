// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional equality for the clean kernel type checker.
//!
//! Core algorithm here; lazy delta-reduction in `delta` submodule.
//! Key: `is_def_eq` (public), `is_def_eq_core` (8-phase), `quick_is_def_eq`,
//! `DefEqCacheKey` (unordered pair cache), `is_def_eq_proof_irrel`.

mod binding;
mod cubical;
mod delta;
mod delta_helpers;
mod proof_irrel;
mod structural;
mod template_cumul;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_branch_sharing_cache;
#[cfg(test)]
mod tests_delta;
#[cfg(test)]
mod tests_delta_ordering;
#[cfg(test)]
mod tests_reduce_bool_nat;
#[cfg(test)]
mod tests_struct_eta_app;
#[cfg(test)]
mod tests_template_cumul;
#[cfg(test)]
mod tests_trace;
#[cfg(test)]
mod tests_ws15_struct_field_count;

use crate::env::TransparencyMode;
use crate::expr::{stack_safe, Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;
#[cfg(test)]
use std::cell::Cell;
use std::hash::{Hash, Hasher};
use std::sync::LazyLock;

static BOOL_TRUE_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));

#[cfg(test)]
thread_local! {
    static PROOF_IRREL_FALLBACK_INFER_COUNT: Cell<u64> = const { Cell::new(0) };
}

#[inline(always)]
fn is_bool_true_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, levels) if levels.is_empty() && *name == *BOOL_TRUE_NAME)
}

/// Cache key for def_eq using structural hash.
///
/// Uses structural hashing of expression content to avoid pointer-identity
/// issues with stack temporaries. This is correct because:
///
/// 1. Expressions are immutable once created
/// 2. Structurally equal expressions produce the same hash
/// 3. No dependence on pointer lifetime or stack reuse
///
/// # Performance
///
/// - Hash: O(1) cached hash via expression metadata (computed once at creation)
/// - Eq: O(1) hash pre-filter rejects most mismatches; O(n) structural fallback
///
/// # Correctness (Fixes #957)
///
/// Previous implementation used raw pointers which could collide when
/// stack temporaries were cached and later addresses were reused. See
/// reports/research/2026-02-02-defeq-cache-audit.md for analysis.
///
/// Structural hashing avoids this by not depending on memory addresses.
/// Structurally equal expressions now produce cache hits regardless of
/// their memory location.
///
/// # Unordered Pair Semantics (Fixes #968)
///
/// The key represents an unordered pair {a, b}. Since def_eq is symmetric,
/// is_def_eq(a,b) and is_def_eq(b,a) must share the same cache entry.
///
/// We achieve this by:
/// 1. Using hash-based ordering for canonical construction (not pointers)
/// 2. Implementing Hash to combine hashes commutatively (min/max)
/// 3. Implementing Eq to compare as unordered pairs
#[derive(Clone)]
pub(crate) struct DefEqCacheKey {
    /// First expression (cloned for structural comparison)
    a: Expr,
    /// Second expression (cloned for structural comparison)
    b: Expr,
    /// Transparency mode under which this def-eq result was computed.
    /// Different transparency levels can yield different results (e.g., an
    /// `@[irreducible]` def unfolds under `All` but not `Default`), so
    /// the cache must distinguish them. Part of #1636.
    transparency: TransparencyMode,
}

impl DefEqCacheKey {
    /// Create a cache key from expression references and transparency mode.
    ///
    /// Clones expressions to store structural content, avoiding pointer
    /// lifetime issues. Uses hash-based ordering for canonical key construction:
    /// the expression with the smaller hash goes in `a`.
    ///
    /// Hash-based ordering is deterministic and structural, unlike pointer
    /// ordering which fails when structurally equal expressions are at
    /// different memory addresses (see #968).
    ///
    /// Uses O(1) cached hash from expression metadata instead of recomputing.
    pub(super) fn new(a: &Expr, b: &Expr, transparency: TransparencyMode) -> Self {
        let a_hash = a.hash_cached();
        let b_hash = b.hash_cached();

        // Canonical ordering: smaller hash first
        // On hash collision, order doesn't matter since Eq handles both orderings
        if a_hash <= b_hash {
            Self {
                a: a.clone(),
                b: b.clone(),
                transparency,
            }
        } else {
            Self {
                a: b.clone(),
                b: a.clone(),
                transparency,
            }
        }
    }
}

impl PartialEq for DefEqCacheKey {
    /// Unordered pair equality: {a, b, tm} == {c, d, tm2} iff tm==tm2 && ({a,b}=={c,d})
    fn eq(&self, other: &Self) -> bool {
        self.transparency == other.transparency
            && ((self.a == other.a && self.b == other.b)
                || (self.a == other.b && self.b == other.a))
    }
}

impl Eq for DefEqCacheKey {}

impl Hash for DefEqCacheKey {
    /// Commutative hash: H({a,b,tm}) == H({b,a,tm})
    ///
    /// Uses min/max of O(1) cached hashes for commutative combination.
    /// Previous XOR-based approach collapsed to 0 for reflexive pairs
    /// (a ^ a == 0), causing all self-comparisons that reach the cache
    /// to collide in the same bucket — O(n) linear probing. See #1774.
    ///
    /// min/max is commutative (min(a,b) == min(b,a)) and does not degenerate
    /// for equal inputs: when a == b, we get (a, a) which is just as distributed
    /// as the inputs themselves.
    fn hash<H: Hasher>(&self, state: &mut H) {
        let a_hash = self.a.hash_cached();
        let b_hash = self.b.hash_cached();
        // Commutative: min/max are order-independent
        std::cmp::min(a_hash, b_hash).hash(state);
        std::cmp::max(a_hash, b_hash).hash(state);
        self.transparency.hash(state);
    }
}

impl<'env> TypeChecker<'env> {
    /// Check definitional equality (beta, delta, proof irrelevance, eta).
    ///
    /// # Contract
    ///
    /// REQUIRES: All FVars in `a` and `b` are defined in `self.ctx`
    /// REQUIRES: All Consts in `a` and `b` are defined in `self.env`
    /// ENSURES: Reflexive, Symmetric, Transitive, Deterministic
    /// ENSURES: Terminates for well-typed input
    pub fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool {
        // No stack_safe here — is_def_eq_impl already wraps its inner call
        // in stack_safe, and all recursive paths go through is_def_eq_impl.
        let result = self.is_def_eq_impl(a, b);
        // Record positive results in the equiv_manager for cross-call
        // amortization. Lean 4 reference: type_checker.cpp:1138.
        // Sliding window eviction retains previous generation on trim (#2410).
        if result {
            let mut em = self.equiv_manager.borrow_mut();
            em.trim_if_needed(self.max_cache_entries);
            em.add_equiv(a, b);
        }
        result
    }

    /// Cumulative subtyping check: `a ≤ b` under Coq/pCIC cumulativity.
    ///
    /// Used ONLY at type-ascription points (application argument, `let` value,
    /// and `check_type`) and ONLY when `self.cumulative` is set (the Coq
    /// verification lane). When `cumulative` is `false` this is exactly
    /// `is_def_eq`, so the Lean-faithful non-cumulative path is unchanged.
    ///
    /// Rules (pCIC):
    /// - `Sort i ≤ Sort j`  iff  `i ≤ j`  (`Prop 0 ≤ Set 1 ≤ Type k`).
    /// - `Π(x:A) B ≤ Π(x:A') B'`  iff  `A =def A'` (domain INVARIANT) and
    ///   `B ≤ B'` (codomain COVARIANT).
    /// - otherwise fall back to `is_def_eq` (symmetric equality implies `≤`).
    ///
    /// SOUNDNESS: cumulativity is a sound rule of pCIC. `is_le` only accepts
    /// additional terms that are genuinely well-typed under Coq's type theory,
    /// is gated to the Coq lane (`cumulative == true`), and never weakens the
    /// Lean default (`cumulative == false` ⇒ identical to `is_def_eq`).
    /// Tracking: #3300.
    pub fn is_le(&self, a: &Expr, b: &Expr) -> bool {
        if !self.cumulative {
            return self.is_def_eq(a, b);
        }
        // Symmetric definitional equality implies subtyping, and it performs all
        // the reduction/unification work, so try it first.
        if self.is_def_eq(a, b) {
            return true;
        }
        // Only sorts and products are related by strict cumulativity; expose the
        // head via weak-head normalization, then apply the covariant rules.
        let a_w = self.whnf(a);
        let b_w = self.whnf(b);
        match (a_w.kind(), b_w.kind()) {
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => crate::level::Level::leq(l1, l2),
            (ExprKind::Pi(_, d1, c1), ExprKind::Pi(bi2, d2, c2)) => {
                // Domain INVARIANT (dependent types forbid contravariant domains);
                // codomain COVARIANT.
                if !self.is_def_eq(d1, d2) {
                    return false;
                }
                let save_len = self.ctx_len();
                let local_id = self.ctx_push(Name::anon(), d2.as_ref().clone(), *bi2);
                let c1_open = self.open_bvar(c1, local_id);
                let c2_open = self.open_bvar(c2, local_id);
                let result = stack_safe(|| self.is_le(&c1_open, &c2_open));
                self.ctx_truncate_to(save_len);
                result
            }
            // Coq template-inductive cumulativity: two universe instances of the
            // SAME template-polymorphic inductive (e.g. `prod.{0,0} A B ≤
            // prod.{1,1} A B`). See `template_cumul.rs` for the rule and its
            // soundness argument. Inert outside the Coq lane.
            _ => self.is_le_template_inductive(&a_w, &b_w),
        }
    }

    /// Implementation of definitional equality (called via stacker::maybe_grow).
    ///
    /// Every recursive call goes through `stack_safe` to prevent stack overflow
    /// on deeply nested expressions. See #1455.
    pub(super) fn is_def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        stack_safe(|| self.is_def_eq_inner(a, b))
    }

    /// Inner implementation of definitional equality.
    fn is_def_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        // Quick check: pointer equality (still valid optimization)
        if std::ptr::eq(a, b) {
            return true;
        }

        // Check equiv_manager for cross-call accumulated knowledge (O(α(n))).
        // This catches repeated sub-expression comparisons across is_def_eq calls
        // within this TypeChecker session. Hash pre-filter rejects mismatches in O(1).
        // Lean 4 reference: type_checker.cpp:743 (quick_is_def_eq).
        if self.equiv_manager.borrow_mut().is_equiv(a, b, true) {
            return true;
        }

        // Fast-path: Structural equality check before cache key construction.
        // For nested lambdas/pis comparing identical expressions, Expr::eq short-circuits
        // on first difference. Avoids clone overhead of DefEqCacheKey::new.
        // See #1052 for the complexity analysis.
        if a == b {
            return true;
        }

        // Check def_eq cache. Key uses O(1) hash_cached() with hash-based
        // canonical ordering (smaller hash first), so we only need one lookup.
        // SlidingCache promotes hits from previous→current generation (#2410).
        let cache_key = DefEqCacheKey::new(a, b, self.transparency);
        #[cfg(feature = "reduction-stats")]
        {
            let hit = self.def_eq_cache.borrow_mut().get(&cache_key).is_some();
            crate::tc::reduction_stats::record_defeq_cache(hit);
        }
        if let Some(cached) = self.def_eq_cache.borrow_mut().get(&cache_key) {
            // Kernel-robustness path for negative cache results (#1773, #38):
            // A negative result is only trustworthy if both expressions are
            // fully in-context. FVarIds are monotonically increasing and never
            // reused after ctx_pop, so in well-behaved kernel-internal usage a
            // popped FVar should never be re-queried. BUT the elaborator/tactic
            // layer can hand the kernel a term whose negative-cache key carries
            // an FVar that is NOT a context declaration (e.g. a sibling
            // subgoal's binder leaked through a metavariable's stored type —
            // see the induction-tactic leak in #38). A tactic-supplied term
            // must never panic the trusted kernel (#![forbid(unsafe_code)]),
            // and a stale-looking negative entry must never be trusted blindly.
            //
            // Therefore: only return a cached NEGATIVE result when both sides
            // are fully in-context. Cached POSITIVE results stay trusted
            // (def-eq is monotone — once equal, always equal). When the
            // out-of-context guard trips we fall through and RECOMPUTE from
            // the source of truth (`is_def_eq_core`), never panic and never
            // trust the stale entry.
            let out_of_context = !cached
                && ((a.has_fvar_quick() && !self.all_fvars_in_context(a))
                    || (b.has_fvar_quick() && !self.all_fvars_in_context(b)));
            if !out_of_context {
                return cached;
            }
        }

        // Compute the result
        let result = self.is_def_eq_core(a, b);

        // Cache the result using canonical key (no need for reversed key)
        // Sliding window eviction retains hot entries across trim cycles (#2410).
        {
            let mut cache = self.def_eq_cache.borrow_mut();
            cache.trim_if_needed(self.max_cache_entries);
            cache.insert(cache_key, result);
        }

        result
    }

    /// Core definitional equality logic (called by is_def_eq_impl after cache check)
    pub(super) fn is_def_eq_core(&self, a: &Expr, b: &Expr) -> bool {
        // Heartbeat tick — Lean parity: `check_system` runs at the top of
        // `is_def_eq_core` (type_checker.cpp:1057), AFTER the caching layer in
        // `is_def_eq`. Comparisons resolved by pointer equality, the equiv
        // manager, structural equality, or the def-eq cache consume no budget
        // (they consume none in Lean either); only cache-missing comparisons
        // that reach the real algorithm tick. Part of the 2026-06-12 kernel
        // performance-parity fix.
        self.inc_heartbeat_def_eq();
        // Early bail: if heartbeat counter is exhausted, return false.
        // This is conservative — returning false means "not proven equal"
        // which may cause a type error to be reported upstream.
        // The actual HeartbeatExceeded error surfaces at the next
        // `tick_heartbeat()` call in `infer_type`.
        if self.heartbeat_exhausted() {
            return false;
        }

        #[cfg(feature = "reduction-stats")]
        crate::tc::reduction_stats::record_core_pair(a, b);

        // GRIND TRACE: track this comparison as the live def-eq frame so a
        // large-literal iota grind fired deep inside its WHNF can name the
        // exact enclosing `a =?= b` pair. Guard pops on every return path.
        #[cfg(feature = "reduction-stats")]
        let _grind_frame = crate::tc::reduction_stats::DefEqFrameGuard::enter(a, b);

        #[cfg(feature = "debug-def-eq")]
        eprintln!("[def_eq_core] a = {}, b = {}", a, b);

        // Lean 4 parity: quick_is_def_eq at entry (type_checker.cpp:1061-1062).
        // This keeps recursive is_def_eq_core calls on the same fast path as
        // top-level calls (equiv_manager, Lam/Pi, Sort, MData, Lit).
        if let Some(result) = self.quick_is_def_eq(a, b) {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => {} (quick)", result);
            return result;
        }

        // Lean 4 parity: proof-by-reflection shortcut (type_checker.cpp:1064-1072).
        // If one side is `Bool.true` and the other side is closed (or eager_reduce
        // is active — type_checker.cpp:1066), fully reduce that side (with delta)
        // and re-check for `Bool.true`.
        // This is required for `decide`-style proofs.
        let eager = self.eager_reduce.get();
        if (!a.has_fvar_quick() || eager)
            && is_bool_true_const(b)
            && is_bool_true_const(&self.whnf(a))
        {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => true (Bool.true reflection lhs)");
            return true;
        }
        if (!b.has_fvar_quick() || eager)
            && is_bool_true_const(a)
            && is_bool_true_const(&self.whnf(b))
        {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => true (Bool.true reflection rhs)");
            return true;
        }

        // Phase 1: Partial WHNF — beta/zeta/iota/projection/quotient only, NO delta.
        // This matches Lean 4's `whnf_core(t, false, true)` at type_checker.cpp:1081.
        // Delta reduction is deferred to the lazy delta loop below.
        let a_n = self.whnf_core_no_delta(a, true);
        let b_n = self.whnf_core_no_delta(b, true);

        #[cfg(feature = "debug-def-eq")]
        if a_n != *a || b_n != *b {
            eprintln!("[def_eq_core] P1 WHNF: a_n = {}, b_n = {}", a_n, b_n);
        }

        // Quick check after partial reduction
        if a_n == b_n {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => true (equal after P1 WHNF)");
            return true;
        }

        // Lean 4 parity: quick_is_def_eq after Phase-1 WHNF only when either side
        // changed (type_checker.cpp:1084-1087). If neither changed, we already ran
        // quick_is_def_eq on (a, b) above.
        if a_n != *a || b_n != *b {
            if let Some(result) = self.quick_is_def_eq(&a_n, &b_n) {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[def_eq_core] => {} (quick after P1 WHNF)", result);
                return result;
            }
        }

        // Proof irrelevance: any two proofs of the same Prop are definitionally equal.
        // Matches Lean 4 type_checker.cpp:1089 — full infer_type + is_prop via RefCell.
        let proof_irrel = self.is_def_eq_proof_irrel(&a_n, &b_n);
        #[cfg(feature = "reduction-stats")]
        crate::tc::reduction_stats::record_proof_irrel(proof_irrel);
        if proof_irrel == Some(true) {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => true (proof irrel)");
            return true;
        }

        // Branch-sharing optimization for recursor congruence (#3402).
        //
        // When both sides are applications of the same recursor with the same
        // parameters and motive, compare the minor premises (branch functions)
        // pairwise instead of reducing the entire recursor via iota. This
        // avoids O(N * prefix_cost) redundant WHNF work for N branches with
        // a shared monadic prefix.
        //
        // Fires before lazy delta because congruence on unreduced recursor
        // applications is cheaper than iota-reducing both sides and then
        // comparing the results.
        if let Some(result) = self.try_branch_sharing_def_eq(&a_n, &b_n) {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => {} (branch sharing)", result);
            return result;
        }

        // Phase 2: Lazy delta reduction loop (#1421).
        // Unfold definitions one at a time using height-based ordering,
        // re-checking equality after each unfold. This replaces the old approach
        // of doing full WHNF (including all delta) upfront.
        // Reference: Lean 4 type_checker.cpp:957 `lazy_delta_reduction`
        //
        // NB: lazy_delta_reduction returns the FINAL expressions when delta is
        // exhausted (neither side can be unfolded further). These may differ from
        // a_n/b_n due to partial delta reduction during the loop.
        // Reference: Lean 4 type_checker.cpp:1094 updates t_n/s_n in place.
        let (t_n, s_n) = match self.lazy_delta_reduction(&a_n, &b_n) {
            Ok(result) => {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[def_eq_core] => {} (P2 lazy delta)", result);
                return result;
            }
            Err(final_exprs) => final_exprs,
        };

        #[cfg(feature = "debug-def-eq")]
        eprintln!("[def_eq_core] delta exhausted: t = {}, s = {}", t_n, s_n);

        // Phase 3: Const/FVar head comparison after delta reduction.
        // Reference: Lean 4 type_checker.cpp:1096-1101
        if let (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) = (t_n.kind(), s_n.kind()) {
            if n1 == n2
                && ls1.len() == ls2.len()
                && ls1
                    .iter()
                    .zip(ls2.iter())
                    .all(|(l1, l2)| self.levels_eq(l1, l2))
            {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[def_eq_core] => true (P3 same Const)");
                return true;
            }
        }
        if let (ExprKind::FVar(i), ExprKind::FVar(j)) = (t_n.kind(), s_n.kind()) {
            if i == j {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[def_eq_core] => true (P3 same FVar)");
                return true;
            }
        }

        // Phase 4: Projection comparison with lazy delta (Lean 4 type_checker.cpp:1103-1108).
        if let (ExprKind::Proj(_, i1, e1), ExprKind::Proj(_, i2, e2)) = (t_n.kind(), s_n.kind()) {
            if i1 == i2 && self.lazy_delta_proj_reduction(e1, e2, *i1) {
                #[cfg(feature = "debug-def-eq")]
                eprintln!("[def_eq_core] => true (P4 proj)");
                return true;
            }
        }

        // Phase 5: Second whnf_core pass with full projection reduction
        // (Lean 4 type_checker.cpp:1110-1114).
        let t_full = self.whnf_core_no_delta(&t_n, false);
        let s_full = self.whnf_core_no_delta(&s_n, false);
        if t_full != t_n || s_full != s_n {
            #[cfg(feature = "debug-def-eq")]
            eprintln!(
                "[def_eq_core] P5 full proj WHNF: t = {}, s = {}",
                t_full, s_full
            );
            return self.is_def_eq_impl(&t_full, &s_full);
        }

        // Phase 6: Structural comparison on the fully-reduced forms.
        // Includes App, eta, struct-eta. (Lean 4 lines 1117-1124)
        if self.is_def_eq_structural(&t_n, &s_n) {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => true (P6 structural)");
            return true;
        }

        // Phase 7: String literal expansion (Lean 4 type_checker.cpp:1126-1127).
        if self.try_string_lit_expansion(&t_n, &s_n) {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => true (P7 string lit)");
            return true;
        }

        // Phase 8: Unit-like types (Lean 4 type_checker.cpp:1129-1130).
        if self.is_def_eq_unit_like(&t_n, &s_n) {
            #[cfg(feature = "debug-def-eq")]
            eprintln!("[def_eq_core] => true (P8 unit-like)");
            return true;
        }

        #[cfg(feature = "debug-def-eq")]
        eprintln!(
            "[def_eq_core] => false (exhausted): t = {}, s = {}",
            t_n, s_n
        );
        false
    }

    /// Lean 4-style quick definitional equality checks (`quick_is_def_eq`).
    ///
    /// Handles "easy" cases before expensive lazy delta unfolding:
    /// - Equiv-manager class hit (true)
    /// - `Lam` / `Pi`: binder-aware comparison
    /// - `Sort`: universe level defeq
    /// - `MData`: recurse on wrapped expressions
    /// - `Lit`: literal value equality (including fast false on unequal literals)
    ///
    /// Returns `Some(result)` when handled, `None` otherwise.
    fn quick_is_def_eq(&self, a: &Expr, b: &Expr) -> Option<bool> {
        // Lean 4 quick_is_def_eq first checks the equivalence manager.
        if self.equiv_manager.borrow_mut().is_equiv(a, b, true) {
            return Some(true);
        }

        match (a.kind(), b.kind()) {
            (ExprKind::Lam(..), ExprKind::Lam(..)) | (ExprKind::Pi(..), ExprKind::Pi(..)) => {
                Some(self.is_def_eq_binding(a, b))
            }
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => Some(self.levels_eq(l1, l2)),
            // MData is transparent for definitional equality.
            // Symmetric case: both sides MData — compare inner expressions.
            (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2)) => {
                Some(self.is_def_eq_impl(inner1, inner2))
            }
            // Asymmetric cases: one side has MData wrapper, the other does not.
            // Strip the MData and recurse. Lean 4 handles this via WHNF in
            // is_def_eq_core Phase 1, but when MData is nested inside App/Pi
            // subexpressions, the top-level WHNF doesn't reach it. Handling
            // it here in quick_is_def_eq ensures MData transparency at every
            // recursive comparison level. Part of #3134.
            (ExprKind::MData(_, inner), _) => Some(self.is_def_eq_impl(inner, b)),
            (_, ExprKind::MData(_, inner)) => Some(self.is_def_eq_impl(a, inner)),
            // Squash structural equality: Squash(a) =?= Squash(b) iff a =?= b.
            // Unlike MData, Squash is NOT reduced through by WHNF (#2164).
            (ExprKind::Squash(inner1), ExprKind::Squash(inner2)) => {
                Some(self.is_def_eq_impl(inner1, inner2))
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => Some(l1 == l2),
            _ => None,
        }
    }

    /// Check that all FVars in an expression are present in the current context.
    ///
    /// This is a debug-only validation for the FVarId-unreachability invariant
    /// (#1773): since FVarIds are monotonically increasing and never reused
    /// after `ctx_pop`, expressions containing popped FVars should never appear
    /// in cache lookups. A `false` return here indicates a soundness concern.
    ///
    /// Performance: O(n) expression traversal — this call site (`:251-252`) has
    /// **no** `debug_assert!`/`cfg(debug_assertions)` gate despite the doc
    /// comment above; it runs on every build as a guard on whether a negative
    /// def-eq cache result is safe to trust across a context pop.
    ///
    /// PERF (Track XX, extended): delegates to a pointer-identity-memoized
    /// worker ([`Self::all_fvars_in_context_memo`]) — same discipline as
    /// [`FoldMemo`](crate::expr::subst) in `expr/subst.rs`: match-lowering
    /// shares one "fallback" continuation `Arc<Expr>` across many `casesOn`
    /// minors, so an unmemoized walk re-visits that shared node once per
    /// occurrence (a DAG walked as a tree). The memo is built **fresh for this
    /// call only** — never persisted across separate `all_fvars_in_context`
    /// invocations — because the walk reads `self.ctx`, which is stable within
    /// one call but mutates between calls via `ctx_push_let`/`ctx_pop`. A memo
    /// hit returns exactly the bool the unmemoized walk would have produced for
    /// the same (node, ctx) pair — same verdict, fewer re-walks.
    fn all_fvars_in_context(&self, e: &Expr) -> bool {
        let mut memo = std::collections::HashMap::new();
        self.all_fvars_in_context_memo(e, &mut memo)
    }

    /// Memoized worker for [`Self::all_fvars_in_context`]. `memo` is keyed on
    /// the visited node's pointer identity alone (no depth component — the
    /// FVar-in-context question does not depend on binder nesting, only on
    /// `self.ctx`, which is fixed for the lifetime of this call).
    fn all_fvars_in_context_memo(
        &self,
        e: &Expr,
        memo: &mut std::collections::HashMap<usize, bool>,
    ) -> bool {
        let key = e as *const Expr as usize;
        if let Some(cached) = memo.get(&key) {
            return *cached;
        }
        let result = self.all_fvars_in_context_inner(e, memo);
        memo.insert(key, result);
        result
    }

    fn all_fvars_in_context_inner(
        &self,
        e: &Expr,
        memo: &mut std::collections::HashMap<usize, bool>,
    ) -> bool {
        match e.kind() {
            ExprKind::FVar(id) => self.ctx.borrow().get(*id).is_some(),
            ExprKind::App(f, a) => {
                self.all_fvars_in_context_memo(f, memo) && self.all_fvars_in_context_memo(a, memo)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                self.all_fvars_in_context_memo(ty, memo)
                    && self.all_fvars_in_context_memo(body, memo)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                self.all_fvars_in_context_memo(ty, memo)
                    && self.all_fvars_in_context_memo(val, memo)
                    && self.all_fvars_in_context_memo(body, memo)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                self.all_fvars_in_context_memo(inner, memo)
            }
            // Leaf nodes without FVars
            ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => {
                true
            }
            // Mode extensions — check contained exprs
            ExprKind::Squash(inner) => self.all_fvars_in_context_memo(inner, memo),
            // Cubical mode extensions: recurse into children so the cross-context
            // negative-cache guard (the `out_of_context` check above, #1773/#38)
            // stays correct for cubical terms. The prior unconditional `true` for
            // these kinds defeated that guard for exactly the constructs the
            // cubical layer introduces — a stale NEGATIVE def-eq result could be
            // trusted across a context pop instead of being recomputed. A plain
            // structural walk is correct: the interval cofibration `phi` and the
            // partial element `u` of the Kan operations are ordinary sub-exprs,
            // and the path-lam body's bound interval variable is a BVar (not an
            // FVar), so it is never "out of context".
            ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => true,
            ExprKind::CubicalPath { ty, left, right } => {
                self.all_fvars_in_context_memo(ty, memo)
                    && self.all_fvars_in_context_memo(left, memo)
                    && self.all_fvars_in_context_memo(right, memo)
            }
            ExprKind::CubicalPathLam { body } => self.all_fvars_in_context_memo(body, memo),
            ExprKind::CubicalPathApp { path, arg } => {
                self.all_fvars_in_context_memo(path, memo)
                    && self.all_fvars_in_context_memo(arg, memo)
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                self.all_fvars_in_context_memo(ty, memo)
                    && self.all_fvars_in_context_memo(phi, memo)
                    && self.all_fvars_in_context_memo(u, memo)
                    && self.all_fvars_in_context_memo(base, memo)
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                self.all_fvars_in_context_memo(ty, memo)
                    && self.all_fvars_in_context_memo(phi, memo)
                    && self.all_fvars_in_context_memo(base, memo)
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                self.all_fvars_in_context_memo(ty, memo)
                    && self.all_fvars_in_context_memo(r, memo)
                    && self.all_fvars_in_context_memo(s, memo)
                    && self.all_fvars_in_context_memo(base, memo)
            }
            // ZFC set-theoretic kinds wrap a `ZFCSetExpr` enum that needs its own
            // dedicated traversal; until that exists, stay conservative. `SProp`
            // is childless. Returning `true` here only risks trusting a stale
            // NEGATIVE cache entry (a completeness, not soundness, concern), and
            // ZFC terms are off the cubical path.
            ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. }
            | ExprKind::SProp => true,
        }
    }
}
