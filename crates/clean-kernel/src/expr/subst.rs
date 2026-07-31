// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! De Bruijn substitution operations for Expr.
//!
//! Contains: instantiate, lift, has_loose_bvars, collect_constants,
//! abstract_fvar, subst_fvar, and instantiate_level_params.

use super::*;
use crate::level::Level;
use crate::name::Name;
use std::collections::HashMap;
use std::sync::Arc;

const SMALL_LEVEL_PARAM_SUBST_THRESHOLD: usize = 4;

/// Pointer-identity memo for sharing-preserving folds (Track XX).
///
/// `instantiate` / `lift` / `instantiate_rev` walk an expression as a TREE. When
/// the term is a DAG with shared `Arc<Expr>` children — which match lowering
/// produces in abundance (`compile_ctor_dispatch_alt_chain` duplicates a
/// fallback alternative into every `casesOn` minor as the SAME `Arc`) — a naive
/// walk re-folds each shared subtree once PER occurrence, so a DAG that is linear
/// in distinct nodes is rebuilt as a tree that is EXPONENTIAL in its depth.
///
/// Measured (probe): a 25-node DAG balloons to 12.5M nodes after one
/// `instantiate`; the resulting megaterm then dominates inference, drop, and
/// (in the parallel re-verify) the per-thread infer-arc memo, stalling the
/// full-corpus run for hours and spiking RSS to ~100 GB.
///
/// The classic Lean `replace_fn` memo (already applied to `Abstractor`, #WW)
/// keys on the *pointer identity* of the visited node plus the current binder
/// depth. Shared `Arc`s hit the cache and are folded exactly once, collapsing
/// the traversal back to linear in DISTINCT nodes AND preserving DAG sharing in
/// the output (the same `Some(Expr)` is cloned per occurrence, so the rebuilt
/// children stay `Arc`-shared).
///
/// SOUNDNESS: the result of folding a fixed-state folder over a given node at a
/// given depth is a pure function of `(node-address, depth)` — the only mutable
/// state, `depth`, is part of the key, and all other folder fields (`val`,
/// `start`, `amount`, `vals`) are immutable for the call. So a memo hit returns
/// the identical `Option<Expr>` the unmemoized walk would have produced —
/// same accept/reject, byte-identical output term, NO change to any verdict.
/// The memo lives only for the duration of one fold call; every visited node is
/// reachable from `self` (kept alive across the walk), so its address is stable
/// and cannot be reused while an entry referencing it lives.
#[derive(Default)]
struct FoldMemo {
    map: HashMap<(usize, u32), Option<Expr>>,
}

impl FoldMemo {
    #[inline]
    fn get(&self, expr: &Expr, depth: u32) -> Option<Option<Expr>> {
        self.map
            .get(&(expr as *const Expr as usize, depth))
            .cloned()
    }

    #[inline]
    fn put(&mut self, expr: &Expr, depth: u32, result: Option<Expr>) -> Option<Expr> {
        self.map
            .insert((expr as *const Expr as usize, depth), result.clone());
        result
    }
}

/// ExprFolderOpt impl for BVar instantiation (substituting BVar(depth) with val).
///
/// Replaces the hand-rolled `instantiate_at_opt` function (~179 lines) with a
/// ~25-line trait impl. The structural dispatch over all ExprKind variants lives
/// in ExprFolderOpt's default `fold_expr_opt`.
///
/// Lean 4 equivalent: `instantiate.cpp` replace_fn pattern.
struct Instantiator<'a> {
    val: &'a Expr,
    depth: u32,
    /// Pointer-identity memo (Track XX): collapses shared-`Arc` DAGs to a single
    /// fold per distinct node, preserving output sharing. See [`FoldMemo`].
    memo: FoldMemo,
}

impl ExprFolderOpt for Instantiator<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        // O(1) metadata guard: skip if no loose BVars at or above `depth`.
        // Lean 4 equivalent: instantiate.cpp:16 `s >= get_loose_bvar_range(a)`
        self.depth < expr.loose_bvar_range()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        if let Some(cached) = self.memo.get(expr, self.depth) {
            return cached;
        }
        let depth = self.depth;
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.put(expr, depth, result)
    }

    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        use std::cmp::Ordering;
        match idx.cmp(&self.depth) {
            Ordering::Equal => Some(self.val.lift_at(0, self.depth)),
            Ordering::Greater => Some(Expr::bvar(idx - 1)),
            Ordering::Less => None,
        }
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let saved = self.depth;
        self.depth = checked_add_u32(self.depth, 1, "instantiate depth");
        let result = self.fold_expr_opt(expr);
        self.depth = saved;
        result
    }
}

/// ExprFolderOpt impl for multi-arg BVar instantiation.
///
/// Replaces BVar(depth)..BVar(depth+n-1) with vals[0]..vals[n-1] simultaneously,
/// and shifts higher BVars down by n. This is the multi-arg generalization of
/// `Instantiator` and matches Lean 4's `instantiate(body, n, args)`.
///
/// Used for multi-argument beta reduction: when we have `(λ x. λ y. λ z. body) a b c`,
/// we can instantiate body with [a, b, c] in one pass instead of three sequential
/// single-arg instantiates.
///
/// Part of #3210.
///
/// TOTALITY: `fold_bvar_opt` is total for every `(idx, depth, n)` — it never
/// evaluates the `depth + n` sum that could overflow `u32`. It branches on
/// `idx < depth` and on `offset = idx - depth` against `n`, both of which are
/// always representable (the subtraction is guarded by `idx >= depth`). On every
/// input for which `depth + n` *is* representable the branch outcomes are
/// identical to the arithmetic form `idx < depth + n` / `idx >= depth + n`, so
/// behavior is unchanged on all reachable inputs; on the pathological remainder
/// it still returns the mathematically-correct term. `depth` itself only advances
/// via `fold_binder_body_opt`, which uses the saturating [`checked_add_u32`], and
/// a `fold_bvar_opt` call is only ever reached through `should_descend` passing
/// (`depth < loose_bvar_range() <= MAX_BVAR_RANGE`), so in practice `depth` is
/// bounded far below `u32::MAX` regardless.
struct MultiInstantiator<'a> {
    vals: &'a [Expr],
    depth: u32,
    /// Pointer-identity memo (Track XX): see [`FoldMemo`].
    memo: FoldMemo,
}

impl ExprFolderOpt for MultiInstantiator<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        self.depth < expr.loose_bvar_range()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        if let Some(cached) = self.memo.get(expr, self.depth) {
            return cached;
        }
        let depth = self.depth;
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.put(expr, depth, result)
    }

    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        let n = self.vals.len() as u32;
        if idx < self.depth {
            // BVar below the window: bound by an inner binder, unchanged.
            return None;
        }
        // idx >= self.depth, so `offset` is this BVar's position relative to the
        // start of the substitution window `[depth, depth + n)`. It is computed as
        // `idx - self.depth` (which cannot underflow here) rather than by comparing
        // against `self.depth + n` — the sum that overflowed the old code. `offset
        // < n` is exactly `idx < self.depth + n` whenever that sum is representable
        // (every reachable input; see the struct's TOTALITY note), and it stays
        // *correct* even when the sum would overflow: an overflowing `depth + n`
        // means the window covers every representable index at or above `depth`, so
        // every `idx >= depth` is inside it — which is precisely what `offset < n`
        // selects. The result therefore never depends on the un-representable sum.
        let offset = idx - self.depth;
        if offset < n {
            // BVar(depth + offset) → vals[offset], lifted by depth.
            Some(self.vals[offset as usize].lift_at(0, self.depth))
        } else {
            // BVar above the window: shift down by n. `offset >= n` gives
            // `idx - self.depth >= n`, hence `idx >= n`, so `idx - n` never underflows.
            Some(Expr::bvar(idx - n))
        }
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let saved = self.depth;
        self.depth = checked_add_u32(self.depth, 1, "multi-instantiate depth");
        let result = self.fold_expr_opt(expr);
        self.depth = saved;
        result
    }
}

/// ExprFolderOpt impl for De Bruijn lifting (shifting loose BVars >= start up by amount).
///
/// Replaces the hand-rolled `lift_at_opt` function (~180 lines) with a
/// ~20-line trait impl. Lean 4 equivalent: expr.cpp:449 lift_loose_bvars.
struct Lifter {
    start: u32,
    amount: u32,
    /// Pointer-identity memo (Track XX): keyed on `(node, start)` since `start`
    /// is the only mutable per-node state (`amount` is fixed). See [`FoldMemo`].
    memo: FoldMemo,
}

impl ExprFolderOpt for Lifter {
    fn should_descend(&self, expr: &Expr) -> bool {
        self.start < expr.loose_bvar_range()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        if let Some(cached) = self.memo.get(expr, self.start) {
            return cached;
        }
        let start = self.start;
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.put(expr, start, result)
    }

    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        if idx >= self.start {
            Some(ek(ExprKind::BVar(checked_add_u32(
                idx,
                self.amount,
                "lift bvar index",
            ))))
        } else {
            None
        }
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let saved = self.start;
        self.start = checked_add_u32(self.start, 1, "lift binder start");
        let result = self.fold_expr_opt(expr);
        self.start = saved;
        result
    }
}

/// ExprFolderOpt impl for De Bruijn lowering (shifting loose BVars >= start
/// down by amount). Inverse of [`Lifter`] under the precondition — enforced
/// by the [`Expr::lower_loose_bvars`] wrapper's range precheck — that no
/// loose bvar has root-relative index below `amount`, so the subtraction
/// below never crosses the loose/bound threshold.
///
/// TOTALITY: `fold_bvar_opt` is panic-free at the source. The wrapper precheck
/// establishes `idx - start >= amount` for every loose bvar reached, so the
/// lowered index `idx - amount` never underflows; it is computed with
/// `saturating_sub`, which agrees with true subtraction on that (reachable)
/// domain. See the per-fold `// SOUNDNESS / TOTALITY` note.
///
/// Lean 4 equivalent: expr.cpp `lower_loose_bvars`.
struct Lowerer {
    start: u32,
    amount: u32,
    /// Pointer-identity memo keyed on `(node, start)` — same discipline as
    /// [`Lifter`]: `start` is the only mutable per-node state.
    memo: FoldMemo,
}

impl ExprFolderOpt for Lowerer {
    fn should_descend(&self, expr: &Expr) -> bool {
        self.start < expr.loose_bvar_range()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        if let Some(cached) = self.memo.get(expr, self.start) {
            return cached;
        }
        let start = self.start;
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.put(expr, start, result)
    }

    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        if idx >= self.start {
            // SOUNDNESS / TOTALITY: the only path that constructs a `Lowerer` is
            // [`Expr::lower_loose_bvars`], which first rejects any term satisfying
            // `has_loose_bvar_in_range(0, amount)`. A bvar with local index `idx`
            // at binder depth `self.start` is loose iff `idx >= self.start`, and
            // its root-relative index is `idx - self.start`; the precheck therefore
            // guarantees every loose bvar reaching this fold has
            // `idx - self.start >= self.amount`, i.e. `idx >= self.start + self.amount
            // >= self.amount`. Under that caller-established invariant `idx -
            // self.amount` is the exact lowered index and never underflows, so
            // `saturating_sub` equals true subtraction on every reachable input.
            // The former `debug_assert!(idx - start >= amount, ...)` merely restated
            // that precondition as a trap; it is dropped so the fold is total
            // (panic-free) at the source — the fact is established by the caller,
            // not a branch to fault on here.
            Some(ek(ExprKind::BVar(idx.saturating_sub(self.amount))))
        } else {
            None
        }
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let saved = self.start;
        self.start = checked_add_u32(self.start, 1, "lower binder start");
        let result = self.fold_expr_opt(expr);
        self.start = saved;
        result
    }
}

/// ExprFolderOpt impl for FVar-to-BVar abstraction (replace FVar(id) → BVar(depth), shift BVars up).
///
/// Replaces the hand-rolled `abstract_fvar_at_opt` function (~180 lines).
/// abstract_fvar does two things: (1) replace FVar(id) → BVar(depth),
/// (2) shift BVar(idx >= depth) up by 1.
///
/// PERF (Track WW): match lowering (`compile_ctor_dispatch_alt_chain` +
/// `wrap_with_nested_ctor_caseson_with_fallback`) duplicates the accumulated
/// "fallback" alternative into every non-matching `casesOn` minor. Because
/// `Expr::clone` is an `Arc` clone, all those duplicates share the SAME
/// `Arc<Expr>` node — but a naive `abstract_fvar` walk re-traverses each copy,
/// turning a chain of N nat/ctor patterns into an `O(branching^N)` traversal
/// (observed node counts 21K → 694K → 22.9M for `semIntBinOp`, then OOM/timeout).
///
/// The fix is the classic Lean `replace_fn` memo: a per-call cache keyed on the
/// *pointer identity* of the visited `Expr` node plus the current binder depth.
/// Shared `Arc`s hit the cache and are abstracted exactly once, collapsing the
/// traversal back to linear in the number of DISTINCT nodes.
///
/// SOUNDNESS: the cache is keyed on `(node-address, depth)`. For a fixed
/// `Abstractor` the result of abstracting a given node at a given depth is a pure
/// function of those two values (the only mutable state, `depth`, is part of the
/// key), so memoization returns the identical `Option<Expr>` the unmemoized walk
/// would have produced — same accept/reject, byte-identical output term. The
/// cache lives only for the duration of one `abstract_fvar_at` call; node
/// addresses are stable for that call because every visited node is reachable
/// from `self` (kept alive across the walk).
struct Abstractor {
    id: FVarId,
    depth: u32,
    /// Memo: `(node pointer, depth) -> abstraction result`. `None`-valued
    /// entries record "unchanged" (the `ExprFolderOpt` sharing signal) so a
    /// shared unchanged subtree is also visited only once.
    memo: HashMap<(usize, u32), Option<Expr>>,
}

impl Abstractor {
    fn new(id: FVarId, depth: u32) -> Self {
        Abstractor {
            id,
            depth,
            memo: HashMap::new(),
        }
    }
}

impl ExprFolderOpt for Abstractor {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_fvar_quick() || self.depth < expr.loose_bvar_range()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        // Pointer-identity memo: shared `Arc<Expr>` duplicates produced by match
        // lowering are abstracted once. Key includes `depth` because the same
        // node may be visited at different binder depths (distinct results).
        let key = (expr as *const Expr as usize, self.depth);
        if let Some(cached) = self.memo.get(&key) {
            return cached.clone();
        }
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.insert(key, result.clone());
        result
    }

    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        if id == self.id {
            Some(ek(ExprKind::BVar(self.depth)))
        } else {
            None
        }
    }

    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        if idx >= self.depth {
            Some(ek(ExprKind::BVar(checked_add_u32(
                idx,
                1,
                "abstract_fvar bvar shift",
            ))))
        } else {
            None
        }
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let saved = self.depth;
        self.depth = checked_add_u32(self.depth, 1, "abstract_fvar depth");
        let result = self.fold_expr_opt(expr);
        self.depth = saved;
        result
    }
}

/// ExprFolderOpt impl for FVar substitution (replace FVar(id) → replacement).
///
/// Replaces the hand-rolled `subst_fvar_opt` function (~165 lines).
/// No depth tracking needed — FVars are not affected by binder scope.
///
/// PERF (Track XX, extended): `subst_fvar` backs `infer_type`'s `Let`-case
/// zeta-reduction (open-then-close via fvar, `tc/infer.rs`), which is exactly
/// the pattern match-lowering's shared "fallback" `Arc<Expr>` duplication
/// hits. Carries the same pointer-identity [`FoldMemo`] as `Instantiator` et
/// al. `FVarSubst` has no depth concept — FVar substitution never depends on
/// binder nesting — so the memo key pins depth to the constant `0`.
struct FVarSubst<'a> {
    id: FVarId,
    replacement: &'a Expr,
    /// Pointer-identity memo (Track XX): see [`FoldMemo`]. Depth is always `0`
    /// (FVarSubst has no binder-depth dependence).
    memo: FoldMemo,
}

impl ExprFolderOpt for FVarSubst<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_fvar_quick()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        if let Some(cached) = self.memo.get(expr, 0) {
            return cached;
        }
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.put(expr, 0, result)
    }

    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        if id == self.id {
            Some(self.replacement.clone())
        } else {
            None
        }
    }
}

/// ExprFolderOpt impl for universe level parameter substitution.
///
/// Replaces the hand-rolled `instantiate_level_params_opt` function (~180 lines).
/// Only Sort and Const nodes carry level parameters.
///
/// PERF (Track XX, extended): backs `instantiate_level_params`, invoked from
/// the same reduction paths as `FVarSubst` above. Same [`FoldMemo`] discipline,
/// depth pinned to `0` (no binder-depth dependence).
struct LevelParamSubst<'a> {
    subst: &'a HashMap<Name, Level>,
    /// Pointer-identity memo (Track XX): see [`FoldMemo`]. Depth pinned to `0`.
    memo: FoldMemo,
}

impl ExprFolderOpt for LevelParamSubst<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_level_param_quick()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        if let Some(cached) = self.memo.get(expr, 0) {
            return cached;
        }
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.put(expr, 0, result)
    }

    fn fold_sort_opt(&mut self, level: &Level) -> Option<Expr> {
        let nl = level.substitute_map(self.subst);
        if nl == *level {
            None
        } else {
            Some(ek(ExprKind::Sort(nl)))
        }
    }

    fn fold_const_opt(&mut self, name: &Name, levels: &LevelVec) -> Option<Expr> {
        let new_levels: LevelVec = levels
            .iter()
            .map(|l| l.substitute_map(self.subst))
            .collect();
        if new_levels == *levels {
            None
        } else {
            Some(ek(ExprKind::Const(name.clone(), new_levels)))
        }
    }
}

/// ExprFolderOpt impl for small universe parameter substitutions from parallel slices.
///
/// This avoids building a `HashMap` on the hot path where the number of universe
/// parameters is typically 0-2.
///
/// PERF (Track XX, extended): same [`FoldMemo`] discipline as [`LevelParamSubst`]
/// above, depth pinned to `0`.
struct LevelParamSubstSlice<'a> {
    params: &'a [Name],
    levels: &'a [Level],
    /// Pointer-identity memo (Track XX): see [`FoldMemo`]. Depth pinned to `0`.
    memo: FoldMemo,
}

impl ExprFolderOpt for LevelParamSubstSlice<'_> {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_level_param_quick()
    }

    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if !self.should_descend(expr) {
            return None;
        }
        if let Some(cached) = self.memo.get(expr, 0) {
            return cached;
        }
        let result = stack_safe(|| self.fold_expr_opt_inner(expr));
        self.memo.put(expr, 0, result)
    }

    fn fold_sort_opt(&mut self, level: &Level) -> Option<Expr> {
        let nl = level.substitute_slice(self.params, self.levels);
        if nl == *level {
            None
        } else {
            Some(ek(ExprKind::Sort(nl)))
        }
    }

    fn fold_const_opt(&mut self, name: &Name, levels: &LevelVec) -> Option<Expr> {
        let new_levels: LevelVec = levels
            .iter()
            .map(|l| l.substitute_slice(self.params, self.levels))
            .collect();
        if new_levels == *levels {
            None
        } else {
            Some(ek(ExprKind::Const(name.clone(), new_levels)))
        }
    }
}

impl Expr {
    /// Substitute bound variable 0 with the given expression
    ///
    /// This performs capture-avoiding substitution, replacing BVar(0) with `val`
    /// while decrementing all other BVar indices.
    ///
    /// # Contract
    ///
    /// REQUIRES: `val` is well-formed (no internal invariant violations)
    ///
    /// ENSURES: Result has no loose BVar(0) references from `self` (bound BVar(0) inside binders preserved)
    /// ENSURES: If `self : A` and `val : B` where B unifies with binding type,
    ///          then result is well-typed
    /// ENSURES: For closed `e` (no loose bvars), `e.instantiate(v) == e` for any `v`
    /// ENSURES: Deterministic - same inputs yield same output
    pub fn instantiate(&self, val: &Expr) -> Expr {
        self.instantiate_at(val, 0)
    }

    /// Substitute BVar(depth) with `val`, decrementing BVars above `depth`.
    ///
    /// Generalization of `instantiate` to an arbitrary depth.
    /// Useful when substituting a bound variable that isn't the innermost binder.
    pub fn instantiate_at(&self, val: &Expr, depth: u32) -> Expr {
        let mut folder = Instantiator {
            val,
            depth,
            memo: FoldMemo::default(),
        };
        self.fold_opt_or_clone(&mut folder)
    }

    /// Substitute BVar(0)..BVar(n-1) with vals[0]..vals[n-1] simultaneously.
    ///
    /// This is the multi-argument generalization of `instantiate`. For a lambda
    /// telescope `λ x₀. λ x₁. ... λ xₙ₋₁. body`, calling
    /// `body.instantiate_rev(&[a₀, a₁, ..., aₙ₋₁])` produces `body[a₀/x₀, ..., aₙ₋₁/xₙ₋₁]`.
    ///
    /// Note: `vals[0]` replaces BVar(0) (the innermost binder), `vals[n-1]` replaces
    /// BVar(n-1) (the outermost binder). BVars >= n are shifted down by n.
    ///
    /// Lean 4 equivalent: `instantiate(body, n, args)` in `instantiate.cpp`.
    /// Part of #3210.
    pub fn instantiate_rev(&self, vals: &[Expr]) -> Expr {
        if vals.is_empty() {
            return self.clone();
        }
        if vals.len() == 1 {
            return self.instantiate(&vals[0]);
        }
        let mut folder = MultiInstantiator {
            vals,
            depth: 0,
            memo: FoldMemo::default(),
        };
        self.fold_opt_or_clone(&mut folder)
    }

    /// Beta-normalize: contract every beta-redex `(fun x => body) arg` to
    /// `body[x := arg]`, everywhere in the term, to a beta-normal form.
    ///
    /// This is a **pure, syntactic** transformation performing **beta and
    /// only beta**. It deliberately does NOT perform:
    /// - **delta** (definition unfolding — there is no `Environment`, so every
    ///   `Const` is inert),
    /// - **eta** (`fun x => f x ↦ f`),
    /// - **iota** (recursor / `match` / projection-of-constructor reduction),
    /// - **zeta** (`let`-substitution).
    ///
    /// So a `Const`, `Let`, `Proj`, recursor application, etc. is left intact;
    /// only an application whose head reduces (by beta alone) to a `Lam` is
    /// contracted. Contraction reuses the existing, de-Bruijn-correct
    /// [`Expr::instantiate`] (`BVar(0) ↦ arg`, all higher loose bvars
    /// decremented). Children are normalized first (so a head that is itself a
    /// redex is contracted before the enclosing application is inspected), and
    /// each contraction re-normalizes its result because a substitution can
    /// expose a fresh redex (e.g. `(fun f => f a) (fun x => x)`).
    ///
    /// TERMINATION: this is applied only to well-typed type expressions (the
    /// aux mirror constructor/type-former terms produced by nested-inductive
    /// elimination), which are strongly normalizing, so the fixpoint
    /// terminates.
    ///
    /// SOUNDNESS (`designs/2026-07-05-nested-dependent-param-container.md` §7):
    /// beta ⊆ whnf, so this only reaches a normal form Lean's kernel reaches
    /// lazily at each check site; on a redex-free term it is the identity
    /// (returns a structurally identical term — `None` from the core reuses
    /// `self`). Contraction can only **expose** a hidden negative / invalid
    /// occurrence, never **hide** one, so the downstream strict-positivity gate
    /// keeps its full rejection power on the reduced term.
    pub(crate) fn beta_normalize(&self) -> Expr {
        stack_safe(|| self.beta_normalize_opt()).unwrap_or_else(|| self.clone())
    }

    /// Sharing-preserving core of [`Expr::beta_normalize`]: `None` ⇔ already
    /// beta-normal (the caller reuses `self`), `Some(e)` ⇔ `e` is the normal
    /// form of `self`.
    fn beta_normalize_opt(&self) -> Option<Expr> {
        match &self.kind {
            ExprKind::App(f, a) => {
                let nf = f.beta_normalize_opt();
                let na = a.beta_normalize_opt();
                // Inspect the head AFTER normalizing `f`.
                let head = nf.as_ref().unwrap_or(f);
                if let ExprKind::Lam(_, _, body) = &head.kind {
                    // Beta-redex: contract, then re-normalize (the substitution
                    // may expose a fresh redex).
                    let arg = na.as_ref().unwrap_or(a);
                    return Some(body.instantiate(arg).beta_normalize());
                }
                match (nf, na) {
                    (None, None) => None,
                    (nf, na) => Some(Expr::app(
                        nf.unwrap_or_else(|| (**f).clone()),
                        na.unwrap_or_else(|| (**a).clone()),
                    )),
                }
            }
            ExprKind::Lam(bi, ty, body) => {
                let nty = ty.beta_normalize_opt();
                let nbody = body.beta_normalize_opt();
                match (nty, nbody) {
                    (None, None) => None,
                    (nty, nbody) => Some(Expr::lam(
                        *bi,
                        nty.unwrap_or_else(|| (**ty).clone()),
                        nbody.unwrap_or_else(|| (**body).clone()),
                    )),
                }
            }
            ExprKind::Pi(bi, ty, body) => {
                let nty = ty.beta_normalize_opt();
                let nbody = body.beta_normalize_opt();
                match (nty, nbody) {
                    (None, None) => None,
                    (nty, nbody) => Some(Expr::pi(
                        *bi,
                        nty.unwrap_or_else(|| (**ty).clone()),
                        nbody.unwrap_or_else(|| (**body).clone()),
                    )),
                }
            }
            ExprKind::Let(name, ty, val, body, non_dep) => {
                let nty = ty.beta_normalize_opt();
                let nval = val.beta_normalize_opt();
                let nbody = body.beta_normalize_opt();
                match (&nty, &nval, &nbody) {
                    (None, None, None) => None,
                    _ => Some(ek(ExprKind::Let(
                        name.clone(),
                        Arc::new(nty.unwrap_or_else(|| (**ty).clone())),
                        Arc::new(nval.unwrap_or_else(|| (**val).clone())),
                        Arc::new(nbody.unwrap_or_else(|| (**body).clone())),
                        *non_dep,
                    ))),
                }
            }
            ExprKind::Proj(name, idx, inner) => inner
                .beta_normalize_opt()
                .map(|ni| ek(ExprKind::Proj(name.clone(), *idx, Arc::new(ni)))),
            ExprKind::MData(meta, inner) => inner
                .beta_normalize_opt()
                .map(|ni| ek(ExprKind::MData(meta.clone(), Arc::new(ni)))),
            // Atoms (BVar/FVar/Sort/Const/Lit) carry no redex; the
            // impredicative/Cubical/ZFC extension variants never occur in a
            // constructor type produced by nested-inductive elimination, and a
            // redex left un-contracted there would only make the downstream
            // gate MORE conservative (reject), never unsound. Leave untouched.
            _ => None,
        }
    }

    /// Lift loose bound variables >= `start` by `amount`
    ///
    /// This is used when substituting into a binder. For example, when we substitute
    /// `val` into `body` where body is inside a lambda, we need to lift the free
    /// variables in `val` by 1 so they refer to the right things.
    ///
    /// # Contract
    ///
    /// REQUIRES: `amount` does not cause overflow (amount + max_bvar < u32::MAX)
    /// ENSURES: On overflow, BVar indices saturate at `u32::MAX` (never panics)
    ///
    /// ENSURES: `self.lift(0) == self` (identity)
    /// ENSURES: All loose BVar(i) in `self` become BVar(i + amount) (bound BVars unaffected)
    /// ENSURES: `self.lift(a).lift(b) == self.lift(a + b)` (composition)
    /// ENSURES: For closed `self` (no loose bvars), `self.lift(n) == self` for any `n`
    /// ENSURES: Type preservation - if e is well-typed, result is well-typed
    ///          in appropriately extended context
    /// ENSURES: Deterministic - same inputs yield same output
    pub fn lift(&self, amount: u32) -> Expr {
        self.lift_at(0, amount)
    }

    /// Lift loose bound variables >= `start` by `amount`.
    ///
    /// More general than `lift()` - only affects BVars at or above `start`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `start + amount` does not overflow
    ///
    /// ENSURES: BVar(i) where i >= start becomes BVar(i + amount)
    /// ENSURES: BVar(i) where i < start is unchanged
    /// ENSURES: `lift_from(0, n)` is equivalent to `lift(n)`
    /// ENSURES: Deterministic - same inputs yield same output
    pub fn lift_from(&self, start: u32, amount: u32) -> Expr {
        self.lift_at(start, amount)
    }

    /// Lift loose bound variables >= `start` by `amount`
    pub(crate) fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 {
            return self.clone();
        }
        let mut folder = Lifter {
            start,
            amount,
            memo: FoldMemo::default(),
        };
        self.fold_opt_or_clone(&mut folder)
    }

    /// Lower every loose bound variable by `k`, or `None` if any loose bvar
    /// (root-relative) has index `< k` — those would refer to one of the `k`
    /// binders being removed, so the expression cannot be lowered.
    ///
    /// This is the fallible inverse of [`Expr::lift`]:
    /// `e.lift(k).lower_loose_bvars(k) == Some(e)`, and
    /// `e.lower_loose_bvars(k).map(|d| d.lift(k)) == Some(e)` when it
    /// succeeds. BVars bound *inside* `self` are untouched (the `< k` test is
    /// root-relative).
    ///
    /// Used by nested-inductive elimination to canonicalize a container
    /// occurrence's instantiation args from constructor-field depth `k` into
    /// the declaration's shared parameter telescope
    /// (`designs/2026-07-02-parameterized-nested-inductives.md` §1.2).
    ///
    /// Lean 4 equivalent: expr.cpp `lower_loose_bvars` (whose precondition
    /// `!has_loose_bvar_in_range(0, k)` is checked here instead of assumed).
    #[must_use]
    pub(crate) fn lower_loose_bvars(&self, k: u32) -> Option<Expr> {
        if k == 0 {
            return Some(self.clone());
        }
        if self.has_loose_bvar_in_range(0, k) {
            return None;
        }
        let mut folder = Lowerer {
            start: 0,
            amount: k,
            memo: FoldMemo::default(),
        };
        Some(self.fold_opt_or_clone(&mut folder))
    }

    /// Check if expression has any loose bound variables
    ///
    /// Uses stack_safe for stack overflow protection on deeply nested expressions.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `self` contains any `BVar(i)` not bound by an enclosing binder
    /// ENSURES: `!e.has_loose_bvars()` implies `e.lift(n) == e` for all `n` (closed expressions don't lift)
    /// ENSURES: `!e.has_loose_bvars()` implies `e.instantiate(v) == e` for all `v` (closed expressions don't instantiate)
    /// ENSURES: Deterministic - same input yields same output
    /// ENSURES: Pure - no side effects
    pub fn has_loose_bvars(&self) -> bool {
        // O(1) via cached metadata — replaces O(n) tree traversal.
        self.meta.has_loose_bvars()
    }

    /// Check if expression contains a specific loose bound variable.
    ///
    /// Reference: lean4-ref/src/kernel/expr.cpp:389 `has_loose_bvar`
    ///
    /// # Totality
    ///
    /// TOTAL for every `idx: u32` — including `u32::MAX` and `u32::MAX - 1`,
    /// which the naive `has_loose_bvar_in_range(idx, idx + 1)` form mishandles:
    /// `idx == u32::MAX` overflows `idx + 1` (panic in a checked build), and
    /// `idx == u32::MAX - 1` makes `idx + 1 == u32::MAX` collide with the
    /// "unbounded above" sentinel of [`Expr::has_loose_bvar_in_range`], silently
    /// widening the queried point `{idx}` into the ray `[idx, ∞)`.
    ///
    /// Both edges are removed by the O(1) metadata pre-guard below. Every loose
    /// `BVar` index in a well-formed `Expr` is `< self.loose_bvar_range()`, and
    /// `loose_bvar_range()` is physically a 20-bit field, so it is
    /// `<= ExprMeta::MAX_BVAR_RANGE` (`1_048_575`) `< u32::MAX - 1`
    /// *unconditionally* — a bit-layout fact, not the `ExprMeta::pack` runtime
    /// assertion (which `trust_verify` compiles out). Therefore:
    ///   * for `idx >= loose_bvar_range()` the true answer is `false` (no bvar
    ///     lives that high); returning it directly covers every `idx` in
    ///     `[MAX_BVAR_RANGE, u32::MAX]`, so `idx + 1` is never evaluated there;
    ///   * for `idx < loose_bvar_range() <= MAX_BVAR_RANGE`, `idx + 1` is
    ///     `<= MAX_BVAR_RANGE < u32::MAX`, so it neither overflows nor equals the
    ///     `u32::MAX` sentinel.
    ///
    /// The guard is behavior-preserving on every constructible input:
    /// `has_loose_bvar_in_range` already short-circuits to `false` when
    /// `loose_bvar_range() <= start` (`== idx` here), so this returns exactly the
    /// original verdict — only the overflow/sentinel edge is repaired.
    pub fn has_loose_bvar(&self, idx: u32) -> bool {
        // A loose BVar equal to `idx` can only exist when `idx < loose_bvar_range()`.
        // Returning early there also keeps `idx + 1` in-range and clear of the
        // `u32::MAX` "unbounded" sentinel (see the Totality note above).
        if idx >= self.loose_bvar_range() {
            return false;
        }
        self.has_loose_bvar_in_range(idx, idx + 1)
    }

    /// Infer implicit binder info for a Pi chain.
    ///
    /// Walks the Pi chain and marks explicit binders as Implicit when their
    /// bound variable appears in a subsequent Pi domain.
    ///
    /// If `strict` is true, only checks Pi domains (not the result body).
    /// If `strict` is false, also checks if the variable appears in the result body.
    ///
    /// Reference: lean4-ref/src/kernel/expr.cpp:480-496 `infer_implicit`
    pub(crate) fn infer_implicit(&self, strict: bool) -> Expr {
        self.infer_implicit_n(u32::MAX, strict)
    }

    /// Infer implicit binder info for the first `num_params` binders of a Pi chain.
    ///
    /// Reference: lean4-ref/src/kernel/expr.cpp:480-496
    pub(crate) fn infer_implicit_n(&self, num_params: u32, strict: bool) -> Expr {
        if num_params == 0 {
            return self.clone();
        }
        match &self.kind {
            ExprKind::Pi(bd, domain, body) => {
                let new_body = body.infer_implicit_n(num_params - 1, strict);
                if bd.info != BinderInfo::Default {
                    // Already non-explicit — keep as-is, just update body
                    Expr::pi(*bd, (**domain).clone(), new_body)
                } else if has_loose_bvars_in_domain(&new_body, 0, strict) {
                    // BVar 0 appears in a subsequent domain — mark implicit
                    Expr::pi(
                        BinderData::new(BinderInfo::Implicit, bd.mult),
                        (**domain).clone(),
                        new_body,
                    )
                } else {
                    Expr::pi(*bd, (**domain).clone(), new_body)
                }
            }
            _ => self.clone(),
        }
    }

    /// Check if expression has loose bound variables in range [start, end)
    /// Wrapper that goes through stack_safe for recursive calls
    #[allow(dead_code)]
    pub(crate) fn has_loose_bvar_in_range(&self, start: u32, end: u32) -> bool {
        stack_safe(|| self.has_loose_bvar_in_range_impl(start, end))
    }

    /// Implementation (called via stacker::maybe_grow)
    #[allow(dead_code)]
    fn has_loose_bvar_in_range_impl(&self, start: u32, end: u32) -> bool {
        if end != u32::MAX && start >= end {
            return false;
        }
        // O(1) metadata guard: all loose BVar indices are < loose_bvar_range(),
        // so if loose_bvar_range() <= start, no BVars exist in [start, end).
        if self.loose_bvar_range() <= start {
            return false;
        }
        match &self.kind {
            ExprKind::BVar(idx) => bvar_in_range(*idx, start, end),
            ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => {
                false
            }
            ExprKind::App(f, a) => {
                f.has_loose_bvar_in_range(start, end) || a.has_loose_bvar_in_range(start, end)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end) || body_has_loose
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end)
                    || val.has_loose_bvar_in_range(start, end)
                    || body_has_loose
            }
            ExprKind::Proj(_, _, e) => e.has_loose_bvar_in_range(start, end),
            ExprKind::MData(_, inner) => inner.has_loose_bvar_in_range(start, end),

            // Impredicative mode extensions
            ExprKind::SProp => false,
            ExprKind::Squash(inner) => inner.has_loose_bvar_in_range(start, end),

            // Cubical mode extensions
            ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => false,
            ExprKind::CubicalPath { ty, left, right } => {
                ty.has_loose_bvar_in_range(start, end)
                    || left.has_loose_bvar_in_range(start, end)
                    || right.has_loose_bvar_in_range(start, end)
            }
            ExprKind::CubicalPathLam { body } => match shift_bvar_range(start, end) {
                Some((next_start, next_end)) => body.has_loose_bvar_in_range(next_start, next_end),
                None => false,
            },
            ExprKind::CubicalPathApp { path, arg } => {
                path.has_loose_bvar_in_range(start, end) || arg.has_loose_bvar_in_range(start, end)
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                ty.has_loose_bvar_in_range(start, end)
                    || phi.has_loose_bvar_in_range(start, end)
                    || u.has_loose_bvar_in_range(start, end)
                    || base.has_loose_bvar_in_range(start, end)
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                ty.has_loose_bvar_in_range(start, end)
                    || phi.has_loose_bvar_in_range(start, end)
                    || base.has_loose_bvar_in_range(start, end)
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                ty.has_loose_bvar_in_range(start, end)
                    || r.has_loose_bvar_in_range(start, end)
                    || s.has_loose_bvar_in_range(start, end)
                    || base.has_loose_bvar_in_range(start, end)
            }

            // SetTheoretic mode extensions
            ExprKind::ZFCSet(set_expr) => set_expr.has_loose_bvar_in_range(start, end),
            ExprKind::ZFCMem { element, set } => {
                element.has_loose_bvar_in_range(start, end)
                    || set.has_loose_bvar_in_range(start, end)
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                let pred_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        pred.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                domain.has_loose_bvar_in_range(start, end) || pred_has_loose
            }
        }
    }

    /// Collect all constant names referenced in this expression.
    ///
    /// Traverses the expression tree and returns a set of all `Name`s
    /// that appear in `Const` nodes. Used for proof dependency analysis.
    ///
    /// # Contract
    ///
    /// ENSURES: Result contains exactly the names from all `ExprKind::Const(name, _)` nodes
    /// ENSURES: Duplicates are deduplicated (HashSet)
    /// ENSURES: Order is not guaranteed (HashSet semantics)
    /// ENSURES: Expressions without Const nodes return empty set
    /// ENSURES: Deterministic - same input yields same set of names
    #[must_use]
    pub fn collect_constants(&self) -> std::collections::HashSet<Name> {
        let mut result = std::collections::HashSet::new();
        self.collect_constants_into(&mut result);
        result
    }

    /// Collect constants into an existing set — the allocation-reusing companion
    /// to [`collect_constants`](Self::collect_constants). Public so callers walking
    /// many terms (e.g. a dependency-closure BFS) can keep one scratch set instead
    /// of allocating a fresh `HashSet` per node. Adds to (does not clear) `result`.
    pub fn collect_constants_into(&self, result: &mut std::collections::HashSet<Name>) {
        stack_safe(|| self.collect_constants_into_impl(result));
    }

    /// Implementation (called via stacker::maybe_grow)
    fn collect_constants_into_impl(&self, result: &mut std::collections::HashSet<Name>) {
        match &self.kind {
            ExprKind::Const(name, _) => {
                result.insert(name.clone());
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            ExprKind::App(f, a) => {
                f.collect_constants_into(result);
                a.collect_constants_into(result);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                ty.collect_constants_into(result);
                body.collect_constants_into(result);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                ty.collect_constants_into(result);
                val.collect_constants_into(result);
                body.collect_constants_into(result);
            }
            ExprKind::Proj(_, _, e) => e.collect_constants_into(result),
            ExprKind::MData(_, inner) => inner.collect_constants_into(result),

            // Impredicative mode extensions
            ExprKind::SProp => {}
            ExprKind::Squash(inner) => inner.collect_constants_into(result),

            // Cubical mode extensions
            ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => {}
            ExprKind::CubicalPath { ty, left, right } => {
                ty.collect_constants_into(result);
                left.collect_constants_into(result);
                right.collect_constants_into(result);
            }
            ExprKind::CubicalPathLam { body } => body.collect_constants_into(result),
            ExprKind::CubicalPathApp { path, arg } => {
                path.collect_constants_into(result);
                arg.collect_constants_into(result);
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                ty.collect_constants_into(result);
                phi.collect_constants_into(result);
                u.collect_constants_into(result);
                base.collect_constants_into(result);
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                ty.collect_constants_into(result);
                phi.collect_constants_into(result);
                base.collect_constants_into(result);
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                ty.collect_constants_into(result);
                r.collect_constants_into(result);
                s.collect_constants_into(result);
                base.collect_constants_into(result);
            }

            // SetTheoretic mode extensions
            ExprKind::ZFCSet(set_expr) => set_expr.collect_constants_into(result),
            ExprKind::ZFCMem { element, set } => {
                element.collect_constants_into(result);
                set.collect_constants_into(result);
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                domain.collect_constants_into(result);
                pred.collect_constants_into(result);
            }
        }
    }

    /// Abstract: replace FVar(id) with BVar(0), shifting other bound variables up
    ///
    /// This is the inverse of instantiation with a free variable. Given an expression
    /// containing `FVar(id)`, produces an expression where that free variable is replaced
    /// by `BVar(0)` and all existing bound variables are shifted up by 1.
    ///
    /// # Contract
    ///
    /// ENSURES: Result contains no `FVar(id)` - all occurrences replaced by `BVar`
    /// ENSURES: `e.abstract_fvar(id).instantiate(&ExprKind::FVar(id)) == e` (roundtrip identity)
    /// ENSURES: All `BVar(i)` referring to enclosing binders become `BVar(i+1)` (shift up by 1)
    ///          (This accounts for the new binder introduced by abstraction)
    /// ENSURES: Type preservation - if `e : T` in context `x : A, Γ`, then `e.abstract_fvar(x) : T`
    ///          under binder with type `A` in context `Γ`
    /// ENSURES: Deterministic - same inputs yield same output
    /// ENSURES: Pure - no side effects
    pub fn abstract_fvar(&self, id: FVarId) -> Expr {
        self.abstract_fvar_at(id, 0)
    }

    pub(crate) fn abstract_fvar_at(&self, id: FVarId, depth: u32) -> Expr {
        let mut folder = Abstractor::new(id, depth);
        self.fold_opt_or_clone(&mut folder)
    }

    /// Substitute a free variable with an expression
    ///
    /// This is similar to instantiate but for free variables instead of bound variables.
    /// Replaces all occurrences of `FVar(id)` with `replacement`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `replacement` is well-formed (no internal invariant violations)
    ///
    /// ENSURES: Result contains no `FVar(id)` - all occurrences replaced by `replacement`
    /// ENSURES: All other free variables are preserved unchanged
    /// ENSURES: Bound variable structure is preserved (no shifting needed, unlike instantiate)
    /// ENSURES: Type preservation - if `e : T` in context `x : A, Γ` and `v : A`,
    ///          then `e.subst_fvar(x, v) : T[v/x]`
    /// ENSURES: Deterministic - same inputs yield same output
    /// ENSURES: Pure - no side effects
    pub fn subst_fvar(&self, id: FVarId, replacement: &Expr) -> Expr {
        let mut folder = FVarSubst {
            id,
            replacement,
            memo: FoldMemo::default(),
        };
        self.fold_opt_or_clone(&mut folder)
    }

    /// Substitute universe parameters in this expression.
    ///
    /// Replaces universe level parameters with concrete levels throughout
    /// the expression. Used when instantiating polymorphic definitions.
    ///
    /// # Contract
    ///
    /// REQUIRES: `subst` contains valid (parameter_name, replacement_level) pairs
    ///
    /// ENSURES: If `subst` is empty, returns `self` unchanged
    /// ENSURES: All `Level::Param(name)` where `name` is in `subst` are replaced
    /// ENSURES: Level parameters not in `subst` are preserved
    /// ENSURES: Expression structure is preserved (only levels change)
    /// ENSURES: Deterministic - same inputs yield same output
    pub fn instantiate_level_params(&self, subst: &[(Name, Level)]) -> Expr {
        if subst.is_empty() {
            return self.clone();
        }
        // Build HashMap once for O(1) lookup during recursive traversal
        let subst_map: HashMap<Name, Level> = subst.iter().cloned().collect();
        self.instantiate_level_params_map(&subst_map)
    }

    /// Substitute universe parameters from parallel name/level slices.
    ///
    /// For up to 4 parameters, uses linear scan to avoid allocating a `HashMap`.
    /// For larger substitutions, falls back to the existing map-backed path.
    pub fn instantiate_level_params_direct(&self, params: &[Name], levels: &[Level]) -> Expr {
        // No length assertion needed — provably panic-free for any relative lengths:
        // both paths consume the slices via `zip` (the small-`params` folder through
        // `Level::substitute_slice`, the large path through `params.iter().zip(levels)`
        // below), and `zip` truncates to the shorter slice rather than indexing out of
        // bounds. Callers also pass matching lists. So no skip / cfg-gate / contract is
        // needed; the verifier discharges it directly.
        if params.is_empty() {
            return self.clone();
        }
        if params.len() <= SMALL_LEVEL_PARAM_SUBST_THRESHOLD {
            let mut folder = LevelParamSubstSlice {
                params,
                levels,
                memo: FoldMemo::default(),
            };
            self.fold_opt_or_clone(&mut folder)
        } else {
            let subst_map: HashMap<Name, Level> =
                params.iter().cloned().zip(levels.iter().cloned()).collect();
            self.instantiate_level_params_map(&subst_map)
        }
    }

    /// Apply level parameter substitution using a pre-built HashMap.
    ///
    /// Public because ZFCSetExpr needs to call this on contained Expr values.
    pub(crate) fn instantiate_level_params_map(&self, subst: &HashMap<Name, Level>) -> Expr {
        let mut folder = LevelParamSubst {
            subst,
            memo: FoldMemo::default(),
        };
        self.fold_opt_or_clone(&mut folder)
    }
}

#[cfg(test)]
mod dag_sharing_tests {
    use crate::expr::{Expr, ExprKind};
    use std::collections::HashSet;
    use std::sync::Arc;

    /// Count DISTINCT `Arc<Expr>` identities reachable from `e` (true DAG size).
    /// A blowup that loses sharing makes this explode toward the TREE size.
    fn dag_node_count(e: &Expr) -> usize {
        fn children(e: &Expr) -> Vec<Arc<Expr>> {
            match e.kind() {
                ExprKind::App(f, a) => vec![f.clone(), a.clone()],
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => vec![t.clone(), b.clone()],
                _ => vec![],
            }
        }
        fn go(e: &Expr, seen: &mut HashSet<usize>) -> usize {
            let mut n = 1;
            for c in children(e) {
                if seen.insert(Arc::as_ptr(&c) as usize) {
                    n += go(&c, seen);
                }
            }
            n
        }
        go(e, &mut HashSet::new())
    }

    /// Build a DAG that mimics match-lowering fan-out: at each level the SAME
    /// shared `Arc` child (carrying a loose `BVar(0)`) appears in BOTH `App`
    /// positions. With `levels` levels the term is `2^levels` nodes as a TREE but
    /// only `O(levels)` distinct `Arc` nodes as a DAG.
    fn shared_dag(levels: usize) -> Expr {
        let mut node = Expr::app(Expr::bvar(0), Expr::const_str("leaf"));
        for _ in 0..levels {
            let arc = Arc::new(node);
            node = Expr::from_kind(ExprKind::App(arc.clone(), arc));
        }
        node
    }

    /// REGRESSION (Track XX): `instantiate` must preserve `Arc`-sharing on a DAG.
    /// Before the pointer-identity memo a 25-node DAG ballooned to 12.5M nodes,
    /// stalling the full-corpus Mathlib re-verify. The output DAG size must stay
    /// within a small constant factor of the input — never the tree size.
    #[test]
    fn test_instantiate_preserves_dag_sharing() {
        for levels in [10usize, 18, 24] {
            let dag = shared_dag(levels);
            let out = dag.instantiate(&Expr::const_str("X"));
            let out_sz = dag_node_count(&out);
            assert!(
                out_sz <= 4 * (levels + 4),
                "instantiate lost DAG sharing: levels={levels} produced {out_sz} \
                 distinct nodes (tree size would be 2^{levels})"
            );
        }
    }

    /// REGRESSION (Track XX): `lift` must likewise preserve `Arc`-sharing.
    #[test]
    fn test_lift_preserves_dag_sharing() {
        for levels in [10usize, 18, 24] {
            let dag = shared_dag(levels);
            let out = dag.lift(1);
            let out_sz = dag_node_count(&out);
            assert!(
                out_sz <= 4 * (levels + 4),
                "lift lost DAG sharing: levels={levels} produced {out_sz} distinct nodes"
            );
        }
    }

    /// REGRESSION (Track XX): `instantiate_rev` (multi-arg) must preserve sharing.
    #[test]
    fn test_instantiate_rev_preserves_dag_sharing() {
        for levels in [10usize, 18, 24] {
            let dag = shared_dag(levels);
            // Two vals so it routes through MultiInstantiator (not the n==1 alias).
            let out = dag.instantiate_rev(&[Expr::const_str("X"), Expr::const_str("Y")]);
            let out_sz = dag_node_count(&out);
            assert!(
                out_sz <= 4 * (levels + 4),
                "instantiate_rev lost DAG sharing: levels={levels} produced {out_sz} nodes"
            );
        }
    }

    /// CORRECTNESS: the memo must not change the RESULT of instantiation. On a
    /// plain (non-shared) tree the memoized fold yields exactly the term the
    /// unmemoized fold would: `(λ. BVar(0) BVar(1)) [X]` → `X (BVar 0)`.
    #[test]
    fn test_instantiate_result_unchanged_by_memo() {
        // body = App(BVar(0), BVar(1)); instantiate BVar(0)→X, shift BVar(1)→BVar(0).
        let body = Expr::app(Expr::bvar(0), Expr::bvar(1));
        let out = body.instantiate(&Expr::const_str("X"));
        let expected = Expr::app(Expr::const_str("X"), Expr::bvar(0));
        assert_eq!(
            out, expected,
            "instantiate result must be unaffected by the memo"
        );
    }
}

/// Tests for [`Expr::lower_loose_bvars`] (B0 of
/// `designs/2026-07-02-parameterized-nested-inductives.md`).
#[cfg(test)]
mod lower_loose_bvars_tests {
    use crate::expr::{BinderInfo, Expr};

    #[test]
    fn test_lower_zero_is_identity() {
        let e = Expr::app(Expr::bvar(0), Expr::const_str("c"));
        assert_eq!(
            e.lower_loose_bvars(0),
            Some(e.clone()),
            "lowering by 0 must be the identity"
        );
    }

    #[test]
    fn test_lower_closed_expr_unchanged() {
        let e = Expr::app(Expr::const_str("f"), Expr::const_str("x"));
        assert_eq!(
            e.lower_loose_bvars(7),
            Some(e.clone()),
            "closed expressions lower to themselves for any k"
        );
    }

    #[test]
    fn test_lower_loose_bvar_shifts_down() {
        assert_eq!(
            Expr::bvar(3).lower_loose_bvars(2),
            Some(Expr::bvar(1)),
            "loose BVar(3) lowered by 2 must become BVar(1)"
        );
    }

    #[test]
    fn test_lower_boundary_values() {
        // idx == k is the smallest lowerable loose bvar.
        assert_eq!(
            Expr::bvar(2).lower_loose_bvars(2),
            Some(Expr::bvar(0)),
            "BVar(k) lowers to BVar(0)"
        );
        // idx == k - 1 refers to a removed binder: must fail.
        assert_eq!(
            Expr::bvar(1).lower_loose_bvars(2),
            None,
            "BVar(k-1) must refuse to lower"
        );
        assert_eq!(
            Expr::bvar(0).lower_loose_bvars(1),
            None,
            "BVar(0) must refuse to lower by 1"
        );
    }

    #[test]
    fn test_lower_ignores_bound_bvars_under_binder() {
        // Π (x : BVar(5)). BVar(0) BVar(6)
        //   domain BVar(5): root-loose, k=2 → BVar(3)
        //   body BVar(0):   bound by the Pi → untouched
        //   body BVar(6):   loose at depth 1 (root-relative 5) → BVar(4)
        let e = Expr::pi(
            BinderInfo::Default,
            Expr::bvar(5),
            Expr::app(Expr::bvar(0), Expr::bvar(6)),
        );
        let expected = Expr::pi(
            BinderInfo::Default,
            Expr::bvar(3),
            Expr::app(Expr::bvar(0), Expr::bvar(4)),
        );
        assert_eq!(
            e.lower_loose_bvars(2),
            Some(expected),
            "bound bvars must be untouched; loose bvars lowered root-relative"
        );
    }

    #[test]
    fn test_lower_fails_on_loose_bvar_under_binder() {
        // Π (x : c). BVar(2) — at depth 1, root-relative index is 1 < k=2.
        let e = Expr::pi(BinderInfo::Default, Expr::const_str("c"), Expr::bvar(2));
        assert_eq!(
            e.lower_loose_bvars(2),
            None,
            "a root-relative loose bvar below k under a binder must refuse"
        );
    }

    #[test]
    fn test_lower_inverts_lift() {
        // Mixed expression with loose and bound bvars.
        let e = Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(1), Expr::const_str("c")),
            Expr::app(Expr::bvar(0), Expr::bvar(3)),
        );
        for k in [1u32, 2, 5] {
            assert_eq!(
                e.lift(k).lower_loose_bvars(k),
                Some(e.clone()),
                "lower_loose_bvars({k}) must invert lift({k})"
            );
        }
    }

    #[test]
    fn test_lower_then_lift_round_trips() {
        let e = Expr::app(Expr::bvar(4), Expr::bvar(2));
        let lowered = e
            .lower_loose_bvars(2)
            .expect("all loose bvars are >= 2, lowering must succeed");
        assert_eq!(
            lowered.lift(2),
            e,
            "lift(k) must invert a successful lower_loose_bvars(k)"
        );
    }
}

/// Direct unit tests for [`Expr::beta_normalize`]
/// (`designs/2026-07-05-nested-dependent-param-container.md` §5.1.1).
#[cfg(test)]
mod beta_normalize_tests {
    use crate::expr::{BinderInfo, Expr};

    /// A `fun _ : D => body` with an irrelevant domain.
    fn lam(body: Expr) -> Expr {
        Expr::lam(BinderInfo::Default, Expr::const_str("D"), body)
    }

    /// No redex anywhere ⇒ beta_normalize is the identity (the §7.1 regression
    /// guarantee for every non-dependent-container family).
    #[test]
    fn test_beta_normalize_no_redex_is_identity() {
        // f (g x) — application spine with Const heads, no Lam in fn position.
        let e = Expr::app(
            Expr::const_str("f"),
            Expr::app(Expr::const_str("g"), Expr::const_str("x")),
        );
        assert_eq!(e.beta_normalize(), e, "redex-free term must be unchanged");

        // A Pi whose field is a bare block application — the Json/Trie shape
        // AFTER the rewriter, never a redex.
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::const_str("Ty"),
            Expr::app(Expr::const_str("C"), Expr::bvar(0)),
        );
        assert_eq!(
            pi.beta_normalize(),
            pi,
            "Pi with no redex must be unchanged"
        );
    }

    /// A lambda that is NOT applied is left intact (a `fun x => V` sitting in
    /// ARGUMENT position — the surviving `Impl α (fun x => V)` self-reference
    /// the worklist rewriter still needs, design §5.1 placement note).
    #[test]
    fn test_beta_normalize_unapplied_lambda_untouched() {
        // C α (fun _ => V)  — head Const, the Lam is an argument, not a redex.
        let e = Expr::app(
            Expr::app(Expr::const_str("C"), Expr::bvar(0)),
            lam(Expr::const_str("V")),
        );
        assert_eq!(
            e.beta_normalize(),
            e,
            "a lambda in argument position is not a redex and must survive"
        );
    }

    /// The const-map shape `(fun x => V) k ↦ V` (V closed): the exact Json
    /// field defect.
    #[test]
    fn test_beta_normalize_const_map_redex() {
        // (fun _ => Json) k  ↦  Json
        let redex = Expr::app(lam(Expr::const_str("Json")), Expr::const_str("k"));
        assert_eq!(
            redex.beta_normalize(),
            Expr::const_str("Json"),
            "const-map redex must reduce to the map body"
        );
    }

    /// Redex in ARGUMENT position: `f ((fun x => x) c) ↦ f c`.
    #[test]
    fn test_beta_normalize_redex_in_argument() {
        let inner = Expr::app(lam(Expr::bvar(0)), Expr::const_str("c"));
        let e = Expr::app(Expr::const_str("f"), inner);
        let expected = Expr::app(Expr::const_str("f"), Expr::const_str("c"));
        assert_eq!(
            e.beta_normalize(),
            expected,
            "a redex nested in an argument must be contracted"
        );
    }

    /// Redex UNDER a binder with correct de-Bruijn instantiation (the §7.4
    /// `PrefixTreeNode` p=3 hazard, in miniature): under the outer Pi the
    /// const-map body's telescope bvar sits at depth +1; contracting
    /// `(fun x => C α) α` must decrement it back so the reduced `C α` carries
    /// the telescope bvar at the depth the strict gate expects.
    #[test]
    fn test_beta_normalize_redex_under_binder_debruijn() {
        // Π (α : Ty). (fun _x => C #1) #0   ↦   Π (α : Ty). C #0
        // Inside the Pi body (depth 1): #0 = α (the Pi binder = the map index).
        // Inside the lam body (depth 2): #1 = α (skipping x = #0).
        let field = Expr::app(
            lam(Expr::app(Expr::const_str("C"), Expr::bvar(1))),
            Expr::bvar(0),
        );
        let e = Expr::pi(BinderInfo::Default, Expr::const_str("Ty"), field);
        let expected = Expr::pi(
            BinderInfo::Default,
            Expr::const_str("Ty"),
            Expr::app(Expr::const_str("C"), Expr::bvar(0)),
        );
        assert_eq!(
            e.beta_normalize(),
            expected,
            "the telescope bvar must be decremented by exactly the dropped binder"
        );
    }

    /// Nested / curried redexes where the OUTER application only becomes a
    /// redex after the inner one is contracted: `((fun x => fun y => x) a) b ↦ a`.
    #[test]
    fn test_beta_normalize_nested_curried_redex() {
        let curried = lam(lam(Expr::bvar(1))); // fun x => fun y => x
        let e = Expr::app(
            Expr::app(curried, Expr::const_str("a")),
            Expr::const_str("b"),
        );
        assert_eq!(
            e.beta_normalize(),
            Expr::const_str("a"),
            "outer redex exposed by inner contraction must also reduce"
        );
    }

    /// A contraction whose SUBSTITUTION exposes a fresh redex must be
    /// re-normalized: `(fun f => f a) (fun x => x) ↦ a`.
    #[test]
    fn test_beta_normalize_substitution_exposes_redex() {
        // fun f => f a
        let outer = lam(Expr::app(Expr::bvar(0), Expr::const_str("a")));
        // (fun f => f a) (fun x => x)
        let e = Expr::app(outer, lam(Expr::bvar(0)));
        assert_eq!(
            e.beta_normalize(),
            Expr::const_str("a"),
            "the redex exposed by substituting the identity must be contracted"
        );
    }
}

/// Boundary / totality tests for the arithmetic-hardened fold family in this
/// module: [`Expr::has_loose_bvar`], [`MultiInstantiator::fold_bvar_opt`], and
/// [`Lowerer::fold_bvar_opt`]. Each pins the behavior at the input that used to
/// overflow (`idx + 1`, `depth + n`) or trip a `debug_assert` panic arm.
#[cfg(test)]
mod arith_hardening_tests {
    use super::{FoldMemo, Lowerer, MultiInstantiator};
    use crate::expr::{Expr, ExprFolderOpt};

    // ── (a) has_loose_bvar: total for every u32, incl. u32::MAX / u32::MAX-1 ──

    #[test]
    fn test_has_loose_bvar_max_index_is_total_and_false() {
        // Closed expression: no loose bvar exists at ANY index.
        let closed = Expr::const_str("c");
        assert!(
            !closed.has_loose_bvar(u32::MAX),
            "closed: no bvar at u32::MAX"
        );
        assert!(
            !closed.has_loose_bvar(u32::MAX - 1),
            "closed: no bvar at u32::MAX-1 (the sentinel edge)"
        );
        assert!(!closed.has_loose_bvar(0), "closed: no bvar at 0");

        // Expression with a single loose bvar at index 3.
        let e = Expr::bvar(3);
        assert!(e.has_loose_bvar(3), "bvar(3) has loose bvar 3");
        assert!(!e.has_loose_bvar(2), "bvar(3) has no loose bvar 2");
        assert!(!e.has_loose_bvar(4), "bvar(3) has no loose bvar 4");
        // The formerly-overflowing / sentinel-colliding queries: total, false.
        assert!(
            !e.has_loose_bvar(u32::MAX),
            "bvar(3): u32::MAX query is false"
        );
        assert!(
            !e.has_loose_bvar(u32::MAX - 1),
            "bvar(3): u32::MAX-1 query is false (no sentinel widening)"
        );
    }

    #[test]
    fn test_has_loose_bvar_at_max_bvar_index() {
        // The largest constructible loose bvar index.
        let e = Expr::bvar(Expr::MAX_BVAR_INDEX);
        assert!(
            e.has_loose_bvar(Expr::MAX_BVAR_INDEX),
            "the max-index bvar is detected at its own index"
        );
        assert!(
            !e.has_loose_bvar(u32::MAX),
            "querying u32::MAX on the max-index bvar is false, not a panic"
        );
    }

    // ── (b) MultiInstantiator::fold_bvar_opt: no `depth + n` overflow ──

    #[test]
    fn test_multi_instantiator_fold_bvar_no_overflow_at_max_depth() {
        // depth == u32::MAX, n == 1. The old `self.depth + n` overflowed here.
        let vals = [Expr::const_str("a")];
        let mut folder = MultiInstantiator {
            vals: &vals,
            depth: u32::MAX,
            memo: FoldMemo::default(),
        };
        // idx == depth: offset 0 < n=1 → substitute vals[0] (closed → lift is id).
        assert_eq!(
            folder.fold_bvar_opt(u32::MAX),
            Some(Expr::const_str("a")),
            "BVar(depth) at max depth substitutes vals[0] without overflow"
        );
        // idx < depth: below the window, unchanged.
        assert_eq!(
            folder.fold_bvar_opt(u32::MAX - 1),
            None,
            "BVar below max depth is unchanged (no overflow)"
        );
    }

    #[test]
    fn test_multi_instantiator_fold_bvar_matches_arithmetic_form() {
        // Ordinary (non-overflowing) inputs must match the old arithmetic branches.
        let vals = [Expr::const_str("a"), Expr::const_str("b")]; // n = 2
        let mut folder = MultiInstantiator {
            vals: &vals,
            depth: 2,
            memo: FoldMemo::default(),
        };
        // idx=1 < depth=2 → None.
        assert_eq!(folder.fold_bvar_opt(1), None, "below window → unchanged");
        // idx=2 in [2,4): offset 0 → vals[0] (closed) = "a".
        assert_eq!(
            folder.fold_bvar_opt(2),
            Some(Expr::const_str("a")),
            "window start → vals[0]"
        );
        // idx=3 in [2,4): offset 1 → vals[1] = "b".
        assert_eq!(
            folder.fold_bvar_opt(3),
            Some(Expr::const_str("b")),
            "window → vals[1]"
        );
        // idx=5 >= depth+n=4: shift down by n → BVar(3).
        assert_eq!(
            folder.fold_bvar_opt(5),
            Some(Expr::bvar(3)),
            "above window → shift down by n"
        );
    }

    // ── (c) Lowerer::fold_bvar_opt: total, no `debug_assert` panic ──

    #[test]
    fn test_lowerer_fold_bvar_in_domain_exact() {
        // Precondition holds (idx - start >= amount): exact lowered index.
        let mut lo = Lowerer {
            start: 0,
            amount: 5,
            memo: FoldMemo::default(),
        };
        assert_eq!(
            lo.fold_bvar_opt(7),
            Some(Expr::bvar(2)),
            "7 lowers by 5 → 2"
        );
        assert_eq!(
            lo.fold_bvar_opt(5),
            Some(Expr::bvar(0)),
            "5 lowers by 5 → 0"
        );
    }

    #[test]
    fn test_lowerer_fold_bvar_below_start_unchanged() {
        let mut lo = Lowerer {
            start: 4,
            amount: 2,
            memo: FoldMemo::default(),
        };
        assert_eq!(
            lo.fold_bvar_opt(1),
            None,
            "bvar below start is bound, left unchanged"
        );
    }

    #[test]
    fn test_lowerer_fold_bvar_off_domain_is_total_not_panic() {
        // idx >= start but idx - start < amount: the input the removed
        // `debug_assert` used to fault on. Must now saturate, not panic.
        let mut lo = Lowerer {
            start: 0,
            amount: 5,
            memo: FoldMemo::default(),
        };
        assert_eq!(
            lo.fold_bvar_opt(3),
            Some(Expr::bvar(0)),
            "off-domain (3 - 0 < 5) saturates to BVar(0) without panicking"
        );
    }
}
