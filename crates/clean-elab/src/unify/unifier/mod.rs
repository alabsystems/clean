// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unification algorithm for constraint solving.

mod pattern;
mod unify_expr;

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, Level, LocalContext, TypeChecker};
use std::cell::RefCell;
use std::collections::HashSet;

use super::meta_id::MetaId;
use super::meta_state::MetaState;

/// Result of a unification attempt.
///
/// Callers must treat `Stuck` as an error (typically `CannotInfer`).
/// `Stuck` means unification could not determine whether the types are equal,
/// e.g. due to unsolved metavariables. Silently accepting `Stuck` as success
/// would allow ill-typed terms to pass elaboration.
#[derive(Debug)]
pub enum UnifyResult {
    /// Unification succeeded — the two expressions are definitionally equal.
    Success,
    /// Unification failed — the expressions are definitionally unequal.
    Failure(String),
    /// Unification is stuck — cannot determine equality (e.g. unsolved metavariables).
    /// Must be treated as an error by callers; never silently accept as success.
    Stuck,
}

/// Unifier for constraint solving
///
/// # WHNF Reduction
///
/// The unifier reduces expressions to WHNF (weak head normal form) before
/// structural comparison. This is essential for correctly handling:
/// - Beta reduction: `(λ x. e) a` reduces to `e[a/x]`
/// - Delta reduction: constants unfold to their definitions
/// - Iota reduction: recursor applications reduce on constructors
/// - Zeta reduction: `let x := v in e` reduces to `e[v/x]`
///
/// Without WHNF reduction, the unifier would fail on expressions like:
/// ```text
/// (λ x. Prop) c  vs  Prop
/// ```
/// because the discriminants (App vs Sort) don't match.
///
/// See: `reports/2026-01-28-R325-elaborator-whnf-research.md`
pub struct Unifier<'a> {
    metas: &'a mut MetaState,
    /// Cached TypeChecker for WHNF reduction
    ///
    /// Using RefCell allows WHNF calls through &self while caching results.
    /// This is safe because TypeChecker::whnf() takes &self and only mutates
    /// its internal whnf_cache, which is also RefCell-based.
    ///
    /// Performance: Avoids creating a fresh TypeChecker (and cache) per try_whnf call.
    /// None means no WHNF capability (legacy mode for tests).
    tc_cache: RefCell<Option<TypeChecker<'a>>>,
    /// When `true`, an argument whose head is one of the protected bitwise
    /// constants (`Nat.land`/`lor`/`xor`) is NOT δ-unfolded while being assigned
    /// to a bare metavariable — preserving its surface head for a later
    /// head-pattern tactic. OFF by default; the `apply` tactic opts in via
    /// [`Unifier::with_protected_heads`] so that ONLY `apply`-conclusion
    /// unification is affected (e.g. `Nat.eq_of_testBit_eq` against
    /// `Nat.land m n = Nat.land n m`), leaving every other unification path
    /// (notably the `cases` motive/constructor matching) at its normal behavior.
    protect_heads: bool,
}

impl<'a> Unifier<'a> {
    /// Create a unifier without WHNF support (legacy)
    ///
    /// This constructor is kept for backwards compatibility with tests.
    /// For production use, prefer `with_env` which enables WHNF reduction.
    pub fn new(metas: &'a mut MetaState) -> Self {
        Self {
            metas,
            tc_cache: RefCell::new(None),
            protect_heads: false,
        }
    }

    /// Create a unifier with environment for WHNF reduction
    ///
    /// This enables proper WHNF reduction during unification, which is
    /// required for correctly handling beta/delta/iota/zeta reductions.
    pub fn with_env(metas: &'a mut MetaState, env: &'a Environment, ctx: LocalContext) -> Self {
        // Pre-create the TypeChecker so the WHNF cache persists across calls
        let tc = TypeChecker::with_context(env, ctx);
        // B14: unification-time WHNF/def-eq honors reducibility hints, so an
        // `@[irreducible]` definition stays folded when the unifier reduces
        // rigid heads (e.g. matching `rfl`'s `f =?= v`). Matches MetaM
        // `canUnfold` at `.default`; the kernel's final check stays blind.
        tc.set_honor_reducibility(true);
        let _ = env;
        Self {
            metas,
            tc_cache: RefCell::new(Some(tc)),
            protect_heads: false,
        }
    }

    /// Create a unifier that reduces at `withReducible` transparency (B15).
    ///
    /// Like [`Unifier::with_env`], but the WHNF/def-eq path unfolds ONLY
    /// `@[reducible]` (abbreviation) constants — `Regular` (semireducible),
    /// `@[irreducible]`, and theorem heads stay folded, matching MetaM
    /// `withReducible` / `canUnfold` at `.reducible`. `simp` uses this when
    /// matching lemma LHSs against a target so that a bare `def f := e`
    /// (semireducible) is opaque to lemma matching, exactly as in Lean 4's
    /// `simp` (`Lean/Meta/Tactic/Simp` runs at reducible transparency).
    ///
    /// Strictly narrowing relative to [`Unifier::with_env`]: it can only turn a
    /// former (semireducible-unfolding) match into a non-match.
    pub fn with_env_reducible(
        metas: &'a mut MetaState,
        env: &'a Environment,
        ctx: LocalContext,
    ) -> Self {
        let mut tc = TypeChecker::with_context(env, ctx);
        tc.set_transparency(clean_kernel::TransparencyMode::Reducible);
        tc.set_honor_reducibility(true);
        Self {
            metas,
            tc_cache: RefCell::new(Some(tc)),
            protect_heads: false,
        }
    }

    fn allowed_locals_for_meta(&self, meta_id: MetaId) -> Option<HashSet<clean_kernel::FVarId>> {
        let meta = self.metas.get(meta_id)?;
        Some(meta.locals.iter().map(|(_, fvar, _)| *fvar).collect())
    }

    /// Enable protected-head preservation (see [`Unifier::protect_heads`]).
    /// Used by `apply` so its conclusion unification keeps `Nat.land`/`lor`/`xor`
    /// surface heads for the subsequent `rw [Nat.testBit_and]`.
    #[must_use]
    pub fn with_protected_heads(mut self) -> Self {
        self.protect_heads = true;
        self
    }

    /// Returns `true` if protected-head preservation is enabled (apply only)
    /// AND `e`'s application head is one of the Track II bitwise constants
    /// (`Nat.land`/`lor`/`xor`). Such a head must NOT be δ-unfolded when the
    /// term is being assigned to a bare metavariable during unification: the
    /// surface head is load-bearing for the subsequent `rw [Nat.testBit_and]`.
    /// Keying on (a) the opt-in `protect_heads` flag — set only by `apply` — and
    /// (b) the exact constant names confines this to the `nat_land_comm`-style
    /// proofs and leaves every other unification path (notably `cases` motive /
    /// constructor matching in `Int.land_comm`) unchanged.
    pub(super) fn head_is_protected_def(&self, e: &Expr) -> bool {
        if !self.protect_heads {
            return false;
        }
        let head = e.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            let s = name.to_string();
            s == "Nat.land" || s == "Nat.lor" || s == "Nat.xor"
        } else {
            false
        }
    }

    /// Whether `left` and `right` are two applications whose ultimate spine
    /// heads are both *rigid constants* that cannot unify because their `Name`s
    /// differ or their spines have different arities.
    ///
    /// "Rigid" means the spine head is a `Const` and is NOT a metavariable /
    /// flex application (those are handled earlier by `try_pattern_unify` and the
    /// bare-meta checks in `unify_core_inner`). When this returns `true`, the
    /// App/App structural rule must NOT positionally pair the argument spines —
    /// doing so can bury a bare metavariable in one spine against a mismatched
    /// subterm of the other and spuriously "succeed". See the call site in
    /// `unify_expr.rs` for the `rw [Nat.add_zero]` failure this guards against.
    ///
    /// A `false` result means "do not block" — either side is not a rigid-const
    /// application, or the heads + arities agree (in which case the normal
    /// structural decomposition is correct).
    pub(super) fn rigid_spine_head_mismatch(&self, left: &Expr, right: &Expr) -> bool {
        let lhead = left.get_app_fn();
        let rhead = right.get_app_fn();
        // Heads must both be rigid constants. A metavar head (flex application)
        // is intentionally excluded so higher-order assignment still works.
        let (ExprKind::Const(lname, _), ExprKind::Const(rname, _)) = (lhead.kind(), rhead.kind())
        else {
            return false;
        };
        // Same const, same arity → the normal decomposition is correct; do not
        // block. Otherwise the two rigid applications cannot be def-eq by
        // congruence, so block the positional pairing.
        lname != rname || left.get_app_num_args() != right.get_app_num_args()
    }

    /// Check if WHNF reduction is available
    pub(super) fn has_whnf(&self) -> bool {
        self.tc_cache.borrow().is_some()
    }

    /// Push a fresh local FVar of type `ty` onto the cached typechecker's local
    /// context (if a typechecker is present) and return its `FVarId`. Used by
    /// the `Pi`/`Lam` body comparison to open a binder with a genuine local
    /// fvar so the Miller-pattern solver can solve `?f x =?= f x` (where `x`
    /// is the introduced fvar) instead of seeing a loose `BVar(0)` it cannot
    /// treat as a pattern argument. Mirrors Lean 4's `isDefEq` forallE/lambdaE
    /// path. Returns `None` in legacy (no-WHNF) mode; the caller then falls
    /// back to the old loose-BVar comparison.
    ///
    /// The cached checker owns a clone of the elaborator context, so its local
    /// allocator cannot see locals retained only in a metavariable's historical
    /// scope after the elaborator has popped them. Never reuse one of those
    /// numeric ids for the temporary binder: scope checks compare FVarIds, and
    /// an alias would otherwise make the temporary local look like a captured
    /// historical local and permit it to escape in a metavariable assignment.
    ///
    /// Each successful push MUST be matched by a [`Unifier::pop_binder_local`].
    pub(super) fn push_binder_local(&self, ty: &Expr) -> Option<clean_kernel::FVarId> {
        let tc_cache = self.tc_cache.borrow();
        let tc = tc_cache.as_ref()?;
        // The maintained superset replaces a per-crossing rebuild of the
        // exact captured-locals set (long unifier sessions cross millions
        // of binders; the rebuild was a measured constant-factor drag).
        // Superset ⇒ only MORE candidates rejected ⇒ no-alias preserved.
        let historical = self.metas.historical_local_fvars();
        debug_assert!(
            {
                let exact: HashSet<_> = self
                    .metas
                    .iter()
                    .flat_map(|(_, meta)| meta.locals.iter().map(|(_, fvar, _)| *fvar))
                    .collect();
                exact.iter().all(|f| historical.contains(f))
            },
            "historical_local_fvars must stay a superset of captured locals \
             (a new MetaVar::locals writer forgot to extend it)"
        );
        loop {
            let fvar = tc.push_binder_local(
                Name::anon(),
                ty.clone(),
                clean_kernel::BinderData::default(),
            );
            if !historical.contains(&fvar) {
                return Some(fvar);
            }
            // `LocalContext::used_ids` retains a popped id, so the next
            // allocation advances instead of returning the same collision.
            tc.pop_binder_local();
        }
    }

    /// Pop the binder local pushed by [`Unifier::push_binder_local`].
    pub(super) fn pop_binder_local(&self) {
        if let Some(tc) = self.tc_cache.borrow().as_ref() {
            tc.pop_binder_local();
        }
    }

    /// Reduce expression to WHNF if environment is available
    ///
    /// Uses cached TypeChecker to preserve WHNF cache across calls.
    pub(super) fn try_whnf(&self, e: &Expr) -> Expr {
        let tc_cache = self.tc_cache.borrow();
        if let Some(tc) = tc_cache.as_ref() {
            tc.whnf(e)
        } else {
            e.clone()
        }
    }

    /// Check if expression is an unsolved metavariable
    pub(super) fn as_meta(&self, expr: &Expr) -> Option<MetaId> {
        if let ExprKind::FVar(id) = expr.kind() {
            if let Some(meta_id) = MetaState::from_fvar(*id) {
                if self.metas.get(meta_id).is_some() {
                    return Some(meta_id);
                }
            }
        }
        None
    }

    /// If `pat` is a bare (unapplied, unassigned) metavariable, assign it the
    /// SURFACE form of `hay` (no WHNF reduction) and return `true`. Otherwise
    /// return `false` without touching state.
    ///
    /// Used by the `rw` head-keyed matcher to bind a rewrite-rule pattern
    /// argument `?a` to the goal's actual surface subterm, rather than to its
    /// δ-unfolded WHNF — so the subsequent SYNTACTIC `replace_expr` in
    /// `finish_rewrite` still locates the `from` pattern in the goal. Goes
    /// through `unify_meta`, which performs the occurs/level checks and
    /// instantiates (but does NOT WHNF) the assigned term.
    pub(crate) fn try_assign_bare_meta(&mut self, pat: &Expr, hay: &Expr) -> bool {
        if let Some(meta_id) = self.as_meta(pat) {
            matches!(self.unify_meta(meta_id, hay), UnifyResult::Success)
        } else {
            false
        }
    }

    pub(super) fn unify_meta(&mut self, meta_id: MetaId, other: &Expr) -> UnifyResult {
        let other = self.metas.instantiate(other);

        // Use occurs_in directly on the already-instantiated expression to avoid
        // the redundant O(n) re-instantiation inside occurs(). Part of #1921 F1.
        if MetaState::occurs_in(&other, meta_id) {
            return UnifyResult::Failure(format!("occurs check failed for {meta_id:?}"));
        }

        if let Some(existing) = self.metas.get_assignment(meta_id).cloned() {
            return self.unify_core(&existing, &other);
        }

        // A bare metavariable may depend only on the locals captured when it
        // was created. In particular, Pi/Lambda comparison opens binders with
        // temporary FVars; assigning one of those FVars to a metavariable that
        // predates the binder would let the local escape after the comparison
        // pops it. Miller-pattern assignments handle legitimate dependency on
        // an opened binder by abstracting the pattern arguments first. The bare
        // assignment path must therefore reject any non-meta FVar outside the
        // metavariable's recorded scope.
        //
        // This check must precede universe propagation because a rejected
        // assignment is observationally a no-op. This is a definite failure:
        // no later assignment may make this metavariable legally capture a
        // local outside its creation scope.
        if let Some(allowed) = self.allowed_locals_for_meta(meta_id) {
            if let Some(escaped) = pattern::find_escaping_fvar(&other, &allowed) {
                return UnifyResult::Failure(format!(
                    "metavariable {meta_id:?} cannot capture out-of-scope local {escaped:?}"
                ));
            }
            if pattern::find_scope_widening_meta(&other, &allowed, self.metas).is_some() {
                return UnifyResult::Stuck;
            }
        }

        // Get the metavar's expected type for universe level inference.
        // When the metavar itself stands for a type, assignments like `?α := β`
        // must still constrain β's sort, even if the expected sort is concrete
        // (for example `Type`). We only skip direct `Sort(_)` assignments here
        // because `infer_level_for_type(Sort u) = Succ u`, which would compare
        // the typing judgment level instead of the type's own level.
        //
        // There are two cases:
        // 1. The metavar is a type (e.g., ?α : Sort u), and we're assigning a type (e.g., Real)
        //    In this case, infer_level_for_type(Real) = Sort(1), so u = 1
        //
        // 2. The metavar is a value (e.g., ?x : T), and we're assigning a value (e.g., a^2)
        //    In this case, we need to check if T has parametric levels
        if let Some(meta) = self.metas.get(meta_id) {
            let meta_ty = meta.ty.clone();
            // If the metavar's type is Sort(...), the metavar itself stands for a type.
            if let ExprKind::Sort(expected_level) = meta_ty.kind() {
                let should_constrain_level =
                    expected_level.has_params() || !matches!(other.kind(), ExprKind::Sort(_));
                if should_constrain_level {
                    if let Some(inferred_level) = self.infer_level_for_type(&other) {
                        // Universe cumulativity: a type in Sort(l) also belongs
                        // to Sort(l') for any l' ≥ l. When both levels are
                        // concrete, check ≤ (e.g., ?α : Type can be assigned
                        // A : Prop because Sort(0) ≤ Sort(1)). When either
                        // level has params, use unify_levels to propagate
                        // constraints (e.g., ?α : Sort(u) := β needs u solved).
                        if !inferred_level.has_params() && !expected_level.has_params() {
                            if !Level::leq(&inferred_level, expected_level) {
                                return UnifyResult::Failure(format!(
                                    "universe level conflict: {expected_level:?} vs {inferred_level:?}"
                                ));
                            }
                        } else {
                            match self.unify_levels(expected_level, &inferred_level) {
                                UnifyResult::Success => {}
                                failure => return failure,
                            }
                        }
                    }
                }
            } else if meta_ty.has_level_param_quick() {
                // Non-Sort meta type with level params (e.g., ?m : Type u → Type v).
                // Infer the type of the assigned value and unify the two types to
                // propagate level constraints.
                //
                // Without this, assigning ?m := Except.{0} MyError (which has type
                // Type 0 → Type 0) to a meta of type Type u_2 → Type u_3 would not
                // constrain u_3 to 0, because the level params only appear in the
                // meta's TYPE, not in any expression that gets structurally unified.
                // Part of #3396.
                self.propagate_meta_type_levels(&meta_ty, &other);
            }
        }

        if self.metas.assign(meta_id, other) {
            UnifyResult::Success
        } else {
            UnifyResult::Failure(format!("failed to assign metavariable {meta_id:?}"))
        }
    }

    /// Propagate universe-level constraints from a metavariable's *type* to the
    /// value it is being assigned.
    ///
    /// When a metavariable `?m` has a type carrying level params that appear
    /// *only* in the type — never in a structurally-unified expression — solving
    /// `?m` by direct assignment (e.g. via Miller-pattern unification) leaves
    /// those params unconstrained. They then leak into the kernel term as
    /// uninstantiated `Level::Param` (the monad universe-normalization bug:
    /// `Pure.pure.{0, u_2}` where `u_2` should be `0`).
    ///
    /// We recover the missing constraints by inferring the assigned value's type
    /// and unifying it against `?m`'s declared type, exactly as the non-pattern
    /// `unify_meta` path does. This is best-effort: a failure here does not
    /// invalidate the assignment itself (the kernel re-checks the final term), so
    /// we discard the result. The work is gated on `has_level_param_quick()` so it
    /// is a no-op for the overwhelmingly common param-free meta types.
    pub(super) fn propagate_meta_type_levels(&mut self, meta_ty: &Expr, value: &Expr) {
        if !meta_ty.has_level_param_quick() {
            return;
        }
        let actual_ty = {
            let tc_cache = self.tc_cache.borrow();
            let Some(tc) = tc_cache.as_ref() else {
                return;
            };
            match tc.infer_type(value) {
                Ok(ty) => ty,
                Err(_) => return,
            }
        };
        // Instantiate levels in the meta type to resolve any already-solved
        // params before unification.
        let meta_ty_inst = self
            .metas
            .instantiate_levels(&self.metas.instantiate(meta_ty));
        let actual_ty_inst = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&actual_ty));
        // Non-fatal: level constraint propagation is best-effort.
        let _ = self.unify_core(&meta_ty_inst, &actual_ty_inst);
    }

    /// Try to infer the universe level for a type expression.
    ///
    /// Uses the cached TypeChecker to look up the type in the environment
    /// and extract the Sort level. Returns `None` if no environment is
    /// available or if the type is not a Sort.
    fn infer_level_for_type(&self, expr: &Expr) -> Option<Level> {
        match expr.kind() {
            // A Sort is a type itself - its level is Succ of the inner level
            ExprKind::Sort(level) => Some(Level::succ(level.clone())),
            // FVars, Constants, and Applications: look up the type in the environment
            ExprKind::FVar(_) | ExprKind::Const(_, _) | ExprKind::App(_, _) => {
                let tc_cache = self.tc_cache.borrow();
                let tc = tc_cache.as_ref()?;
                let inferred_ty = tc.infer_type(expr).ok()?;
                let inferred_ty = tc.whnf(&inferred_ty);
                match inferred_ty.kind() {
                    ExprKind::Sort(level) => Some(level.clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Unify two universe levels.
    ///
    /// Delegates to THE shared level solver (`unify::level_solve`, U2 rung
    /// 3a) — one arm set for both this primary site and `unify_ext`.
    pub(crate) fn unify_levels(&mut self, l1: &Level, l2: &Level) -> UnifyResult {
        crate::unify::level_solve::solve_level_eq(self.metas, l1, l2)
    }

    /// Try to unify two expressions
    pub fn unify(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        if std::env::var_os("CLEAN_UNIFY_TRACE").is_some() {
            let l: String = format!("{left:?}").chars().take(150).collect();
            let r: String = format!("{right:?}").chars().take(150).collect();
            eprintln!("unify-top: L={l} R={r}");
        }
        // Instantiate any assigned metavariables
        let left = self.metas.instantiate(left);
        let right = self.metas.instantiate(right);

        // Structural fast path BEFORE any reduction, mirroring the kernel's
        // `is_def_eq` ordering (ptr/structural short-circuit first, reduce
        // only on disagreement). Syntactically identical terms are def-eq
        // as-is — including when both sides share the same unsolved
        // metavariables, which then need no assignment. Reducing first is
        // not merely wasted work: for ground interpreter-style terms
        // (e.g. trust-ir's `stepNWithContext` at concrete fuel) whose
        // normal forms are catastrophically large, the reduce-first
        // ordering turned a byte-identical `A = A` theorem (proved by a
        // zero-metavariable `@rfl`) into a >12GB whnf that OOMs — the two
        // copies of `A` differed only in solved level metavariables, so we
        // instantiate levels before comparing. Measured reproducer:
        // trust-clean's `dataloop_composed_wall_reproducer`.
        let left = self.metas.instantiate_levels(&left);
        let right = self.metas.instantiate_levels(&right);
        if left == right {
            return UnifyResult::Success;
        }

        // Reduce to WHNF before structural comparison (#325)
        // This handles beta/delta/iota/zeta reductions that may expose
        // structurally equal expressions. For example:
        //   (λ x. Prop) c  ~~>  Prop
        // Without WHNF, we'd compare App vs Sort and fail.
        let left_whnf = self.try_whnf(&left);
        let right_whnf = self.try_whnf(&right);

        self.unify_core(&left_whnf, &right_whnf)
    }

    /// Unify `left` and `right` WITHOUT the eager leading WHNF that [`unify`]
    /// applies to both sides.
    ///
    /// `unify` reduces both sides to WHNF up front. That is the right default
    /// for the common case, but it is *wrong* when one side is a flex
    /// application whose head metavariable stands for a partially-applied
    /// definition: e.g. `?m ?α =?= StateT σ (Except ε) α`. Pre-WHNF unfolds the
    /// rigid `StateT … α` into its `Pi` body, leaving `App(?m, ?α) =?= Pi(…)` —
    /// a shape mismatch the structural dispatch cannot bridge, so `?m` (the
    /// carrier monad) never gets solved and leaks to the kernel as a free
    /// variable.
    ///
    /// Skipping only the *initial* WHNF lets the structural App rule decompose
    /// the spines, pairing `?m` with the partial application and `?α` with the
    /// final argument. `unify_core` still applies WHNF internally wherever the
    /// discriminants disagree (`unify_core_inner`, see the #325 path), so no
    /// genuine def-eq is lost. Soundness is unchanged: the kernel re-checks the
    /// instantiated term, so this can only solve metavars the constraint already
    /// determines.
    pub fn unify_no_initial_whnf(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        let left = self.metas.instantiate(left);
        let right = self.metas.instantiate(right);
        self.unify_core(&left, &right)
    }
}
