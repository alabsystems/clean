// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unification algorithm for constraint solving.

mod app_heads;
mod assignment;
mod constructors;
mod head_meta;
mod pattern;
mod postponed_args;
mod proof_irrel;
mod unify_expr;

#[cfg(test)]
mod assignment_tests;
#[cfg(test)]
mod congruence_tests;

use clean_kernel::expr::Literal;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, Level, LocalContext, TypeChecker};
use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::sync::LazyLock;

/// Cached `BitVec` type-former name for the payload-literal re-wrap in
/// [`Unifier::unify_meta`].
static BITVEC_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("BitVec"));
/// Cached `BitVec.ofNat` name for the payload-literal re-wrap.
static BITVEC_OF_NAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("BitVec.ofNat"));

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
    /// The checker's environment, for questions WHNF does not answer (a
    /// constant's reducibility hint, `app_heads.rs`). `None` without WHNF.
    env: Option<&'a Environment>,
    /// When `true`, an argument whose head is one of the protected bitwise
    /// constants (`Nat.land`/`lor`/`xor`) is NOT δ-unfolded while being assigned
    /// to a bare metavariable — preserving its surface head for a later
    /// head-pattern tactic. OFF by default; the `apply` tactic opts in via
    /// [`Unifier::with_protected_heads`] so that ONLY `apply`-conclusion
    /// unification is affected (e.g. `Nat.eq_of_testBit_eq` against
    /// `Nat.land m n = Nat.land n m`), leaving every other unification path
    /// (notably the `cases` motive/constructor matching) at its normal behavior.
    protect_heads: bool,
    /// Local declarations are immutable once pushed. Only the original prefix
    /// is eligible; temporarily extended binder contexts decline the shortcut.
    initial_context_len: usize,
    /// Inspect that exact original context only after admitting a real rigid
    /// candidate, then reuse the result without retaining/cloning the context.
    rigid_congruence_context: Cell<Option<bool>>,
    /// Nesting depth of [`Unifier::check_types_before_assign`] (see
    /// `assignment.rs`); bounds a cycle through ill-formed metavariable types.
    check_types_depth: Cell<u32>,
    /// Failed unreduced-first attempts of the App/App arm (see
    /// `app_heads.rs`); a budget that returns to the historical reduced
    /// comparison once spent.
    unreduced_failures: Cell<u32>,
}

impl<'a> Unifier<'a> {
    fn rigid_context_len(ctx: &LocalContext, metas: &MetaState) -> Option<usize> {
        if ctx.len() > 128 {
            return None;
        }
        let mut remaining = 256;
        ctx.iter()
            .all(|decl| {
                MetaState::from_fvar(decl.id)
                    .is_none_or(|id| metas.get(id).is_some_and(|meta| meta.assignment.is_some()))
                    && Self::rigid_expr(&decl.type_, &mut remaining)
                    && decl
                        .value
                        .as_ref()
                        .is_none_or(|value| Self::rigid_expr(value, &mut remaining))
            })
            .then_some(ctx.len())
    }

    /// Bounded, mutation-free eligibility check, including unknown tagged meta
    /// FVars. Cached flags prune ground subtrees. Unsupported expression forms
    /// and work-budget exhaustion decline the optimization, never unification.
    fn rigid_expr(expr: &Expr, remaining: &mut usize) -> bool {
        if expr.has_level_param_quick() {
            return false;
        }
        if !expr.has_fvar_quick() {
            return true;
        }
        // Fixed scratch avoids allocating for the common short symbolic spine.
        // Excess pending depth declines the optimization rather than recursing.
        let mut pending = [None; 32];
        pending[0] = Some(expr);
        let mut len = 1;
        while len != 0 {
            len -= 1;
            let Some(expr) = pending[len].take() else {
                return false;
            };
            if *remaining == 0 {
                return false;
            }
            *remaining -= 1;
            if !expr.has_fvar_quick() {
                continue;
            }
            let children: [Option<&Expr>; 3] = match expr.kind() {
                ExprKind::FVar(id) => {
                    if MetaState::from_fvar(*id).is_some() {
                        return false;
                    }
                    continue;
                }
                ExprKind::App(f, a) => [Some(f), Some(a), None],
                ExprKind::Pi(_, ty, body) | ExprKind::Lam(_, ty, body) => {
                    [Some(ty), Some(body), None]
                }
                ExprKind::Let(_, ty, value, body, _) => [Some(ty), Some(value), Some(body)],
                ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => {
                    [Some(inner), None, None]
                }
                _ => return false,
            };
            for child in children.into_iter().flatten() {
                if len == pending.len() {
                    return false;
                }
                pending[len] = Some(child);
                len += 1;
            }
        }
        true
    }

    fn allowed_locals_for_meta(&self, meta_id: MetaId) -> Option<HashSet<clean_kernel::FVarId>> {
        let meta = self.metas.get(meta_id)?;
        Some(meta.locals.iter().map(|(_, fvar, _)| *fvar).collect())
    }

    /// Enable protected-head preservation (see [`Unifier::protect_heads`]).
    /// Used by `apply` so its conclusion unification keeps `Nat.land`/`lor`/`xor`
    /// surface heads for the subsequent `rw [Nat.testBit_and]`.
    #[must_use]
    pub(crate) fn with_protected_heads(mut self) -> Self {
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
            // Normal callers pair temporary pushes/pops. If that private
            // discipline is violated, never reuse admission for a replacement
            // prefix merely because it later has the original length again.
            if tc.local_context_len() <= self.initial_context_len {
                self.rigid_congruence_context.set(Some(false));
            }
            tc.pop_binder_local();
        }
    }

    /// Reduce expression to WHNF if environment is available
    ///
    /// Uses cached TypeChecker to preserve WHNF cache across calls.
    ///
    /// An assigned metavariable at the head is read first, as Lean's
    /// `whnfCore` does (`head_meta.rs`).
    pub(super) fn try_whnf(&self, e: &Expr) -> Expr {
        let instantiated = self.instantiate_assigned_head(e);
        let e = instantiated.as_ref().unwrap_or(e);
        let tc_cache = self.tc_cache.borrow();
        if let Some(tc) = tc_cache.as_ref() {
            tc.whnf(e)
        } else {
            e.clone()
        }
    }

    /// Reuse the kernel's same-head argument congruence before eager delta
    /// reduction. This is only an affirmative fast path: declining, a failed
    /// comparison, or an exhausted checker leaves the historical solver next.
    ///
    /// No metavariable is solved here. Requiring all existing expression metas
    /// to be assigned also covers metas hidden in local-let values, not merely
    /// those visible in these two expressions. Parameterized levels stay with
    /// the existing level solver. The small eligibility budgets only abandon
    /// this optimization; they impose no new limit on accepted input.
    fn try_rigid_congruence(&self, left: &Expr, right: &Expr) -> bool {
        const MAX_SPINE: usize = 64;
        const MAX_META_ENTRIES: usize = 128;

        let (mut left_head, mut right_head) = (left, right);
        let mut arity = 0;
        while let (ExprKind::App(lf, la), ExprKind::App(rf, ra)) =
            (left_head.kind(), right_head.kind())
        {
            if arity == MAX_SPINE {
                return false;
            }
            // Argument congruence cannot establish unequal literals. Decline
            // before scanning meta/context closures or probing the defeq cache;
            // the ordinary head reduction may legitimately ignore this slot.
            if matches!((la.kind(), ra.kind()), (ExprKind::Lit(_), ExprKind::Lit(_))) && la != ra {
                return false;
            }
            arity += 1;
            left_head = lf;
            right_head = rf;
        }
        if arity == 0 || !matches!(left_head.kind(), ExprKind::Const(..)) || left_head != right_head
        {
            return false;
        }
        let tc_cache = self.tc_cache.borrow();
        let Some(tc) = tc_cache.as_ref() else {
            return false;
        };
        if tc.heartbeat_spent()
            || self.initial_context_len != tc.local_context_len()
            || left.has_level_param_quick()
            || right.has_level_param_quick()
        {
            return false;
        }
        for (index, (_, meta)) in self.metas.iter().enumerate() {
            if index == MAX_META_ENTRIES || meta.assignment.is_none() {
                return false;
            }
        }
        let mut remaining = 256;
        if !Self::rigid_expr(left, &mut remaining) || !Self::rigid_expr(right, &mut remaining) {
            return false;
        }
        let context_eligible = match self.rigid_congruence_context.get() {
            Some(eligible) => eligible,
            None => {
                // Drop the immutable borrow before any checker operation that
                // might temporarily push locals. No extra context owner/copy.
                let eligible = {
                    let context = tc.local_context();
                    Self::rigid_context_len(&context, self.metas) == Some(self.initial_context_len)
                };
                self.rigid_congruence_context.set(Some(eligible));
                eligible
            }
        };
        if !context_eligible {
            return false;
        }

        // Use the already configured checker: transparency, the ambient
        // declaration budget, heartbeat accounting, and caches are retained.
        // In particular, do not use the elaborator's lenient Bool/Prop fallback
        // as evidence for this shortcut and do not reset any checker budget.
        // Check corresponding arguments only. If one differs, leave unfolding
        // of this head (which may ignore that argument) to the old path rather
        // than asking whole-app defeq to do that work speculatively too.
        for (left_arg, right_arg) in left.get_app_args_iter().zip(right.get_app_args_iter()) {
            if left_arg != right_arg && (!tc.is_def_eq(left_arg, right_arg) || tc.heartbeat_spent())
            {
                return false;
            }
        }
        true
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

    /// Re-wrap a kernel-internal BitVec payload literal into its well-typed
    /// spelling before it can be STORED as a metavariable solution.
    ///
    /// The kernel's def-eq machinery represents a fully reduced `BitVec w`
    /// value as a bare `Lit(Nat payload)` — a canonical form that is valid
    /// ONLY inside `whnf`/`is_def_eq` recursion. `infer_type` (correctly)
    /// types `Lit(Nat _)` as `Nat`, never as `BitVec w`: accepting one
    /// literal at two types would break typing. The unifier, however,
    /// compares WHNF'd forms and assigns what it compared, so a constraint
    /// `?a =?= t` with `t : BitVec w` and `whnf(t) = Lit(Nat p)` would store
    /// the payload literal in the elaborated term, and the kernel re-check
    /// then rejects the declaration ("expected BitVec w, got Nat").
    ///
    /// The reference (standalone) Clean stack never hits this because its
    /// `BitVec.ofNat` native reducer fires only on operands ALREADY in bare
    /// payload form, which no elaborator-visible term contains — the payload
    /// convention stays confined to kernel def-eq internals. This stack's
    /// reducers additionally fire on surface spellings (`OfNat.ofNat`-wrapped
    /// and pre-WHNF'd composite operands, for the multi-limb pipeline), so
    /// the confinement must be re-established here, at the single point where
    /// a compared term becomes a stored term.
    ///
    /// The wrap: when the solution is a bare Nat literal and the metavar's
    /// (instantiated, WHNF'd) type is `BitVec w`, store `BitVec.ofNat w p`
    /// instead of `p`. `BitVec.ofNat w p` is the definitional spelling of
    /// exactly the value the payload denotes (`BitVec.ofNat w p` natively
    /// reduces to `p mod 2^w`, and a whnf-produced payload is already
    /// reduced mod `2^w`), so this substitutes one spelling of the same
    /// value, never a different value — and it is fail-closed regardless:
    /// the kernel re-checks every declaration built from this assignment,
    /// with typing and def-eq untouched. Metavars typed `Nat` (where a bare
    /// literal is correctly typed) and every non-literal solution pass
    /// through unchanged.
    fn rewrap_bitvec_payload_solution(&self, meta_id: MetaId, other: Expr) -> Expr {
        if !matches!(other.kind(), ExprKind::Lit(Literal::Nat(_))) {
            return other;
        }
        let Some(meta) = self.metas.get(meta_id) else {
            return other;
        };
        let ty = meta.ty.clone();
        let ty = self.metas.instantiate(&ty);
        let ty = self.try_whnf(&ty);
        // `BitVec w` is `App(Const(BitVec, []), w)`.
        let ExprKind::App(f, w) = ty.kind() else {
            return other;
        };
        let ExprKind::Const(name, _) = f.kind() else {
            return other;
        };
        if *name != *BITVEC_NAME {
            return other;
        }
        Expr::app(
            Expr::app(
                Expr::const_(BITVEC_OF_NAT_NAME.clone(), Vec::<Level>::new()),
                w.as_ref().clone(),
            ),
            other,
        )
    }

    pub(super) fn unify_meta(&mut self, meta_id: MetaId, other: &Expr) -> UnifyResult {
        let other = self.metas.instantiate(other);
        let other = self.rewrap_bitvec_payload_solution(meta_id, other);

        // Use occurs_in directly on the already-instantiated expression to avoid
        // the redundant O(n) re-instantiation inside occurs(). Part of #1921 F1.
        if MetaState::occurs_in(&other, meta_id) {
            return UnifyResult::Failure(format!("occurs check failed for ?m{}", meta_id.0));
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
                    "metavariable ?m{} cannot capture out-of-scope local {}",
                    meta_id.0,
                    crate::error_render::fvar(escaped, None)
                ));
            }
            // A metavariable of `other` minted in a WIDER context than
            // `?m`'s: Lean's `ctxApprox` narrows it to `?m`'s context and
            // proceeds (`assignment.rs`); where Lean would refuse, so do we,
            // and the constraint stays `Stuck` for a later retry.
            if pattern::find_scope_widening_meta(&other, &allowed, self.metas).is_some()
                && !self.approximate_context(meta_id, &allowed, &other)
            {
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
            let meta_ty_raw = meta.ty.clone();
            // A metavariable's `ty` is stored UNINSTANTIATED, and neither arm
            // below looks through an assignment. That is inert for the common
            // ground type (`?x : Nat`), but a HOLE's type is itself a
            // metavariable — `elab_hole` mints `?h : ?t` — so by the time `?h`
            // is solved, `?t` typically already stands for a real `Sort u`
            // while `meta.ty` still reads the bare `FVar(?t)`. `FVar` is not
            // `Sort(_)` and carries no level param, so BOTH arms were skipped
            // and the callee's universe was never constrained at all: the
            // measured `theorem forallTrueIff : (α → True) ↔ True := impTrue _`
            // registered `impTrue.{u_4} α` with `u_4` free of `α`'s `u_3`,
            // generalized both, and was rejected by the kernel with
            // `expected Sort(u_4), got Sort(u_3) … at body of lambda`.
            //
            // So resolve the type before dispatching — Lean's
            // `checkTypesAndAssign` works on `instantiateMVars mvarType`. The
            // work is confined to the case that previously did NOTHING: a type
            // already `Sort(_)` or already carrying a level param takes the
            // arms it always took, on the same expression as before, and a
            // meta-free type cannot change under instantiation. So this ADDS
            // constraint propagation where there was none and alters none that
            // existed.
            //
            // Ordered cheapest-first so the hot path pays nothing new: an
            // `ExprKind` discriminant, then two O(1) metadata bits, and only a
            // type that is fvar-bearing AND meta-bearing is walked. A ground
            // `?x : Nat` — the overwhelming majority — exits on
            // `has_fvar_quick`.
            let meta_ty = if matches!(meta_ty_raw.kind(), ExprKind::Sort(_))
                || meta_ty_raw.has_level_param_quick()
                || !meta_ty_raw.has_fvar_quick()
                || !Self::expr_mentions_meta(&meta_ty_raw)
            {
                meta_ty_raw
            } else {
                self.metas.instantiate(&meta_ty_raw)
            };
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
                                    "universe level conflict: {} vs {}",
                                    crate::error_render::level(expected_level),
                                    crate::error_render::level(&inferred_level)
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

            // TYPE-GUARDED head projection for FUNCTION-typed metavariables.
            //
            // The first-order App decomposition proposes spine-head
            // projections without ever comparing types: `?f a =?= g b` pairs
            // `?f := g` positionally. When `g`'s argument is itself an
            // application, that projection can be TYPE-INCORRECT — the
            // postponed-lambda `congrArg` shape reaches here as
            //   `?f (state.scalar name) =?= Ev s n (Value.nat (state.scalar name))`
            // pairing `?f : Nat → Prop` with `Ev s n : Value → Prop`. The
            // assignment then poisons every consumer of `?f` (`?a := ?f a₁`
            // instantiates to the ill-typed `Ev s n a₁`), and the eventual
            // failure surfaces far away as an opaque shape mismatch with a
            // mangled expected type (the trust-spec-temporal FiniteModel
            // `exactScalarVar` regression).
            //
            // Lean's assignment path type-checks (`checkTypesAssign`); mirror
            // the piece of that check this bug class needs: when BOTH the
            // metavariable's type and the candidate's inferred type are Pis
            // with META-FREE domains, the domains must be kernel-def-eq.
            // Returning Stuck (not Failure) leaves the constraint for retry
            // once the real argument pins the head — exactly Lean's postpone.
            // Conservative on purpose: any meta in either domain, or a failed
            // type inference (e.g. `other` mentions elaborator metas the
            // kernel cannot type), skips the guard and keeps prior behavior.
            {
                let tc_cache = self.tc_cache.borrow();
                if let Some(tc) = tc_cache.as_ref() {
                    let meta_ty_whnf = tc.whnf(&self.metas.instantiate(&meta_ty));
                    if let ExprKind::Pi(_, meta_dom, _) = meta_ty_whnf.kind() {
                        if !Self::expr_mentions_meta(meta_dom) {
                            if let Ok(other_ty) = tc.infer_type(&other) {
                                let other_ty_whnf = tc.whnf(&self.metas.instantiate(&other_ty));
                                if let ExprKind::Pi(_, other_dom, _) = other_ty_whnf.kind() {
                                    // Narrow deliberately: fire ONLY when both
                                    // domains whnf to DIFFERENTLY-NAMED rigid
                                    // Const heads that kernel def-eq cannot
                                    // reconcile (`Nat` vs `Value`). Anything
                                    // subtler — level metas, local fvars,
                                    // reducibility-shadowed equalities — keeps
                                    // the prior permissive behavior, so the
                                    // do-notation flex-monad projections
                                    // (`?m ?α =?= StateT σ (Except ε) α`) are
                                    // untouched.
                                    let meta_head = tc.whnf(meta_dom);
                                    let other_head = tc.whnf(other_dom);
                                    if let (
                                        ExprKind::Const(meta_name, _),
                                        ExprKind::Const(other_name, _),
                                    ) = (
                                        meta_head.get_app_fn().kind(),
                                        other_head.get_app_fn().kind(),
                                    ) {
                                        if meta_name != other_name
                                            && !Self::expr_mentions_meta(other_dom)
                                            && !tc.is_def_eq(&meta_head, &other_head)
                                        {
                                            return UnifyResult::Stuck;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Lean's `checkTypesAndAssign`: `?m`'s type against `other`'s, so a
        // type implicit reachable only through `?m`'s type is solved
        // (`assignment.rs`). Unifying the types cannot normally solve `?m`
        // itself, but a nested assignment's own type check could; honour an
        // assignment made that way instead of failing to overwrite it.
        self.check_types_before_assign(meta_id, &other);
        if let Some(existing) = self.metas.get_assignment(meta_id).cloned() {
            return self.unify_core(&existing, &other);
        }

        if std::env::var_os("CLEAN_UNIFY_TRACE").is_some() {
            let t: String = format!("{other:?}").chars().take(2000).collect();
            eprintln!("meta-assign: {meta_id:?} := {t}");
            eprintln!(
                "assign-backtrace: {}",
                std::backtrace::Backtrace::force_capture()
            );
        }
        if self.metas.assign(meta_id, other) {
            UnifyResult::Success
        } else {
            UnifyResult::Failure(format!("failed to assign metavariable ?m{}", meta_id.0))
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
            // FVars, Constants, Applications — and, U2 stage 2 (2026-08-25),
            // Pi types: infer through the cached TypeChecker.
            //
            // Pi used to fall through to the `None` arm, so a Sort-typed
            // metavariable assigned a FUNCTION type never had its level
            // constrained AT ALL — the equation was never generated, not
            // mis-solved (the CLEAN_U2_HISTOGRAM discriminator for the
            // measured class: zero solver events). The minted `Sort ?u`
            // param then survived to `finalize_level_params`, was
            // GENERALIZED into the declaration's `level_params`, and the
            // mandatory kernel re-check refused the declaration with the
            // sub-class-B face (docs/analysis/u2-implementation-plan-2026-08-24.md
            // §1.2): `expected Sort(Param(u_N)), got Sort(Max(Succ(..), Succ(..)))`.
            // Measured minimal reproducer, builtin prelude:
            // `def f {α β : Type*} : (α → β) → (α → β) := id` — `id`'s
            // implicit `?A : Sort ?u` is assigned `α → β : Sort (max (u_0+1)
            // (u_1+1))`, and `?u` never met that level. Single-binder
            // spellings never hit this because their assigned type is an
            // FVar, which the arm below always handled — which is why the
            // face surfaced selectively on telescopes wide enough to need
            // `max` (Function.hasUncurryBase, Set.SeparatesPoints,
            // Pi.map_id). The kernel's own Pi inference supplies the
            // imax/max semantics; this arm stays best-effort (`.ok()?`)
            // exactly like the lookup cases. Lam/Let/Proj spellings of a
            // type remain out: no measured failure names them, and each
            // would widen the surface past the measured edge.
            ExprKind::FVar(_)
            | ExprKind::Const(_, _)
            | ExprKind::App(_, _)
            | ExprKind::Pi(_, _, _) => {
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
            let l: String = format!("{left:?}").chars().take(4000).collect();
            let r: String = format!("{right:?}").chars().take(4000).collect();
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

        // A harmless projected argument (e.g. layout.align = 8) must not force
        // expansion of the surrounding symbolic Nat.rec alignment predicate.
        // The checked 64-step regression previously remained in App WHNF
        // recursion beyond the bounded baseline observation. The kernel already
        // has same-head args-first conversion; reuse it without solving metas.
        if self.try_rigid_congruence(&left, &right) {
            return UnifyResult::Success;
        }
        // Two proofs are compared by their propositions before the WHNF below
        // can unfold either one (WS6.11 / F-106; `proof_irrel.rs`). The rigid
        // congruence above declines a pair whose literal arguments differ, so
        // the F-106 pair (`Nat.mod_lt` at the wrapped product against the
        // reduced literal) reaches this point. An additional success path only.
        if let Some(result) = self.try_unify_proof_args(&left, &right) {
            return result;
        }

        // A BARE unassigned metavariable on exactly one side is solved with the
        // other side AS WRITTEN — Lean's `isDefEq` assigns `?α := VM`, it does
        // not whnf `VM` first. The eager whnf below would unfold a `def` alias
        // (`VM := Nat → Option Nat`, `Set α := α → Prop`) INTO the
        // assignment, after which field notation on a value of that type finds
        // no namespace (G28: `acc.set` with `acc : ?α`, `?α := VM`) and
        // instance search at `.instances` transparency no longer sees the
        // alias its instances are declared on (G47). Speculative: if the
        // folded assignment is refused (scope / occurs / type check), nothing
        // is kept and the historical whnf path runs unchanged.
        if Self::is_bare_meta(&left) != Self::is_bare_meta(&right) {
            self.metas.push_scope();
            if matches!(self.unify_core(&left, &right), UnifyResult::Success) {
                self.metas.commit();
                return UnifyResult::Success;
            }
            self.metas.pop_scope();
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

    /// Is `e` (already instantiated) a bare elaborator metavariable?
    fn is_bare_meta(e: &Expr) -> bool {
        matches!(e.kind(), ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some())
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
    pub(crate) fn unify_no_initial_whnf(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        let left = self.metas.instantiate(left);
        let right = self.metas.instantiate(right);
        self.unify_core(&left, &right)
    }
}
