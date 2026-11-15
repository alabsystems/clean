// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Weak-head normalization — **one outer reduction relation** (design §5.1).
//!
//! ```text
//! whnf(e):  loop {
//!     e = whnf_core(e)      // β, ζ (let), proj-of-constructor, native Nat/String
//!     match try_delta(e), try_quot(e):
//!         progressed -> continue
//!         stuck      -> return e
//! }
//! ```
//!
//! `whnf_core` performs the head-structural reductions that need no env lookup
//! (β, ζ) plus the env-light ones (proj-of-constructor, native literal
//! reduction). δ (transparency-gated unfolding) and the `Quot.lift/ind` ι-rules
//! are applied in the outer loop and then re-fed to `whnf_core`. There is
//! exactly one relation, budget-threaded and `Result`-returning; **recursor**
//! (inductive ι) reduction is **M2** — a recursor application is left *stuck*.

use crate::budget::{Budget, BudgetError};
use crate::infer::{infer_in_context, infer_sort_in_context, InferError};
use crate::level::Level;
use crate::name::Name;
use crate::term::{Lit, Term, TermKind};
use crate::term_dag::NodeKey;
mod context;
use crate::validate::{Env, QuotKind, Transparency};
use context::context_key;

mod iota;
mod native_nat;
mod string;
use iota::*;
use native_nat::*;

/// Weak-head-normalize `e` to a fixpoint (or until the budget is exhausted).
///
/// Returns `Err(OutOfBudget)` on exhaustion — callers in soundness *rejection*
/// positions collapse that to reject (never fail open).
pub fn whnf(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Term, BudgetError> {
    whnf_in_context(env, &[], e, budget)
}

/// [`whnf`] under an explicit local context `ctx` (de Bruijn binder types,
/// innermost last, as [`crate::infer_in_context`] takes it). Reduction itself
/// needs no context; structure η at a recursor's major premise does, because
/// it infers the major's type (Lean's `to_cnstr_when_structure`, R147).
///
/// The result is cached for the decision in progress (R162's
/// [`DecisionScope`]). The key is the term and, when the term has a loose
/// bound variable, the context too: a closed term (and every reduct of it,
/// down to the majors whose types structure η infers) reduces the same in
/// every context, while an open term's structure η depends on the types
/// `ctx` gives its variables.
pub(crate) fn whnf_in_context(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, BudgetError> {
    let _scope = DecisionScope::enter();
    let _frame = ReductionFrame::enter()?;
    let key_ctx = context_key(ctx, e.loose);
    let hit = WHNF_CACHE.with(|c| {
        c.borrow()
            .get(&key_ctx)
            .and_then(|m| m.get(&NodeKey(e.clone())))
            .cloned()
    });
    if let Some(hit) = hit {
        return Ok(hit);
    }
    let out = whnf_uncached(env, ctx, e, budget)?;
    WHNF_CACHE.with(|c| {
        c.borrow_mut()
            .entry(key_ctx)
            .or_default()
            .insert(NodeKey(e.clone()), out.clone())
    });
    Ok(out)
}

/// `whnf`'s (or `infer`'s) results within one decision, by context (empty for
/// a closed term) and then by term.
type WhnfCache = std::collections::HashMap<Vec<NodeKey>, std::collections::HashMap<NodeKey, Term>>;

/// Conversion's answers within one decision, by context (empty when both
/// sides are closed) and then by ordered pair.
type DefEqCache =
    std::collections::HashMap<Vec<NodeKey>, std::collections::HashMap<(NodeKey, NodeKey), bool>>;

thread_local! {
    /// `whnf`'s results within ONE decision (R162): a term the decision has
    /// reduced is not reduced again. Without it a term that names a shared
    /// subterm twice (`⟨f acc.1, g acc.2⟩` folded over a list) is reduced once
    /// per path, exponentially in the fold's length. Cleared when the outermost
    /// [`DecisionScope`] of the thread opens and when it closes, so no entry
    /// outlives the decision (and the one environment) it was computed in.
    static WHNF_CACHE: std::cell::RefCell<WhnfCache> =
        std::cell::RefCell::new(std::collections::HashMap::new());
    /// `infer`'s successful results within ONE decision, keyed as
    /// [`WHNF_CACHE`] is: a closed term's type is the same in every context
    /// (`infer` reads the context only at a loose variable), an open term's
    /// is keyed by its dependency-closed context suffix. Keys own node identities; scoped
    /// hash-consing preserves equal nodes (binder annotations included).
    /// Without it, conversion's proof irrelevance and
    /// η infer the same subterm once per path: on Clean's CIC_L export
    /// (2026-11-13, Q4 follow-up) `judgment_convert_definition` ran past
    /// eleven minutes in `def_eq`'s η and proof-irrelevance paths. A refusal
    /// is never cached. Cleared with [`WHNF_CACHE`].
    static INFER_CACHE: std::cell::RefCell<WhnfCache> =
        std::cell::RefCell::new(std::collections::HashMap::new());
    /// `def_eq`'s answers within ONE decision, keyed by context as
    /// [`WHNF_CACHE`] is (empty when both sides are closed) and then by the
    /// ordered pair. An answer is a fact about the pair: every exhaustion
    /// (fuel, the frame cap, a level past its bound) propagates as an error
    /// and is never cached, and the rules that fail closed do so only on a
    /// sub-decision's type error, which is the same each time; so a `false`
    /// is reused as a `true` is. With the infer cache alone,
    /// Q4's CIC_L run took 54,222,330 steps before both answers were
    /// memoized; the complete cost sequence is archived in the Q4 report.
    /// Cleared with [`WHNF_CACHE`].
    static DEFEQ_CACHE: std::cell::RefCell<DefEqCache> =
        std::cell::RefCell::new(std::collections::HashMap::new());
    static DECISION_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// The type the decision in progress has already inferred for `e` in `ctx`.
pub(crate) fn cached_infer(ctx: &[Term], e: &Term) -> Option<Term> {
    let key = context_key(ctx, e.loose);
    INFER_CACHE.with(|c| {
        c.borrow()
            .get(&key)
            .and_then(|m| m.get(&NodeKey(e.clone())))
            .cloned()
    })
}

/// Record the type `infer` found for `e` in `ctx`, for the decision in progress.
pub(crate) fn remember_infer(ctx: &[Term], e: &Term, ty: &Term) {
    let key = context_key(ctx, e.loose);
    INFER_CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if let Some(m) = c.get_mut(&key) {
            m.insert(NodeKey(e.clone()), ty.clone());
        } else {
            c.entry(key)
                .or_default()
                .insert(NodeKey(e.clone()), ty.clone());
        }
    });
}

/// The decision in progress's earlier answer to `a ≡ b` in `ctx`.
pub(crate) fn cached_def_eq(ctx: &[Term], a: &Term, b: &Term) -> Option<bool> {
    let key = context_key(ctx, a.loose.max(b.loose));
    DEFEQ_CACHE.with(|c| {
        c.borrow()
            .get(&key)
            .and_then(|m| m.get(&(NodeKey(a.clone()), NodeKey(b.clone()))).copied())
    })
}

/// Record conversion's answer to `a ≡ b` in `ctx`, for the decision in progress.
pub(crate) fn remember_def_eq(ctx: &[Term], a: &Term, b: &Term, equal: bool) {
    let key = context_key(ctx, a.loose.max(b.loose));
    DEFEQ_CACHE.with(|c| {
        let mut c = c.borrow_mut();
        let pair = (NodeKey(a.clone()), NodeKey(b.clone()));
        if let Some(m) = c.get_mut(&key) {
            m.insert(pair, equal);
        } else {
            c.entry(key).or_default().insert(pair, equal);
        }
    });
}

/// One public decision (`whnf`, `is_def_eq`, `infer`, `check`, …) in progress on
/// this thread. Nested entries share the outermost one's cache; the cache is
/// emptied when the outermost opens and when it closes. A decision reads one
/// environment throughout (every entry point takes it by shared reference), so
/// a cached reduction is the reduction in that environment.
pub(crate) struct DecisionScope {
    _dag: crate::term_dag::DagScope,
}

impl DecisionScope {
    pub(crate) fn enter() -> Self {
        DECISION_DEPTH.with(|d| {
            if d.get() == 0 {
                WHNF_CACHE.with(|c| c.borrow_mut().clear());
                INFER_CACHE.with(|c| c.borrow_mut().clear());
                DEFEQ_CACHE.with(|c| c.borrow_mut().clear());
            }
            d.set(d.get().saturating_add(1));
        });
        DecisionScope {
            _dag: crate::term_dag::DagScope::enter(),
        }
    }
}

impl Drop for DecisionScope {
    fn drop(&mut self) {
        DECISION_DEPTH.with(|d| {
            d.set(d.get().saturating_sub(1));
            if d.get() == 0 {
                WHNF_CACHE.with(|c| c.borrow_mut().clear());
                INFER_CACHE.with(|c| c.borrow_mut().clear());
                DEFEQ_CACHE.with(|c| c.borrow_mut().clear());
            }
        });
    }
}

/// Pinned maximum nesting of reduction and conversion frames on one thread
/// (`docs/DECISIONS.md` R166): `whnf`, `whnf_core` and `def_eq` each count one
/// frame while they run. `infer` counts none of its own: it recurses over a
/// term's structure, which the depth bound below holds, and reduces and compares
/// through the counted entries.
///
/// [`crate::MAX_VALIDATE_DEPTH`] bounds how deep an input can be, and
/// `whnf_core` holds every reduct to the same bound, which bounds every walk over
/// a term. Neither bounds how deep reduction recurses, and a
/// term of depth 1 can make that unbounded: R162 reads a `Nat` literal major of
/// `Nat.rec` as its constructor, so `Nat.rec m z (fun _ ih => Nat.succ ih) N`
/// reduces to `Nat.succ (Nat.rec … (N - 1))`, and native `succ` reduction
/// whnf's that argument, nesting frames per unit of `N`; the fuel budget
/// allows far more frames than a thread's stack holds. Past this cap a
/// decision fails as [`BudgetError::OutOfBudget`], the exhaustion every
/// soundness caller already collapses to reject, instead of aborting the
/// process.
///
/// Lean's kernel guards the same recursion by stack space instead
/// (`check_system` in `whnf_core`, `infer` and `is_def_eq`, pinned v4.30.0-rc2),
/// and so finishes recursion this count refuses. A native `succ` level holds two
/// frames (`whnf` and `whnf_core`), so here a non-tail chain of about 255 levels
/// is refused where Lean reduces it: a known gap, pinned as a refusal in
/// `tests/nat_lit_iota_depth.rs`, and fail-closed. The count keeps the verdict
/// independent of the stack a caller runs on. The costliest measured path needs
/// about 2.2 MiB of debug-build stack for 512 frames; [`crate::MAX_VALIDATE_DEPTH`]
/// sits at about half the depth that overflows `validate`'s own walk on the main
/// thread. A decision at both bounds at once is not measured.
pub(crate) const MAX_REDUCTION_DEPTH: u32 = 512;

thread_local! {
    /// Reduction and conversion frames now running on this thread.
    static REDUCTION_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// One reduction or conversion frame; counted while it lives (R166).
pub(crate) struct ReductionFrame;

impl ReductionFrame {
    /// Count one more frame, or refuse past [`MAX_REDUCTION_DEPTH`].
    pub(crate) fn enter() -> Result<Self, BudgetError> {
        REDUCTION_DEPTH.with(|d| {
            let next = d.get().saturating_add(1);
            if next > MAX_REDUCTION_DEPTH {
                return Err(BudgetError::OutOfBudget);
            }
            d.set(next);
            Ok(ReductionFrame)
        })
    }
}

impl Drop for ReductionFrame {
    fn drop(&mut self) {
        REDUCTION_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

fn whnf_uncached(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, BudgetError> {
    let mut cur = whnf_core(env, ctx, e, budget)?;
    loop {
        budget.step()?;
        // δ: transparency-gated unfolding of the head constant.
        if let Some(unfolded) = try_delta(env, &cur)? {
            cur = whnf_core(env, ctx, &unfolded, budget)?;
            continue;
        }
        // Quot.lift/ind ι-rule.
        if let Some(reduced) = try_quot(env, ctx, &cur, budget)? {
            cur = whnf_core(env, ctx, &reduced, budget)?;
            continue;
        }
        // Recursor (inductive) ι-rule (M2).
        if let Some(reduced) = try_iota(env, ctx, &cur, budget)? {
            cur = whnf_core(env, ctx, &reduced, budget)?;
            continue;
        }
        return Ok(cur);
    }
}

/// The env-light core: β, ζ (let), proj-of-constructor, native Nat/String.
/// Reduces the head to fixpoint over *these* rules only.
fn whnf_core(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, BudgetError> {
    // `whnf_core` recurses into an applied projection or `let` head itself.
    let _frame = ReductionFrame::enter()?;
    let mut cur = e.clone();
    loop {
        budget.step()?;
        // Every reduct passes here. Head reduction is a loop, so it can build a
        // term far deeper than any input (`Nat.rec id (fun _ ih x => ih (g x)) N
        // a` is `g (g (… a))`, `N` deep); one past the input bound is refused
        // rather than handed to a natively recursive consumer (R166).
        if cur.depth > crate::MAX_VALIDATE_DEPTH {
            return Err(BudgetError::OutOfBudget);
        }
        match cur.kind() {
            TermKind::Lit(Lit::Str(value)) if env.string_literal_view() => {
                cur = string::constructor_view(env, value, budget)?;
            }
            // ζ: let _ : ty := val; body  ~>  body[val]
            TermKind::Let(_, val, body) => {
                cur = body.instantiate(val);
            }
            // β / native head reductions on an application spine.
            TermKind::App(_, _) => {
                let (head, args) = cur.unfold_apps();
                // β: (λ x. body) a rest..  ~>  (body[a]) rest..
                if let TermKind::Lam(_, _, body) = head.kind() {
                    if let Some((first, rest)) = args.split_first() {
                        let beta = body.instantiate(first);
                        cur = Term::apply(beta, rest);
                        continue;
                    }
                }
                // A projection or `let` in head position (`(S.i e) a..`, the
                // shape a class method applied to its arguments unfolds to):
                // reduce the head, then re-apply the arguments (R162). Without
                // this an applied projection of a constructor stayed stuck.
                if matches!(head.kind(), TermKind::Proj(..) | TermKind::Let(..)) {
                    let reduced = whnf_core(env, ctx, &head, budget)?;
                    if reduced != head {
                        cur = Term::apply(reduced, &args);
                        continue;
                    }
                }
                // native Nat reduction (succ / binary ops on literals).
                if let Some(reduced) = try_native_nat(env, ctx, &head, &args, budget)? {
                    cur = reduced;
                    continue;
                }
                return Ok(cur);
            }
            // proj-of-constructor: S.i (C p.. f..)  ~>  f_i
            TermKind::Proj(struct_name, idx, inner) => {
                let inner_whnf = whnf_in_context(env, ctx, inner, budget)?;
                if let Some(field) = try_proj_ctor(env, struct_name, *idx, &inner_whnf) {
                    cur = field;
                    continue;
                }
                // stuck on the (reduced) inner term.
                return Ok(Term::proj(struct_name.clone(), *idx, inner_whnf));
            }
            _ => return Ok(cur),
        }
    }
}

/// δ: if the head is a `Const` with a [`Transparency::Transparent`] definition,
/// substitute its level args into the body and replace the head. Returns the
/// whole spine with the head unfolded, or `None` if the head is δ-stuck.
fn try_delta(env: &dyn Env, e: &Term) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Const(cref) = head.kind() else {
        return Ok(None);
    };
    let Some(def) = env.const_def(cref.name()) else {
        return Ok(None);
    };
    if def.transparency != Transparency::Transparent {
        return Ok(None);
    }
    let body = def.body.instantiate_levels(cref.levels())?;
    Ok(Some(Term::apply(body, &args)))
}

/// The `Quot.lift`/`Quot.ind` ι-rules (design §5.1):
/// `Quot.lift α r β f h (Quot.mk α r a) ~> f a`
/// `Quot.ind  α r β f   (Quot.mk α r a) ~> f a`
/// The head and the `Quot.mk` are recognized via the *closed* [`QuotKind`]
/// classification, never by free name lookup.
fn try_quot(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Const(cref) = head.kind() else {
        return Ok(None);
    };
    let Some(kind) = env.quot_kind(cref.name()) else {
        return Ok(None);
    };
    // Argument layout (Lean): lift = [α, r, β, f, h, q]; ind = [α, r, β, f, q].
    // The major premise `q` is the last argument; `f` sits two before it for
    // lift (after `h`) and one before for ind.
    let (f_idx, q_idx) = match kind {
        QuotKind::Lift => (3usize, 5usize),
        QuotKind::Ind => (3usize, 4usize),
        QuotKind::Type | QuotKind::Mk => return Ok(None),
    };
    if args.len() <= q_idx {
        return Ok(None);
    }
    // The major premise must whnf to `Quot.mk α r a`.
    let q = whnf_in_context(env, ctx, &args[q_idx], budget)?;
    let (q_head, q_args) = q.unfold_apps();
    let TermKind::Const(q_cref) = q_head.kind() else {
        return Ok(None);
    };
    if env.quot_kind(q_cref.name()) != Some(QuotKind::Mk) {
        return Ok(None);
    }
    // Quot.mk layout: [α, r, a]; the value `a` is the last argument.
    let Some(a) = q_args.last() else {
        return Ok(None);
    };
    let f = args[f_idx].clone();
    // f a, then re-apply any trailing args beyond the major premise.
    let mut result = Term::app(f, a.clone());
    if let Some(trailing) = args.get(q_idx.saturating_add(1)..) {
        result = Term::apply(result, trailing);
    }
    Ok(Some(result))
}

/// proj-of-constructor: if `inner` (already whnf'd) is a constructor application
/// `C p_0..p_{k-1} f_0..f_{m-1}`, return field `idx` (`f_idx`). Uses the env's
/// recorded `(num_params, num_fields)` so the field offset is `num_params+idx`.
/// `C` must be the constructor of `struct_name` (Lean v4.33.1 `reduce_proj_core`,
/// leanprover/lean4#14632; decision R147): another inductive's constructor is
/// not projected, and the projection stays stuck.
fn try_proj_ctor(env: &dyn Env, struct_name: &Name, idx: u32, inner: &Term) -> Option<Term> {
    let (head, args) = inner.unfold_apps();
    let TermKind::Const(cref) = head.kind() else {
        return None;
    };
    if env.structure_info(struct_name)?.ctor != *cref.name() {
        return None;
    }
    let arity = env.constructor_arity(cref.name())?;
    if idx >= arity.num_fields {
        return None;
    }
    let offset = usize::try_from(arity.num_params).ok()?;
    let field_idx = usize::try_from(idx).ok()?.checked_add(offset)?;
    args.get(field_idx).cloned()
}

/// Helper for tests / level instantiation parity: a `Sort` head check.
#[must_use]
pub fn is_sort(t: &Term) -> Option<Level> {
    match t.kind() {
        TermKind::Sort(l) => Some(l.clone()),
        _ => None,
    }
}
