// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional equality — `ck0` **decides**; it never trusts advice
//! (design §1, §5.1).
//!
//! The fixed, documented order (design §5.1):
//!
//! 1. **structural + hash fast-reject** then **pointer eq** (cheap accepts);
//! 2. **sort / level eq** on canonical levels;
//! 3. **congruence under binders** (`Pi`/`Lam`/`Let`, context push/pop) and on
//!    `App`/`Proj`/`Const`/`Elim`/`Lit` heads;
//! 4. **β / δ / ζ / native** reduction via [`crate::whnf`] (lazy: only when the
//!    cheap structural compare fails) — both sides to whnf, then re-compare;
//! 5. **function-η** (`λ x. f x ≡ f`);
//! 6. **structure-η** (`s ≡ S.mk s.1 s.2 …`);
//! 7. **proof-irrelevance for `Prop`** — with the full side condition;
//! 8. **`Quot`** (handled inside whnf's ι-rule, then re-compared structurally).
//!
//! Returns `Result<bool, BudgetError>` with **three real outcomes**:
//! `Ok(true)` (equal), `Ok(false)` (provably unequal *within budget*), and
//! `Err(OutOfBudget)` (gave up). No `bool` conflates "unequal" with "gave up".
//!
//! ## Proof-irrelevance side condition (design §5.1, non-negotiable)
//!
//! `a ≡ b` by irrelevance **iff** `is_def_eq(typeof(a), typeof(b))` *and* that
//! common type `: Prop`. The shortcut never skips re-inferring the sort of the
//! bridged subterm — [`is_def_eq_proof_irrel`] re-infers `typeof(a)`, checks it
//! is in `Prop`, and confirms `typeof(a) ≡ typeof(b)`.
//!
//! ## η / structure-η / proj interaction order
//!
//! After whnf, if exactly one side is a `Lam`, function-η is attempted; if one
//! side's whnf'd type is a structure and the other is not already its
//! constructor, structure-η is attempted. Proj *typing* (in `infer`) pulls the
//! field type from the inferred structure type and does not require a
//! constructor head; proj *reduction* on a constructor is a separate whnf rule.

use crate::budget::{Budget, BudgetError};
use crate::infer::{infer, infer_in_context, InferError};
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::term::{Term, TermKind};
use crate::validate::Env;
use crate::whnf::whnf;

/// Decide whether `a` and `b` are definitionally equal in `env`.
///
/// Three-valued by `Result`: `Ok(true)`/`Ok(false)`/`Err(OutOfBudget)`.
pub fn is_def_eq(
    env: &dyn Env,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    is_def_eq_at(env, &mut Ctx::new(), a, b, budget)
}

/// The local context for congruence under binders: binder types (de Bruijn,
/// innermost last). We only need the depth for η/proof-irrel inference, but keep
/// the types so the proof-irrelevance side condition can `infer` under binders
/// in a later milestone; at M1 proof-irrel runs at the empty context (top
/// level), matching where the corpus exercises it.
type Ctx = Vec<Term>;

fn is_def_eq_at(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    budget.step()?;

    // (1) pointer / structural-hash fast accept.
    if a == b {
        return Ok(true);
    }

    // (2) cheap structural congruence *before* reducing (lazy δ): try to match
    // heads without unfolding. If that conclusively succeeds, accept.
    if structural_congruence(env, ctx, a, b, budget)? {
        return Ok(true);
    }

    // (3) reduce both sides to whnf and compare heads.
    let a_w = whnf(env, a, budget)?;
    let b_w = whnf(env, b, budget)?;

    // (2) sort/level eq on canonical levels.
    if let (TermKind::Sort(la), TermKind::Sort(lb)) = (a_w.kind(), b_w.kind()) {
        return Ok(la == lb);
    }

    // structural congruence on the reduced terms.
    if structural_congruence(env, ctx, &a_w, &b_w, budget)? {
        return Ok(true);
    }

    // (5) function-η.
    if let Some(r) = try_eta(env, ctx, &a_w, &b_w, budget)? {
        if r {
            return Ok(true);
        }
    }

    // (6) structure-η.
    if let Some(r) = try_struct_eta(env, ctx, &a_w, &b_w, budget)? {
        if r {
            return Ok(true);
        }
    }

    // (7) proof-irrelevance for Prop (full side condition). M2: runs UNDER
    // BINDERS too — `infer` now takes a local context, so the bridged subterm's
    // sort is re-inferred in the current context (closing the M1 top-level-only
    // gap). The side condition is never skipped: `typeof(a) ≡ typeof(b)` AND
    // `typeof(a) : Prop`.
    if let Some(true) = is_def_eq_proof_irrel(env, ctx, &a_w, &b_w, budget)? {
        return Ok(true);
    }

    // exhausted the relation -> provably unequal *within budget*.
    Ok(false)
}

/// Structural congruence: equal heads with recursively-def-eq children. Does not
/// itself reduce (the caller reduces between attempts), so it implements the
/// "congruence under binders / on App-Proj-Const-Elim-Lit heads" leg. β/δ are
/// the caller's whnf step.
fn structural_congruence(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    match (a.kind(), b.kind()) {
        (TermKind::BVar(x), TermKind::BVar(y)) => Ok(x == y),
        (TermKind::Sort(x), TermKind::Sort(y)) => Ok(x == y),
        (TermKind::Lit(x), TermKind::Lit(y)) => Ok(x == y),
        (TermKind::Const(x), TermKind::Const(y)) => {
            Ok(x.name() == y.name() && x.levels() == y.levels())
        }
        (TermKind::Elim(x), TermKind::Elim(y)) => {
            Ok(x.inductive() == y.inductive() && x.levels() == y.levels())
        }
        // Cross-form recursor heads: the kernel-internal ι-rule RHSs reference a
        // recursor as `Const(I.rec, levels)` (their recursive IH calls), while the
        // untrusted boundary only ever produces `Elim(I, levels)`. Both denote the
        // SAME recursor and fire the SAME ι-rules, so a STUCK recursor reached via
        // an IH (e.g. `Nat.rec.{l} … x` under a binder, from `beq (succ x)(succ
        // y)`) must be recognized as the same head as the boundary `Elim(I).{l} …
        // x`. Equal iff the `Const` is a recursor whose inductive is `I` and the
        // level vectors match. (Soundness-neutral: this only ADDS accepts for
        // already-identical canonical recursors; it never blesses distinct heads.)
        (TermKind::Const(c), TermKind::Elim(el)) | (TermKind::Elim(el), TermKind::Const(c)) => Ok(
            env.recursor_inductive(c.name()).as_ref() == Some(el.inductive())
                && c.levels() == el.levels(),
        ),
        (TermKind::App(_, _), TermKind::App(_, _)) => {
            let (fa, aa) = a.unfold_apps();
            let (fb, ab) = b.unfold_apps();
            if aa.len() != ab.len() {
                return Ok(false);
            }
            // heads must be congruent without reduction (def-eq handles the
            // reducible case via whnf in the caller); recurse def-eq on args.
            if !is_def_eq_at(env, ctx, &fa, &fb, budget)? {
                return Ok(false);
            }
            for (x, y) in aa.iter().zip(ab.iter()) {
                if !is_def_eq_at(env, ctx, x, y, budget)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (TermKind::Lam(_, ta, ba), TermKind::Lam(_, tb, bb))
        | (TermKind::Pi(_, ta, ba), TermKind::Pi(_, tb, bb)) => {
            if !is_def_eq_at(env, ctx, ta, tb, budget)? {
                return Ok(false);
            }
            ctx.push(ta.clone());
            let r = is_def_eq_at(env, ctx, ba, bb, budget);
            ctx.pop();
            r
        }
        (TermKind::Let(_, _, _), _) | (_, TermKind::Let(_, _, _)) => {
            // Let is reduced by whnf; never compared structurally here.
            Ok(false)
        }
        (TermKind::Proj(na, ia, ea), TermKind::Proj(nb, ib, eb)) => {
            if na != nb || ia != ib {
                return Ok(false);
            }
            is_def_eq_at(env, ctx, ea, eb, budget)
        }
        _ => Ok(false),
    }
}

/// function-η: `λ x. body ≡ other` iff `other` is a function and
/// `λ x. body ≡ λ x. other x`. Symmetric (tries either side as the lambda).
fn try_eta(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    match (a.kind(), b.kind()) {
        (TermKind::Lam(bi, dom, _), _) if !matches!(b.kind(), TermKind::Lam(_, _, _)) => {
            Ok(Some(eta_one(env, ctx, *bi, dom, a, b, budget)?))
        }
        (_, TermKind::Lam(bi, dom, _)) if !matches!(a.kind(), TermKind::Lam(_, _, _)) => {
            Ok(Some(eta_one(env, ctx, *bi, dom, b, a, budget)?))
        }
        _ => Ok(None),
    }
}

/// `lam` is a `Lam(bi, dom, _)`; `other` is a non-lambda. Compare
/// `lam ≡ λ (x:dom). other x` (η-expanding `other`).
fn eta_one(
    env: &dyn Env,
    ctx: &mut Ctx,
    bi: BinderInfo,
    dom: &Term,
    lam: &Term,
    other: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    // λ (x:dom). (other↑1) (BVar 0)
    let expanded = Term::lam(bi, dom.clone(), Term::app(other.lift(1), Term::bvar(0)));
    is_def_eq_at(env, ctx, lam, &expanded, budget)
}

/// structure-η: if one side's whnf'd *type* is a single-constructor structure
/// and the other side is not already that constructor applied, expand it to
/// `S.mk (proj0) … (projn)` and compare fieldwise. M2: runs UNDER BINDERS too
/// (`infer` is now context-aware), so structure-η fires wherever the corpus
/// needs it, not only at the top level.
fn try_struct_eta(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    // Try expanding `a` to match `b`'s structure shape, then vice versa.
    if let Some(r) = struct_eta_one(env, ctx, a, b, budget)? {
        return Ok(Some(r));
    }
    struct_eta_one(env, ctx, b, a, budget)
}

/// Expand `e` (the candidate to be η-expanded) into constructor form and compare
/// to `other`. Returns `Some(result)` if `e`'s type is a structure *and* the
/// expansion is licensed (Lean-faithful gating — see below), else `None`.
///
/// ## Lean-faithful gating (totality + soundness-preserving)
///
/// Structure-η exists to decide `s ≡ S.mk f0 … fn`: η-expand the NEUTRAL side
/// `s` to `S.mk (proj0 s) … (projn s)` so it matches the CONSTRUCTOR-headed
/// side. It is therefore fired ONLY when `other` (already whnf'd by the caller)
/// is headed by this structure's constructor `S.mk`. This mirrors Lean's kernel
/// `isDefEqEtaStruct`, which η-expands a term solely to match a constructor.
///
/// Two genuinely distinct NEUTRAL terms of a structure type (e.g. opaque
/// `p q : Pair Nat Nat`, neither `Pair.mk`-headed) need NO η: η-expanding both
/// and comparing fieldwise reduces (via `Proj` congruence) `p.i ≡ q.i` back to
/// `p ≡ q`, an unbounded native recursion that overflows the stack. Gating on a
/// constructor-headed `other` makes the path TOTAL — two neutrals fall through
/// to the structural/neutral comparison, which terminates — WITHOUT changing any
/// real outcome: the only def-eqs structure-η ever decided are `neutral ≡
/// S.mk …`, and those still fire. (Soundness-preserving: this can only make
/// fewer η-accepts; it never blesses two distinct terms.)
fn struct_eta_one(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    other: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    // Determine e's structure type (in the current local context).
    let e_ty = match infer_in_context(env, ctx, e, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    let e_ty = whnf(env, &e_ty, budget)?;
    let (head, ty_args) = e_ty.unfold_apps();
    let TermKind::Const(ty_cref) = head.kind() else {
        return Ok(None);
    };
    let Some(info) = env.structure_info(ty_cref.name()) else {
        return Ok(None);
    };
    // Don't η-expand a term already headed by the same constructor (would loop).
    let (e_head, _) = e.unfold_apps();
    if let TermKind::Const(c) = e_head.kind() {
        if *c.name() == info.ctor {
            return Ok(None);
        }
    }
    // LEAN-FAITHFUL GATING (totality): only η-expand `e` to MATCH a constructor.
    // Fire iff `other` is headed by this structure's constructor `S.mk`; two
    // neutrals (other not mk-headed) need no η and are compared structurally,
    // which terminates. This is what kills the runaway recursion on distinct
    // neutral structure terms (e.g. `p q : Pair Nat Nat`) — fail-closed: `None`
    // falls through to the structural/neutral comparison.
    let (other_head, _) = other.unfold_apps();
    let other_is_ctor = matches!(
        other_head.kind(),
        TermKind::Const(c) if *c.name() == info.ctor
    );
    if !other_is_ctor {
        return Ok(None);
    }
    // Build S.mk params... (proj_0 e) ... (proj_{n-1} e).
    let mut ctor = Term::const_ref(crate::ConstRef::mk(
        env,
        info.ctor.clone(),
        ty_cref.levels().to_vec(),
    )?);
    let num_params = usize::try_from(info.num_params).unwrap_or(usize::MAX);
    for p in ty_args.iter().take(num_params) {
        ctor = Term::app(ctor, p.clone());
    }
    for field in 0..info.num_fields {
        ctor = Term::app(ctor, Term::proj(ty_cref.name().clone(), field, e.clone()));
    }
    let mut ctx_vec = ctx.to_vec();
    Ok(Some(is_def_eq_at(env, &mut ctx_vec, &ctor, other, budget)?))
}

impl From<crate::term::TermError> for BudgetError {
    fn from(_: crate::term::TermError) -> Self {
        // A structure-η constructor build whose levels mismatch the constructor
        // arity is impossible (we pass the inductive's own validated levels);
        // collapse defensively to OutOfBudget so the caller rejects, never
        // accepts (fail-closed).
        BudgetError::OutOfBudget
    }
}

/// Proof-irrelevance with the **full side condition** (design §5.1):
/// `a ≡ b` iff `typeof(a) ≡ typeof(b)` *and* `typeof(a) : Prop`. Re-infers the
/// sort of the bridged subterm every time; never relies on a cache.
///
/// Returns `Some(true)` if the bridge applies and types match, `Some(false)` if
/// it applies but types differ (so the caller does not accept), `None` if the
/// bridge does not apply (not a Prop).
fn is_def_eq_proof_irrel(
    env: &dyn Env,
    ctx: &[Term],
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    // typeof(a) in the current local context.
    let ty_a = match infer_in_context(env, ctx, a, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    // typeof(a) : Prop?  i.e. infer(ty_a) whnf's to Sort 0.
    if !type_is_prop(env, ctx, &ty_a, budget)? {
        return Ok(None);
    }
    let ty_b = match infer_in_context(env, ctx, b, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    // The common type must itself be def-eq (a and b must be proofs of the
    // *same* proposition).
    let mut ctx_vec = ctx.to_vec();
    Ok(Some(is_def_eq_at(env, &mut ctx_vec, &ty_a, &ty_b, budget)?))
}

/// True iff `ty`'s own type whnf's to `Sort 0` (i.e. `ty : Prop`) in `ctx`.
fn type_is_prop(
    env: &dyn Env,
    ctx: &[Term],
    ty: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    // A Sort is never in Prop (Sort l : Sort (succ l) which is never Sort 0).
    let ty_w = whnf(env, ty, budget)?;
    if matches!(ty_w.kind(), TermKind::Sort(_)) {
        return Ok(false);
    }
    let sort = match infer_in_context(env, ctx, &ty_w, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(false),
    };
    let sort = whnf(env, &sort, budget)?;
    Ok(matches!(sort.kind(), TermKind::Sort(l) if l.is_zero()))
}

/// Re-export for test ergonomics: build a `Const` with a dotted name and no
/// levels (used by tests building Prop-typed proof terms).
#[must_use]
#[doc(hidden)]
pub fn dotted_const_no_levels(env: &dyn Env, name: &str) -> Option<Term> {
    crate::ConstRef::mk(env, Name::from_dotted(name), Vec::new())
        .ok()
        .map(Term::const_ref)
}

#[cfg(kani)]
mod kani_harnesses {
    //! Tier-1 Kani skeletons (design §8): the proof-irrelevance *side condition*
    //! and def_eq *reflexivity*. Compiled out of normal builds; the bounded
    //! proptest corpus in `tests/m1_def_eq_proptest.rs` covers the same laws for
    //! ordinary CI.
    use super::*;
    use crate::minimal_env::MinimalEnv;

    /// Reflexivity: `is_def_eq(e, e)` is `Ok(true)` for the literal terms the
    /// native reducer can produce (a `Nat` literal). Bounded to keep the harness
    /// decidable; the general statement is the §8 mechanized obligation.
    #[kani::proof]
    #[kani::unwind(4)]
    fn def_eq_reflexive_on_nat_lit() {
        let v: u64 = kani::any();
        kani::assume(v < 4);
        let env = MinimalEnv::new();
        let t = Term::lit(crate::term::Lit::Nat(crate::BigNat::from_u64(v)));
        let mut budget = Budget::new(64);
        assert_eq!(is_def_eq(&env, &t, &t, &mut budget), Ok(true));
    }

    /// Proof-irrelevance side condition is *gated on Prop*: a `Nat` literal's
    /// type is `Nat` (not Prop), so the irrelevance bridge must NOT fire — two
    /// distinct literals are `Ok(false)`, never silently equated.
    #[kani::proof]
    #[kani::unwind(4)]
    fn proof_irrel_does_not_bridge_non_prop() {
        let a: u64 = kani::any();
        let b: u64 = kani::any();
        kani::assume(a < 3 && b < 3 && a != b);
        // env where Nat : Type 0 so the type-of-type is Sort 1, not Prop.
        let nat_ty = Term::sort(crate::Level::nat(1));
        let env = MinimalEnv::new().with_const_typed(Name::from_dotted("Nat"), 0, nat_ty);
        let ta = Term::lit(crate::term::Lit::Nat(crate::BigNat::from_u64(a)));
        let tb = Term::lit(crate::term::Lit::Nat(crate::BigNat::from_u64(b)));
        let mut budget = Budget::new(256);
        assert_eq!(is_def_eq(&env, &ta, &tb, &mut budget), Ok(false));
    }
}
