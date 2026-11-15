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
//! 4. **β / δ / ζ / native** reduction via [`crate::whnf()`] (lazy: only when the
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
//! bridged subterm — `is_def_eq_proof_irrel` re-infers `typeof(a)`, checks it
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
use crate::infer::{infer_in_context, InferError};
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::term::{Term, TermKind};
use crate::validate::Env;
mod eta;
#[cfg(test)]
mod memo_tests;
use crate::whnf::whnf_in_context;
use eta::{try_eta, try_struct_eta};

/// Decide whether `a` and `b` are definitionally equal in `env`.
///
/// Three-valued by `Result`: `Ok(true)`/`Ok(false)`/`Err(OutOfBudget)`.
pub fn is_def_eq(
    env: &dyn Env,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    let _scope = crate::whnf::DecisionScope::enter();
    is_def_eq_at(env, &mut Ctx::new(), a, b, budget)
}

/// [`is_def_eq`] under an explicit local context `ctx` (de Bruijn binder
/// types, innermost last; `infer`'s convention). `infer` compares types of
/// open terms through this, so the type-directed rules (structure-η, proof
/// irrelevance, K-like reduction, structure η at a recursor's major) can type
/// the bound variables those terms mention (R147, R162; until then `infer`
/// compared argument types under binders in the EMPTY context, where these
/// rules fail closed on any open term).
pub(crate) fn is_def_eq_in_context(
    env: &dyn Env,
    ctx: &[Term],
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    let _scope = crate::whnf::DecisionScope::enter();
    is_def_eq_at(env, &mut ctx.to_vec(), a, b, budget)
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
    let _frame = crate::whnf::ReductionFrame::enter()?;

    // (1) pointer / structural-hash fast accept, then this decision's earlier
    // answer for the pair (`crate::whnf`'s conversion cache).
    if a == b {
        return Ok(true);
    }
    if let Some(equal) = crate::whnf::cached_def_eq(ctx, a, b) {
        return Ok(equal);
    }
    let equal = is_def_eq_uncached(env, ctx, a, b, budget)?;
    crate::whnf::remember_def_eq(ctx, a, b, equal);
    Ok(equal)
}

/// [`is_def_eq_at`]'s rules, past its fast accepts.
fn is_def_eq_uncached(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    // (2) cheap structural congruence *before* reducing (lazy δ): try to match
    // heads without unfolding. If that conclusively succeeds, accept.
    if structural_congruence(env, ctx, a, b, budget)? {
        return Ok(true);
    }

    // (3) reduce both sides to whnf and compare heads.
    let a_w = whnf_in_context(env, ctx, a, budget)?;
    let b_w = whnf_in_context(env, ctx, b, budget)?;

    // (2) sort/level eq on canonical levels.
    if let (TermKind::Sort(la), TermKind::Sort(lb)) = (a_w.kind(), b_w.kind()) {
        return Ok(la == lb);
    }

    // structural congruence on the reduced terms.
    if structural_congruence(env, ctx, &a_w, &b_w, budget)? {
        return Ok(true);
    }

    // A `Nat` literal against a `Nat` constructor application (R162).
    if let Some(r) = try_nat_lit_ctor(env, ctx, &a_w, &b_w, budget)? {
        return Ok(r);
    }

    // K-like reduction (R162): a stuck eliminator of a K-target whose major
    // premise has the constructor's type is the eliminator of the constructor.
    for (x, y) in [(&a_w, &b_w), (&b_w, &a_w)] {
        if let Some(x2) = k_like_major(env, ctx, x, budget)? {
            return is_def_eq_at(env, ctx, &x2, y, budget);
        }
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

/// A `Nat` literal against a whnf'd `Nat.zero` or `Nat.succ x`: Lean's kernel
/// reads the literal as its constructor form (`0` is `Nat.zero`, `n + 1` is
/// `Nat.succ n`), so `Lit 0 ≡ Nat.zero`, `Lit (n+1) ≡ Nat.succ x` iff `Lit n ≡
/// x`, and a literal never equals the other constructor. `None` when neither
/// side is a literal facing a `Nat` constructor (the caller goes on). The literal
/// is never expanded on its own: `Nat.succ (Lit n)` whnf's back to a literal.
fn try_nat_lit_ctor(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    let lit_of = |t: &Term| match t.kind() {
        TermKind::Lit(crate::term::Lit::Nat(n)) => Some(n.clone()),
        _ => None,
    };
    let (lit, other) = match (lit_of(a), lit_of(b)) {
        (Some(n), None) => (n, b),
        (None, Some(n)) => (n, a),
        _ => return Ok(None),
    };
    let (head, args) = other.unfold_apps();
    let TermKind::Const(c) = head.kind() else {
        return Ok(None);
    };
    if *c.name() == Name::from_dotted("Nat.zero") && args.is_empty() {
        return Ok(Some(lit.is_zero()));
    }
    if *c.name() == Name::from_dotted("Nat.succ") && args.len() == 1 {
        if lit.is_zero() {
            return Ok(Some(false));
        }
        // Native arithmetic: the work meter charges the predecessor's size
        // before it is built (R166).
        let one = crate::BigNat::one();
        budget.charge(crate::bignat::result_words::sum(&lit, &one))?;
        let pred = Term::lit(crate::term::Lit::Nat(lit.sub(&one)));
        return is_def_eq_at(env, ctx, &pred, &args[0], budget).map(Some);
    }
    Ok(None)
}

/// Lean's K-like reduction, applied where `ck0` has a context. Since the
/// round-5 merge, `whnf` applies the same rule at a recursor's major
/// (`major_is_k_constructor`), so both sides usually arrive here reduced. The
/// eliminator of an inductive `I` that is a K-target — `I` lives in `Prop` and
/// has exactly one constructor `C`, with no fields — whose saturated major
/// premise `m` is not `C` itself: when `m : I ps is` and `C ps : I ps is'` with
/// the two types definitionally equal, `m` is replaced by `C ps` (proof
/// irrelevance makes them equal; the replacement lets the ι-rule fire). `None`
/// when `e` is not such an application or any step does not hold (the
/// eliminator stays stuck: fail-closed).
pub(crate) fn k_like_major(
    env: &dyn Env,
    ctx: &mut Ctx,
    e: &Term,
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Elim(eref) = head.kind() else {
        return Ok(None);
    };
    let ind = eref.inductive().clone();
    let (Some(shape), Some(rules)) = (env.recursor_shape(&ind), env.recursor_rules(&ind)) else {
        return Ok(None);
    };
    if shape.num_motives != 1 {
        return Ok(None);
    }
    let [rule] = rules.as_slice() else {
        return Ok(None);
    };
    if rule.num_fields != 0 {
        return Ok(None);
    }
    // `I : (params) → (indices) → Prop`.
    let Some(mut ty) = env.const_type(&ind) else {
        return Ok(None);
    };
    while let TermKind::Pi(_, _, body) = ty.kind() {
        let next = body.clone();
        ty = next;
    }
    match ty.kind() {
        TermKind::Sort(l) if l.is_zero() => {}
        _ => return Ok(None),
    }
    let to_usize = |x: u32| usize::try_from(x).unwrap_or(usize::MAX);
    let np = to_usize(shape.num_params);
    let major_pos = np
        .checked_add(to_usize(shape.num_motives))
        .and_then(|x| x.checked_add(to_usize(shape.num_minors)))
        .and_then(|x| x.checked_add(to_usize(shape.num_indices)));
    let Some(major_pos) = major_pos else {
        return Ok(None);
    };
    let Some(major) = args.get(major_pos) else {
        return Ok(None);
    };
    let major_w = whnf_in_context(env, ctx, major, budget)?;
    if let TermKind::Const(c) = major_w.unfold_apps().0.kind() {
        if *c.name() == rule.constructor {
            return Ok(None); // the ι-rule's own case
        }
    }
    let major_ty = match infer_in_context(env, ctx, major, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    let major_ty = whnf_in_context(env, ctx, &major_ty, budget)?;
    let (ty_head, ty_args) = major_ty.unfold_apps();
    let TermKind::Const(ty_ref) = ty_head.kind() else {
        return Ok(None);
    };
    if *ty_ref.name() != ind || Some(ty_args.len()) != np.checked_add(to_usize(shape.num_indices)) {
        return Ok(None);
    }
    let Ok(ctor) =
        crate::term::ConstRef::mk(env, rule.constructor.clone(), ty_ref.levels().to_vec())
    else {
        return Ok(None);
    };
    let ctor_app = Term::apply(Term::const_ref(ctor), &ty_args[..np]);
    let ctor_ty = match infer_in_context(env, ctx, &ctor_app, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    if !is_def_eq_at(env, ctx, &ctor_ty, &major_ty, budget)? {
        return Ok(None);
    }
    let mut new_args = args.clone();
    new_args[major_pos] = ctor_app;
    Ok(Some(whnf_in_context(
        env,
        ctx,
        &Term::apply(head, &new_args),
        budget,
    )?))
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
    let ty_w = whnf_in_context(env, ctx, ty, budget)?;
    if matches!(ty_w.kind(), TermKind::Sort(_)) {
        return Ok(false);
    }
    let sort = match infer_in_context(env, ctx, &ty_w, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(false),
    };
    let sort = whnf_in_context(env, ctx, &sort, budget)?;
    Ok(matches!(sort.kind(), TermKind::Sort(l) if l.is_zero()))
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
