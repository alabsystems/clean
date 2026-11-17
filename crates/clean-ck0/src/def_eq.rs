// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional equality — `ck0` **decides**; it never trusts advice
//! (design §1, §5.1).
//!
//! The bounded conversion strategy follows pinned Lean's kernel:
//!
//! 1. exact equality and decision-scoped, context-keyed memoization;
//! 2. quick sort/literal/binder comparisons;
//! 3. proof irrelevance with the full same-proposition and `Prop` checks;
//! 4. head reduction and pair-directed lazy delta, using untrusted definition
//!    heights only to schedule which checked body unfolds first;
//! 5. delayed projections and String expansion, constructor/literal equality,
//!    recursor reduction, function eta and structure/unit-like eta.
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
use crate::infer::{infer_for_conversion, CheckedType, InferError, TypeQueryScope};
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::term::{Term, TermKind};
use crate::validate::Env;
mod argument_delta;
mod eta;
mod k;
pub(crate) use k::k_like_major;
mod lazy;
mod offset;
mod proof;
use proof::is_def_eq_proof_irrel;
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
    let _unknown = TypeQueryScope::unknown();
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
    let _unknown = TypeQueryScope::unknown();
    is_def_eq_at(env, &mut ctx.to_vec(), a, b, budget)
}

/// Conversion of well-formed types, with witnesses produced only by full
/// inference/checking. No caller can mint a witness from a merely scoped term.
pub(crate) fn is_def_eq_checked_types(
    env: &dyn Env,
    ctx: &[Term],
    a: CheckedType<'_>,
    b: CheckedType<'_>,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    let _scope = crate::whnf::DecisionScope::enter();
    let _known = TypeQueryScope::checked(&a, &b);
    is_def_eq_at(env, &mut ctx.to_vec(), a.term(), b.term(), budget)
}

/// The local context for congruence under binders: binder types (de Bruijn,
/// innermost last). We only need the depth for η/proof-irrel inference, but keep
/// the types so the proof-irrelevance side condition can `infer` under binders
/// in a later milestone; at M1 proof-irrel runs at the empty context (top
/// level), matching where the corpus exercises it.
type Ctx = Vec<Term>;

/// A tail conversion step changes neither context nor typing assumptions.
/// Retrying it in a loop preserves the fuel charge without growing native stack.
enum ConversionStep {
    Answer(bool),
    Retry(Term, Term),
}

fn is_def_eq_at(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    budget.step()?;
    let _frame = crate::whnf::ReductionFrame::enter()?;
    let (mut left, mut right) = (a.clone(), b.clone());
    let mut pending = Vec::new();
    let answer = loop {
        if left == right {
            break true;
        }
        if let Some(equal) = crate::whnf::cached_def_eq(ctx, &left, &right) {
            break equal;
        }
        pending.push((left.clone(), right.clone()));
        match is_def_eq_uncached(env, ctx, &left, &right, budget)? {
            ConversionStep::Answer(answer) => break answer,
            ConversionStep::Retry(a, b) => {
                // Exactly the charge formerly made by the recursive tail call.
                // The frame bound still protects actual nested congruence,
                // inference and reduction; tail iteration uses no extra frame.
                budget.step()?;
                left = a;
                right = b;
            }
        }
    };
    // As before, only completed answers are memoized. An exhaustion above
    // records no answer for any of the still-pending tail pairs.
    for (a, b) in pending.into_iter().rev() {
        crate::whnf::remember_def_eq(ctx, &a, &b, answer);
    }
    Ok(answer)
}

/// [`is_def_eq_at`]'s rules, past its fast accepts.
fn is_def_eq_uncached(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<ConversionStep, BudgetError> {
    // Lean's quick cases decide sorts, literals and matching binders before
    // proof irrelevance. Applications are deliberately not quick cases: proof
    // bodies need not normalize when their checked proposition types agree.
    if matches!(
        (a.kind(), b.kind()),
        (TermKind::Sort(_), TermKind::Sort(_))
            | (TermKind::Lit(_), TermKind::Lit(_))
            | (TermKind::Pi(..), TermKind::Pi(..))
            | (TermKind::Lam(..), TermKind::Lam(..))
    ) {
        return structural_congruence(env, ctx, a, b, budget).map(ConversionStep::Answer);
    }
    if let Some(answer) = is_def_eq_proof_irrel(env, ctx, a, b, budget)? {
        return Ok(ConversionStep::Answer(answer));
    }

    let (a_w, b_w) = match lazy::reduce(env, ctx, a, b, budget)? {
        lazy::Reduced::Answer(answer) => return Ok(ConversionStep::Answer(answer)),
        lazy::Reduced::Retry(a, b) => return Ok(ConversionStep::Retry(a, b)),
        lazy::Reduced::Stuck(a, b) => (a, b),
    };

    // (2) sort/level eq on canonical levels.
    if let (TermKind::Sort(la), TermKind::Sort(lb)) = (a_w.kind(), b_w.kind()) {
        return Ok(ConversionStep::Answer(la == lb));
    }

    // Projections compare their subjects before the expensive retry below.
    // Applied projections must expose their selected function first: app
    // congruence here can force a false, arbitrarily expensive argument pair.
    if !matches!(a_w.kind(), TermKind::App(..))
        && structural_congruence(env, ctx, &a_w, &b_w, budget)?
    {
        return Ok(ConversionStep::Answer(true));
    }

    // A `Nat` literal against a `Nat` constructor application (R162).
    if let Some(step) = offset::step(&a_w, &b_w, budget)? {
        return Ok(step);
    }

    // Lean retries expensive projections only after pair-directed delta has
    // stopped. Literal String expansion is likewise a fallback against a
    // constructor, rather than work performed on every literal comparison.
    let needs_full = |x: &Term, y: &Term| {
        matches!(x.unfold_apps().0.kind(), TermKind::Proj(..))
            || (matches!(x.kind(), TermKind::Lit(crate::term::Lit::Str(_)))
                && matches!(y.kind(), TermKind::App(..)))
    };
    if needs_full(&a_w, &b_w) || needs_full(&b_w, &a_w) {
        let expand = |x: &Term, budget: &mut Budget| {
            if matches!(x.kind(), TermKind::Lit(crate::term::Lit::Str(_))) {
                whnf_in_context(env, ctx, x, budget)
            } else {
                crate::whnf::conversion_project(env, ctx, x, budget)
            }
        };
        let a_full = expand(&a_w, budget)?;
        let b_full = expand(&b_w, budget)?;
        if a_full != a_w || b_full != b_w {
            return Ok(ConversionStep::Retry(a_full, b_full));
        }
    }

    // K-like reduction (R162): a stuck eliminator of a K-target whose major
    // premise has the constructor's type is the eliminator of the constructor.
    for (x, y) in [(&a_w, &b_w), (&b_w, &a_w)] {
        if let Some(x2) = k_like_major(env, ctx, x, budget)? {
            return Ok(ConversionStep::Retry(x2, y.clone()));
        }
    }

    // Lean's final application congruence follows the projection retry.
    if matches!(a_w.kind(), TermKind::App(..))
        && structural_congruence(env, ctx, &a_w, &b_w, budget)?
    {
        return Ok(ConversionStep::Answer(true));
    }

    // (5) function-η.
    if let Some(r) = try_eta(env, ctx, &a_w, &b_w, budget)? {
        if r {
            return Ok(ConversionStep::Answer(true));
        }
    }

    // (6) structure-η.
    if let Some(r) = try_struct_eta(env, ctx, &a_w, &b_w, budget)? {
        if r {
            return Ok(ConversionStep::Answer(true));
        }
    }

    // (7) proof-irrelevance for Prop (full side condition). M2: runs UNDER
    // BINDERS too — `infer` now takes a local context, so the bridged subterm's
    // sort is re-inferred in the current context (closing the M1 top-level-only
    // gap). The side condition is never skipped: `typeof(a) ≡ typeof(b)` AND
    // `typeof(a) : Prop`.
    if let Some(true) = is_def_eq_proof_irrel(env, ctx, &a_w, &b_w, budget)? {
        return Ok(ConversionStep::Answer(true));
    }

    // exhausted the relation -> provably unequal *within budget*.
    Ok(ConversionStep::Answer(false))
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
            lazy::project_pair(env, ctx, na, *ia, ea, eb, budget)
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
