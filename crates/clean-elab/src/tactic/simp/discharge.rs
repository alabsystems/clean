// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Side-condition discharge for **conditional** simp lemmas (RC-J).
//!
//! A conditional simp lemma is one whose statement carries hypotheses:
//!
//! ```text
//! @[simp] theorem Nat.sub_add_cancel (a b : Nat) (h : b ≤ a) : a - b + b = a
//! ```
//!
//! Matching the LHS `a - b + b` determines `a` and `b` but says nothing about
//! `h`. Lean resolves this with a `discharge?` hook
//! (`Lean/Meta/Tactic/Simp/Types.lean`): every hypothesis left over after the
//! LHS match is handed to the discharger, and the rewrite is **abandoned** if
//! any of them cannot be closed. `Simp.Config.maxDischargeDepth` (upstream
//! default `2`) bounds the recursion so a lemma whose premise requires itself
//! terminates rather than looping.
//!
//! This module is Clean's discharger. It is deliberately conservative — three
//! stages, each of which produces a real proof term:
//!
//! 1. **`assumption`** — a local hypothesis whose type is def-eq to the premise.
//! 2. **trivial closers** — `True.intro` when the premise WHNFs to `True`,
//!    `Eq.refl` when it is a reflexive equality.
//! 3. **recursive `simp`** — simplify the premise; when it normalizes to `True`
//!    with a witness `h : premise = True`, the discharge proof is
//!    `@Eq.mpr.{0} premise True h True.intro : premise` (exactly the shape
//!    `simp/expr.rs::try_simp_ite` already uses to turn a `c = True` rewrite
//!    into a proof of `c`).
//!
//! # Soundness
//!
//! Every stage's candidate is re-checked by [`proves`] before it is returned:
//! the candidate's *inferred* type must be def-eq to the premise, in the
//! premise's own goal context. A premise that cannot be discharged yields
//! `None`, and the caller (`try_apply_simp_lemma_with_proof`) then abandons the
//! entire rewrite. Nothing here skips an argument slot, fabricates a witness,
//! emits a `sorry`, or closes a goal: a discharged proof only ever becomes an
//! **argument** of the lemma application, whose assembled type is validated by
//! `proof_matches_rewrite` and re-checked downstream by `ProofState::close_goal`
//! and the kernel's `add_decl`.
//!
//! # Scope (what is deliberately NOT covered yet)
//!
//! * Only lemmas that name an ENVIRONMENT constant carry premises here — the
//!   binder telescope is read back from `decl.type_`. A simp rule built from a
//!   *local hypothesis* (`collect_hypothesis_lemmas`) or from a hand-written
//!   builtin pattern keeps its pre-existing unconditional handling.
//! * A side condition that is still open (mentions a binder simp is recursing
//!   under) is not discharged; it has no context to be proved in.
//! * Undischarged premises produce `NoProgress`, never a side goal. Lean can
//!   also *postpone* a hypothesis as a new goal (`simp` with `Simp.Config`
//!   discharge hooks that mimic `rw`'s side goals); Clean does not, so the
//!   conservative answer is always "abandon".

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::expr::simp_expr;
use super::proof::mk_eq_refl_expr;
use super::types::{SimpConfig, SimpLemmaSet};
use crate::tactic::core::{Goal, ProofState};
use crate::tactic::match_equality;

/// Try to build a proof of `premise` in `goal`'s local context.
///
/// # Contract
///
/// REQUIRES: `premise` is fully instantiated (no unassigned pattern metas) and
///   closed — an open premise cannot be stated as a side goal, so it is
///   rejected outright.
/// ENSURES: On `Some(p)`, `state.infer_type(goal, &p)` succeeded and its result
///   is def-eq to `premise` — i.e. `p : premise` was *checked*, never assumed.
/// ENSURES: On `None`, no term is produced and the caller must abandon the
///   rewrite (fail-closed).
pub(crate) fn discharge_premise(
    state: &ProofState,
    goal: &Goal,
    premise: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
) -> Option<Expr> {
    // A side condition mentioning a binder-opened variable has no local
    // context to be proved in; `infer_type` would be meaningless there.
    if premise.has_loose_bvars() {
        return None;
    }

    if let Some(proof) = by_assumption(state, goal, premise) {
        return Some(proof);
    }
    if let Some(proof) = by_trivial(state, goal, premise) {
        return Some(proof);
    }
    if config.discharge_depth > 0 {
        if let Some(proof) = by_recursive_simp(state, goal, premise, lemmas, config) {
            return Some(proof);
        }
    }
    None
}

/// Stage 1 — `assumption`: a local hypothesis already proves the premise.
///
/// SOUNDNESS: the returned `FVar` has exactly `decl.ty` as its type, and
/// `decl.ty` is checked def-eq to `premise`, so the conversion rule gives
/// `fvar : premise`. [`proves`] re-checks this independently.
fn by_assumption(state: &ProofState, goal: &Goal, premise: &Expr) -> Option<Expr> {
    for decl in &goal.local_ctx {
        // Cheap syntactic prefilter before the def-eq check: local contexts
        // under real imports are long and `is_def_eq` is not free.
        let candidate = Expr::fvar(decl.fvar);
        if (decl.ty == *premise || state.is_def_eq(goal, &decl.ty, premise))
            && proves(state, goal, &candidate, premise)
        {
            return Some(candidate);
        }
    }
    None
}

/// Stage 2 — trivial closers: `True.intro`, and `Eq.refl` for a premise whose
/// two sides are definitionally equal.
///
/// SOUNDNESS: `True.intro : True` fires only when the premise WHNFs to the
/// `True` constant, and `@Eq.refl.{u} α a : a = a` only when the premise is an
/// `@Eq` whose sides are def-eq. Both are re-checked by [`proves`], so a
/// mis-built level or carrier argument is rejected rather than emitted.
fn by_trivial(state: &ProofState, goal: &Goal, premise: &Expr) -> Option<Expr> {
    let whnf = state.whnf(goal, premise);

    if super::is_true_const(&whnf) {
        let intro = Expr::const_(Name::from_string("True.intro"), vec![]);
        if proves(state, goal, &intro, premise) {
            return Some(intro);
        }
    }

    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(&whnf) {
        if state.is_def_eq(goal, &lhs, &rhs) {
            if let Some(refl) = mk_eq_refl_expr(state, goal, &lhs) {
                if proves(state, goal, &refl, premise) {
                    return Some(refl);
                }
            }
        }
    }

    None
}

/// Stage 3 — recursive `simp`: normalize the premise, discharge the NORMALIZED
/// form, and transport the witness back.
///
/// Simp rarely drives a proposition all the way to the `True` constant. What it
/// does reliably is *normalize*: the side condition `(b && true) = b` simplifies
/// to `b = b`, which stage 2 then closes by `Eq.refl`. Demanding a literal
/// `True` here would leave this whole stage dead for exactly the premise shapes
/// real conditional lemmas carry, so the recursion is stated on
/// [`discharge_premise`] itself:
///
/// ```text
/// h  : premise = premise'                  -- from the simp engine
/// p' : premise'                            -- discharged at depth-1
/// @Eq.mpr.{0} premise premise' h p' : premise
/// ```
///
/// Clean's `Eq.mpr` is `{α β : Sort u} → α = β → β → α`
/// (`clean-kernel/src/env/core_eq/transport.rs`), so all four arguments are
/// supplied positionally — the same construction `simp/expr.rs::try_simp_ite`
/// uses for its `if_pos` condition witness. Recursing through
/// `discharge_premise` (rather than only `by_trivial`) also lets the normalized
/// premise be closed by `assumption`, which a `simp`-rewritten hypothesis often
/// is.
///
/// The child config decrements [`SimpConfig::discharge_depth`], and the
/// `result.expr == *premise` guard rejects a no-op normalization, so the
/// recursion strictly descends: a conditional lemma whose premise requires
/// itself runs out of budget and the discharge fails closed.
///
/// SOUNDNESS: a definitional-only normalization carries no witness
/// (`result.proof == None`) and is rejected here rather than papered over.
/// The assembled term is re-checked by [`proves`].
fn by_recursive_simp(
    state: &ProofState,
    goal: &Goal,
    premise: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
) -> Option<Expr> {
    let child = SimpConfig {
        discharge_depth: config.discharge_depth - 1,
        ..config.clone()
    };
    let result = simp_expr(state, goal, premise, lemmas, &child);
    if result.expr == *premise {
        return None;
    }
    let witness = result.proof?;
    let normalized = discharge_premise(state, goal, &result.expr, lemmas, &child)?;

    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]),
        [premise.clone(), result.expr, witness, normalized],
    );
    proves(state, goal, &proof, premise).then_some(proof)
}

/// The single soundness gate every discharge candidate passes through:
/// `candidate` is accepted only when its *inferred* type is def-eq to
/// `premise`.
///
/// ENSURES: Returns `false` for any candidate carrying loose bound variables or
///   whose type cannot be inferred, so an unchecked term is never accepted.
fn proves(state: &ProofState, goal: &Goal, candidate: &Expr, premise: &Expr) -> bool {
    if candidate.has_loose_bvars() {
        return false;
    }
    match state.infer_type(goal, candidate) {
        Ok(ty) => state.is_def_eq(goal, &ty, premise),
        Err(_) => false,
    }
}
