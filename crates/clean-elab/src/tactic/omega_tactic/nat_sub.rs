// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded Nat truncated-subtraction lane for `omega`.
//!
//! Proves the everyday truncation fact `⊢ a - b = 0` when a hypothesis states
//! `a ≤ b` (or `a < b`). Nat subtraction is *truncated* (`a - b = 0` whenever
//! `a ≤ b`), a fact the linear (Fourier–Motzkin) relaxation cannot express
//! without a case-split, so this family always fell through to the (failing)
//! linarith delegate. `expr_to_mathverse_constraint` drops the `a - b` atom, the
//! hypotheses-only system is satisfiable, and the goal is never proved.
//!
//! The proof is the single closed term
//! `@Nat.ulpRound.sub_eq_zero_of_le a b le` — the prelude's proven
//! (double-induction, zero-axiom) `∀ (a b : Nat), Nat.le a b → a - b = 0` — where
//! `le` is the `a ≤ b` hypothesis directly, or `@Nat.le_of_lt a b h` weakening an
//! `a < b` hypothesis (also a proven, axiom-clean lemma). The whole term is
//! re-checked by `close_goal` (kernel-grade strict inference), so soundness never
//! rests on the detection logic. FAIL-CLOSED: the lane fires only on the exact
//! `a - b = 0` goal shape with a matching `a ≤ b` / `a < b` hypothesis and only
//! when the backing lemma is present; otherwise it returns `None` and the
//! pipeline is byte-identical. A wrong match (e.g. mismatched operands) is
//! rejected by `close_goal` and the pipeline proceeds to linarith unchanged.
//!
//! A sibling lane ([`try_nat_sub_add_cancel`]) proves the dual shape
//! `b ≤ a → a - b + b = a` via the proven, axiom-clean
//! `Nat.ulpRound.sub_add_cancel`. Both lemmas are `Nat.ulpRound.`-namespaced and
//! import-suppressed, so in import mode the lanes disengage (present-in-default-
//! lane guard) — the honest loud floor is unchanged there. `a + k ≤ b` offset
//! hypotheses and `b < a → 0 < a - b` (no proven `Nat.sub_pos` lemma registered
//! yet) are the next lever.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::super::arith_mathverse_parse::extract_constant;
use super::super::{match_eq, match_le, match_lt};
use super::{Goal, ProofState, TacticError, TacticResult};

/// The proven prelude lemma `∀ (a b : Nat), Nat.le a b → @Eq Nat (a - b) 0`.
const SUB_EQ_ZERO_OF_LE: &str = "Nat.ulpRound.sub_eq_zero_of_le";

/// The proven, axiom-clean prelude Theorem
/// `∀ (a b : Nat), @Eq Nat (Nat.add a b) (Nat.add b a)` (Nat.add_comm), used to
/// commute the addends so the `(a - b) + b = a` truncation lemma discharges a
/// `b + (a - b) = a` goal. Its axiom closure is empty, so the reconstructed
/// proof stays axiom-clean.
const ADD_COMM: &str = "Nat.add_comm";

/// The proven prelude lemma `∀ {a b : Nat}, Nat.lt a b → Nat.le a b`, used to
/// weaken a `<` hypothesis into the `≤` the truncation lemma needs. Both this
/// and `SUB_EQ_ZERO_OF_LE` are proven Theorems with an EMPTY axiom closure
/// (`axiom_deps == {}`), so the reconstructed proof stays axiom-clean.
const LE_OF_LT: &str = "Nat.le_of_lt";

/// The proven prelude lemma `∀ (a n : Nat), Nat.le n a → @Eq Nat ((a - n) + n) a`
/// (axiom-clean Theorem), backing the `b ≤ a → a - b + b = a` truncation shape.
const SUB_ADD_CANCEL: &str = "Nat.ulpRound.sub_add_cancel";

/// The proven, axiom-clean prelude Theorem
/// `∀ (a b : Nat), @Eq Nat ((a + b) - a) b` (Nat.ulpRound.add_sub_cancel_left),
/// backing the UNCONDITIONAL `(a + b) - a = b` left-cancellation. Its axiom
/// closure is empty, so the reconstructed proof stays axiom-clean.
const ADD_SUB_CANCEL_LEFT: &str = "Nat.ulpRound.add_sub_cancel_left";

/// Try to prove `⊢ a - b = 0` from a hypothesis `a ≤ b` or `a < b`.
///
/// ENSURES: returns `None` iff the goal is outside the slice (shape, matching
///   hypothesis, or lemma-presence gate failed) — the caller's pipeline
///   proceeds unchanged.
/// ENSURES: returns `Some(Ok(()))` only when `close_goal` kernel-accepted the
///   synthesized closed proof term for the current goal.
/// ENSURES: returns `Some(Err(_))` (loud, tactic "omega") only when a matching
///   hypothesis was found but the kernel rejected the reconstruction; `state`
///   is unchanged.
pub(crate) fn try_nat_sub_eq_zero(state: &mut ProofState, goal: &Goal) -> Option<TacticResult> {
    // Disengage entirely if the backing lemma is absent (import mode).
    state
        .env()
        .get_const(&Name::from_string(SUB_EQ_ZERO_OF_LE))?;

    // Goal must be `@Eq Nat (a - b) 0`.
    let target = state.metas.instantiate(&goal.target);
    let (carrier, lhs, rhs) = match_eq(&target)?;
    if !is_nat_const(&carrier) {
        return None;
    }
    if extract_constant(&rhs)? != 0 {
        return None;
    }
    let (a, b) = match_nat_sub(&lhs)?;

    // Find a proof of `a ≤ b` over the same operands (from an `a ≤ b` hypothesis
    // directly, or an `a < b` hypothesis weakened via `Nat.le_of_lt`).
    let le_proof = find_le_proof(goal, &a, &b)?;

    // `@Nat.ulpRound.sub_eq_zero_of_le a b le_proof` : `Nat.sub a b = 0`, def-eq
    // to the goal's (possibly `HSub`/`OfNat`-spelled) `a - b = 0`. `close_goal`
    // re-checks the whole term against the goal, so a mismatch fails closed.
    let proof = Expr::apps(
        Expr::const_(Name::from_string(SUB_EQ_ZERO_OF_LE), vec![]),
        [a, b, le_proof],
    );
    Some(match state.close_goal(goal, proof) {
        Ok(()) => Ok(()),
        Err(err) => Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!("nat-sub truncation: kernel rejected the reconstructed proof: {err:?}"),
        }),
    })
}

/// Try to prove `⊢ a - b + b = a` from a hypothesis `b ≤ a` (or `b < a`).
///
/// The dual truncation fact: when `b ≤ a`, subtracting then re-adding `b`
/// recovers `a`. Like the eq-zero lane, this needs a case-split the linear
/// relaxation cannot express, so it fell through to the failing linarith
/// delegate. The proof is the single closed term
/// `@Nat.ulpRound.sub_add_cancel a b le` (the prelude's proven, axiom-clean
/// `∀ (a n : Nat), Nat.le n a → (a - n) + n = a`), re-checked by `close_goal`.
/// FAIL-CLOSED with the same guarantees as [`try_nat_sub_eq_zero`].
pub(crate) fn try_nat_sub_add_cancel(state: &mut ProofState, goal: &Goal) -> Option<TacticResult> {
    // Disengage entirely if the backing lemma is absent (import mode).
    state.env().get_const(&Name::from_string(SUB_ADD_CANCEL))?;

    // Goal must be `@Eq Nat ((a - b) + b) a`.
    let target = state.metas.instantiate(&goal.target);
    let (carrier, lhs, rhs) = match_eq(&target)?;
    if !is_nat_const(&carrier) {
        return None;
    }
    let (add_l, add_r) = match_nat_add(&lhs)?;
    let (a, b) = match_nat_sub(&add_l)?;
    // The re-added operand and the RHS must be the subtrahend `b` and minuend `a`.
    if add_r != b || rhs != a {
        return None;
    }

    // Find a proof of `b ≤ a` (note the operand order: the subtrahend bounds the
    // minuend), directly or by weakening a `b < a` hypothesis.
    let le_proof = find_le_proof(goal, &b, &a)?;

    // `@Nat.ulpRound.sub_add_cancel a b le_proof` : `(Nat.sub a b) + b = a`,
    // def-eq to the goal's `HSub`/`HAdd`-spelled `a - b + b = a`.
    let proof = Expr::apps(
        Expr::const_(Name::from_string(SUB_ADD_CANCEL), vec![]),
        [a, b, le_proof],
    );
    Some(match state.close_goal(goal, proof) {
        Ok(()) => Ok(()),
        Err(err) => Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!("nat-sub-add cancel: kernel rejected the reconstructed proof: {err:?}"),
        }),
    })
}

/// Try to prove `⊢ b + (a - b) = a` from a hypothesis `b ≤ a` (or `b < a`).
///
/// The add-commuted sibling of [`try_nat_sub_add_cancel`]: Lean writes the
/// re-addition on either side of the truncated difference, but the backing lemma
/// `Nat.ulpRound.sub_add_cancel` states only the `(a - b) + b = a` orientation,
/// so a `b + (a - b) = a` goal fell through to the failing linarith delegate. The
/// proof commutes the addends with the proven, axiom-clean `@Nat.add_comm b
/// (a - b)` and chains through `Eq.trans`:
///
///   `@Eq.trans.{1} Nat (b + (a - b)) ((a - b) + b) a`
///   `    (@Nat.add_comm b (a - b))`
///   `    (@Nat.ulpRound.sub_add_cancel a b le)`
///
/// `Nat.add_comm` emits the middle term in raw `Nat.add` spelling — identical to
/// the lemma's LHS and def-eq to the goal's `HAdd`/`HSub` spelling — so the
/// `Eq.trans` chain type-checks. The whole term is re-checked by `close_goal`
/// (kernel-grade strict inference), so soundness never rests on the detection
/// logic. FAIL-CLOSED with the same guarantees as [`try_nat_sub_eq_zero`].
pub(crate) fn try_nat_add_sub_cancel(state: &mut ProofState, goal: &Goal) -> Option<TacticResult> {
    // Disengage entirely if either backing lemma is absent (import mode / bare
    // env) — the caller's pipeline then proceeds byte-identically.
    state.env().get_const(&Name::from_string(SUB_ADD_CANCEL))?;
    state.env().get_const(&Name::from_string(ADD_COMM))?;

    // Goal must be `@Eq Nat (b + (a - b)) a`.
    let target = state.metas.instantiate(&goal.target);
    let (carrier, lhs, rhs) = match_eq(&target)?;
    if !is_nat_const(&carrier) {
        return None;
    }
    let (add_l, add_r) = match_nat_add(&lhs)?; // add_l = b, add_r = (a - b)
    let (a, b) = match_nat_sub(&add_r)?;
    // The left addend must be the subtrahend `b`, and the RHS the minuend `a`.
    if add_l != b || rhs != a {
        return None;
    }

    // Find a proof of `b ≤ a` (subtrahend bounds minuend), directly or by
    // weakening a `b < a` hypothesis.
    let le_proof = find_le_proof(goal, &b, &a)?;

    // `@Nat.ulpRound.sub_add_cancel a b le` : `(a - b) + b = a`.
    let cancel = Expr::apps(
        Expr::const_(Name::from_string(SUB_ADD_CANCEL), vec![]),
        [a.clone(), b.clone(), le_proof],
    );
    // `@Nat.add_comm b (a - b)` : `Nat.add b (a - b) = Nat.add (a - b) b`.
    let comm = Expr::apps(
        Expr::const_(Name::from_string(ADD_COMM), vec![]),
        [b.clone(), add_r.clone()],
    );
    // Middle term `Nat.add (a - b) b` — exactly `Nat.add_comm`'s RHS and def-eq
    // to `sub_add_cancel`'s LHS, so the kernel accepts the `Eq.trans` chain.
    let mid = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [add_r.clone(), b.clone()],
    );
    // `@Eq.trans.{1} Nat (b + (a - b)) ((a - b) + b) a comm cancel`.
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [nat, lhs.clone(), mid, a.clone(), comm, cancel],
    );
    Some(match state.close_goal(goal, proof) {
        Ok(()) => Ok(()),
        Err(err) => Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!("nat-add-sub cancel: kernel rejected the reconstructed proof: {err:?}"),
        }),
    })
}

/// Try to prove `⊢ (a + b) - a = b` — the UNCONDITIONAL left-cancellation.
///
/// Nat's truncated subtraction makes `(a + b) - a = b` hold for ALL `a, b` (no
/// side condition: `a ≤ a + b` always), but the linear relaxation drops the
/// `- a` atom, so the goal fell through to the failing linarith delegate. The
/// proof is the single closed term `@Nat.ulpRound.add_sub_cancel_left a b`
/// (proven, axiom-clean), re-checked by `close_goal`. Unlike the sibling lanes,
/// no hypothesis is needed. FAIL-CLOSED: fires only on the exact `(a + b) - a = b`
/// shape — the subtracted term is the LEFT addend and the RHS is the right
/// addend — and only when the backing lemma is present; otherwise returns `None`
/// and the pipeline is byte-identical. A wrong match is rejected by `close_goal`.
pub(crate) fn try_nat_add_sub_cancel_left(
    state: &mut ProofState,
    goal: &Goal,
) -> Option<TacticResult> {
    // Disengage entirely if the backing lemma is absent (import mode / bare env).
    state
        .env()
        .get_const(&Name::from_string(ADD_SUB_CANCEL_LEFT))?;

    // Goal must be `@Eq Nat ((a + b) - a) b`.
    let target = state.metas.instantiate(&goal.target);
    let (carrier, lhs, rhs) = match_eq(&target)?;
    if !is_nat_const(&carrier) {
        return None;
    }
    let (sub_l, sub_r) = match_nat_sub(&lhs)?; // sub_l = a + b, sub_r = a
    let (add_l, add_r) = match_nat_add(&sub_l)?; // add_l = a, add_r = b
                                                 // The subtracted term must be the LEFT addend, and the RHS the right addend.
    if sub_r != add_l || rhs != add_r {
        return None;
    }

    // `@Nat.ulpRound.add_sub_cancel_left a b` : `(a + b) - a = b`, def-eq to the
    // goal's `HAdd`/`HSub`-spelled form.
    let proof = Expr::apps(
        Expr::const_(Name::from_string(ADD_SUB_CANCEL_LEFT), vec![]),
        [add_l, add_r],
    );
    Some(match state.close_goal(goal, proof) {
        Ok(()) => Ok(()),
        Err(err) => Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!(
                "nat add-sub-cancel-left: kernel rejected the reconstructed proof: {err:?}"
            ),
        }),
    })
}

/// Find a hypothesis proving `lo ≤ hi` over Nat, returning a closed proof term:
/// an `lo ≤ hi` hypothesis used directly, or an `lo < hi` hypothesis weakened
/// via `@Nat.le_of_lt lo hi h`. Both underlying lemmas are proven and
/// axiom-clean, and `close_goal` re-checks the caller's whole term, so a
/// spurious match fails closed.
fn find_le_proof(goal: &Goal, lo: &Expr, hi: &Expr) -> Option<Expr> {
    goal.local_ctx.iter().find_map(|decl| {
        if let Some((c2, l2, r2)) = match_le(&decl.ty) {
            if is_nat_const(&c2) && &l2 == lo && &r2 == hi {
                return Some(Expr::fvar(decl.fvar));
            }
        }
        if let Some((c2, l2, r2)) = match_lt(&decl.ty) {
            if is_nat_const(&c2) && &l2 == lo && &r2 == hi {
                // @Nat.le_of_lt lo hi h : Nat.le lo hi
                return Some(Expr::apps(
                    Expr::const_(Name::from_string(LE_OF_LT), vec![]),
                    [lo.clone(), hi.clone(), Expr::fvar(decl.fvar)],
                ));
            }
        }
        None
    })
}

/// Match a Nat addition `a + b`, spelled `@HAdd.hAdd _ _ _ _ a b` /
/// `@Add.add _ _ a b` or the raw `Nat.add a b`, returning `(a, b)`.
fn match_nat_add(e: &Expr) -> Option<(Expr, Expr)> {
    let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
        return None;
    };
    let args = e.get_app_args();
    match name.to_string().as_str() {
        "HAdd.hAdd" | "Add.add" if args.len() >= 2 => {
            Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()))
        }
        "Nat.add" if args.len() == 2 => Some((args[0].clone(), args[1].clone())),
        _ => None,
    }
}

/// Match a Nat subtraction `a - b`, spelled either as the surface
/// `@HSub.hSub _ _ _ _ a b` / `@Sub.sub _ _ a b` or the raw `Nat.sub a b`,
/// returning `(a, b)`.
fn match_nat_sub(e: &Expr) -> Option<(Expr, Expr)> {
    let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
        return None;
    };
    let args = e.get_app_args();
    let name = name.to_string();
    match name.as_str() {
        "HSub.hSub" | "Sub.sub" if args.len() >= 2 => {
            Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()))
        }
        "Nat.sub" if args.len() == 2 => Some((args[0].clone(), args[1].clone())),
        _ => None,
    }
}

/// `true` when `e` is the constant `Nat`.
fn is_nat_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}
