// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded Nat modulo-bound lane for `omega`.
//!
//! Proves the everyday fact `⊢ a % k < k` when a hypothesis states `0 < k`.
//! The bound `a % k < k` holds exactly when the divisor is positive, a fact the
//! linear (Fourier–Motzkin) relaxation cannot express without knowing the
//! defining division constraints, so `a % k` is dropped as an unparseable atom
//! and the goal falls through to the (failing) linarith delegate.
//!
//! The proof is the single closed term `@Nat.mod_lt a k h` — the prelude's
//! proven `∀ (a n : Nat), Nat.lt 0 n → Nat.lt (Nat.mod a n) n` — where `h` is
//! the `0 < k` hypothesis directly. The `Nat.mod a k` in the lemma's conclusion
//! is definitionally equal to the goal's `HMod.hMod .. instHModNat a k` spelling
//! (the native HMod reducer unfolds the homogeneous instance to `Nat.mod`), and
//! `Nat.lt` is def-eq to the goal's `@LT.lt Nat instLTNat` spelling, so
//! `close_goal` (kernel-grade strict inference) re-checks the whole term against
//! the goal. Soundness never rests on the detection logic.
//!
//! FAIL-CLOSED: the lane fires only when the complete comparison, modulo
//! operation, bound, and positivity hypothesis are definitionally equal to
//! their canonical Nat forms and `Nat.mod_lt` is present. Otherwise it returns
//! `None` and the pipeline is unchanged. A reconstruction failure after those
//! gates is reported loudly instead of hiding an internal inconsistency.
//!
//! Positive literal divisors are handled by synthesizing `Nat.zero_lt_succ`;
//! the exact div/mod identity `(a / k) * k + a % k = a` is handled by
//! `Nat.div_add_mod`. The parity disjunction `n % 2 = 0 ∨ n % 2 = 1` (which
//! needs a case split / `Nat.mod_two_eq_zero_or_one`) remains a future lever.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Literal};

use super::super::match_eq;
use super::{Goal, ProofState, TacticError, TacticResult};

/// The proven prelude lemma `∀ (a n : Nat), Nat.lt 0 n → Nat.lt (Nat.mod a n) n`.
const MOD_LT: &str = "Nat.mod_lt";

/// The proven prelude lemma
/// `∀ (a n : Nat), @Eq Nat ((Nat.div a n) * n + Nat.mod a n) a` — the Euclidean
/// division identity, with NO side condition (it holds for every `a`, `n`).
const DIV_ADD_MOD: &str = "Nat.div_add_mod";

/// Try to prove `⊢ a % k < k` from a hypothesis `0 < k`.
///
/// ENSURES: returns `None` iff the goal is outside the slice (shape, matching
///   hypothesis, or lemma-presence gate failed) — the caller's pipeline
///   proceeds unchanged.
/// ENSURES: returns `Some(Ok(()))` only when `close_goal` kernel-accepted the
///   synthesized closed proof term for the current goal.
/// ENSURES: returns `Some(Err(_))` (loud, tactic "omega") only when a matching
///   hypothesis was found but the kernel rejected the reconstruction; `state`
///   is unchanged.
pub(crate) fn try_nat_mod_lt(state: &mut ProofState, goal: &Goal) -> Option<TacticResult> {
    // Disengage entirely if the backing lemma is absent (import mode).
    state.env().get_const(&Name::from_string(MOD_LT))?;

    // Goal must be `@LT.lt Nat _ (a % k) k` (or `Nat.lt (a % k) k`).
    let target = state.metas.instantiate(&goal.target);
    let (lhs, rhs) = match_lt_operands(&target)?;
    if !state.is_def_eq(goal, &target, &nat_lt(lhs.clone(), rhs.clone())) {
        return None;
    }
    let (a, k) = match_mod_operands(&lhs)?;
    if !state.is_def_eq(goal, &lhs, &nat_mod(a.clone(), k.clone())) {
        return None;
    }
    // The modulus and the strict upper bound must be the same term `k`.
    if !state.is_def_eq(goal, &k, &rhs) {
        return None;
    }

    // Find a proof of `0 < k`: a `0 < k` hypothesis, or — when `k` is a positive
    // literal — the synthesized `Nat.zero_lt_succ (k-1)`.
    let pos_proof = find_pos_proof(state, goal, &k).or_else(|| synth_pos_lit(&k))?;

    // `@Nat.mod_lt a k pos_proof` : `Nat.lt (Nat.mod a k) k`, def-eq to the
    // goal's (`HMod`/`LT.lt`-spelled) `a % k < k`. `close_goal` re-checks the
    // whole term against the goal, so a mismatch fails closed.
    let proof = Expr::apps(
        Expr::const_(Name::from_string(MOD_LT), vec![]),
        [a, k, pos_proof],
    );
    Some(match state.close_goal(goal, proof) {
        Ok(()) => Ok(()),
        Err(err) => Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!("nat-mod bound: kernel rejected the reconstructed proof: {err:?}"),
        }),
    })
}

/// Try to prove the Euclidean division identity `⊢ (a / k) * k + a % k = a`.
///
/// Unlike the mod-bound lane this needs NO side condition — `Nat.div_add_mod`
/// holds for every `a`, `k`. The mod/div atoms are dropped by the linear
/// relaxation, so this identity always fell through to the failing linarith
/// delegate.
///
/// The proof is the single closed term `@Nat.div_add_mod a k` — the prelude's
/// proven `∀ (a n : Nat), (Nat.div a n) * n + Nat.mod a n = a`. The goal's
/// `HDiv`/`HMul`/`HMod`/`HAdd`-spelled left side is definitionally equal to the
/// lemma's bare-`Nat` conclusion (the R158 native reduction unfolds the
/// homogeneous instances), so `close_goal` re-checks the whole term.
///
/// FAIL-CLOSED: matches ONLY the exact `(a / k) * k + a % k` spelling (the
/// commuted `k * (a / k)` and the swapped-summand forms fall through); a
/// spurious match is rejected by `close_goal` and the pipeline proceeds to
/// linarith unchanged.
pub(crate) fn try_nat_div_add_mod(state: &mut ProofState, goal: &Goal) -> Option<TacticResult> {
    // Disengage entirely if the backing lemma is absent (import mode).
    state.env().get_const(&Name::from_string(DIV_ADD_MOD))?;

    // Goal must be `@Eq Nat ((a / k) * k + a % k) a`.
    let target = state.metas.instantiate(&goal.target);
    let (_carrier, lhs, rhs) = match_eq(&target)?;
    let (mul_part, mod_part) = match_nat_add(&lhs)?;
    let (div_part, k_mul) = match_nat_mul(&mul_part)?;
    let (a_div, k_div) = match_nat_div(&div_part)?;
    let (a_mod, k_mod) = match_nat_mod(&mod_part)?;

    // Validate the operand relationships: the dividend must be the RHS `a` in
    // both `a / k` and `a % k`, and the divisor `k` must agree across the `* k`,
    // `a / k`, and `a % k` positions. These are checked by `is_def_eq` on the
    // extracted sub-terms — NOT by `is_def_eq` on the whole target against a
    // rebuilt bare-`Nat` identity, which would require an `HMul.hMul → Nat.mul`
    // native unfolding that is not wired (only HMod/HDiv/HAdd are), silently
    // disengaging the lane on every real goal. Soundness never rests on this
    // detection: `close_goal` re-checks the emitted `@Nat.div_add_mod a k`
    // against the goal, so a spurious match fails closed.
    if !state.is_def_eq(goal, &a_div, &rhs)
        || !state.is_def_eq(goal, &a_mod, &rhs)
        || !state.is_def_eq(goal, &k_mul, &k_div)
        || !state.is_def_eq(goal, &k_div, &k_mod)
    {
        return None;
    }

    // `@Nat.div_add_mod a k` : `(Nat.div a k) * k + Nat.mod a k = a`, def-eq to
    // the goal's `HDiv`/`HMul`/`HMod`-spelled identity. `close_goal` re-checks.
    let proof = Expr::apps(
        Expr::const_(Name::from_string(DIV_ADD_MOD), vec![]),
        [a_div, k_div],
    );
    Some(match state.close_goal(goal, proof) {
        Ok(()) => Ok(()),
        Err(err) => Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!(
                "nat div/mod identity: kernel rejected the reconstructed proof: {err:?}"
            ),
        }),
    })
}

/// When `k` is a positive Nat literal `v`, synthesize a closed proof of `0 < v`
/// as `@Nat.zero_lt_succ (v - 1)` — the prelude's proven `∀ n, 0 < Nat.succ n`,
/// whose conclusion `0 < Nat.succ (v-1)` is definitionally equal to `0 < v`.
/// Returns `None` for a non-literal or zero divisor (`k = 0` leaves the goal for
/// linarith, which correctly fails on the false `n % 0 < 0`). `close_goal`
/// re-checks the whole term, so a wrong synthesis fails closed. This mirrors the
/// kernel's own `Nat.div_add_mod` construction, which builds `0 < 3` the same way.
fn synth_pos_lit(k: &Expr) -> Option<Expr> {
    let v = literal_nat_value(k)?;
    // `None` when the divisor is 0 (`n % 0 < 0` is false; the lane disengages and
    // omega correctly fails).
    let predecessor = v.checked_sub(1)?;
    Some(Expr::app(
        Expr::const_(Name::from_string("Nat.zero_lt_succ"), vec![]),
        Expr::nat_lit(predecessor),
    ))
}

/// The `Nat` value of `k` when it is a *surface literal* — a raw `Nat` literal
/// or `@OfNat.ofNat Nat v _` (the shape a real elaborated `3` takes) — else
/// `None`. Deliberately tighter than `extract_constant`, which recurses into any
/// application's trailing argument and so would read `3` out of `f 3`: a modulus
/// must be a genuine literal for the synthesized `Nat.zero_lt_succ (v-1)` to be
/// definitionally equal to `0 < k`.
fn literal_nat_value(k: &Expr) -> Option<u64> {
    match k.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        ExprKind::App(..) => {
            let ExprKind::Const(name, _) = k.get_app_fn().kind() else {
                return None;
            };
            let args = k.get_app_args();
            // `@OfNat.ofNat Nat v inst` — the literal value is the middle argument.
            if name.to_string() == "OfNat.ofNat" && args.len() == 3 {
                literal_nat_value(args[1])
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Find a hypothesis proving `0 < k` over Nat, returning a closed proof term
/// (the hypothesis fvar). `close_goal` re-checks the caller's whole term, so a
/// spurious match fails closed.
fn find_pos_proof(state: &ProofState, goal: &Goal, k: &Expr) -> Option<Expr> {
    let expected = nat_lt(
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
        k.clone(),
    );
    goal.local_ctx.iter().find_map(|decl| {
        let _ = match_lt_operands(&decl.ty)?;
        state
            .is_def_eq(goal, &decl.ty, &expected)
            .then(|| Expr::fvar(decl.fvar))
    })
}

/// Extract operands only from exact, well-formed less-than heads.
///
/// This is a cheap shape prefilter. The caller must definitionally compare the
/// complete expression with [`nat_lt`] before treating it as Nat ordering.
fn match_lt_operands(e: &Expr) -> Option<(Expr, Expr)> {
    let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
        return None;
    };
    let args = e.get_app_args();
    match name.to_string().as_str() {
        "LT.lt" if args.len() == 4 => Some((args[2].clone(), args[3].clone())),
        "Nat.lt" if args.len() == 2 => Some((args[0].clone(), args[1].clone())),
        _ => None,
    }
}

/// Match a binary Nat operation `a <op> b`, spelled as the surface
/// `@H<Op>.h<op> _ _ _ _ a b` / `@<Op>.<op> _ _ a b` or the raw `Nat.<op> a b`,
/// returning `(a, b)`. `hetero`/`homo` are the `HOp.hOp`/`Op.op` heads and
/// `nat` is the bare `Nat.op` head.
fn match_nat_binop(e: &Expr, hetero: &str, homo: &str, nat: &str) -> Option<(Expr, Expr)> {
    let ExprKind::Const(name, _) = e.get_app_fn().kind() else {
        return None;
    };
    let args = e.get_app_args();
    match name.to_string().as_str() {
        name if name == hetero && args.len() == 6 => Some((args[4].clone(), args[5].clone())),
        name if name == homo && args.len() == 4 => Some((args[2].clone(), args[3].clone())),
        name if name == nat && args.len() == 2 => Some((args[0].clone(), args[1].clone())),
        _ => None,
    }
}

/// Match a Nat addition `a + b`.
fn match_nat_add(e: &Expr) -> Option<(Expr, Expr)> {
    match_nat_binop(e, "HAdd.hAdd", "Add.add", "Nat.add")
}

/// Match a Nat multiplication `a * b`.
fn match_nat_mul(e: &Expr) -> Option<(Expr, Expr)> {
    match_nat_binop(e, "HMul.hMul", "Mul.mul", "Nat.mul")
}

/// Match a Nat division `a / b`.
fn match_nat_div(e: &Expr) -> Option<(Expr, Expr)> {
    match_nat_binop(e, "HDiv.hDiv", "Div.div", "Nat.div")
}

/// Match a Nat modulo `a % k`.
fn match_nat_mod(e: &Expr) -> Option<(Expr, Expr)> {
    match_nat_binop(e, "HMod.hMod", "Mod.mod", "Nat.mod")
}

/// Extract operands only from exact, well-formed modulo heads.
///
/// This is a cheap shape prefilter. The caller must definitionally compare the
/// complete expression with [`nat_mod`] before treating an overloaded
/// `HMod.hMod`/`Mod.mod` application as `Nat.mod`.
fn match_mod_operands(e: &Expr) -> Option<(Expr, Expr)> {
    match_nat_mod(e)
}

fn nat_lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.lt"), vec![]),
        [lhs, rhs],
    )
}

fn nat_mod(dividend: Expr, divisor: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.mod"), vec![]),
        [dividend, divisor],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn const_(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    fn hmod(instance: &str) -> Expr {
        Expr::apps(
            const_("HMod.hMod"),
            [
                const_("Nat"),
                const_("Nat"),
                const_("Nat"),
                const_(instance),
                Expr::bvar(0),
                Expr::bvar(1),
            ],
        )
    }

    fn mod_(instance: &str) -> Expr {
        Expr::apps(
            const_("Mod.mod"),
            [
                const_("Nat"),
                const_(instance),
                Expr::bvar(0),
                Expr::bvar(1),
            ],
        )
    }

    fn lt(instance: &str, lhs: Expr) -> Expr {
        Expr::apps(
            const_("LT.lt"),
            [const_("Nat"), const_(instance), lhs, Expr::bvar(1)],
        )
    }

    #[test]
    fn shape_matcher_extracts_all_exact_hmod_spines_for_later_defeq_check() {
        assert!(match_mod_operands(&hmod("instHModNat")).is_some());
        assert!(match_mod_operands(&hmod("instHModNatNatNat")).is_some());
        assert!(match_mod_operands(&hmod("customNatHMod")).is_some());
    }

    #[test]
    fn shape_matcher_extracts_all_exact_mod_spines_for_later_defeq_check() {
        assert!(match_mod_operands(&mod_("Nat.instMod")).is_some());
        assert!(match_mod_operands(&mod_("customNatMod")).is_some());
    }

    #[test]
    fn matcher_rejects_non_nat_and_malformed_hmod_spines() {
        let wrong_carrier = Expr::apps(
            const_("HMod.hMod"),
            [
                const_("Int"),
                const_("Nat"),
                const_("Nat"),
                const_("instHModNat"),
                Expr::bvar(0),
                Expr::bvar(1),
            ],
        );
        assert!(match_mod_operands(&wrong_carrier).is_some());

        let missing_instance = Expr::apps(
            const_("HMod.hMod"),
            [const_("Nat"), Expr::bvar(0), Expr::bvar(1)],
        );
        assert!(match_mod_operands(&missing_instance).is_none());
    }

    #[test]
    fn lt_shape_matcher_leaves_instance_semantics_to_defeq_check() {
        assert!(match_lt_operands(&lt("instLTNat", Expr::nat_lit(0))).is_some());
        assert!(match_lt_operands(&lt("customNatLT", Expr::nat_lit(0))).is_some());
    }

    #[test]
    fn shape_matchers_reject_lookalike_heads() {
        let fake_mod = Expr::apps(
            const_("User.HMod.hMod"),
            [
                const_("Nat"),
                const_("Nat"),
                const_("Nat"),
                const_("customNatHMod"),
                Expr::bvar(0),
                Expr::bvar(1),
            ],
        );
        let fake_lt = Expr::apps(
            const_("User.LT.lt"),
            [
                const_("Nat"),
                const_("customNatLT"),
                Expr::bvar(0),
                Expr::bvar(1),
            ],
        );
        assert!(match_mod_operands(&fake_mod).is_none());
        assert!(match_lt_operands(&fake_lt).is_none());
    }

    #[test]
    fn positive_literal_synthesis_is_strictly_literal_only() {
        assert!(synth_pos_lit(&Expr::nat_lit(3)).is_some());
        assert!(synth_pos_lit(&Expr::nat_lit(0)).is_none());

        let application_ending_in_a_literal = Expr::app(const_("f"), Expr::nat_lit(3));
        assert!(synth_pos_lit(&application_ending_in_a_literal).is_none());
    }
}
