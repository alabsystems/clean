// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8's `simpCtorEq` (`Lean/Meta/Tactic/Simp/Rewrite.lean`): an
//! equation between two DIFFERENT constructors simplifies to `False`.
//!
//! It is a step of Lean's `postDefault`, so it runs on every simp call, the
//! simprocs notwithstanding — under `simp only [↓reduceIte]` it is what turns
//! the condition `false = true` into `False` for `reduceIte` to collapse
//! (trust-ir's `simp only [bne_self_eq_false, ↓reduceIte]`). Clean runs it in
//! every simprocs scope too: it used to run only under
//! [`super::types::SimprocScope::Named`], on the theory that the default
//! scope's table and lemma set reach the same goals — they do not reach
//! `(true = true ∧ true = false) ↔ P.a = P.b` (G40, ledger (110)).
//!
//! The 4.30 oracle registers this same operation as `reduceCtorEq`.
//! `lean_builtin_simprocs` configures whether it runs from that source world's
//! ordered simproc list; this proof-producing implementation is shared.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level, Literal};

use super::lemmas_local::prop_false_proof;
use super::types::SimpResult;
use crate::tactic::core::{Goal, ProofState};

/// `expr` is `@Eq.{u} T lhs rhs` with `lhs`/`rhs` applications of two
/// different constructors: rewrite it to `False`, proved by `propext` over the
/// `noConfusion` refutation (Lean's `mkEqFalse'` over `mkNoConfusion`).
///
/// A side is a constructor application as Lean's `constructorApp'?` reads it:
/// a fully applied constructor or a Nat literal (`litToCtor`: `0` is
/// `Nat.zero`, `n + 1` is `Nat.succ`), as written or after weak-head
/// reduction at instance transparency (Lean's `withReducibleAndInstances`).
/// Equal constructors leave it alone, as Lean's does — injection is not this
/// step's job.
///
/// SOUNDNESS: the refutation comes from `build_noconfusion_ne_proof`, which
/// answers only for distinct constructors of one inductive, and the step's
/// proof is re-checked with the rest of simp's at `close_goal`.
pub(super) fn simp_ctor_eq(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<SimpResult> {
    let ExprKind::Const(head, levels) = expr.get_app_fn().kind() else {
        return None;
    };
    let args = expr.get_app_args();
    if *head != Name::from_string("Eq") || args.len() != 3 {
        return None;
    }
    let (eq_type, lhs, rhs) = (args[0], args[1], args[2]);
    let lhs = constructor_side(state, goal, lhs)?;
    let rhs = constructor_side(state, goal, rhs)?;
    if lhs.0 == rhs.0 {
        return None;
    }
    let level = levels
        .first()
        .cloned()
        .unwrap_or_else(|| Level::succ(Level::zero()));
    let refutation = crate::tactic::decide_eq_noconfusion::build_noconfusion_ne_proof(
        state.env(),
        eq_type,
        &lhs.1,
        &rhs.1,
        &level,
    )?;
    Some(SimpResult {
        expr: Expr::const_(Name::from_string("False"), vec![]),
        proof: Some(prop_false_proof(expr, &refutation)),
    })
}

/// The constructor `side` is an application of, with the form it was read in
/// (as written, or weak-head reduced at instance transparency).
fn constructor_side(state: &ProofState, goal: &Goal, side: &Expr) -> Option<(Name, Expr)> {
    if let Some(ctor) = constructor_head(state, side) {
        return Some((ctor, side.clone()));
    }
    let reduced = state.whnf_instances(goal, side);
    constructor_head(state, &reduced).map(|ctor| (ctor, reduced))
}

/// Lean's `constructorApp?` after `litToCtor`: the constructor a fully
/// applied constructor application, or a Nat literal, is built by.
fn constructor_head(state: &ProofState, expr: &Expr) -> Option<Name> {
    if let ExprKind::Lit(Literal::Nat(n)) = expr.kind() {
        let zero = n.to_u64() == Some(0);
        return Some(Name::from_string(if zero {
            "Nat.zero"
        } else {
            "Nat.succ"
        }));
    }
    let ExprKind::Const(name, _) = expr.get_app_fn().kind() else {
        return None;
    };
    let ctor = state.env().get_constructor(name)?;
    let arity = usize::try_from(ctor.num_params + ctor.num_fields).ok()?;
    (expr.get_app_args().len() == arity).then(|| name.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::Environment;

    fn option_eq(lhs: Expr, rhs: Expr) -> Expr {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let option_nat = Expr::app(
            Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
            nat,
        );
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [option_nat, lhs, rhs],
        )
    }

    fn some(n: u64) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
            [
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::nat_lit(n),
            ],
        )
    }

    fn none() -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Option.none"), vec![Level::zero()]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        )
    }

    #[test]
    fn test_simp_ctor_eq_refutes_different_constructors_with_a_checked_proof() {
        let eq = option_eq(some(1), none());
        let state = ProofState::new(Environment::with_prelude(), Expr::prop());
        let goal = state.current_goal().cloned().expect("a goal");
        let step = simp_ctor_eq(&state, &goal, &eq).expect("`some 1 = none` is refuted");
        assert_eq!(step.expr, Expr::const_(Name::from_string("False"), vec![]));
        let proof = step.proof.expect("a proof");
        let ty = state
            .infer_type_strict(&goal, &proof)
            .expect("the refutation type-checks");
        let expected = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Expr::prop(), eq, step.expr],
        );
        assert!(
            state.is_def_eq(&goal, &ty, &expected),
            "the proof must prove `(some 1 = none) = False`, proves {ty:?}"
        );
    }

    #[test]
    fn test_simp_ctor_eq_leaves_equal_constructors_alone() {
        // Lean's `simpCtorEq` refutes DIFFERENT constructors only: `some 1 =
        // some 2` needs injection, which is not this step (pinned Lean 4.8.0:
        // "simp made no progress" under `simp only [↓reduceIte]`).
        let state = ProofState::new(Environment::with_prelude(), Expr::prop());
        let goal = state.current_goal().cloned().expect("a goal");
        for eq in [
            option_eq(some(1), some(2)),
            option_eq(some(1), some(1)),
            option_eq(none(), none()),
        ] {
            assert!(
                simp_ctor_eq(&state, &goal, &eq).is_none(),
                "{eq:?} has equal constructor heads"
            );
        }
    }
}
