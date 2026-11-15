// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit coverage for `proof_irrel.rs`: two proof arguments are compared by
//! their propositions, before either is reduced, and nothing else changes.
//! The end-to-end row is `tests/bitvec_multilimb_pipeline_e2e.rs`.

use super::super::*;
use crate::unify::MetaState;
use clean_kernel::mode::CleanMode;
use std::sync::mpsc;
use std::time::Duration;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn ofnat_nat(literal: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            c("Nat"),
            literal.clone(),
            Expr::app(c("instOfNatNat"), literal),
        ],
    )
}

/// `0 ≤ n` by `Nat.zero_le`.
fn zero_le(n: u64) -> Expr {
    Expr::app(c("Nat.zero_le"), Expr::nat_lit(n))
}

#[test]
fn two_proofs_of_one_proposition_unify_by_their_propositions() {
    let env = Environment::with_prelude();
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    // Two DIFFERENT proof terms of `0 ≤ 0`: the theorem, and `Nat.le`'s
    // constructor. Neither is reduced to find that out.
    let by_theorem = zero_le(0);
    let by_constructor = Expr::app(c("Nat.le.refl"), Expr::nat_lit(0));
    assert!(matches!(
        unifier.try_unify_proof_args(&by_theorem, &by_constructor),
        Some(UnifyResult::Success)
    ));
}

#[test]
fn cubical_and_directed_modes_keep_proofs_relevant_as_the_kernel_does() {
    // The kernel's def-eq has no proof irrelevance in the cubical and directed
    // layers (it would be axiom K there); the elaborator must not supply one.
    // Control first: the same pair in the default mode IS identified.
    let env = Environment::with_prelude();
    let by_theorem = zero_le(0);
    let by_constructor = Expr::app(c("Nat.le.refl"), Expr::nat_lit(0));
    for mode in [None, Some(CleanMode::Cubical), Some(CleanMode::Directed)] {
        let mut metas = MetaState::new();
        let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
        if let (Some(mode), Some(tc)) = (mode, unifier.tc_cache.borrow_mut().as_mut()) {
            tc.set_mode(mode);
        }
        let answer = unifier.try_unify_proof_args(&by_theorem, &by_constructor);
        match mode {
            None => assert!(matches!(answer, Some(UnifyResult::Success))),
            Some(mode) => assert!(answer.is_none(), "{mode:?} must keep proofs relevant"),
        }
    }
}

#[test]
fn proofs_of_different_propositions_are_left_to_the_reduced_comparison() {
    let env = Environment::with_prelude();
    let mut metas = MetaState::new();
    let generation = metas.generation();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    // `0 ≤ 3` and `0 ≤ 4` are different propositions: the proof path declines
    // (it never answers Failure) and leaves the state exactly as it found it.
    assert!(unifier
        .try_unify_proof_args(&zero_le(3), &zero_le(4))
        .is_none());
    drop(unifier);
    assert_eq!(metas.generation(), generation);
}

#[test]
fn data_arguments_are_not_proofs() {
    let env = Environment::with_prelude();
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    for (left, right) in [
        (Expr::nat_lit(3), Expr::nat_lit(3)),
        (Expr::nat_lit(3), Expr::nat_lit(4)),
        (Expr::app(c("Nat.succ"), Expr::nat_lit(2)), Expr::nat_lit(3)),
        // A proposition is not a proof of one.
        (
            Expr::apps(c("Nat.le"), [Expr::nat_lit(0), Expr::nat_lit(3)]),
            Expr::apps(c("Nat.le"), [Expr::nat_lit(0), Expr::nat_lit(3)]),
        ),
    ] {
        assert!(
            unifier.try_unify_proof_args(&left, &right).is_none(),
            "{left:?} =?= {right:?} is not a pair of proofs"
        );
    }
    // And the ordinary comparison still decides data by value.
    assert!(matches!(
        unifier.unify(&Expr::nat_lit(3), &Expr::nat_lit(4)),
        UnifyResult::Failure(_)
    ));
}

/// The stall this module exists for, bounded so a regression FAILS instead of
/// hanging the suite.
///
/// Once the kernel refused `BitVec.ofNat`'s payload reducer in this world,
/// both sides WHNF to `BitVec.ofFin 64 (Fin.mk (2^64) (x % 2^64)
/// (Nat.mod_lt x (2^64) _))`. The value arguments agree (`2^63`); the proof
/// arguments mention a 128-bit `x` on one side and `2^63` on the other, and
/// δι-reducing the first is the proof's own recursion on `x` (53 CPU-minutes
/// without finishing, measured 2026-10-07 at ee34e4e22). A heartbeat limit
/// does not bound that reduction (measured: the comparison with this call
/// removed was still running after 15 minutes under a 200,000-heartbeat
/// limit), so the bound is a wall-clock deadline three orders of magnitude
/// above the fixed path's cost, on a thread the test abandons when it fires.
#[test]
fn multilimb_bitvec_proof_argument_is_compared_by_proposition_not_reduced() {
    const DEADLINE: Duration = Duration::from_secs(600);
    let (report, outcome) = mpsc::channel();
    std::thread::spawn(move || {
        let env = Environment::with_prelude();
        let big: u128 = 340_282_366_920_938_463_454_151_235_394_913_435_648; // 2^128 - 2^63
        let side = |operand: Expr| {
            let tc = TypeChecker::new(&env);
            tc.whnf(&Expr::apps(
                c("BitVec.ofNat"),
                [ofnat_nat(Expr::nat_lit(64)), operand],
            ))
        };
        let left = side(Expr::app(
            c("Int.toNat"),
            Expr::app(c("Int.ofNat"), ofnat_nat(Expr::nat_lit_u128(big))),
        ));
        let right = side(ofnat_nat(Expr::nat_lit(9_223_372_036_854_775_808)));
        let spine = matches!(
            left.get_app_fn().kind(),
            ExprKind::Const(name, _) if *name == Name::from_string("BitVec.ofFin")
        );
        let mut metas = MetaState::new();
        let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
        // `unify_core`, not `unify`: the entry's kernel congruence fast path
        // closes this pair before the App/App arm runs, but the elaborator
        // reaches it through `unify_meta` (an assigned `?a` of `rfl`'s
        // `@Eq ?α ?a ?a` against the other side), which enters here.
        let unified = matches!(unifier.unify_core(&left, &right), UnifyResult::Success);
        let _ = report.send((spine, unified));
    });
    let (spine, unified) = outcome.recv_timeout(DEADLINE).unwrap_or_else(|_| {
        panic!(
            "no answer in {DEADLINE:?}: the unifier is reducing a proof argument \
             instead of comparing the two propositions"
        )
    });
    assert!(
        spine,
        "the payload reducer stays refused here, so WHNF exposes the Fin.mk spine"
    );
    assert!(unified, "two proofs of `2^63 < 2^64` must unify");
}

/// A proof that still mentions an unassigned metavariable is NOT answered by
/// proof irrelevance: the structural comparison runs and solves it.
///
/// `And.intro ?m (Nat.zero_le 0) =?= And.intro (Nat.le.refl 0) (Nat.zero_le 0)`
/// are two proofs of `0 ≤ 0 ∧ 0 ≤ 0`. Answered by their propositions, the pair
/// unified with `?m` never assigned, and an elaborated term carried it to the
/// kernel as a free variable (Mathlib's `Classical.choose_eq`, 2026-10-16).
/// Lean assigns `?m` here: it compares the same-head applications argument by
/// argument before it ever reaches proof irrelevance.
#[test]
fn a_proof_with_an_unassigned_metavariable_is_solved_not_skipped() {
    let env = Environment::with_prelude();
    let le00 = Expr::apps(c("Nat.le"), [Expr::nat_lit(0), Expr::nat_lit(0)]);
    let mut metas = MetaState::new();
    let m = metas.fresh(le00.clone());
    let and_intro =
        |a: Expr, b: Expr| Expr::apps(c("And.intro"), [le00.clone(), le00.clone(), a, b]);
    let with_meta = and_intro(Expr::fvar(MetaState::to_fvar(m)), zero_le(0));
    let ground = and_intro(Expr::app(c("Nat.le.refl"), Expr::nat_lit(0)), zero_le(0));
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(
        unifier.try_unify_proof_args(&with_meta, &ground).is_none(),
        "a proof mentioning an unassigned metavariable must decline the proof-irrelevance answer"
    );
    assert!(matches!(
        unifier.unify(&with_meta, &ground),
        UnifyResult::Success
    ));
    drop(unifier);
    assert!(
        metas.is_assigned(m),
        "the structural comparison must assign the metavariable the proof mentions"
    );
}
