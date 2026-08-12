// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ExtractionIR reference-semantics tests (rank 7, B4).
//!
//! The load-bearing test is [`doubler_matches_the_kernel_proved_values`]: the
//! interpreter must reproduce the depth-k observations that the kernel PROVED
//! about the source in `tests/fixtures/codata/is2_indexed_stream.lean`. Those
//! `rfl` theorems are the source side of the observational claim; these values
//! are the target side.
//!
//! What that test is and is not: it is a DIFFERENTIAL over the depths actually
//! run, not a proof over all depths. Calling it more than that would be the
//! masquerade this rung is most exposed to.

use super::*;

/// `doubler` from the width-1 fixture, in extraction form.
///
/// Source:
/// ```lean
/// codef doubler (n : Nat) (acc : Nat) : IS2 n where
///   val  := acc
///   next := doubler (Nat.succ n) (acc + acc)
/// ```
///
/// State is `[n, acc]`; the observation is `acc`; the step is
/// `[n+1, acc+acc]`. Written out here rather than produced by a lowering
/// because no lowering exists yet — B5 is what will have to reproduce exactly
/// this, and having the expected form pinned first is the point.
fn doubler(n0: u64, acc0: u64) -> Corec {
    Corec {
        init: vec![Op::Lit(n0), Op::Lit(acc0)],
        observe: Op::State(1),
        step: vec![
            Op::Succ(Box::new(Op::State(0))),
            Op::Add(Box::new(Op::State(1)), Box::new(Op::State(1))),
        ],
    }
}

/// The interpreter reproduces the values the KERNEL proved about the source.
///
/// `tests/fixtures/codata/is2_indexed_stream.lean` proves, by `rfl`:
///
/// ```lean
/// theorem nth_d0 : IS2.nth 0 0 (doubler 0 1) = 1 := rfl
/// theorem nth_d1 : IS2.nth 1 0 (doubler 0 1) = 2 := rfl
/// theorem nth_d2 : IS2.nth 2 0 (doubler 0 1) = 4 := rfl
/// theorem nth_d3 : IS2.nth 3 0 (doubler 0 1) = 8 := rfl
/// ```
///
/// If the two sides ever disagree, either the extraction form is wrong or the
/// reference semantics is — and that disagreement is exactly what the eventual
/// soundness statement is meant to rule out for ALL depths rather than these.
#[test]
fn doubler_matches_the_kernel_proved_values() {
    let c = doubler(0, 1);
    for (k, want) in [(0u64, 1u64), (1, 2), (2, 4), (3, 8)] {
        assert_eq!(
            eval_nth(&c, k, &[]).expect("no black hole"),
            want,
            "depth {k}: interpreter disagrees with the kernel-proved value"
        );
    }
}

/// Beyond the proved depths the doubling continues, as `2^k`.
#[test]
fn doubler_continues_past_the_proved_depths() {
    let c = doubler(0, 1);
    for k in 0..16u64 {
        assert_eq!(eval_nth(&c, k, &[]).expect("no black hole"), 1u64 << k);
    }
}

/// The index really moves: starting at `n₀` and observing the state slot the
/// index lives in tracks `n₀ + k`.
///
/// The index is what makes this an INDEXED stream rather than a plain one, so
/// it is pinned independently of the observation.
#[test]
fn the_index_advances_with_depth() {
    let c = Corec {
        init: vec![Op::Lit(7), Op::Lit(0)],
        observe: Op::State(0), // observe the index itself
        step: vec![
            Op::Succ(Box::new(Op::State(0))),
            Op::Add(Box::new(Op::State(1)), Box::new(Op::State(1))),
        ],
    };
    for k in 0..8u64 {
        assert_eq!(eval_nth(&c, k, &[]).expect("no black hole"), 7 + k);
    }
}

/// A thunk runs its initializer at most once, however often it is forced.
///
/// Memoization is not an optimization here: the observational-equivalence
/// argument for call-by-need assumes initialization has no observable effects
/// and happens once.
#[test]
fn forcing_is_memoized() {
    let counter = Rc::new(std::cell::Cell::new(0u32));
    let c = Rc::clone(&counter);
    let t = Thunk::new(move || {
        c.set(c.get() + 1);
        42u64
    });
    assert!(!t.is_forced());
    for _ in 0..5 {
        assert_eq!(*t.force().expect("no black hole"), 42);
    }
    assert!(t.is_forced());
    assert_eq!(counter.get(), 1, "the initializer must run exactly once");
}

/// Re-entrant forcing is reported as a black hole rather than diverging.
///
/// The soundness argument requires that reachable black holes be excluded, so
/// the machine has to be able to SAY it hit one. A thunk that silently hung
/// would make that unstatable.
#[test]
fn reentrant_forcing_is_a_black_hole() {
    use std::cell::RefCell;
    use std::rc::{Rc, Weak};

    let slot: Rc<RefCell<Weak<Thunk<u64>>>> = Rc::new(RefCell::new(Weak::new()));
    let inner = Rc::clone(&slot);
    let t: Rc<Thunk<u64>> = Rc::new(Thunk::new(move || {
        // Force ourselves from inside our own initializer.
        let me = inner.borrow().upgrade().expect("self reference");
        match me.force() {
            Err(ForceError::BlackHole) => 1,
            Err(ForceError::Overflow) | Ok(_) => 0,
        }
    }));
    *slot.borrow_mut() = Rc::downgrade(&t);

    assert_eq!(
        *t.force().expect("outer force succeeds"),
        1,
        "the re-entrant inner force must report a black hole"
    );
}

/// Laziness is real: a tail is not computed until it is forced.
///
/// If the tail were computed eagerly this would be an unfolding wearing lazy
/// clothes, and the `Delay`/`Force` structure would be decorative.
#[test]
fn tails_are_not_computed_until_forced() {
    let c = doubler(0, 1);
    let init: Vec<u64> = c
        .init
        .iter()
        .map(|op| op.eval(&[], &[]).expect("no overflow"))
        .collect();
    let layer = force_layer(&c, init, vec![]);
    assert_eq!(layer.head, Some(1));
    assert!(
        !layer.tail.is_forced(),
        "the tail must still be suspended after the head is observed"
    );
    let next = layer.tail.force().expect("no black hole");
    assert!(layer.tail.is_forced());
    assert_eq!(next.head, Some(2));
}

/// An out-of-range state slot reads 0 rather than panicking.
///
/// A malformed IR must not be able to crash the interpreter — the differential
/// harness has to get a WRONG ANSWER it can report, not a process abort.
#[test]
fn malformed_state_access_is_total() {
    let c = Corec {
        init: vec![Op::Lit(1)],
        observe: Op::State(9),
        step: vec![Op::State(0)],
    };
    assert_eq!(eval_nth(&c, 0, &[]).expect("no black hole"), 0);
}
