// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ExtractionIR — the lazy-lowering waist (rank 7, brick B4).
//!
//! The rank-7 pipeline is
//!
//! ```text
//! codata source → canonical M.corec → ExtractionIR Corec/Delay/Force → lazy target
//! ```
//!
//! and this is the third stage. It is ladder rung 5's waist, which was skipped
//! when rung 6 (the codata surface) landed ahead of it, so rank 7 is being
//! built with its own prerequisite missing. This module supplies the minimum
//! that makes the width-1 chain expressible.
//!
//! # Why a separate IR rather than widening L5CNF/L5IR
//!
//! Deliberate. Laziness is not a new node in an eager IR: the existing L5IR is
//! reference-counted, and a memoizing cell under RC is a use-after-free class
//! of bug rather than a compile error. Widening `IRExpr` would also touch every
//! consumer of a type matched in dozens of files, to express something only the
//! codata lane can produce. This IR is small, standalone, and fed directly from
//! validated recognition ([`super::to_lcnf::codata_recognize`]).
//!
//! # What the interpreter is for
//!
//! [`eval_nth`] is a REFERENCE SEMANTICS: a small operational reading of the IR
//! that is deliberately independent of how the source computes. Its purpose is
//! to be the target side of the observational claim
//!
//! ```text
//! for every finite depth n, observing the source n layers
//!   = decoding n forced target layers
//! ```
//!
//! Independence is the whole point, and the trap to avoid. If the "target
//! semantics" were written by transcribing the source's own recursion, the
//! resulting theorem would be true, nearly `rfl`, and would say nothing about
//! any emitted program. This interpreter therefore models the LAZY machine —
//! suspensions, forcing, memoization, black holes — and never consults the
//! source at all.
//!
//! # What this brick does NOT establish
//!
//! Nothing here is proved. This is executable Rust, so agreement between it and
//! the kernel is a DIFFERENTIAL CHECK over the depths actually run, not a proof
//! over all depths. The proof obligation is B7 and it does not exist yet. Nor
//! does any emitter consume this IR yet: B5 is the safe-lazy Rust backend.

use std::cell::RefCell;
use std::rc::Rc;

use serde::{Deserialize, Serialize};

/// A pure, first-order expression over a corecursive value's state.
///
/// Deliberately tiny: the width-1 chain observes `Nat` and steps a `Nat` state,
/// so machine words and the operations the fixture actually uses are enough.
/// Widening this is a width problem, to be driven by a second real chain rather
/// than by speculation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op {
    /// A literal machine word.
    Lit(u64),
    /// Slot `i` of the current state tuple.
    State(usize),
    /// Parameter `i` of the enclosing corecursive definition.
    ///
    /// A `codef` with parameters is a FAMILY of streams, so the initial state
    /// is symbolic in those parameters rather than a closed value. Keeping them
    /// a distinct namespace from state slots is what lets `init` mention them
    /// while `observe`/`step` mention state.
    Param(usize),
    /// `a + b`, wrapping — the target is a machine, not the naturals.
    Add(Box<Op>, Box<Op>),
    /// `a + 1`, wrapping.
    Succ(Box<Op>),
}

impl Op {
    /// Evaluate against a state tuple and the enclosing definition's
    /// parameters.
    ///
    /// Returns `None` on ARITHMETIC OVERFLOW. That is the whole point of the
    /// signature: the source's `Nat` is unbounded and the target's word is not,
    /// so beyond 2^64 there is no target value that represents the source's.
    /// Wrapping would make the interpreter and the emitted binary agree on the
    /// same WRONG number — a differential that silently passes is worse than
    /// one that fails, because it converts a real divergence into evidence of
    /// correctness.
    ///
    /// Out-of-range slots remain total (they read 0): a malformed IR must yield
    /// a reportable answer, not a crash. Overflow is different — it is a real
    /// source/target divergence and must be visible.
    #[must_use]
    pub fn eval(&self, state: &[u64], params: &[u64]) -> Option<u64> {
        match self {
            Op::Lit(n) => Some(*n),
            Op::State(i) => Some(state.get(*i).copied().unwrap_or(0)),
            Op::Param(i) => Some(params.get(*i).copied().unwrap_or(0)),
            Op::Add(a, b) => a.eval(state, params)?.checked_add(b.eval(state, params)?),
            Op::Succ(a) => a.eval(state, params)?.checked_add(1),
        }
    }
}

/// A corecursive stream in extraction form.
///
/// This is the `Corec` node: an initial state, a pure observation of the state,
/// and a step producing the next state. `Delay`/`Force` do not appear as
/// separate constructors because in this shape they are structural — the tail
/// IS the delayed re-application of `step`, and [`Thunk`] is where forcing
/// actually happens. Naming them as data would suggest the interpreter can
/// choose not to honor them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Corec {
    /// The initial state tuple.
    pub init: Vec<Op>,
    /// The observation at the current layer: a pure function of state.
    pub observe: Op,
    /// The next state: one expression per slot, over the current state.
    pub step: Vec<Op>,
}

/// A memoizing suspension with black-hole detection.
///
/// Mirrors the design's safe single-threaded thunk: force returns the cached
/// value if present, otherwise runs the initializer exactly once and caches it.
/// Re-entrant forcing is a BLACK HOLE and is reported rather than diverging —
/// the soundness argument for call-by-need requires that reachable black holes
/// be excluded, so the machine has to be able to say when it hit one.
pub struct Thunk<T> {
    state: RefCell<ThunkState<T>>,
}

enum ThunkState<T> {
    /// Not yet forced.
    Pending(Box<dyn FnOnce() -> T>),
    /// Currently being forced — re-entry here is a black hole.
    Forcing,
    /// Forced and cached.
    Done(Rc<T>),
}

/// Why evaluation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForceError {
    /// A thunk was re-entered while it was already being forced.
    BlackHole,
    /// Arithmetic exceeded the target's machine word.
    ///
    /// The source's `Nat` is unbounded; the target's is 64 bits. Past that
    /// point the extraction has no faithful target value, so it refuses rather
    /// than wrapping. See [`Op::eval`].
    Overflow,
}

impl<T> Thunk<T> {
    /// A suspension over `init`, which runs at most once.
    pub fn new(init: impl FnOnce() -> T + 'static) -> Self {
        Thunk {
            state: RefCell::new(ThunkState::Pending(Box::new(init))),
        }
    }

    /// An already-forced suspension.
    pub fn ready(value: T) -> Self {
        Thunk {
            state: RefCell::new(ThunkState::Done(Rc::new(value))),
        }
    }

    /// Force to a value, memoizing.
    ///
    /// Returns [`ForceError::BlackHole`] if this thunk is already being forced
    /// further up the stack.
    pub fn force(&self) -> Result<Rc<T>, ForceError> {
        // Take the initializer out under a short borrow, so the closure below
        // can itself touch other thunks without holding this one's RefCell.
        let init = {
            let mut st = self.state.borrow_mut();
            match &*st {
                ThunkState::Done(v) => return Ok(Rc::clone(v)),
                ThunkState::Forcing => return Err(ForceError::BlackHole),
                ThunkState::Pending(_) => {
                    let ThunkState::Pending(f) = std::mem::replace(&mut *st, ThunkState::Forcing)
                    else {
                        unreachable!("state was just observed to be Pending")
                    };
                    f
                }
            }
        };
        let value = Rc::new(init());
        *self.state.borrow_mut() = ThunkState::Done(Rc::clone(&value));
        Ok(value)
    }

    /// Has this thunk been forced?
    #[must_use]
    pub fn is_forced(&self) -> bool {
        matches!(&*self.state.borrow(), ThunkState::Done(_))
    }
}

/// One forced layer of a stream: the observation, and the suspended tail.
pub struct Layer {
    /// The value observed at this layer, or `None` if computing it overflowed.
    pub head: Option<u64>,
    /// The rest of the stream, not yet computed.
    pub tail: Thunk<Layer>,
}

/// Force a [`Corec`] into its first layer.
///
/// The tail is a genuine suspension: stepping the state happens only when the
/// tail is forced, which is what makes this call-by-need rather than an eager
/// unfolding wearing lazy clothes.
#[must_use]
pub(crate) fn force_layer(c: &Corec, state: Vec<u64>, params: Vec<u64>) -> Layer {
    let head = c.observe.eval(&state, &params);
    let corec = c.clone();
    Layer {
        head,
        tail: Thunk::new(move || {
            // An overflowing step has no faithful next state; the rest of the
            // stream is unrepresentable from here, so every later layer reports
            // overflow rather than continuing from a wrapped value.
            let next: Option<Vec<u64>> = corec
                .step
                .iter()
                .map(|op| op.eval(&state, &params))
                .collect();
            match next {
                Some(next) => force_layer(&corec, next, params),
                None => overflow_layer(),
            }
        }),
    }
}

/// A layer whose value is unrepresentable, and whose every successor is too.
///
/// Once a step overflows there is no faithful next state, so the stream cannot
/// be continued from a wrapped value — every later depth reports overflow.
fn overflow_layer() -> Layer {
    Layer {
        head: None,
        tail: Thunk::new(overflow_layer),
    }
}

/// The finite observation: the value at depth `k`.
///
/// This is the target side of the observational claim — the decode of `k`
/// forced layers. It is the counterpart of the source's `IS2.nth`.
pub fn eval_nth(c: &Corec, k: u64, params: &[u64]) -> Result<u64, ForceError> {
    let init: Option<Vec<u64>> = c.init.iter().map(|op| op.eval(&[], params)).collect();
    let init = init.ok_or(ForceError::Overflow)?;
    let mut layer = Rc::new(force_layer(c, init, params.to_vec()));
    for _ in 0..k {
        layer = layer.tail.force()?;
    }
    layer.head.ok_or(ForceError::Overflow)
}

pub mod emit_rust;
pub mod lower;

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
