// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe [`Level`]s — the Lean 4 lattice, **canonicalized at construction**.
//!
//! `Level = Zero | Succ | Max | IMax | Param(u32)`. Unlike the legacy kernel,
//! `Param` is a **positional index into the declaration's level telescope**
//! (design §2, §4.2), never a [`crate::Name`]: the caller cannot smuggle a
//! free-form universe name in.
//!
//! **Canonical-by-construction.** Every smart constructor returns a level in
//! the canonical normal form (offset-stripped, `Max` operands flattened /
//! sorted / deduped / subsumed, `IMax(_, Zero) = Zero` collapsed, `IMax`
//! reducing to `Max` when the right operand is provably non-zero). Therefore
//! **`==` on canonical levels is exactly definitional equality** — no separate
//! `normalize` pass is needed at use sites. This mirrors Lean's
//! `level.cpp` normalization, restricted to the positional-`Param` lattice.

use std::sync::Arc;

mod geq;
mod limit;
mod normalize;

use geq::{is_geq_core, Geq};
pub(crate) use limit::LevelTooDeep;
use limit::{total, Bounded, Limit, Unbounded};
pub use limit::{MAX_LEVEL_GEQ_WORK, MAX_LEVEL_SIZE};
use normalize::*;

/// Errors constructing a level (M0 surface is small; positional params can't be
/// out of range at construction — that is a *validation* concern checked in
/// [`crate::validate`] against the declaration arity).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum LevelError {
    /// A level-param index exceeded the declared number of params (raised by the
    /// validation chokepoint, not by construction).
    #[error("level param index {index} >= declared arity {arity}")]
    ParamOutOfRange {
        /// The offending positional index.
        index: u32,
        /// The declaration's level-param count.
        arity: u32,
    },
}

/// A universe level in canonical form.
///
/// The inner representation is private; the only way to build one is via the
/// smart constructors, all of which canonicalize. Two canonical levels are
/// definitionally equal iff they are structurally `==`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Level {
    repr: Repr,
    /// `Succ`, `Max` and `IMax` nodes on the longest path from the root (`Zero`
    /// and a `Param` are 0), computed in O(1) by [`Level::mk`], the only
    /// constructor. A level counts toward the depth of the term it sits in
    /// (R166), so the bounds `validate` and `whnf_core` hold terms to hold the
    /// natively recursive level operations too. A function of `repr`, so the
    /// derived equality and hash mean what they meant without it.
    depth: u32,
    /// Nodes in the level's tree, a shared subterm counted at each occurrence,
    /// saturating: the work a walk over it does (R166). Also a function of
    /// `repr`.
    size: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Repr {
    Zero,
    Succ(Arc<Level>),
    Max(Arc<Level>, Arc<Level>),
    IMax(Arc<Level>, Arc<Level>),
    Param(u32),
}

impl Level {
    /// The one place a `Level` value is made: caches its depth and size
    /// (R166).
    fn mk(repr: Repr) -> Self {
        let (depth, size) = match &repr {
            Repr::Zero | Repr::Param(_) => (0, 1),
            Repr::Succ(l) => (l.depth.saturating_add(1), l.size.saturating_add(1)),
            Repr::Max(a, b) | Repr::IMax(a, b) => (
                a.depth.max(b.depth).saturating_add(1),
                a.size.saturating_add(b.size).saturating_add(1),
            ),
        };
        Level { repr, depth, size }
    }

    /// `Succ`, `Max` and `IMax` nodes on the longest path from the root: `0`
    /// for `Zero` and a `Param` (R166).
    #[must_use]
    pub(crate) fn depth(&self) -> u32 {
        self.depth
    }

    // --- smart constructors (all canonicalizing) ---

    /// The zero level (`Prop`'s level).
    #[must_use]
    pub fn zero() -> Self {
        Level::mk(Repr::Zero)
    }

    /// A positional universe parameter (index into the declaration's telescope).
    #[must_use]
    pub fn param(index: u32) -> Self {
        Level::mk(Repr::Param(index))
    }

    /// `succ(l)`, canonicalized. `Succ` distributes over `Max`
    /// (`succ(max(a,b)) = max(succ a, succ b)`), so a raw `Succ(Max(..))` is not
    /// canonical; we normalize to keep the by-construction invariant. `succ` of
    /// a non-`Max` base is already canonical, so this is cheap in the common case.
    #[must_use]
    pub fn succ(l: Level) -> Self {
        total(Level::succ_in::<Unbounded>(l))
    }

    /// [`Level::succ`], refused past the depth bound (R166).
    ///
    /// # Errors
    /// [`LevelTooDeep`] when a level it builds is deeper than
    /// [`crate::MAX_VALIDATE_DEPTH`] or has more nodes than [`MAX_LEVEL_SIZE`].
    pub(crate) fn try_succ(l: Level) -> Result<Self, LevelTooDeep> {
        Level::succ_in::<Bounded>(l)
    }

    fn succ_in<L: Limit>(l: Level) -> Result<Self, L::Error> {
        let distributes = matches!(l.repr, Repr::Max(_, _) | Repr::IMax(_, _));
        let raw = Level::mk(Repr::Succ(Arc::new(l)));
        if distributes {
            raw.normalize_in::<L>()
        } else {
            L::admit(&raw)?;
            Ok(raw)
        }
    }

    /// Raw `succ` without canonicalization — internal use only, for the
    /// normalizer's own offset re-application where the base is already a
    /// canonical non-`Max` leaf.
    fn raw_succ(l: Level) -> Self {
        Level::mk(Repr::Succ(Arc::new(l)))
    }

    /// `n` as a level: `succ^n(zero)`.
    #[must_use]
    pub fn nat(n: u32) -> Self {
        let mut l = Level::zero();
        for _ in 0..n {
            l = Level::succ(l);
        }
        l
    }

    /// `max(l1, l2)`, canonicalized.
    #[must_use]
    pub fn max(l1: Level, l2: Level) -> Self {
        total(Level::max_in::<Unbounded>(l1, l2))
    }

    /// [`Level::max`], refused past the depth bound (R166).
    ///
    /// # Errors
    /// [`LevelTooDeep`] when a level it builds is deeper than
    /// [`crate::MAX_VALIDATE_DEPTH`] or has more nodes than [`MAX_LEVEL_SIZE`].
    pub(crate) fn try_max(l1: Level, l2: Level) -> Result<Self, LevelTooDeep> {
        Level::max_in::<Bounded>(l1, l2)
    }

    fn max_in<L: Limit>(l1: Level, l2: Level) -> Result<Self, L::Error> {
        // Build a raw Max then renormalize the whole thing so flatten/sort/dedup
        // run. Both inputs are already canonical, so this is a single pass.
        let raw = Level::mk(Repr::Max(Arc::new(l1), Arc::new(l2)));
        raw.normalize_in::<L>()
    }

    /// `imax(l1, l2)`, canonicalized.
    ///
    /// `imax(l, 0) = 0`; `imax(l, l')=max(l,l')` when `l'` is provably non-zero;
    /// `imax(0,l)=l`; `imax(1,l)=l`; `imax(l,l)=l`; else `IMax(l,l')`.
    #[must_use]
    pub fn imax(l1: Level, l2: Level) -> Self {
        total(Level::imax_in::<Unbounded>(l1, l2))
    }

    /// [`Level::imax`], refused past the depth bound (R166).
    ///
    /// # Errors
    /// [`LevelTooDeep`] when a level it builds is deeper than
    /// [`crate::MAX_VALIDATE_DEPTH`] or has more nodes than [`MAX_LEVEL_SIZE`].
    pub(crate) fn try_imax(l1: Level, l2: Level) -> Result<Self, LevelTooDeep> {
        Level::imax_in::<Bounded>(l1, l2)
    }

    fn imax_in<L: Limit>(l1: Level, l2: Level) -> Result<Self, L::Error> {
        let raw = Level::mk(Repr::IMax(Arc::new(l1), Arc::new(l2)));
        raw.normalize_in::<L>()
    }

    // --- queries ---

    /// True iff *provably* zero (structural; canonical form makes this exact for
    /// closed levels).
    #[must_use]
    pub fn is_zero(&self) -> bool {
        match &self.repr {
            Repr::Zero => true,
            Repr::Succ(_) | Repr::Param(_) => false,
            Repr::Max(a, b) => a.is_zero() && b.is_zero(),
            Repr::IMax(_, b) => b.is_zero(),
        }
    }

    /// True iff the canonical form is a `max` of two or more levels (R177).
    #[must_use]
    pub(crate) fn is_max(&self) -> bool {
        matches!(self.repr, Repr::Max(_, _))
    }

    /// True iff *provably* non-zero.
    #[must_use]
    pub fn is_nonzero(&self) -> bool {
        match &self.repr {
            Repr::Zero | Repr::Param(_) => false,
            Repr::Succ(_) => true,
            Repr::Max(a, b) => a.is_nonzero() || b.is_nonzero(),
            Repr::IMax(_, b) => b.is_nonzero(),
        }
    }

    /// The maximum `Param` index appearing in this level, plus one (i.e. the
    /// minimal telescope arity that makes every param in-range), or `0` if no
    /// param appears. Used by [`crate::validate`] to check level-arity.
    #[must_use]
    pub fn max_param_plus_one(&self) -> u32 {
        match &self.repr {
            Repr::Zero => 0,
            Repr::Param(i) => i.saturating_add(1),
            Repr::Succ(l) => l.max_param_plus_one(),
            Repr::Max(a, b) | Repr::IMax(a, b) => {
                a.max_param_plus_one().max(b.max_param_plus_one())
            }
        }
    }

    /// Strip leading `Succ`s: returns `(base, offset)` with `base` not a `Succ`.
    fn get_offset(&self) -> (Level, u32) {
        let mut cur = self.clone();
        let mut off: u32 = 0;
        while let Repr::Succ(inner) = &cur.repr {
            // Index *count*, not a numeric value; saturating is the right
            // overflow behaviour and policy-clean (no value arithmetic).
            off = off.saturating_add(1);
            let next = Level::clone(inner);
            cur = next;
        }
        (cur, off)
    }

    /// Re-apply an offset: `succ^n(self)`, admitting each node it builds. Used
    /// by the normalizer on already-leaf bases (non-`Max`), so it uses
    /// `raw_succ` to avoid re-triggering normalization.
    fn add_offset_in<L: Limit>(&self, n: u32) -> Result<Level, L::Error> {
        let mut l = self.clone();
        L::admit(&l)?;
        for _ in 0..n {
            l = Level::raw_succ(l);
            L::admit(&l)?;
        }
        Ok(l)
    }

    /// True iff `succ^n(Zero)` (a literal universe with no params).
    fn is_explicit(&self) -> bool {
        matches!(self.get_offset().0.repr, Repr::Zero)
    }

    // --- canonicalization (idempotent normal form) ---

    /// Produce the canonical form. Public smart constructors call this so that
    /// every `Level` a caller can hold is already canonical; exposed for tests.
    #[must_use]
    pub fn normalize(&self) -> Level {
        total(self.normalize_in::<Unbounded>())
    }

    /// [`Level::normalize`] under a limit: every node it builds is admitted by
    /// `L` (R166). Each return builds its result and admits its depth; the
    /// `Max` chain, the one construction that can be far deeper than the
    /// input, admits each node as it builds it.
    fn normalize_in<L: Limit>(&self) -> Result<Level, L::Error> {
        // Canonicalising walks the input as a tree, so its size bounds the walk.
        L::admit_walk(self)?;
        // Strip the `Succ` spine (as `get_offset` does) and dispatch on the base
        // in one match, so the base is never re-inspected for a `Succ` it
        // cannot have.
        let mut base = self;
        let mut off: u32 = 0;
        loop {
            match &base.repr {
                Repr::Succ(inner) => {
                    // An index count, saturating like `get_offset`.
                    off = off.saturating_add(1);
                    base = inner.as_ref();
                }
                Repr::Zero | Repr::Param(_) => return base.add_offset_in::<L>(off),
                Repr::IMax(l1, l2) => {
                    let n1 = l1.normalize_in::<L>()?;
                    let n2 = l2.normalize_in::<L>()?;
                    let reduced = reduce_imax::<L>(n1, n2)?;
                    let shifted = reduced.add_offset_in::<L>(off)?;
                    return if matches!(reduced.repr, Repr::Max(_, _)) {
                        // Distribute the outer offset into the Max and renormalize so
                        // succ(max(a,b)) = max(succ a, succ b). Keeps idempotence.
                        shifted.normalize_in::<L>()
                    } else {
                        Ok(shifted)
                    };
                }
                Repr::Max(_, _) => return normalize_max::<L>(base, off),
            }
        }
    }

    // --- ordering / def-eq ---

    /// `l1 >= l2` on canonical levels, by the rules of Lean's
    /// `level.cpp:is_geq_core` in their order (R174). Like Lean's, it is sound
    /// and incomplete for the lattice order: a `true` holds at every
    /// assignment, and some orders that hold, such as
    /// `succ (imax u v) >= imax u v`, answer `false`. The operands are ck0's
    /// canonical forms, not Lean's normal forms, which order a `max`'s
    /// operands differently. Where that changes an answer is a level written
    /// in one of three forms, where it could differ from Lean's kernel either
    /// way, and validation refuses those (R177, `tests/level_as_written.rs`).
    /// An answer can also differ on a level that instantiating a parameter
    /// builds, which validation never sees: Lean's kernel refuses
    /// `succ (max u v) >= succ (imax w (max v u))` at `w := max u v`, and ck0
    /// answers `true` (R177's residue, pinned there).
    #[must_use]
    pub fn is_geq(l1: &Level, l2: &Level) -> bool {
        total(is_geq_core::<Unbounded>(
            &l1.normalize(),
            &l2.normalize(),
            &mut Geq::new(),
        ))
    }

    /// [`Level::is_geq`] for the checker (R172): the same comparison, with
    /// its operands canonicalised and its work bounded.
    ///
    /// # Errors
    ///
    /// [`LevelTooDeep`] when canonicalising an operand passes the depth or
    /// size bound, or the comparison passes [`MAX_LEVEL_GEQ_WORK`]. That is
    /// a refusal, never an answer.
    pub(crate) fn try_is_geq(l1: &Level, l2: &Level) -> Result<bool, LevelTooDeep> {
        is_geq_core::<Bounded>(
            &l1.normalize_in::<Bounded>()?,
            &l2.normalize_in::<Bounded>()?,
            &mut Geq::new(),
        )
    }

    /// `l1 <= l2`.
    #[must_use]
    pub fn leq(l1: &Level, l2: &Level) -> bool {
        Level::is_geq(l2, l1)
    }

    /// Substitute positional `Param(i)` by `subst[i]` (universe instantiation),
    /// re-canonicalizing. A `Param` index out of range for `subst` is left
    /// unchanged — callers (δ-unfold, const-type instantiation) pass a `subst`
    /// of exactly `num_level_params` length, so in-range substitution is total;
    /// the clamp is defensive, never relied on for soundness.
    #[must_use]
    pub fn instantiate_params(&self, subst: &[Level]) -> Level {
        total(self.subst_raw(subst).normalize_in::<Unbounded>())
    }

    /// [`Level::instantiate_params`], refused past the depth bound (R166).
    /// The substitution itself follows `self`'s structure, so it builds a
    /// tree no deeper than `self` plus the deepest of `subst`; canonicalising
    /// it is where a chain can grow, and that is bounded.
    ///
    /// # Errors
    /// [`LevelTooDeep`] when a level it builds is deeper than
    /// [`crate::MAX_VALIDATE_DEPTH`] or has more nodes than [`MAX_LEVEL_SIZE`].
    pub(crate) fn try_instantiate_params(&self, subst: &[Level]) -> Result<Level, LevelTooDeep> {
        self.subst_raw(subst).normalize_in::<Bounded>()
    }

    fn subst_raw(&self, subst: &[Level]) -> Level {
        match &self.repr {
            Repr::Zero => Level::zero(),
            Repr::Param(i) => match usize::try_from(*i).ok().and_then(|i| subst.get(i)) {
                Some(l) => l.clone(),
                None => self.clone(),
            },
            Repr::Succ(l) => Level::mk(Repr::Succ(Arc::new(l.subst_raw(subst)))),
            Repr::Max(a, b) => Level::mk(Repr::Max(
                Arc::new(a.subst_raw(subst)),
                Arc::new(b.subst_raw(subst)),
            )),
            Repr::IMax(a, b) => Level::mk(Repr::IMax(
                Arc::new(a.subst_raw(subst)),
                Arc::new(b.subst_raw(subst)),
            )),
        }
    }
}

impl std::fmt::Display for Level {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.repr {
            Repr::Zero => write!(f, "0"),
            Repr::Param(i) => write!(f, "u{i}"),
            Repr::Succ(_) => {
                let (base, off) = self.get_offset();
                if matches!(base.repr, Repr::Zero) {
                    write!(f, "{off}")
                } else {
                    write!(f, "{base}+{off}")
                }
            }
            Repr::Max(a, b) => write!(f, "max({a}, {b})"),
            Repr::IMax(a, b) => write!(f, "imax({a}, {b})"),
        }
    }
}

#[cfg(test)]
mod tests;
