// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How far a level operation may build and walk (R166).

use std::convert::Infallible;

use super::Level;
use crate::validate::MAX_VALIDATE_DEPTH;

/// The most nodes a level the checker builds may have, a shared subterm
/// counted at each of its occurrences (R166): that is what canonicalising,
/// hashing and testing a level for equality walk, so it bounds each of them.
/// Ordering two levels (the universe check's `Level::try_is_geq`) can take
/// far more steps than either has nodes, and has its own bound, [`MAX_LEVEL_GEQ_WORK`]. A `Level`
/// shares its subterms, so a δ chain that substitutes a level twice per step,
/// `c(k+1).{u, p} := ck.{imax u (imax u p), p}`, doubles that walk at every
/// unfolding while fuel counts one step: on main 22 steps took 8.6 s, and 40
/// were killed at 6.3 GB. Real universe levels have a few dozen nodes.
pub const MAX_LEVEL_SIZE: u32 = 1 << 16;

/// The most work one level comparison may do (R172), each step charged one
/// plus both operands' sizes; the universe check's `Level::try_is_geq`
/// refuses past it. The comparison remembers
/// its answer for each pair of operands, so its steps are bounded by the
/// pairs of their subterms: in a debug build a sort that is the `max` of 80
/// parameters, against a field over 40 binders whose sorts form an `imax`
/// spine, is decided in 0.28 s, and the bound refuses 120 against 60 after
/// about 0.85 s. Real universe constraints take a few dozen steps.
pub const MAX_LEVEL_GEQ_WORK: u64 = 1 << 22;

/// A level the checker would build past [`MAX_VALIDATE_DEPTH`] or
/// [`MAX_LEVEL_SIZE`] (R166), or a level comparison past
/// [`MAX_LEVEL_GEQ_WORK`] (R172).
///
/// Canonicalising flattens a `Max` into a right-nested chain of its distinct
/// arguments, so a level built from a shallow one can be far deeper than its
/// input: a raw `Max` tree 21 deep over 2^20 parameters is a chain 2^20 deep,
/// and instantiating a constant's level parameters can multiply chain lengths.
/// Every level operation recurses natively over its input, so the checker's
/// paths ([`Level::try_succ`], [`Level::try_max`], [`Level::try_imax`],
/// [`Level::try_instantiate_params`]) refuse as soon as a node they build
/// passes the bound, before anything walks the level, and
/// [`Level::try_is_geq`] refuses a comparison past its work bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("a universe level, or a term it is instantiated into, past the depth bound {MAX_VALIDATE_DEPTH} or the level size bound {MAX_LEVEL_SIZE}, or a level comparison past the work bound {MAX_LEVEL_GEQ_WORK}")]
pub(crate) struct LevelTooDeep;

/// How far a level operation may build and walk. The public builders are
/// [`Unbounded`]; the checker's paths are [`Bounded`] at
/// [`MAX_VALIDATE_DEPTH`] and [`MAX_LEVEL_SIZE`].
pub(super) trait Limit {
    type Error;
    /// A node the operation builds.
    fn admit(level: &Level) -> Result<(), Self::Error>;
    /// An input the operation walks, which can be deeper than what it builds
    /// (an instantiation's raw result is), so only its size is held.
    fn admit_walk(level: &Level) -> Result<(), Self::Error>;
    /// `cost` more units of a comparison's work, `spent` so far (R172).
    fn admit_work(spent: &mut u64, cost: u64) -> Result<(), Self::Error>;
}

/// No bound: the public builders, whose callers build trusted levels.
pub(super) struct Unbounded;

impl Limit for Unbounded {
    type Error = Infallible;
    fn admit(_level: &Level) -> Result<(), Infallible> {
        Ok(())
    }
    fn admit_walk(_level: &Level) -> Result<(), Infallible> {
        Ok(())
    }
    fn admit_work(_spent: &mut u64, _cost: u64) -> Result<(), Infallible> {
        Ok(())
    }
}

/// The checker's bound: a level deeper than [`MAX_VALIDATE_DEPTH`] or larger
/// than [`MAX_LEVEL_SIZE`] is refused, and so is a comparison past
/// [`MAX_LEVEL_GEQ_WORK`].
pub(super) struct Bounded;

impl Limit for Bounded {
    type Error = LevelTooDeep;
    fn admit(level: &Level) -> Result<(), LevelTooDeep> {
        if level.depth > MAX_VALIDATE_DEPTH {
            return Err(LevelTooDeep);
        }
        Bounded::admit_walk(level)
    }
    fn admit_walk(level: &Level) -> Result<(), LevelTooDeep> {
        if level.size > MAX_LEVEL_SIZE {
            Err(LevelTooDeep)
        } else {
            Ok(())
        }
    }
    fn admit_work(spent: &mut u64, cost: u64) -> Result<(), LevelTooDeep> {
        *spent = spent.saturating_add(cost);
        if *spent > MAX_LEVEL_GEQ_WORK {
            Err(LevelTooDeep)
        } else {
            Ok(())
        }
    }
}

/// The value of an operation that cannot fail.
pub(super) fn total<T>(r: Result<T, Infallible>) -> T {
    match r {
        Ok(t) => t,
        Err(never) => match never {},
    }
}
