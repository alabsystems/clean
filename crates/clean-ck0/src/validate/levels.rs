// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validating a level: rebuilt through the canonicalising [`Level`]
//! constructors, with each `Param` in range, and refused where it is written
//! in a form Lean's kernel reads differently from ck0's canonical one (R177).
//!
//! ck0 keeps only a level's canonical form, whose equality is structural.
//! Lean's kernel keeps the form as written: its `normalize` (`level.cpp`)
//! rebuilds an `imax` through `mk_imax` and does not normalise the `max` that
//! can return, so under a `succ` it keeps `succ (max …)` where ck0 distributes
//! the `succ`; and it tests whether a sort is `Prop` on the level as written.
//! Three forms reach those differences, and each is refused here, in every
//! subterm, children first:
//!
//! * an `imax a b` whose `b` is never zero (ck0 makes it `max a b` and
//!   normalises it; Lean's `mk_max a b` stops);
//! * a level that is `0` at every assignment but is not written `0` (Lean's
//!   kernel reads it as a level that is not `Prop`'s, and keeps it so when a
//!   parameter is instantiated around it);
//! * any other `imax` that reduces to a `max` (`imax 0 (max u v)`,
//!   `imax 1 (max u v)`, `imax (max u v) (max v u)`): under a `succ`, written
//!   or the one Lean's kernel adds typing `Sort l` as `Sort (succ l)`, Lean
//!   keeps `succ (max u v)`, and ck0 distributes it.
//!
//! On levels free of the three, ck0's equality is Lean's kernel's on every
//! row of R150's table of equality verdicts, and ck0's equality, order and
//! `Prop` test are those of a port of Lean's level algebra on every random
//! pair measured; the port is checked against R150's table and against the
//! order verdicts Lean's kernel gave in `tests/fixtures/level_gap/`
//! (`tests/level_as_written.rs`). Instantiating a parameter can still build
//! such a form inside Lean's kernel, whose `instantiate` rebuilds a node
//! through `mk_max` / `mk_imax` on its operands as built, where ck0 has only
//! canonical forms: that residue is pinned in the same file and recorded in
//! R177.

use super::{ValidateError, MAX_VALIDATE_DEPTH};
use crate::level::{Level, LevelTooDeep};
use crate::rawexpr::RawLevel;

/// A level form, as written, that Lean's kernel reads differently from ck0's
/// canonical form (R177).
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum WrittenLevel {
    /// `imax a b` with `b` never zero.
    #[error("an `imax` whose right side is never zero")]
    IMaxOfNeverZero,
    /// A level that is `0` at every assignment, not written `0`.
    #[error("a level that is `0` only once canonicalised")]
    ZeroOnceCanonical,
    /// `imax a b` that reduces to a `max`, `b` not never zero.
    #[error("an `imax` that reduces to a `max`")]
    IMaxReducingToMax,
}

pub(super) fn validate_levels(raws: &[RawLevel], arity: u32) -> Result<Vec<Level>, ValidateError> {
    raws.iter().map(|r| validate_level(r, arity)).collect()
}

/// Rebuild a `RawLevel` through the canonicalizing [`Level`] constructors (WF #2)
/// and check every `Param` index is in range (WF #3 for levels). The bounded
/// constructors refuse a level whose canonical form passes the depth bound,
/// which a raw level within it can have, or the level size bound
/// ([`crate::level::MAX_LEVEL_SIZE`]); either is `MaxDepthExceeded` (R166).
/// A form Lean's kernel reads differently is `LevelAsWritten` (R177).
pub(super) fn validate_level(raw: &RawLevel, arity: u32) -> Result<Level, ValidateError> {
    let too_deep = |LevelTooDeep| ValidateError::MaxDepthExceeded {
        max: MAX_VALIDATE_DEPTH,
    };
    let written = |form| ValidateError::LevelAsWritten { form };
    let level = match raw {
        RawLevel::Zero => return Ok(Level::zero()),
        RawLevel::Param(i) => {
            if *i >= arity {
                return Err(ValidateError::LevelParam { index: *i, arity });
            }
            return Ok(Level::param(*i));
        }
        RawLevel::Succ(l) => Level::try_succ(validate_level(l, arity)?).map_err(too_deep)?,
        RawLevel::Max(a, b) => Level::try_max(validate_level(a, arity)?, validate_level(b, arity)?)
            .map_err(too_deep)?,
        RawLevel::IMax(a, b) => {
            let a = validate_level(a, arity)?;
            let b = validate_level(b, arity)?;
            if b.is_nonzero() {
                return Err(written(WrittenLevel::IMaxOfNeverZero));
            }
            let level = Level::try_imax(a, b).map_err(too_deep)?;
            if level.is_max() {
                return Err(written(WrittenLevel::IMaxReducingToMax));
            }
            level
        }
    };
    // Not written `0` (the arm above returned): a canonical `0` is a level
    // that is `0` at every assignment.
    if level.is_zero() {
        return Err(written(WrittenLevel::ZeroOnceCanonical));
    }
    Ok(level)
}
