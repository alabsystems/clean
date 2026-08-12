// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional-axiom handling: `def_axiom_body`, `set_instance_def_body`, the
//! faithful `@Eq α lhs rhs` arm, the statement-shape elimination / classical proof
//! arms and the in-context recovery helpers.
//!
//! Part of the [`super`] Pure proof-term → clean kernel translator; split
//! out of the original single-file module purely for readability — the code is
//! moved verbatim, the behaviour is byte-identical.

use super::*;

mod classical;
mod conj_bundle;
mod elim;
mod eqshape;
mod hilbert;
mod if_the;
mod pointfree;
mod proofs;
mod reprove_elim;
mod shape;
mod wo_rel;

pub(crate) use classical::*;
pub(crate) use conj_bundle::*;
pub(crate) use elim::*;
pub(crate) use eqshape::*;
pub(crate) use hilbert::*;
#[cfg(test)]
pub(crate) use pointfree::*;
pub(crate) use proofs::*;
pub(crate) use reprove_elim::*;
pub(crate) use shape::*;
pub(crate) use wo_rel::*;
