// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean-owned public term handle for the curated Ay backend surface.

use ay::Term;
use std::fmt;

/// clean-owned handle to a solver term on the curated `AyBackend` surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AyTerm(Term);

impl AyTerm {
    pub(crate) fn from_inner(term: Term) -> Self {
        Self(term)
    }

    pub(crate) fn into_inner(self) -> Term {
        self.0
    }
}

impl fmt::Display for AyTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0.to_raw())
    }
}
