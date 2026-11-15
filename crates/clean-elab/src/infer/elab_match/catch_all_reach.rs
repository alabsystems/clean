// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The alternatives behind a catch-all are redundant (trust-ir gap G62,
//! ledger (132)).
//!
//! Lean 4.8.0 refuses a `match` with an alternative no value selects
//! ("redundant alternative", `reportMatcherResultErrors` in
//! `src/Lean/Elab/Match.lean`). The single-column paths had no such check, so
//! `| x => true | _ => false` was accepted — and with it a pattern identifier
//! Clean misreads as a binder (G29's `| two => …`) silently swallowed every
//! later arm. This is the fragment of Lean's check that needs no coverage
//! analysis: once an alternative's pattern matches EVERY value, each later
//! alternative is redundant. (Measured against pinned Lean 4.8.0 on
//! 2026-10-16: `| x => … | _ => …`, `if let _ := 42 then 1 else 0` and
//! `| _ => 0 | Bool.true => 1` are "redundant alternative"; a top-level
//! inaccessible `| .(0) => … | _ => …` is "dependent elimination failed"
//! instead, so it is left to its own refusal.)

use super::*;

impl<'a> ElabCtx<'a> {
    /// The first alternative (0-based) that an earlier catch-all alternative
    /// makes redundant. `patterns` are the alternatives' NORMALIZED patterns
    /// (`normalize_match_pattern_names`: every `Var` is a genuine binder).
    pub(in crate::infer) fn first_alternative_after_catch_all<'p>(
        &self,
        patterns: impl IntoIterator<Item = &'p SurfacePattern>,
    ) -> Option<usize> {
        let mut seen_catch_all = false;
        for (index, pattern) in patterns.into_iter().enumerate() {
            if seen_catch_all {
                return Some(index);
            }
            seen_catch_all = self.pattern_matches_every_value(pattern);
        }
        None
    }

    /// Whether `pattern` matches every value of its type: a binder, `_`, an
    /// alias or alternative of such, or a constructor of
    /// a one-constructor, index-free inductive (a tuple, a structure) whose
    /// fields are all such.
    pub(in crate::infer) fn pattern_matches_every_value(&self, pattern: &SurfacePattern) -> bool {
        match pattern {
            SurfacePattern::Var(_) | SurfacePattern::Wildcard | SurfacePattern::Ellipsis => true,
            // An inaccessible term matches every value its type admits, but
            // Lean reports a top-level one by dependent elimination, not as
            // a redundant alternative; it keeps its own refusal.
            SurfacePattern::Inaccessible(_) => false,
            SurfacePattern::As(_, inner) => self.pattern_matches_every_value(inner),
            SurfacePattern::Or(a, b) => {
                self.pattern_matches_every_value(a) || self.pattern_matches_every_value(b)
            }
            SurfacePattern::Ctor(name, subs) => {
                self.is_sole_constructor(name)
                    && subs.iter().all(|sub| self.pattern_matches_every_value(sub))
            }
            SurfacePattern::Lit(_)
            | SurfacePattern::NumeralAdd(..)
            | SurfacePattern::QPattern(_)
            | SurfacePattern::StructInst { .. } => false,
        }
    }

    /// `name` is the only constructor of an inductive with no indices.
    fn is_sole_constructor(&self, name: &SurfaceName) -> bool {
        let Some(ctor) = self.env.get_constructor(name.name()) else {
            return false;
        };
        self.env
            .get_inductive(&ctor.inductive_name)
            .is_some_and(|ind| ind.constructor_names.len() == 1 && ind.num_indices == 0)
    }
}
