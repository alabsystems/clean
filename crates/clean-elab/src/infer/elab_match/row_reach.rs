// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which alternatives of a `match` a surface decision tree selects, and
//! Lean 4.8.0's refusal of one it never selects.
//!
//! Lean compiles a match into a decision tree and refuses the match when some
//! alternative is selected at no leaf: `reportMatcherResultErrors`
//! (`src/Lean/Elab/Match.lean`) logs "redundant alternative" for every index
//! in `MatcherResult.unusedAltIdxs`. The two surface decision-tree builders
//! here — `compile_pattern_matrix` (equation-form definitions,
//! `infer/elab_decl_value.rs`) and `build_column_split_surface` (constructor
//! field splits of a `match`, and the recursive joint-cover rescue,
//! `infer/elab_match/ctor_order.rs`) — keep the FIRST row that reaches a leaf
//! and drop the rest. Without a record of which rows were kept, an
//! alternative no value reaches was accepted and its body silently never run:
//! `| [] => 0 | none :: r => … | some b :: r => … | none :: r => 99 + …`
//! elaborated, where pinned Lean 4.8.0 reports "redundant alternative".
//!
//! Both builders split a column exactly: by constructor name, with every
//! binder row in every specialization, in source order, and with a default
//! arm only when some constructor of the column's type is not named (see
//! `signature.rs`). So a row no leaf selects is one whose every value an
//! earlier row matches first, and the refusal is Lean's. The converse does not
//! hold: a builder can keep a default arm Lean proves unreachable (a
//! constructor whose index cannot unify, a literal column), and a row that
//! only such an arm selects is not reported. Every reported row is redundant;
//! not every redundant row is reported (ledger class (89) has the paths that
//! report none).

use crate::ElabError;

/// The rows (alternatives, 0-based in source order) a decision tree selects
/// at some leaf, and whether every value of the scrutinee reaches some leaf.
pub(in crate::infer) struct RowReach {
    reached: Vec<bool>,
    exhaustive: bool,
}

impl RowReach {
    /// A record for a tree over `rows` alternatives, none selected yet.
    pub(in crate::infer) fn new(rows: usize) -> Self {
        Self {
            reached: vec![false; rows],
            exhaustive: true,
        }
    }

    /// A leaf selects alternative `origin`.
    pub(in crate::infer) fn reach(&mut self, origin: usize) {
        if let Some(slot) = self.reached.get_mut(origin) {
            *slot = true;
        }
    }

    /// A column was split with neither an arm for every constructor of its
    /// type nor a default arm: some value reaches no leaf.
    pub(in crate::infer) fn mark_partial(&mut self) {
        self.exhaustive = false;
    }

    /// The first alternative no leaf selects.
    pub(in crate::infer) fn first_unreached(&self) -> Option<usize> {
        self.reached.iter().position(|reached| !reached)
    }

    /// Whether every value reaches a leaf (as far as the tree can tell: a
    /// constructor Lean would rule out by its index still counts as a value).
    pub(in crate::infer) fn is_exhaustive(&self) -> bool {
        self.exhaustive
    }
}

/// Lean's refusal of alternative `alt` (0-based, source order) of `context`.
pub(in crate::infer) fn redundant_alternative(context: &str, alt: usize) -> ElabError {
    ElabError::RedundantAlternative {
        detail: format!(
            "alternative {} of {context} is never selected: every value it matches is \
             matched by an earlier alternative",
            alt + 1
        ),
    }
}
