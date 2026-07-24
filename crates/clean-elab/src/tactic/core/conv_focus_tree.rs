// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! N-ary multi-focus `conv => congr` focus tree (#2477 / Phase 4).
//!
//! Replaces the single `(conv_nav, conv_focus_witness)` pair with a focus
//! TREE so that `conv => congr` on `f a b` can open one independently
//! rewritable sub-focus per argument (plus the head), recombined on exit into
//! one kernel-checked proof of the whole-application equality.
//!
//! SOUNDNESS: the tree only RECORDS per-focus equalities; the assembled
//! candidate proof is handed to `replace_target_eq`, which kernel-type-checks
//! it against `@Eq T old_target new_target` before any goal mutation. A wrong
//! motive / level / dependent assumption is therefore a safe kernel REJECT, not
//! a miscertification (INV-4).

use clean_kernel::Expr;

use crate::tactic::conv::ConvPosition;

/// One focus node in a congr'd application.
///
/// For `f a1 .. an`, the head focus tracks `f` and each arg focus tracks `ai`.
/// `before` is captured at tree-construction from the decomposed application
/// (the actual `f`/`ai`); `after` is mutated only by a rewrite ON THIS focus's
/// sub-goal (INV-3). `eq_proof = None` means the focus is untouched and the
/// recombination synthesizes `Eq.refl` (INV-5).
#[derive(Debug, Clone)]
pub(crate) struct ConvFocus {
    /// Path FROM this node's expr down to its hole (for `arg`/`enter` inside
    /// a congr'd focus). Empty for a freshly-opened leaf.
    pub(crate) sub_path: Vec<ConvPosition>,
    /// Sub-expr at the hole on entry (the actual `f` or `ai`).
    pub(crate) before: Expr,
    /// Current sub-expr after body edits (starts equal to `before`).
    pub(crate) after: Expr,
    /// `Some(h : before = after)` once rewritten; `None` => unchanged (refl).
    pub(crate) eq_proof: Option<Expr>,
    /// Populated by a nested `congr` ON this focus (recursion).
    pub(crate) children: Vec<ConvFocus>,
    /// Cached kernel type of `before` (for universe / refl synthesis).
    pub(crate) ty: Expr,
}

impl ConvFocus {
    /// Build a fresh untouched leaf focus on `expr` with cached type `ty`.
    pub(crate) fn leaf(expr: Expr, ty: Expr) -> Self {
        ConvFocus {
            sub_path: Vec::new(),
            before: expr.clone(),
            after: expr,
            eq_proof: None,
            children: Vec::new(),
            ty,
        }
    }
}

/// Conv navigation state for the N-ary multi-focus `conv => congr` form.
///
/// The proven single-focus `lhs`/`rhs`/`enter`/`arg` path keeps using the
/// `ProofState::conv_nav` tuple (`(original, path)`) unchanged; this enum is
/// dedicated to the focus TREE. It is modeled as an enum (rather than a struct)
/// so future navigation modes can be added as variants without disturbing the
/// reconstruction-boundary match sites.
#[derive(Debug, Clone)]
pub(crate) enum ConvNav {
    /// N-ary multi-focus: the original application plus one focus per
    /// head + argument (SOURCE order: `args[0]` is the first argument).
    Congr {
        original: Expr,
        head: ConvFocus,
        args: Vec<ConvFocus>,
    },
}

impl ConvFocus {
    /// Resolve a child slot of this node by component index: `0` = the focus
    /// itself is not addressed here; children are laid out as `[head, a1..an]`.
    fn child_mut(&mut self, comp: usize) -> Option<&mut ConvFocus> {
        self.children.get_mut(comp)
    }

    fn child(&self, comp: usize) -> Option<&ConvFocus> {
        self.children.get(comp)
    }
}

impl ConvNav {
    /// Resolve the focus at `path` (mutable). The first component selects from
    /// the top-level `[head, args..]`; subsequent components descend into the
    /// selected focus's `children` (`[head, args..]` layout). Returns `None` for
    /// an empty path or any out-of-range component.
    pub(crate) fn focus_at_path_mut(&mut self, path: &[usize]) -> Option<&mut ConvFocus> {
        let ConvNav::Congr { head, args, .. } = self;
        let (first, rest) = path.split_first()?;
        let mut node: &mut ConvFocus = if *first == 0 {
            head
        } else {
            args.get_mut(*first - 1)?
        };
        for comp in rest {
            node = node.child_mut(*comp)?;
        }
        Some(node)
    }

    /// Resolve the focus at `path` (shared). See [`Self::focus_at_path_mut`].
    pub(crate) fn focus_at_path(&self, path: &[usize]) -> Option<&ConvFocus> {
        let ConvNav::Congr { head, args, .. } = self;
        let (first, rest) = path.split_first()?;
        let mut node: &ConvFocus = if *first == 0 {
            head
        } else {
            args.get(*first - 1)?
        };
        for comp in rest {
            node = node.child(*comp)?;
        }
        Some(node)
    }

    /// Number of arguments at the node addressed by `parent_path` (the node
    /// whose children an `arg i` step would select among). For the top level
    /// (`parent_path` empty) this is the count of top-level `args`.
    pub(crate) fn arg_count_at(&self, parent_path: &[usize]) -> Option<usize> {
        let ConvNav::Congr { args, .. } = self;
        if parent_path.is_empty() {
            return Some(args.len());
        }
        let node = self.focus_at_path(parent_path)?;
        // children layout is [head, a1..an]; arg count = children.len() - 1.
        Some(node.children.len().saturating_sub(1))
    }
}
