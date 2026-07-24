// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types for the simplification tactic framework.
//!
//! Contains `SimpResult`, `SimpConfig`, and `SimpLemma` — the shared data
//! structures used by all simp submodules.

use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::tactic::discr_tree::{mk_path, query_path_is_too_generic, DiscrTree, IndexMode};
use crate::tactic::{Goal, ProofState};

/// Result of a simplification step.
///
/// Invariant: if `proof` is `Some(p)`, then `p : original = expr` where
/// `original` is the input expression. If `proof` is `None`, the change
/// is definitional (beta/eta/iota/zeta) and `Eq.refl original` is the proof.
///
/// Mirrors Lean 4's `Simp.Result` from `Lean/Meta/Tactic/Simp/Types.lean`.
#[derive(Debug, Clone)]
pub(crate) struct SimpResult {
    pub expr: Expr,
    pub proof: Option<Expr>,
}

impl SimpResult {
    /// Identity result (no change).
    ///
    /// ENSURES: `result.proof` is `None` (definitional equality, no proof needed).
    /// ENSURES: `result.expr` is the input `e` unchanged.
    pub(crate) fn refl(e: Expr) -> Self {
        SimpResult {
            expr: e,
            proof: None,
        }
    }
}

/// Configuration for the `simp` tactic.
#[derive(Debug, Clone)]
pub struct SimpConfig {
    /// Maximum number of simplification steps
    pub max_steps: usize,
    /// Whether to apply beta reduction
    pub beta: bool,
    /// Whether to apply eta reduction
    pub eta: bool,
    /// Whether to unfold definitions
    pub unfold: bool,
    /// Additional lemmas to use for simplification (by name)
    pub extra_lemmas: Vec<String>,
    /// Additional already-constructed simp lemmas (for example aesop rules or
    /// local proof-carry rewrite lemmas).
    pub aesop_simp_lemmas: Vec<SimpLemma>,
    /// Lemmas to exclude from simp set
    pub exclude: HashSet<String>,
    /// Only simplify to get the result, don't close the goal
    pub only_simplify: bool,
    /// `simp only` mode: when true, skip built-in and @[simp] registry lemmas.
    /// Only `extra_lemmas` and `aesop_simp_lemmas` are used for rewriting.
    /// Beta/eta reduction still applies (controlled by `beta`/`eta` flags).
    pub only: bool,
    /// Use local hypotheses as rewrite lemmas (`simp [*]` semantics).
    /// When true, all equality hypotheses in the current goal's local context
    /// are added as extra lemmas.
    pub use_hypotheses: bool,
    /// Whether to run built-in simprocs (simplification procedures).
    /// When true, simprocs like `Nat.reduceAdd` are invoked during simp's
    /// main loop to evaluate ground expressions (e.g., `2 + 3 → 5`).
    /// Default: true.
    pub use_simprocs: bool,
    /// Named constants to delta-unfold during simplification.
    ///
    /// Maps each unfoldable constant name to its stored definition body.
    /// Populated automatically by `collect_simp_lemmas` from `extra_lemmas`:
    /// any name that resolves to a `Declaration::Definition` is registered
    /// here rather than dropped as a non-equality lemma.
    ///
    /// When `simp_expr` encounters a `Const(name, _)` (or an `App` whose
    /// head chain bottoms out in `Const(name, _)`) with `name` present in
    /// this map, the constant is replaced with the stored body. This is a
    /// definitional change (proof: None), matching Lean 4's `simp [foo]`
    /// delta-unfolding semantics. Part of #3518.
    pub unfold_defs: HashMap<Name, Expr>,
}

impl SimpConfig {
    /// Create a default configuration
    ///
    /// ENSURES: `max_steps` is 1000, `beta` and `eta` are enabled,
    ///   `unfold` is disabled, lemma lists and exclude set are empty,
    ///   `only` is false (use full @[simp] set), `use_hypotheses` is false.
    pub fn new() -> Self {
        SimpConfig {
            max_steps: 1000,
            beta: true,
            eta: true,
            unfold: false,
            extra_lemmas: vec![],
            aesop_simp_lemmas: vec![],
            exclude: HashSet::new(),
            only_simplify: false,
            only: false,
            use_hypotheses: false,
            use_simprocs: true,
            unfold_defs: HashMap::new(),
        }
    }
}

impl Default for SimpConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// How a simp lemma should be inserted into the discrimination tree.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SimpIndexMode {
    #[default]
    Normal,
    NoIndexAtArgs,
    /// Never insert into the discrimination tree: the lemma is offered as a
    /// candidate at EVERY subterm (Lean's `[*]`-key star-fallback semantics).
    ///
    /// Required for builtin literal-operand arithmetic patterns
    /// (`Nat.add ?n 0`, `Nat.mul ?n 1`): the key path's `whnf` ι/δ-collapses
    /// such a pattern (`Nat.mul ?n 1` → its stuck `Nat.rec` body), minting a
    /// BOGUS-specific key that the goal's own key never matches, so the lemma
    /// would silently never fire (B102).
    Unindexed,
}

impl From<SimpIndexMode> for IndexMode {
    fn from(value: SimpIndexMode) -> Self {
        match value {
            SimpIndexMode::Normal => IndexMode::Normal,
            SimpIndexMode::NoIndexAtArgs => IndexMode::NoIndexAtArgs,
            // Unreachable by construction: `SimpLemmaSet::with_goal` never
            // inserts an `Unindexed` lemma into the tree, so its mode is never
            // converted. `Normal` is a harmless placeholder if it ever is.
            SimpIndexMode::Unindexed => IndexMode::Normal,
        }
    }
}

/// A simp lemma entry
#[derive(Debug, Clone)]
pub struct SimpLemma {
    /// Name of the lemma
    pub name: Name,
    /// The equality to apply (lhs = rhs)
    pub lhs: Expr,
    pub rhs: Expr,
    /// The type of the equality (the `α` in `@Eq α lhs rhs`)
    pub eq_type: Option<Expr>,
    /// Optional proof source for local or prebuilt rewrites.
    ///
    /// When absent, the proof is reconstructed from `name` plus instantiated
    /// binder arguments. When present, this expression is used directly as the
    /// equality proof witness for the rewrite.
    pub proof_expr: Option<Expr>,
    /// How the lemma should be indexed for candidate retrieval.
    pub index_mode: SimpIndexMode,
    /// Priority (higher = try first)
    pub priority: u32,
}

/// Ordered simp lemmas plus the optional index used for candidate prefiltering.
#[derive(Debug, Clone, Default)]
pub(crate) struct SimpLemmaSet {
    ordered: Vec<SimpLemma>,
    index: DiscrTree<usize>,
    /// Indices (into `ordered`) of lemmas NOT in the discrimination tree —
    /// either explicitly `SimpIndexMode::Unindexed` or too generic to key.
    /// These are offered as candidates at EVERY query (Lean's `[*]`-key
    /// star-fallback semantics): a star-keyed lemma is in every candidate
    /// set, not only when the specific index comes up empty (B102).
    unindexed: Vec<usize>,
}

impl SimpLemmaSet {
    pub(crate) fn with_goal(state: &ProofState, goal: &Goal, ordered: Vec<SimpLemma>) -> Self {
        let mut index = DiscrTree::default();
        let mut unindexed = Vec::new();

        for (index_value, lemma) in ordered.iter().enumerate() {
            if lemma.index_mode == SimpIndexMode::Unindexed
                || !index.insert_if_specific(
                    state,
                    goal,
                    &lemma.lhs,
                    lemma.index_mode.into(),
                    index_value,
                )
            {
                unindexed.push(index_value);
            }
        }

        SimpLemmaSet {
            ordered,
            index,
            unindexed,
        }
    }

    pub(crate) fn from_state(state: &ProofState, ordered: Vec<SimpLemma>) -> Self {
        if let Some(goal) = state.current_goal() {
            Self::with_goal(state, goal, ordered)
        } else {
            Self::without_index(ordered)
        }
    }

    pub(crate) fn without_index(ordered: Vec<SimpLemma>) -> Self {
        SimpLemmaSet {
            ordered,
            index: DiscrTree::default(),
            unindexed: Vec::new(),
        }
    }

    pub(crate) fn candidates<'a>(
        &'a self,
        state: &ProofState,
        goal: &Goal,
        expr: &Expr,
    ) -> Vec<&'a SimpLemma> {
        if self.ordered.is_empty() || self.index.is_empty() {
            return self.ordered.iter().collect();
        }

        let query_path = mk_path(state, goal, expr, IndexMode::Normal);
        if query_path_is_too_generic(&query_path) {
            return self.ordered.iter().collect();
        }

        let mut matched_indices: Vec<usize> = self
            .index
            .get_match_with_extra(state, goal, expr)
            .into_iter()
            .map(|matched| matched.value)
            .collect();

        if matched_indices.is_empty() {
            matched_indices = self.index.get_match_liberal(state, goal, expr);
        }

        if matched_indices.is_empty() {
            // Historical fallback: an empty tree match with any unindexed
            // lemma present falls back to the full scan (also re-offering
            // indexed lemmas whose keys failed to match).
            if !self.unindexed.is_empty() {
                return self.ordered.iter().collect();
            }
            return Vec::new();
        }

        matched_indices.sort_unstable();
        matched_indices.dedup();

        // Unindexed lemmas are star-keyed: candidates at EVERY query. Append
        // them unconditionally (not only when the tree comes up empty), so a
        // specific-but-wrong tree hit cannot shadow an always-applicable lemma
        // (B102: `a * 1` keys as its stuck `Nat.rec` WHNF, matching unrelated
        // Nat lemmas while `Nat.mul_one` was never offered). They go AFTER the
        // tree matches — a specifically-keyed lemma (`Test.wrap_id` at a
        // `Test.wrap _` node) must win over a star-keyed identity whose
        // ι-degenerate pattern (`Nat.add ?n 0` ⇒ bare `?n`) would otherwise
        // fire first and strip the node instead.
        let matched_set: HashSet<usize> = matched_indices.iter().copied().collect();
        let star_indices = self
            .unindexed
            .iter()
            .copied()
            .filter(|index| !matched_set.contains(index));

        // Preserve the original lemma priority order within each tier without
        // falling back to an O(total_lemmas) post-filter scan after the
        // discrimination-tree lookup.
        matched_indices
            .into_iter()
            .chain(star_indices)
            .map(|index| &self.ordered[index])
            .collect()
    }
}

impl Deref for SimpLemmaSet {
    type Target = [SimpLemma];

    fn deref(&self) -> &Self::Target {
        &self.ordered
    }
}

impl IntoIterator for SimpLemmaSet {
    type Item = SimpLemma;
    type IntoIter = std::vec::IntoIter<SimpLemma>;

    fn into_iter(self) -> Self::IntoIter {
        self.ordered.into_iter()
    }
}

impl<'a> IntoIterator for &'a SimpLemmaSet {
    type Item = &'a SimpLemma;
    type IntoIter = std::slice::Iter<'a, SimpLemma>;

    fn into_iter(self) -> Self::IntoIter {
        self.ordered.iter()
    }
}
