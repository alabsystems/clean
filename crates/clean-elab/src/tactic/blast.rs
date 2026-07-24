// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Aggressive automation tactic (`blast`) that chains many existing tactics.
//!
//! `blast` tries immediate closers, search, decision procedures, simplification,
//! arithmetic, type class synthesis, and library search in bounded rounds.

use super::arith_linarith::linarith;
use super::arith_nlinarith::nlinarith;
use super::combinator::try_tactic_preserving_state;
use super::connective::contradiction;
use super::core::{ProofState, TacticError, TacticResult};
use super::library_search::library_search;
use super::omega_tactic::omega;
use super::pattern::infer_instance;
use super::proof_term::{assumption, exact, rfl};
use super::ring::ring_nf;
use super::simp::{simp, SimpConfig};
use super::smt::decide;
use super::tauto::tauto;
use super::{solve_by_elim, trivial};

/// Configuration for the `blast` automation tactic.
#[derive(Debug, Clone)]
pub struct BlastConfig {
    /// Maximum number of rounds to try automation steps
    pub max_rounds: usize,
    /// Depth limit for solve_by_elim search
    pub solve_by_elim_depth: usize,
    /// Whether to try propositional automation (tauto/contradiction)
    pub use_tauto: bool,
    /// Whether to run simplification
    pub use_simp: bool,
    /// Whether to enable arithmetic solvers (linarith/nlinarith/norm_num)
    pub use_arith: bool,
    /// Whether to run mathverse for integer arithmetic
    pub use_mathverse: bool,
    /// Whether to normalize rings
    pub use_ring: bool,
    /// Whether to attempt decide/native_decide
    pub use_decide: bool,
    /// Whether to try instance synthesis
    pub use_instances: bool,
    /// Whether to consult library_search as a last resort
    pub use_library_search: bool,
}

impl Default for BlastConfig {
    fn default() -> Self {
        Self {
            max_rounds: 8,
            solve_by_elim_depth: 5,
            use_tauto: true,
            use_simp: true,
            use_arith: true,
            use_mathverse: true,
            use_ring: true,
            use_decide: true,
            use_instances: true,
            use_library_search: true,
        }
    }
}

impl BlastConfig {
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_max_rounds(mut self, rounds: usize) -> Self {
        self.max_rounds = rounds;
        self
    }

    #[must_use]
    pub fn with_solve_by_elim_depth(mut self, depth: usize) -> Self {
        self.solve_by_elim_depth = depth;
        self
    }

    #[must_use]
    pub fn use_arith(mut self, enabled: bool) -> Self {
        self.use_arith = enabled;
        self
    }

    #[must_use]
    pub fn use_tauto(mut self, enabled: bool) -> Self {
        self.use_tauto = enabled;
        self
    }

    #[must_use]
    pub fn use_simp(mut self, enabled: bool) -> Self {
        self.use_simp = enabled;
        self
    }

    #[must_use]
    pub fn use_library_search(mut self, enabled: bool) -> Self {
        self.use_library_search = enabled;
        self
    }
}

/// Aggressive automation tactic inspired by mathlib's blast-style solvers.
///
/// `blast` chains together many existing tactics in a bounded search:
/// - Immediate closers: `assumption`, `trivial`, `contradiction`, `rfl`
/// - Small search: `solve_by_elim`
/// - Decision procedures: `decide`, `native_decide`
/// - Propositional automation: `tauto`
/// - Simplification and rewriting: `simp`
/// - Arithmetic: `linarith`, `nlinarith`, `norm_num`, `mathverse`, `ring_nf`
/// - Type class synthesis: `infer_instance`
/// - Library search fallback: `library_search` + `exact`
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, all goals are closed (`state.is_complete()` is true).
/// ENSURES: Returns `Err(NoProgress)` if no tactic made progress within 8 rounds.
pub fn blast(state: &mut ProofState) -> TacticResult {
    blast_with_config(state, BlastConfig::default())
}

/// `blast` with custom configuration.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, all goals are closed within `config.max_rounds` rounds.
/// ENSURES: Returns `Err(NoProgress)` if no round made progress or round limit exhausted
///   with goals remaining.
/// ENSURES: State may be partially modified (goals reduced) even on failure.
pub fn blast_with_config(state: &mut ProofState, config: BlastConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    for _ in 0..config.max_rounds {
        if state.is_complete() {
            return Ok(());
        }

        if !blast_round(state, &config) {
            break;
        }
    }

    if state.is_complete() {
        Ok(())
    } else {
        Err(TacticError::NoProgress {
            tactic: "blast".into(),
        })
    }
}

/// Run a single blast automation round. Returns true if any tactic made progress.
fn blast_round(state: &mut ProofState, config: &BlastConfig) -> bool {
    // Quick closers
    if try_tactic_preserving_state(state, assumption) {
        return true;
    }
    if try_tactic_preserving_state(state, trivial) {
        return true;
    }
    if try_tactic_preserving_state(state, contradiction) {
        return true;
    }
    if try_tactic_preserving_state(state, rfl) {
        return true;
    }

    // Small search with context
    if try_tactic_preserving_state(state, |s| solve_by_elim(s, config.solve_by_elim_depth)) {
        return true;
    }

    // Decision procedures
    if config.use_decide && try_tactic_preserving_state(state, decide) {
        return true;
    }
    if config.use_decide && try_tactic_preserving_state(state, super::native_decide) {
        return true;
    }

    // Propositional automation
    if config.use_tauto && try_tactic_preserving_state(state, tauto) {
        return true;
    }

    // Simplification
    if config.use_simp && try_tactic_preserving_state(state, |s| simp(s, SimpConfig::new())) {
        return true;
    }

    // Arithmetic
    if config.use_arith && try_tactic_preserving_state(state, linarith) {
        return true;
    }
    if config.use_arith && try_tactic_preserving_state(state, nlinarith) {
        return true;
    }
    if config.use_arith && try_tactic_preserving_state(state, super::norm_num) {
        return true;
    }

    if config.use_mathverse && try_tactic_preserving_state(state, omega) {
        return true;
    }

    if config.use_ring && try_tactic_preserving_state(state, ring_nf) {
        return true;
    }

    // Type class synthesis
    if config.use_instances && try_tactic_preserving_state(state, infer_instance) {
        return true;
    }

    // Library search fallback: try first candidate with exact
    if config.use_library_search {
        let saved_goals = state.goals.clone();
        state.metas_mut().push_scope();

        if let Ok(results) = library_search(state) {
            for res in results {
                if try_tactic_preserving_state(state, |s| exact(s, res.expr.clone())) {
                    // Commit scope - found a working exact
                    state.metas_mut().commit();
                    return true;
                }
            }
        }

        state.invalidate_tc_cache();
        state.goals = saved_goals;
        state.metas_mut().pop_scope();
    }

    false
}
