// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! simpa tactic: simp followed by assumption.

use super::names::local_name_matches;
use clean_parser::SurfaceName;

use clean_kernel::Expr;

use super::super::{assumption, simp, ProofState, SimpConfig, TacticError, TacticResult};

/// simpa tactic: simp followed by assumption
///
/// This is a convenience tactic that runs `simp` and then tries `assumption`.
/// Useful for goals that simplify to a hypothesis.
///
/// # Example
/// ```text
/// -- h : P
/// -- Goal: P /\ True
/// simpa using h
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Equivalent to `simpa_with_config(state, SimpConfig::new(), None)`
pub fn simpa(state: &mut ProofState) -> TacticResult {
    simpa_with_config(state, SimpConfig::new(), None)
}

/// simpa with custom simp config
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: If `simp` closes the current goal, returns `Ok(())` without running assumption
/// ENSURES: If `using_hyp = Some(h)`, only hypothesis `h` is used for the post-simp assumption step
/// ENSURES: On Ok, the current goal is discharged either by `simp` or a matching hypothesis/assumption
pub fn simpa_with_config(
    state: &mut ProofState,
    config: SimpConfig,
    using_hyp: Option<&SurfaceName>,
) -> TacticResult {
    if let Some(name) = using_hyp {
        super::names::require_binding_name(name, "simpa")?;
    }
    // With a named hypothesis, ONLY that hypothesis may close the goal: the
    // simp step must not close it by `assumption` from another local (Lean's
    // `simpa … using h` checks `h` alone; G49, review r4t s1).
    let mut config = config;
    if using_hyp.is_some() {
        config.assumption_closer = simp::AssumptionCloser::Off;
    }
    // First try simp
    let simp_result = simp(state, config);

    // Check if simp closed the goal
    if state.goals.is_empty() {
        return Ok(());
    }

    // If simp succeeded but goal remains, try assumption
    if simp_result.is_ok() {
        if let Some(hyp_name) = using_hyp {
            // Try to use the specific hypothesis
            let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
            for decl in goal.local_ctx.iter().rev() {
                if local_name_matches(&decl.name, hyp_name) {
                    // Check if this hypothesis can close the goal
                    // (#2229: use goal's local context so FVars resolve)
                    if state.is_def_eq(&goal, &decl.ty, &goal.target) {
                        // Part of #2154 Tier A: is_def_eq guard verified type match.
                        state.close_goal(&goal, Expr::fvar(decl.fvar))?;
                        return Ok(());
                    }
                    break; // A shadowed older local is not the named hypothesis.
                }
            }
            return Err(TacticError::no_progress("simpa"));
        }
        // Try assumption
        return assumption(state);
    }

    // Simp failed, still try assumption on original goal
    assumption(state)
}

/// simpa with only specific lemmas
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Equivalent to `simpa_with_config` with `config.extra_lemmas = lemmas`
pub fn simpa_only(state: &mut ProofState, lemmas: Vec<SurfaceName>) -> TacticResult {
    let mut config = SimpConfig::new();
    config.extra_lemmas = lemmas;
    simpa_with_config(state, config, None)
}
