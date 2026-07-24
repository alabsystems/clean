// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `nn_verify` tactic: domain-specific automation for neural network verification.
//!
//! Inspects the goal structure, matches against known NN verification proof
//! patterns, and applies the appropriate proof strategy. Falls back to
//! `auto_cascade` when no domain-specific pattern matches.
//!
//! # Supported Patterns
//!
//! 1. **IBP soundness** — goals involving `ibp_*_sound` (W+/W- decomposition)
//! 2. **CROWN relaxation** — goals involving `crown_*` (backward propagation)
//! 3. **Certificate composition** — goals involving `cert_*_compose` (transitivity)
//! 4. **Bound propagation** — goals involving `IntervalBounds.contains` (interval arith)
//! 5. **Abstract domain** — goals involving `AbstractDomain.*` (Galois connections)
//!
//! # Extensibility
//!
//! The pattern registry is a Vec of `(classifier, strategy)` pairs. New patterns
//! can be added by pushing entries to the registry without modifying existing code.

use super::combinator::try_tactic_preserving_state;
use super::core::{ProofState, TacticError, TacticResult};
use clean_kernel::{Expr, ExprKind};

// ---------------------------------------------------------------------------
// Pattern classification
// ---------------------------------------------------------------------------

/// Known NN verification proof patterns.
///
/// Each variant corresponds to a class of goals that arise in neural network
/// verification proofs. The tactic inspects the goal head symbol and selects
/// the matching strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum NnVerifyPattern {
    /// IBP (Interval Bound Propagation) soundness: W+/W- decomposition.
    /// Matched when the goal head contains `ibp_` and `sound`.
    IbpSoundness,

    /// CROWN relaxation validity: backward bound propagation.
    /// Matched when the goal head contains `crown_`.
    CrownRelaxation,

    /// Certificate composition: transitivity chain over certificates.
    /// Matched when the goal head contains `cert_` and `compose`.
    CertComposition,

    /// Bound propagation: interval arithmetic on `IntervalBounds.contains`.
    /// Matched when the goal head contains `IntervalBounds` and `contains`.
    BoundPropagation,

    /// Abstract domain properties: Galois connection lemmas.
    /// Matched when the goal head contains `AbstractDomain`.
    AbstractDomain,
}

impl std::fmt::Display for NnVerifyPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IbpSoundness => write!(f, "IBP soundness"),
            Self::CrownRelaxation => write!(f, "CROWN relaxation"),
            Self::CertComposition => write!(f, "certificate composition"),
            Self::BoundPropagation => write!(f, "bound propagation"),
            Self::AbstractDomain => write!(f, "abstract domain"),
        }
    }
}

// ---------------------------------------------------------------------------
// Goal inspection helpers
// ---------------------------------------------------------------------------

/// Extract the head constant name from an expression, traversing the
/// application spine. Returns `None` if the head is not a `Const`.
fn head_const_name(expr: &Expr) -> Option<String> {
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        Some(name.to_string())
    } else {
        None
    }
}

/// Collect all constant names reachable from the top-level application spine
/// of `expr` (head + arguments, one level deep). This gives us enough signal
/// to classify domain-specific goals without a full tree walk.
fn collect_spine_const_names(expr: &Expr) -> Vec<String> {
    let mut names = Vec::new();
    if let Some(head_name) = head_const_name(expr) {
        names.push(head_name);
    }
    // Walk the application spine to collect argument head constants.
    let mut cursor = expr;
    while let ExprKind::App(fun, arg) = cursor.kind() {
        if let Some(arg_name) = head_const_name(arg) {
            names.push(arg_name);
        }
        cursor = fun;
    }
    names
}

/// Check if any of the collected names contains a substring.
fn any_name_contains(names: &[String], substring: &str) -> bool {
    names.iter().any(|n| n.contains(substring))
}

// ---------------------------------------------------------------------------
// Pattern classification
// ---------------------------------------------------------------------------

/// Classify a goal expression into an NN verification pattern.
///
/// Inspects constant names in the goal's application spine and matches
/// against known NN verification idioms.
///
/// REQUIRES: `goal` is a well-formed expression (the goal target).
/// ENSURES: Returns `Some(pattern)` if the goal matches a known NN verification
///          pattern, `None` otherwise.
#[must_use]
pub(crate) fn classify_goal(goal: &Expr) -> Option<NnVerifyPattern> {
    let names = collect_spine_const_names(goal);
    if names.is_empty() {
        return None;
    }

    // Check patterns in priority order (most specific first).
    // IBP soundness: head or args contain "ibp_" AND "sound"
    if any_name_contains(&names, "ibp_") && any_name_contains(&names, "sound") {
        return Some(NnVerifyPattern::IbpSoundness);
    }

    // Certificate composition: "cert_" AND "compose"
    if any_name_contains(&names, "cert_") && any_name_contains(&names, "compose") {
        return Some(NnVerifyPattern::CertComposition);
    }

    // CROWN relaxation: "crown_"
    if any_name_contains(&names, "crown_") {
        return Some(NnVerifyPattern::CrownRelaxation);
    }

    // Bound propagation: "IntervalBounds" AND "contains"
    if any_name_contains(&names, "IntervalBounds") && any_name_contains(&names, "contains") {
        return Some(NnVerifyPattern::BoundPropagation);
    }

    // Abstract domain: "AbstractDomain"
    if any_name_contains(&names, "AbstractDomain") {
        return Some(NnVerifyPattern::AbstractDomain);
    }

    None
}

// ---------------------------------------------------------------------------
// Pattern-specific proof strategies
// ---------------------------------------------------------------------------

/// IBP soundness strategy: decompose into W+ and W- components, then apply
/// interval arithmetic. Tries: simp -> linarith -> mathverse -> decide.
fn strategy_ibp_soundness(state: &mut ProofState) -> TacticResult {
    let tactics: &[(&str, fn(&mut ProofState) -> TacticResult)] = &[
        ("simp", |ps| super::simp(ps, super::SimpConfig::default())),
        ("linarith", super::linarith),
        ("omega", super::omega),
        ("decide", super::decide),
    ];
    run_strategy_cascade("nn_verify.ibp", state, tactics)
}

/// CROWN relaxation strategy: backward propagation validity. Tries:
/// simp -> linarith -> norm_num -> ring -> decide.
fn strategy_crown_relaxation(state: &mut ProofState) -> TacticResult {
    let tactics: &[(&str, fn(&mut ProofState) -> TacticResult)] = &[
        ("simp", |ps| super::simp(ps, super::SimpConfig::default())),
        ("linarith", super::linarith),
        ("norm_num", super::norm_num),
        ("ring", super::ring),
        ("decide", super::decide),
    ];
    run_strategy_cascade("nn_verify.crown", state, tactics)
}

/// Certificate composition strategy: transitivity chains. Tries:
/// decide -> simp -> linarith -> aesop.
fn strategy_cert_composition(state: &mut ProofState) -> TacticResult {
    let tactics: &[(&str, fn(&mut ProofState) -> TacticResult)] = &[
        ("decide", super::decide),
        ("simp", |ps| super::simp(ps, super::SimpConfig::default())),
        ("linarith", super::linarith),
        ("aesop", super::aesop),
    ];
    run_strategy_cascade("nn_verify.cert", state, tactics)
}

/// Bound propagation strategy: interval arithmetic. Tries:
/// mathverse -> linarith -> norm_num -> simp -> decide.
fn strategy_bound_propagation(state: &mut ProofState) -> TacticResult {
    let tactics: &[(&str, fn(&mut ProofState) -> TacticResult)] = &[
        ("omega", super::omega),
        ("linarith", super::linarith),
        ("norm_num", super::norm_num),
        ("simp", |ps| super::simp(ps, super::SimpConfig::default())),
        ("decide", super::decide),
    ];
    run_strategy_cascade("nn_verify.bounds", state, tactics)
}

/// Abstract domain strategy: Galois connection properties. Tries:
/// simp -> decide -> linarith -> aesop -> tauto.
fn strategy_abstract_domain(state: &mut ProofState) -> TacticResult {
    let tactics: &[(&str, fn(&mut ProofState) -> TacticResult)] = &[
        ("simp", |ps| super::simp(ps, super::SimpConfig::default())),
        ("decide", super::decide),
        ("linarith", super::linarith),
        ("aesop", super::aesop),
        ("tauto", super::tauto),
    ];
    run_strategy_cascade("nn_verify.abstract", state, tactics)
}

/// Run a cascade of tactics for a specific strategy, returning the first
/// success. On failure of all tactics, returns `AllTacticsFailed`.
fn run_strategy_cascade(
    strategy_name: &str,
    state: &mut ProofState,
    tactics: &[(&str, fn(&mut ProofState) -> TacticResult)],
) -> TacticResult {
    for &(name, tactic_fn) in tactics {
        if try_tactic_preserving_state(state, tactic_fn) {
            tracing::debug!(
                tactic = "nn_verify",
                strategy = strategy_name,
                winner = name,
                "pattern strategy succeeded"
            );
            return Ok(());
        }
    }
    Err(TacticError::AllTacticsFailed {
        combinator: strategy_name.into(),
    })
}

// ---------------------------------------------------------------------------
// Extensible pattern registry
// ---------------------------------------------------------------------------

/// A classifier function that inspects a goal and returns `true` if the
/// pattern applies.
type PatternClassifier = fn(&Expr) -> bool;

/// A strategy function that attempts to close a goal.
type PatternStrategy = fn(&mut ProofState) -> TacticResult;

/// Entry in the extensible pattern registry.
pub(crate) struct PatternRegistryEntry {
    /// Human-readable name for diagnostics.
    pub(crate) name: &'static str,
    /// Predicate: does this pattern apply to the goal?
    pub(crate) classifier: PatternClassifier,
    /// Strategy to apply when the classifier matches.
    pub(crate) strategy: PatternStrategy,
}

/// Build the default pattern registry.
///
/// ENSURES: Returns entries for all 5 built-in NN verification patterns,
///          in priority order (most specific first).
#[must_use]
fn default_registry() -> Vec<PatternRegistryEntry> {
    vec![
        PatternRegistryEntry {
            name: "IBP soundness",
            classifier: |goal| classify_goal(goal) == Some(NnVerifyPattern::IbpSoundness),
            strategy: strategy_ibp_soundness,
        },
        PatternRegistryEntry {
            name: "certificate composition",
            classifier: |goal| classify_goal(goal) == Some(NnVerifyPattern::CertComposition),
            strategy: strategy_cert_composition,
        },
        PatternRegistryEntry {
            name: "CROWN relaxation",
            classifier: |goal| classify_goal(goal) == Some(NnVerifyPattern::CrownRelaxation),
            strategy: strategy_crown_relaxation,
        },
        PatternRegistryEntry {
            name: "bound propagation",
            classifier: |goal| classify_goal(goal) == Some(NnVerifyPattern::BoundPropagation),
            strategy: strategy_bound_propagation,
        },
        PatternRegistryEntry {
            name: "abstract domain",
            classifier: |goal| classify_goal(goal) == Some(NnVerifyPattern::AbstractDomain),
            strategy: strategy_abstract_domain,
        },
    ]
}

// ---------------------------------------------------------------------------
// Public tactic entry point
// ---------------------------------------------------------------------------

/// Result of a successful `nn_verify` invocation, recording which pattern
/// and sub-tactic closed the goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NnVerifyResult {
    /// Name of the matched pattern (or "auto_cascade" for fallback).
    pub(crate) pattern: String,
}

/// Domain-specific tactic for neural network verification proofs.
///
/// Inspects the current goal, matches against known NN verification patterns,
/// and applies the appropriate proof strategy. Falls back to `auto_cascade`
/// when no domain-specific pattern matches.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok`, the current goal is closed.
/// ENSURES: On `Err`, no sub-tactic succeeded; state is unchanged from pre-call.
pub fn nn_verify(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal_target = state
        .current_goal()
        .expect("checked non-empty")
        .target
        .clone();

    // Try domain-specific patterns first.
    let registry = default_registry();
    for entry in &registry {
        if (entry.classifier)(&goal_target) {
            tracing::debug!(
                tactic = "nn_verify",
                pattern = entry.name,
                "matched NN verification pattern"
            );
            // Try the pattern-specific strategy; if it fails, continue to
            // the next pattern (defensive: classifiers are heuristic).
            if try_tactic_preserving_state(state, entry.strategy) {
                tracing::debug!(
                    tactic = "nn_verify",
                    pattern = entry.name,
                    "pattern strategy succeeded"
                );
                return Ok(());
            }
        }
    }

    // Fallback: delegate to auto_cascade.
    tracing::debug!(
        tactic = "nn_verify",
        "no NN pattern matched, falling back to auto_cascade"
    );
    super::auto_cascade(state)
}

/// Run `nn_verify` and return diagnostic info about which pattern succeeded.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: Same as `nn_verify`, plus returns the pattern name on success.
pub(crate) fn nn_verify_with_info(state: &mut ProofState) -> Result<NnVerifyResult, TacticError> {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal_target = state
        .current_goal()
        .expect("checked non-empty")
        .target
        .clone();

    let registry = default_registry();
    for entry in &registry {
        if (entry.classifier)(&goal_target) && try_tactic_preserving_state(state, entry.strategy) {
            return Ok(NnVerifyResult {
                pattern: entry.name.to_string(),
            });
        }
    }

    // Fallback to auto_cascade.
    super::auto_cascade(state)?;
    Ok(NnVerifyResult {
        pattern: "auto_cascade".to_string(),
    })
}

#[cfg(test)]
#[path = "nn_verify_tests.rs"]
mod tests;
