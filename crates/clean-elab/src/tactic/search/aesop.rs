// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Aesop configuration, entry points, normalization, and safe rules.

use crate::tactic::{
    assumption, decide, extract_equality_from_type, intro, rfl, simp_all_with_config, split_,
    tauto, trivial, try_tactic_preserving_state, ProofState, SimpConfig, SimpIndexMode, SimpLemma,
    TacticError, TacticResult,
};
use clean_kernel::name::Name;
use clean_kernel::{AesopRuleBuilder, Environment, ExprKind};

// =============================================================================
// Aesop Types
// =============================================================================

/// Aesop rule kind
#[derive(Debug, Clone)]
pub enum AesopRuleKind {
    /// Safe rule - always apply without backtracking
    Safe,
    /// Norm rule - normalization that doesn't change provability
    Norm,
    /// Unsafe rule - may need backtracking (with priority)
    Unsafe(i32),
}

/// Aesop rule descriptor
#[derive(Debug, Clone)]
pub struct AesopRule {
    /// Name of the rule
    pub name: String,
    /// Kind of rule (safe, norm, unsafe)
    pub kind: AesopRuleKind,
}

/// Configuration for aesop
#[derive(Debug, Clone)]
pub struct AesopConfig {
    /// Maximum search depth
    pub max_depth: usize,
    /// Maximum number of goals to process
    pub max_goals: usize,
    /// Maximum number of search loop iterations before giving up.
    ///
    /// This bounds the total work done by the AND-OR tree search
    /// independently of `max_goals`. Each iteration expands one goal
    /// node, so this limits the overall search effort.
    pub max_iterations: usize,
    /// Whether to use simp normalization
    pub use_simp: bool,
    /// Whether to try unfold tactics
    pub use_unfold: bool,
    /// Search strategy for goal selection
    pub strategy: super::types::AesopStrategy,
    /// Named rule sets to use (empty = use default rule set)
    ///
    /// When specified, rules from these sets may have priority overrides
    /// that differ from their base priority.
    pub rule_sets: Vec<Name>,
}

impl Default for AesopConfig {
    fn default() -> Self {
        AesopConfig {
            max_depth: 10,
            max_goals: 100,
            max_iterations: 1000,
            use_simp: true,
            use_unfold: true,
            strategy: super::types::AesopStrategy::default(),
            rule_sets: Vec::new(),
        }
    }
}

/// `aesop` - general automated proof search tactic
///
/// Implements a best-first search proof strategy inspired by Isabelle's auto and Lean 4's aesop.
///
/// Strategy:
/// 1. Apply safe rules (intro, split on And, etc.)
/// 2. Try normalization (simp, ring, norm_num)
/// 3. Apply unsafe rules with backtracking (apply, cases)
/// 4. Search for applicable lemmas
///
/// # Example
/// ```text
/// -- goal: P ∧ Q → Q ∧ P
/// aesop
/// -- automatically proves by intro, cases, constructor
/// ```
/// REQUIRES: `state` has a current goal when callers expect search to begin.
/// ENSURES: Delegates to `aesop_with_config(state, AesopConfig::default())`.
pub fn aesop(state: &mut ProofState) -> TacticResult {
    let mut config = AesopConfig::default();
    if let Some(max_depth) = state.options().max_depth_override() {
        config.max_depth = max_depth;
    }
    aesop_with_config(state, config)
}

/// Aesop with custom configuration
/// REQUIRES: `state` has a current goal when callers expect search to begin.
/// REQUIRES: `config.max_depth` and `config.max_goals` bound the intended search effort.
/// ENSURES: Delegates to the AND-OR tree search engine with the supplied configuration.
pub fn aesop_with_config(state: &mut ProofState, config: AesopConfig) -> TacticResult {
    // Use tree-based search with backtracking
    super::aesop_search::aesop_search_tree(state, &config)
}

/// A candidate tactic for aesop
pub(super) struct AesopCandidate {
    pub(super) priority: i32,
    pub(super) apply: Box<dyn Fn(&mut ProofState) -> TacticResult>,
}

/// Apply safe rules that don't require backtracking
/// REQUIRES: If callers expect progress, `state` has a current goal with a well-formed target.
/// REQUIRES: `depth` is the current search depth used for generated intro names.
/// ENSURES: Repeatedly applies only the built-in safe `intro`/`split_` steps until no listed safe rule succeeds.
/// ENSURES: Returns `Ok(())` even when no safe rule matches, leaving `state` unchanged in that case.
pub(super) fn aesop_safe_rules(
    state: &mut ProofState,
    _config: &AesopConfig,
    depth: usize,
) -> TacticResult {
    let mut made_progress = true;

    while made_progress && !state.goals().is_empty() {
        made_progress = false;

        let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
        let target = goal.target.clone();

        // Check goal structure
        let target_head = target.get_app_fn();

        if let ExprKind::Const(name, _) = target_head.kind() {
            let name_str = name.to_string();

            // Safe rule: intro for Pi types (implications/forall)
            if let ExprKind::Pi(_, _, _) = target.kind() {
                if intro(state, "h").is_ok() {
                    made_progress = true;
                    continue;
                }
            }

            // Safe rule: constructor for And
            if name_str == "And" && split_(state).is_ok() {
                made_progress = true;
                continue;
            }

            // Safe rule: constructor for Iff (splits into two implications)
            if name_str == "Iff" && split_(state).is_ok() {
                made_progress = true;
                continue;
            }

            // Safe rule: intro for Not (it's really an implication to False)
            if name_str == "Not" && intro(state, "h").is_ok() {
                made_progress = true;
                continue;
            }
        }

        // If target is Pi (forall/implication)
        if let ExprKind::Pi(_, _, _) = target.kind() {
            if intro(state, &format!("h{depth}")).is_ok() {
                made_progress = true;
            }
        }
    }

    Ok(())
}

/// Apply normalization tactics to hypotheses and goal.
/// REQUIRES: If a current goal exists, it is well-typed in the current proof state.
/// ENSURES: Attempts `trivial` first, then `simp_all` with `@[aesop norm simp]`
///   lemmas when a goal remains, simplifying both hypotheses and target.
/// ENSURES: Returns `Ok(())` even when neither normalization step makes progress.
pub(super) fn aesop_normalize(state: &mut ProofState) -> TacticResult {
    // Try various normalization tactics
    let _ = trivial(state);

    // Simplify hypotheses and goal with aesop norm simp rules.
    // Part of #1867: use simp_all_with_config instead of target-only simp
    // so that hypothesis simplification can enable assumption/rfl closure.
    if state.current_goal().is_some() {
        let mut config = SimpConfig::new();

        // Collect simp lemmas from @[aesop norm simp] rules
        config.aesop_simp_lemmas = collect_aesop_simp_rules(&state.env);

        let _ = simp_all_with_config(state, config);
    }

    Ok(())
}

/// Collect simp lemmas from @[aesop norm simp] rules.
///
/// These are rules registered with `@[aesop norm simp]` attribute.
/// We convert them to SimpLemma format for the simp tactic.
/// ENSURES: Returns only rules whose builder is `AesopRuleBuilder::Simp` and whose types expose an equality.
/// ENSURES: Each returned lemma preserves the source rule's name and priority.
fn collect_aesop_simp_rules(env: &Environment) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();

    // Get normalization rules from the default rule set
    for rule in env.get_aesop_norm_rules() {
        if rule.builder == AesopRuleBuilder::Simp {
            // Look up the constant's type and try to extract lhs = rhs
            if let Some(decl) = env.get_const(&rule.name) {
                if let Some((lhs, rhs)) = extract_equality_from_type(&decl.type_) {
                    lemmas.push(SimpLemma {
                        name: rule.name.clone(),
                        lhs,
                        rhs,
                        eq_type: None,
                        proof_expr: None,
                        index_mode: SimpIndexMode::Normal,
                        priority: rule.priority,
                    });
                }
            }
        }
    }

    lemmas
}

/// Try to close the current goal
/// REQUIRES: If callers expect a closing attempt, `state` has a current goal.
/// ENSURES: Tries closing tactics in order: `assumption`, `rfl`, `trivial`, `tauto`, `decide`.
/// ENSURES: On `Ok(())`, one of those tactics closed the current goal.
/// ENSURES: On `Err(SearchExhausted)`, none of the listed tactics closed the goal.
pub(super) fn aesop_try_close(state: &mut ProofState) -> TacticResult {
    // Part of #2474: wrap every branch in try_tactic_preserving_state to prevent
    // failed tactics from leaking partial state mutations to subsequent branches.
    if try_tactic_preserving_state(state, assumption) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, rfl) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, |s| {
        if trivial(s).is_ok() && s.goals().is_empty() {
            Ok(())
        } else {
            Err(TacticError::NoProgress {
                tactic: "trivial".into(),
            })
        }
    }) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, tauto) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, decide) {
        return Ok(());
    }

    Err(TacticError::SearchExhausted {
        tactic: "aesop".into(),
        detail: "cannot close goal".into(),
    })
}
