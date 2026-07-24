// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured tactic script interpreter.
//!
//! Provides an AST representation for tactic scripts and an interpreter
//! that walks the AST executing tactics against a [`ProofState`]. Supports
//! Lean 4 tactic combinators: sequence (`;`), focus, `first`, `repeat`,
//! `try`, `all_goals`, and `any_goals`.
//!
//! # Architecture
//!
//! 1. Parse a tactic script string into a [`TacticNode`] AST via [`parse_tactic_script`].
//! 2. Walk the AST with [`TacticInterpreter::execute`], dispatching atoms to
//!    the existing `execute_simple_tactic` in `script_runner.rs`.
//!
//! The interpreter reuses the existing combinator infrastructure from
//! `combinator.rs` for state save/restore semantics.

use super::core::{ProofState, TacticError, TacticResult};
use super::script_runner::execute_simple_tactic;
use crate::{ElabCtx, ElabError};
use clean_kernel::Environment;
use clean_parser::SurfaceExpr;

/// Byte range in the source script associated with a post-tactic snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TacticPostSnapshotRange {
    pub start: usize,
    pub end: usize,
}

/// Serializable post-tactic goal payload for editor/LSP consumers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TacticGoalSnapshot {
    pub post_tactic_range: TacticPostSnapshotRange,
    pub remaining_goals: usize,
    pub rendered_targets: Vec<String>,
}

/// Result of running a tactic script with an editor-facing post-tactic snapshot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TacticScriptSnapshotRun {
    pub snapshot: TacticGoalSnapshot,
}

// ---------------------------------------------------------------------------
// AST
// ---------------------------------------------------------------------------

/// AST node for a structured tactic script.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TacticNode {
    /// Single tactic application: `exact h`, `intro x`, `apply f`.
    Atom(TacticAtom),
    /// Sequential composition: `t1 ; t2 ; t3`.
    Seq(Vec<TacticNode>),
    /// Focus on first goal, run inner tactic.
    Focus(Box<TacticNode>),
    /// Try alternatives in order: `first | t1 | t2`.
    First(Vec<TacticNode>),
    /// Repeat until failure or budget: `repeat t`.
    Repeat(Box<TacticNode>),
    /// Try (no-fail wrapper): `try t`.
    Try(Box<TacticNode>),
    /// Apply to all goals: `all_goals t`.
    AllGoals(Box<TacticNode>),
    /// Apply to any goal that succeeds: `any_goals t`.
    AnyGoals(Box<TacticNode>),
    /// Skip / no-op.
    Skip,
    /// Done — assert no remaining goals.
    Done,
}

/// A single atomic tactic with name and arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TacticAtom {
    pub(crate) name: String,
    pub(crate) args: Vec<String>,
}

impl TacticAtom {
    /// Reconstruct the tactic string for dispatch to `execute_simple_tactic`.
    fn to_tactic_string(&self) -> String {
        if self.args.is_empty() {
            self.name.clone()
        } else {
            format!("{} {}", self.name, self.args.join(" "))
        }
    }
}

// ---------------------------------------------------------------------------
// Interpreter
// ---------------------------------------------------------------------------

/// Maximum iterations for `repeat` to prevent infinite loops.
const MAX_REPEAT_ITERATIONS: usize = 1000;

/// Interpreter for structured tactic scripts.
///
/// Walks a [`TacticNode`] AST, executing each node against the proof state.
/// Atomic tactics are dispatched to the existing `execute_simple_tactic`.
pub(crate) struct TacticInterpreter<'a> {
    env: &'a Environment,
}

impl<'a> TacticInterpreter<'a> {
    /// Create a new interpreter with the given environment.
    pub(crate) fn new(env: &'a Environment) -> Self {
        Self { env }
    }

    /// Execute a tactic AST node against the proof state.
    pub(crate) fn execute(&self, node: &TacticNode, state: &mut ProofState) -> TacticResult {
        match node {
            TacticNode::Atom(atom) => self.execute_atom(atom, state),
            TacticNode::Seq(nodes) => self.execute_seq(nodes, state),
            TacticNode::Focus(inner) => self.execute_focus(inner, state),
            TacticNode::First(alternatives) => self.execute_first(alternatives, state),
            TacticNode::Repeat(inner) => self.execute_repeat(inner, state),
            TacticNode::Try(inner) => self.execute_try(inner, state),
            TacticNode::AllGoals(inner) => self.execute_all_goals(inner, state),
            TacticNode::AnyGoals(inner) => self.execute_any_goals(inner, state),
            TacticNode::Skip => Ok(()),
            TacticNode::Done => {
                if state.is_complete() {
                    Ok(())
                } else {
                    Err(TacticError::UnsolvedGoals {
                        count: state.goals().len(),
                        detail: " after `done`".to_string(),
                    })
                }
            }
        }
    }

    /// Dispatch an atomic tactic to the existing `execute_simple_tactic`.
    fn execute_atom(&self, atom: &TacticAtom, state: &mut ProofState) -> TacticResult {
        let tactic_str = atom.to_tactic_string();
        execute_simple_tactic(state, &tactic_str, self.env)
    }

    /// Execute a sequence of tactic nodes, short-circuiting on error.
    fn execute_seq(&self, nodes: &[TacticNode], state: &mut ProofState) -> TacticResult {
        for node in nodes {
            self.execute(node, state)?;
            if state.is_complete() {
                break;
            }
        }
        Ok(())
    }

    /// Focus on the first goal, execute the inner tactic, then restore
    /// the remaining goals.
    fn execute_focus(&self, inner: &TacticNode, state: &mut ProofState) -> TacticResult {
        if state.goals().is_empty() {
            return Err(TacticError::NoGoals);
        }

        let rest = state.goals.split_off(1);
        let result = self.execute(inner, state);
        state.goals.extend(rest);
        result
    }

    /// Try alternatives in order, returning the first success.
    fn execute_first(&self, alternatives: &[TacticNode], state: &mut ProofState) -> TacticResult {
        if alternatives.is_empty() {
            return Err(TacticError::AllTacticsFailed {
                combinator: "first".into(),
            });
        }

        let saved_goals = state.goals.clone();

        for (idx, alt) in alternatives.iter().enumerate() {
            let is_last = idx + 1 == alternatives.len();

            if is_last {
                // Last alternative: run directly so its error propagates.
                return self.execute(alt, state);
            }

            state.metas_mut().push_scope();
            match self.execute(alt, state) {
                Ok(()) => {
                    state.metas_mut().commit();
                    return Ok(());
                }
                Err(_) => {
                    state.invalidate_tc_cache();
                    state.goals = saved_goals.clone();
                    state.metas_mut().pop_scope();
                }
            }
        }

        // Unreachable if alternatives is non-empty, but satisfy the type checker.
        Err(TacticError::AllTacticsFailed {
            combinator: "first".into(),
        })
    }

    /// Repeat the inner tactic until it fails or the budget is exhausted.
    /// Always returns `Ok` (zero-or-more semantics).
    fn execute_repeat(&self, inner: &TacticNode, state: &mut ProofState) -> TacticResult {
        for _ in 0..MAX_REPEAT_ITERATIONS {
            let saved_goals = state.goals.clone();
            state.metas_mut().push_scope();

            match self.execute(inner, state) {
                Ok(()) => {
                    state.metas_mut().commit();
                    if state.is_complete() {
                        break;
                    }
                }
                Err(_) => {
                    state.invalidate_tc_cache();
                    state.goals = saved_goals;
                    state.metas_mut().pop_scope();
                    break;
                }
            }
        }
        Ok(())
    }

    /// Try the inner tactic; succeed regardless of outcome.
    fn execute_try(&self, inner: &TacticNode, state: &mut ProofState) -> TacticResult {
        let saved_goals = state.goals.clone();
        state.metas_mut().push_scope();

        if self.execute(inner, state).is_ok() {
            state.metas_mut().commit();
        } else {
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            state.metas_mut().pop_scope();
        }
        Ok(())
    }

    /// Apply the inner tactic to all goals. Fails if any application fails.
    fn execute_all_goals(&self, inner: &TacticNode, state: &mut ProofState) -> TacticResult {
        let original_count = state.goals.len();
        let mut processed = 0;

        while processed < original_count && !state.goals().is_empty() {
            self.execute(inner, state)?;
            processed += 1;
        }
        Ok(())
    }

    /// Apply the inner tactic to each goal; succeed if at least one succeeds.
    fn execute_any_goals(&self, inner: &TacticNode, state: &mut ProofState) -> TacticResult {
        let original_count = state.goals.len();
        let mut processed = 0;
        let mut any_succeeded = false;

        while processed < original_count && !state.goals().is_empty() {
            let saved_goals = state.goals.clone();
            state.metas_mut().push_scope();

            if self.execute(inner, state).is_ok() {
                state.metas_mut().commit();
                any_succeeded = true;
            } else {
                state.invalidate_tc_cache();
                state.goals = saved_goals;
                state.metas_mut().pop_scope();
                // Rotate the failed goal to the back.
                if let Ok(goal) = state.pop_current_goal() {
                    state.goals.push_back(goal);
                }
            }
            processed += 1;
        }

        if any_succeeded {
            Ok(())
        } else {
            Err(TacticError::AllTacticsFailed {
                combinator: "any_goals".into(),
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a tactic script string into a structured AST.
///
/// Handles:
/// - Semicolons for sequencing: `t1 ; t2 ; t3`
/// - `first | t1 | t2 | t3`
/// - `repeat t`
/// - `try t`
/// - `all_goals t`
/// - `any_goals t`
/// - `focus t`
/// - `skip` / `done`
/// - Bare atom tactics: `intro x`, `exact h`, etc.
///
/// Newlines are treated as sequencing (same as semicolons after comment
/// stripping). Block and line comments are stripped before parsing.
pub(crate) fn parse_tactic_script(input: &str) -> Result<TacticNode, TacticError> {
    let stripped = super::script_runner::comment_strip::strip_block_comments(input);
    let fragments = split_tactic_fragments(&stripped);

    if fragments.is_empty() {
        return Ok(TacticNode::Skip);
    }
    if fragments.len() == 1 {
        return parse_single_fragment(&fragments[0]);
    }

    let nodes: Result<Vec<TacticNode>, TacticError> =
        fragments.iter().map(|f| parse_single_fragment(f)).collect();
    Ok(TacticNode::Seq(nodes?))
}

/// Split a comment-stripped script into fragments on semicolons and newlines.
fn split_tactic_fragments(script: &str) -> Vec<String> {
    script
        .lines()
        .flat_map(|line| line.split(';'))
        .map(|s| strip_line_comment(s).trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

/// Strip a `-- ...` line comment.
fn strip_line_comment(s: &str) -> &str {
    match s.find("--") {
        Some(pos) => &s[..pos],
        None => s,
    }
}

/// Parse a single tactic fragment (no semicolons/newlines) into a node.
fn parse_single_fragment(fragment: &str) -> Result<TacticNode, TacticError> {
    let trimmed = fragment.trim();
    if trimmed.is_empty() {
        return Ok(TacticNode::Skip);
    }

    // Handle combinator prefixes.
    if let Some(rest) = trimmed.strip_prefix("first") {
        return parse_first_combinator(rest.trim());
    }
    if let Some(rest) = trimmed.strip_prefix("repeat ") {
        let inner = parse_single_fragment(rest.trim())?;
        return Ok(TacticNode::Repeat(Box::new(inner)));
    }
    if trimmed == "repeat" {
        return Err(TacticError::MissingArgument {
            tactic: "repeat".to_string(),
            expected: "inner tactic".to_string(),
        });
    }
    if let Some(rest) = trimmed.strip_prefix("try ") {
        let inner = parse_single_fragment(rest.trim())?;
        return Ok(TacticNode::Try(Box::new(inner)));
    }
    if let Some(rest) = trimmed.strip_prefix("all_goals ") {
        let inner = parse_single_fragment(rest.trim())?;
        return Ok(TacticNode::AllGoals(Box::new(inner)));
    }
    if let Some(rest) = trimmed.strip_prefix("any_goals ") {
        let inner = parse_single_fragment(rest.trim())?;
        return Ok(TacticNode::AnyGoals(Box::new(inner)));
    }
    if let Some(rest) = trimmed.strip_prefix("focus ") {
        let inner = parse_single_fragment(rest.trim())?;
        return Ok(TacticNode::Focus(Box::new(inner)));
    }

    // Built-in control keywords.
    if trimmed == "skip" {
        return Ok(TacticNode::Skip);
    }
    if trimmed == "done" {
        return Ok(TacticNode::Done);
    }

    // Otherwise, it is an atomic tactic.
    let parts: Vec<&str> = trimmed.split_whitespace().collect();
    if parts.is_empty() {
        return Ok(TacticNode::Skip);
    }

    Ok(TacticNode::Atom(TacticAtom {
        name: parts[0].to_string(),
        args: parts[1..].iter().map(|s| s.to_string()).collect(),
    }))
}

/// Parse `first | t1 | t2 | ...` into a `First` node.
fn parse_first_combinator(rest: &str) -> Result<TacticNode, TacticError> {
    // Expect alternatives separated by `|`.
    let rest = rest.trim_start_matches('|').trim();
    if rest.is_empty() {
        return Err(TacticError::MissingArgument {
            tactic: "first".to_string(),
            expected: "alternatives after `first`".to_string(),
        });
    }

    let alts: Result<Vec<TacticNode>, TacticError> = rest
        .split('|')
        .map(|s| parse_single_fragment(s.trim()))
        .collect();
    Ok(TacticNode::First(alts?))
}

// ---------------------------------------------------------------------------
// Convenience runner
// ---------------------------------------------------------------------------

/// Parse and execute a structured tactic script against a proof state.
///
/// This is the main entry point for running multi-tactic scripts that may
/// contain combinators (`repeat`, `first`, `try`, etc.).
pub(crate) fn run_tactic_script(
    script: &str,
    state: &mut ProofState,
    env: &Environment,
) -> TacticResult {
    let ast = parse_tactic_script(script)?;
    let interp = TacticInterpreter::new(env);
    interp.execute(&ast, state)
}

/// Run a tactic script and return a post-tactic snapshot for LSP/infoview use.
///
/// The caller supplies the source range to associate with the post-tactic
/// state because this interpreter receives a script string, not the original
/// parsed surface-tactic span. This API proves the elab-side payload boundary:
/// post-tactic range, remaining goal count, and rendered targets.
pub fn run_tactic_script_with_snapshots(
    script: &str,
    post_tactic_range: TacticPostSnapshotRange,
    state: &mut ProofState,
    env: &Environment,
) -> Result<TacticScriptSnapshotRun, TacticError> {
    run_tactic_script(script, state, env)?;
    Ok(TacticScriptSnapshotRun {
        snapshot: TacticGoalSnapshot {
            post_tactic_range,
            remaining_goals: state.goals().len(),
            rendered_targets: state
                .goals()
                .iter()
                .map(|goal| format!("⊢ {:?}", goal.target))
                .collect(),
        },
    })
}

/// Build a typed proof state for a theorem target before tactic execution.
///
/// This is the elab-side bridge LSP needs before it can call
/// [`run_tactic_script_with_snapshots`] from parsed `by` tactic spans.
pub fn proof_state_for_tactic_target(
    env: &Environment,
    target: &SurfaceExpr,
) -> Result<ProofState, ElabError> {
    let mut ctx = ElabCtx::new(env);
    let target_expr = ctx.elaborate(target)?;
    Ok(ProofState::new(env.clone(), target_expr))
}

#[cfg(test)]
mod lsp_snapshot_tests {
    use super::*;
    use clean_kernel::Expr;
    use clean_parser::Span;

    #[test]
    fn run_tactic_script_with_snapshots_returns_required_payload_identity() {
        let env = Environment::new();
        let mut state = ProofState::new(env.clone(), Expr::const_str("PendingGoal"));
        let post_tactic_range = TacticPostSnapshotRange { start: 4, end: 8 };

        let result = run_tactic_script_with_snapshots("skip", post_tactic_range, &mut state, &env)
            .expect("skip should preserve the pending goal and produce a snapshot");

        assert_eq!(result.snapshot.post_tactic_range, post_tactic_range);
        assert_eq!(result.snapshot.remaining_goals, 1);
        assert_eq!(result.snapshot.rendered_targets.len(), 1);
        assert!(
            result.snapshot.rendered_targets[0].contains("PendingGoal"),
            "rendered target should include the post-tactic goal target: {:?}",
            result.snapshot.rendered_targets
        );
    }

    #[test]
    fn proof_state_for_tactic_target_builds_snapshot_ready_state() {
        let env = Environment::new();
        let target = SurfaceExpr::Universe(Span::dummy(), clean_parser::UniverseExpr::Prop);
        let mut state = proof_state_for_tactic_target(&env, &target)
            .expect("Prop target should elaborate into a tactic proof state");
        let post_tactic_range = TacticPostSnapshotRange { start: 0, end: 4 };

        let result = run_tactic_script_with_snapshots("skip", post_tactic_range, &mut state, &env)
            .expect("snapshot runner should accept the typed proof state");

        assert_eq!(result.snapshot.post_tactic_range, post_tactic_range);
        assert_eq!(result.snapshot.remaining_goals, 1);
        assert_eq!(result.snapshot.rendered_targets.len(), 1);
    }
}

#[cfg(test)]
mod tests;
