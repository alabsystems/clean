// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Calculation chain tactics (calc, calc_eq)
//!
//! Split from convert.rs for file size (#2154).

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::calc_trans::{build_trans_chain, lookup_trans_rule};
use super::calc_trans_match::match_goal_rel;
use super::equality::match_equality;
use super::ring::make_eq;
use super::tc_app;
use super::{Goal, ProofState, TacticError, TacticResult};

// ============================================================================
// calc_block: Calculation chain support
// ============================================================================

/// Represents a step in a calculation chain.
#[derive(Debug, Clone)]
pub struct CalcStep {
    /// The relation (=, ≤, <, etc.)
    pub rel: CalcRel,
    /// The right-hand side of this step
    pub rhs: Expr,
    /// The justification (proof term or tactic name)
    pub justification: CalcJustification,
}

/// Relation type for calc steps
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalcRel {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
    Ne,
    Iff,
}

/// Justification for a calc step
#[derive(Debug, Clone)]
pub enum CalcJustification {
    /// A proof term
    Term(Expr),
    /// Name of a hypothesis
    Hyp(String),
    /// Use rfl/refl
    Refl,
    /// Apply a named lemma
    Lemma(String),
}

/// Resolve a calc step justification to a proof term.
fn resolve_justification(
    state: &mut ProofState,
    goal: &Goal,
    justification: &CalcJustification,
    rel: CalcRel,
    current: &Expr,
) -> Result<Expr, TacticError> {
    match justification {
        CalcJustification::Term(t) => Ok(t.clone()),
        CalcJustification::Hyp(name) => {
            let decl = goal
                .local_ctx
                .iter()
                .find(|d| &d.name == name)
                .ok_or_else(|| TacticError::HypothesisNotFound(name.clone()))?;
            Ok(Expr::fvar(decl.fvar))
        }
        CalcJustification::Refl => {
            if rel == CalcRel::Eq || rel == CalcRel::Iff {
                Ok(make_eq_refl(state, &Expr::type_(), current))
            } else if rel == CalcRel::Le || rel == CalcRel::Ge {
                Ok(state.mk_const_str("le_refl"))
            } else {
                Err(TacticError::InvalidTarget {
                    tactic: "calc_block".into(),
                    detail: "refl not applicable for strict inequality".into(),
                })
            }
        }
        CalcJustification::Lemma(name) => Ok(state.mk_const_str(name)),
    }
}

/// Execute a calculation chain proof.
///
/// A calc block is a sequence of steps:
/// ```text
/// calc a = b := by exact h1
///      _ = c := by ring
///      _ ≤ d := by linarith
/// ```
///
/// This constructs the final proof by chaining together the individual steps
/// using transitivity, then closes the original goal with the composite proof.
///
/// Part of #2154 goal-decomposition pattern: builds a nested transitivity
/// chain from resolved step proofs and assigns it via `close_goal` (checked).
///
/// REQUIRES: `steps` is non-empty; for multi-step chains, consecutive step
/// relation pairs must have a valid transitivity rule (see `calc_trans`)
///
/// ENSURES: on Ok, the current goal is closed with a composite proof built
/// from chaining the resolved step justifications via the appropriate
/// transitivity lemma for each consecutive pair;
/// single-step chains assign the proof directly without transitivity
pub fn calc_block(state: &mut ProofState, start: Expr, steps: Vec<CalcStep>) -> TacticResult {
    if steps.is_empty() {
        return Err(TacticError::MissingArgument {
            tactic: "calc_block".into(),
            expected: "at least one step".into(),
        });
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut current = start.clone();
    let mut step_proofs: Vec<Expr> = Vec::new();

    // Resolve each step's justification to a concrete proof term
    for step in &steps {
        let proof = resolve_justification(state, &goal, &step.justification, step.rel, &current)?;
        step_proofs.push(proof);
        current = step.rhs.clone();
    }

    // Single step: assign the resolved proof directly to the original goal.
    if steps.len() == 1 {
        // SAFETY(index): steps.len() == 1 guarantees step_proofs has exactly 1 element
        return state.close_goal(&goal, step_proofs.swap_remove(0));
    }

    // Multi-step chain: supports mixed relations (Eq, LE.le, LT.lt, etc.)
    // via the transitivity rule table in calc_trans.
    let target = state.metas.instantiate(&goal.target);

    // Match the goal target to determine type and universe levels.
    // Accepts Eq, Ne, LE.le, LT.lt, GE.ge, GT.gt, and Iff goal targets.
    let (_goal_rel, ty, _lhs, _rhs, levels) = match_goal_rel(&target).ok_or_else(|| {
        TacticError::GoalMismatch(
            "calc_block: goal must be a relation (Eq, Ne, LE.le, LT.lt, GE.ge, GT.gt, Iff) \
             for multi-step chain"
                .to_string(),
        )
    })?;

    // Delegate to the transitivity chain builder for both pure-Eq and mixed chains.
    let composite_proof = build_trans_chain(state, &steps, &step_proofs, &start, &ty, &levels)?;

    // Close original goal with composite proof (assigns meta + pops goal).
    // Part of #2154 goal-decomposition pattern.
    state.close_goal(&goal, composite_proof)?;

    Ok(())
}

/// Create expression for a calc relation with proper typeclass implicit args.
///
/// Builds `@Rel.{u} ty inst lhs rhs` for comparison relations, or
/// `@Eq.{u} ty lhs rhs` for equality. Iff has no implicit type arg.
///
/// Part of #2078: non-Eq relations previously produced `Rel lhs rhs`
/// (missing type + instance).
///
/// REQUIRES: `lhs` and `rhs` are well-formed expressions of compatible types
///
/// ENSURES: returns a fully-applied relation expression with correct implicit
/// type and instance arguments for the given `CalcRel` variant
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn make_calc_rel(rel: CalcRel, lhs: &Expr, rhs: &Expr, state: &mut ProofState) -> Expr {
    let rel_name = match rel {
        CalcRel::Eq => "Eq",
        CalcRel::Le => "LE.le",
        CalcRel::Lt => "LT.lt",
        CalcRel::Ge => "GE.ge",
        CalcRel::Gt => "GT.gt",
        CalcRel::Ne => "Ne",
        CalcRel::Iff => "Iff",
    };

    match rel {
        CalcRel::Eq => {
            // Eq needs type argument: @Eq.{u} ty lhs rhs
            Expr::app(
                Expr::app(
                    Expr::app(state.mk_const_str(rel_name), Expr::type_()),
                    lhs.clone(),
                ),
                rhs.clone(),
            )
        }
        CalcRel::Iff => {
            // Iff: Prop → Prop → Prop (no implicit type/inst args)
            Expr::app(
                Expr::app(state.mk_const_str(rel_name), lhs.clone()),
                rhs.clone(),
            )
        }
        CalcRel::Ne => {
            // Ne : α → α → Prop (defined as Not (Eq a b)), needs type arg
            Expr::app(
                Expr::app(
                    Expr::app(state.mk_const_str(rel_name), Expr::type_()),
                    lhs.clone(),
                ),
                rhs.clone(),
            )
        }
        _ => {
            // Comparison relations: @Rel.{u} ty inst lhs rhs
            let ty = tc_app::nat_type();
            let inst = tc_app::nat_rel_inst(rel_name);
            tc_app::mk_tc_rel(
                state.mk_const_str(rel_name),
                ty,
                inst,
                lhs.clone(),
                rhs.clone(),
            )
        }
    }
}

/// Simple calc for equality chain: prove a = c from a = b and b = c
///
/// Builds a composite proof `@Eq.trans α a b c ?h1 ?h2` that references
/// fresh metas for the two subgoals, then closes the original goal with
/// that proof so the original metavariable is assigned.
/// Part of #2154 goal-decomposition pattern.
///
/// REQUIRES: current goal is an equality `a = c`; `Eq.trans` must exist
/// in the environment; `middle` is a well-formed expression of the same type
///
/// ENSURES: on Ok, the original goal is closed and two new subgoals are pushed:
/// goal1 `a = middle` (current) and goal2 `middle = c`
pub fn calc_eq(state: &mut ProofState, middle: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Check goal is equality
    let (ty, lhs, rhs, levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("calc_eq: goal must be equality".to_string()))?;

    // Check that Eq.trans exists in environment
    let trans_name = Name::from_string("Eq.trans");
    if state.env.get_const(&trans_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Eq.trans".to_string(),
        });
    }

    let ty = state.metas.instantiate(&ty);
    let lhs = state.metas.instantiate(&lhs);
    let rhs = state.metas.instantiate(&rhs);
    let middle = state.metas.instantiate(&middle);

    // Create subgoal targets: lhs = middle, middle = rhs
    let goal1_target = make_eq(&ty, &lhs, &middle, &levels);
    let goal2_target = make_eq(&ty, &middle, &rhs, &levels);

    // Create fresh metas for subgoals BEFORE closing original goal
    let meta1 = state.fresh_meta(goal1_target.clone());
    let meta1_expr = Expr::fvar(MetaState::to_fvar(meta1));
    let meta2 = state.fresh_meta(goal2_target.clone());
    let meta2_expr = Expr::fvar(MetaState::to_fvar(meta2));

    // Build composite proof: @Eq.trans α a b c h1 h2
    // Eq.trans : ∀ {α : Sort u} {a b c : α}, Eq a b → Eq b c → Eq a c
    let mut proof = Expr::const_(trans_name, levels);
    proof = Expr::app(proof, ty); // {α}
    proof = Expr::app(proof, lhs); // {a}
    proof = Expr::app(proof, middle); // {b}
    proof = Expr::app(proof, rhs); // {c}
    proof = Expr::app(proof, meta1_expr); // h1 : a = b
    proof = Expr::app(proof, meta2_expr); // h2 : b = c

    // Close original goal with composite proof (assigns meta + pops goal)
    // Part of #2154: type-check Eq.trans proof before accepting
    state.close_goal(&goal, proof)?;

    // Push subgoals (goal1 first so it's current)
    state.goals.push_front(Goal {
        meta_id: meta2,
        target: goal2_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    });
    state.goals.push_front(Goal {
        meta_id: meta1,
        target: goal1_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    });

    Ok(())
}

/// Helper to create Eq.refl proof term.
///
/// REQUIRES: `ty` is the Sort/Type of `val`; `val` is a well-formed expression
///
/// ENSURES: returns `@Eq.refl ty val`, a proof of `val = val`
pub(crate) fn make_eq_refl(state: &mut ProofState, ty: &Expr, val: &Expr) -> Expr {
    Expr::app(
        Expr::app(state.mk_const_str("Eq.refl"), ty.clone()),
        val.clone(),
    )
}

// ============================================================================
// CalcState: stateful builder for incremental calc chains
// ============================================================================

/// State for an in-progress calc block.
///
/// `CalcState` provides an incremental builder API for constructing calc chains
/// step by step, validating relation compatibility at each addition. This is
/// useful for elaboration contexts where steps arrive incrementally rather than
/// as a complete `Vec<CalcStep>`.
///
/// # Example (conceptual)
///
/// ```text
/// let mut cs = CalcState::new(a_expr);
/// cs.add_step(CalcStep { rel: CalcRel::Eq, rhs: b, justification: ... })?;
/// cs.add_step(CalcStep { rel: CalcRel::Le, rhs: c, justification: ... })?;
/// // cs.result_relation() == Some(CalcRel::Le)
/// cs.finish(&mut state)?;
/// ```
#[derive(Debug, Clone)]
pub struct CalcState {
    /// The starting left-hand side of the chain.
    start: Expr,
    /// Accumulated steps in order.
    steps: Vec<CalcStep>,
    /// The current right-hand side (becomes the next step's implicit LHS).
    current_rhs: Option<Expr>,
    /// The accumulated result relation after chaining all steps so far.
    current_rel: Option<CalcRel>,
}

impl CalcState {
    /// Create a new calc state with the given starting expression.
    ///
    /// REQUIRES: `start` is a well-formed expression
    /// ENSURES: `self.steps().is_empty()`
    /// ENSURES: `self.start() == &start`
    #[must_use]
    pub fn new(start: Expr) -> Self {
        CalcState {
            start,
            steps: Vec::new(),
            current_rhs: None,
            current_rel: None,
        }
    }

    /// Get the starting expression.
    pub fn start(&self) -> &Expr {
        &self.start
    }

    /// Get the accumulated steps.
    #[must_use]
    pub fn steps(&self) -> &[CalcStep] {
        &self.steps
    }

    /// Get the current right-hand side (the RHS of the last step added).
    ///
    /// Returns `None` if no steps have been added.
    #[must_use]
    pub fn current_rhs(&self) -> Option<&Expr> {
        self.current_rhs.as_ref()
    }

    /// Get the accumulated result relation after all steps so far.
    ///
    /// Returns `None` if no steps have been added.
    #[must_use]
    pub fn result_relation(&self) -> Option<CalcRel> {
        self.current_rel
    }

    /// Add a step to the calc chain, validating relation compatibility.
    ///
    /// For the first step, any relation is accepted. For subsequent steps,
    /// the relation pair `(current_rel, step.rel)` must have a valid
    /// transitivity rule in the calc trans table.
    ///
    /// REQUIRES: `step.rhs` is a well-formed expression
    /// ENSURES: on `Ok`, `self.steps().len()` increases by 1
    /// ENSURES: on `Ok`, `self.current_rhs() == Some(&step.rhs)`
    /// ENSURES: on `Err`, the state is unchanged
    pub fn add_step(&mut self, step: CalcStep) -> Result<(), TacticError> {
        if let Some(prev_rel) = self.current_rel {
            // Validate that the relation pair is supported
            let rule = lookup_trans_rule(prev_rel, step.rel).ok_or_else(|| {
                TacticError::InvalidTarget {
                    tactic: "calc".into(),
                    detail: format!(
                        "unsupported calc transitivity: {:?} followed by {:?}",
                        prev_rel, step.rel
                    ),
                }
            })?;
            self.current_rel = Some(rule.result_rel);
        } else {
            // First step: the result relation is just this step's relation
            self.current_rel = Some(step.rel);
        }

        self.current_rhs = Some(step.rhs.clone());
        self.steps.push(step);
        Ok(())
    }

    /// Finish the calc block, applying all accumulated steps to the current
    /// proof state goal.
    ///
    /// Delegates to `calc_block` with the accumulated start and steps.
    ///
    /// REQUIRES: at least one step has been added
    /// ENSURES: on `Ok`, the current goal is closed
    pub fn finish(self, state: &mut ProofState) -> TacticResult {
        calc_block(state, self.start, self.steps)
    }
}

/// Parse a relation name string into a `CalcRel`.
///
/// Accepts both symbol and name forms:
/// `"="`, `"Eq"` -> `Eq`; `"<="`, `"le"`, `"LE.le"` -> `Le`; etc.
///
/// ENSURES: Returns `Some` for recognized relation names, `None` otherwise.
#[must_use]
pub fn calc_rel_from_name(name: &str) -> Option<CalcRel> {
    match name {
        "=" | "Eq" | "eq" => Some(CalcRel::Eq),
        "<=" | "le" | "LE.le" => Some(CalcRel::Le),
        "<" | "lt" | "LT.lt" => Some(CalcRel::Lt),
        ">=" | "ge" | "GE.ge" => Some(CalcRel::Ge),
        ">" | "gt" | "GT.gt" => Some(CalcRel::Gt),
        "!=" | "ne" | "Ne" => Some(CalcRel::Ne),
        "iff" | "Iff" => Some(CalcRel::Iff),
        _ => None,
    }
}
