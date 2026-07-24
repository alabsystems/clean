// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier instantiation priority scoring and goal-directed instantiation.
//!
//! - [`QuantifierPriorityScorer`]: Heuristic scoring for quantifier instantiation order
//! - [`GoalPatterns`] / [`GoalPatternExtractor`]: Goal-directed pattern extraction
//! - [`GoalDirectedScorer`]: Combined base + goal-relevance scoring

use std::collections::{HashMap, HashSet};

use clean_kernel::{Expr, ExprKind};

use crate::smt::TermId;

use super::expr_classifier::LogicalForm;
use super::{ExprKey, PendingForall};

// ============================================================================
// Quantifier Instantiation Priority Scoring
// ============================================================================

/// Heuristics for scoring quantifier instantiation priority.
///
/// The priority score determines the order in which pending universal
/// quantifiers are tried for E-matching instantiation. Higher scores
/// are instantiated first.
///
/// # Scoring Factors
///
/// Positive factors (increase priority):
/// - Good trigger quality (selective, ground-matchable patterns)
/// - Fewer bound variables (simpler instantiation)
/// - Single-pattern triggers (more efficient matching)
///
/// Negative factors (decrease priority):
/// - Many bound variables (expensive instantiation)
/// - Multi-pattern triggers (complex matching)
/// - High instantiation count (fairness - give other foralls a chance)
/// - Complex body (more overhead per instantiation)
#[derive(Clone, Debug, Default)]
pub(crate) struct QuantifierPriorityScorer {
    /// Weight for trigger quality score
    pub(crate) trigger_quality_weight: i32,
    /// Weight for bound variable count (negative = penalize many vars)
    pub(crate) bound_var_count_weight: i32,
    /// Weight for instantiation count (negative = penalize repeated use)
    pub(crate) instantiation_count_weight: i32,
    /// Bonus for single-pattern triggers
    pub(crate) single_trigger_bonus: i32,
    /// Penalty per additional trigger pattern
    pub(crate) multi_trigger_penalty: i32,
}

impl QuantifierPriorityScorer {
    /// Create a new scorer with default weights.
    ///
    /// Default weights are tuned for typical SMT-style quantifier instantiation:
    /// - Prefer simpler quantifiers (fewer variables)
    /// - Prefer quantifiers with good triggers
    /// - Ensure fairness by penalizing repeated instantiation
    pub fn new() -> Self {
        Self {
            trigger_quality_weight: 2,
            bound_var_count_weight: -5,
            instantiation_count_weight: -10,
            single_trigger_bonus: 15,
            multi_trigger_penalty: 3,
        }
    }

    /// Score a pending forall for instantiation priority.
    ///
    /// Returns an integer score where higher values indicate
    /// higher priority for instantiation.
    pub(super) fn score(&self, pending: &PendingForall) -> i32 {
        let mut score: i32 = 0;

        // Trigger quality: use the best trigger's score
        // Higher depth and more children indicate more selective patterns
        let best_trigger_score = pending
            .triggers
            .iter()
            .map(|t| {
                // Sum pattern scores in the trigger
                t.patterns.iter().map(Self::pattern_score).sum::<i32>()
            })
            .max()
            .unwrap_or(0);
        score += best_trigger_score * self.trigger_quality_weight;

        // Bound variable count: fewer is better
        score += (pending.bound_vars.len() as i32) * self.bound_var_count_weight;

        // Single-pattern trigger bonus
        if pending.triggers.iter().any(|t| t.patterns.len() == 1) {
            score += self.single_trigger_bonus;
        }

        // Multi-trigger penalty: penalize each pattern beyond the first
        let min_patterns = pending
            .triggers
            .iter()
            .map(|t| t.patterns.len())
            .min()
            .unwrap_or(0);
        if min_patterns > 1 {
            score -= ((min_patterns - 1) as i32) * self.multi_trigger_penalty;
        }

        // Fairness: penalize quantifiers that have been instantiated many times
        score += (pending.instantiation_count as i32) * self.instantiation_count_weight;

        score
    }

    /// Compute a quality score for a single E-matching pattern.
    ///
    /// Higher scores indicate more selective patterns:
    /// - Deeper patterns are more selective (more structure to match)
    /// - More children means more constraints
    /// - Variables alone score 0 (match anything)
    pub(super) fn pattern_score(pattern: &crate::egraph::Pattern) -> i32 {
        use crate::egraph::Pattern;
        match pattern {
            Pattern::Var(_) => 0,
            Pattern::App(_, children) => {
                // Base score for having a function symbol
                let mut score = 1;
                // Add depth bonus (recursive)
                for child in children {
                    score += Self::pattern_score(child);
                }
                // Add arity bonus
                score += children.len() as i32;
                score
            }
        }
    }
}

// ============================================================================
// Goal-Directed Quantifier Instantiation
// ============================================================================

/// Patterns extracted from the goal for guiding quantifier instantiation.
///
/// Goal-directed instantiation works "backward" from the goal:
/// - Extract patterns from terms in the goal (especially function applications)
/// - Prioritize quantifier instantiations that produce terms matching goal patterns
/// - This focuses proof search on instantiations likely to be useful
///
/// # Example
///
/// If proving `f(a) = g(b)` with hypothesis `∀x. P(x) → Q(f(x))`:
/// - Goal patterns include: `f(a)`, `g(b)`
/// - Instantiation with `x := a` is prioritized because `f(a)` matches the goal
#[derive(Clone, Debug, Default)]
pub(crate) struct GoalPatterns {
    /// Ground terms from the goal (function applications and constants)
    pub(crate) ground_terms: Vec<GroundTermPattern>,
    /// Function symbols that appear in the goal (for partial matching)
    pub(crate) function_symbols: HashSet<crate::egraph::Symbol>,
}

/// A ground term pattern extracted from the goal
#[derive(Clone, Debug)]
pub(crate) struct GroundTermPattern {
    /// The function symbol at the root
    pub(crate) symbol: crate::egraph::Symbol,
    /// Arity of the function application
    pub(crate) arity: usize,
}

impl GoalPatterns {
    /// Create empty goal patterns
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if any goal patterns exist
    pub fn is_empty(&self) -> bool {
        self.ground_terms.is_empty() && self.function_symbols.is_empty()
    }

    /// Check if a symbol appears in the goal
    #[cfg(test)]
    pub fn contains_symbol(&self, sym: &crate::egraph::Symbol) -> bool {
        self.function_symbols.contains(sym)
    }

    /// Count how many goal patterns match a given trigger pattern.
    ///
    /// This computes a relevance score for a trigger pattern:
    /// - Higher score = trigger is more likely to produce goal-relevant instantiations
    pub fn relevance_score(&self, trigger: &crate::egraph::Trigger) -> i32 {
        let mut score = 0;

        for pattern in &trigger.patterns {
            score += self.pattern_relevance(pattern);
        }

        score
    }

    /// Compute relevance of a single pattern to the goal
    fn pattern_relevance(&self, pattern: &crate::egraph::Pattern) -> i32 {
        use crate::egraph::Pattern;
        match pattern {
            Pattern::Var(_) => 0, // Variables match anything, no specific relevance
            Pattern::App(sym, children) => {
                let mut score = 0;

                // Bonus if this function symbol appears in the goal
                if self.function_symbols.contains(sym) {
                    score += 10;
                }

                // Check if there's a ground term with matching symbol and arity
                let has_matching_ground = self
                    .ground_terms
                    .iter()
                    .any(|gt| gt.symbol == *sym && gt.arity == children.len());
                if has_matching_ground {
                    score += 20; // Strong bonus for exact structural match
                }

                // Recursive relevance from children
                for child in children {
                    score += self.pattern_relevance(child);
                }

                score
            }
        }
    }
}

/// Extracts goal patterns from a classified proposition.
///
/// This analyzer walks the goal expression and extracts:
/// 1. Ground terms (function applications with known children)
/// 2. Function symbols (for partial matching)
pub(crate) struct GoalPatternExtractor<'a> {
    /// Reference to the SMT bridge for term lookup
    expr_to_term: &'a HashMap<ExprKey, TermId>,
    /// Extracted patterns
    patterns: GoalPatterns,
}

impl<'a> GoalPatternExtractor<'a> {
    /// Create a new extractor
    pub(super) fn new(expr_to_term: &'a HashMap<ExprKey, TermId>) -> Self {
        Self {
            expr_to_term,
            patterns: GoalPatterns::new(),
        }
    }

    /// Extract patterns from a classified proposition
    pub(super) fn extract(&mut self, prop: &LogicalForm) -> GoalPatterns {
        self.extract_from_prop(prop);
        std::mem::take(&mut self.patterns)
    }

    /// Recursively extract patterns from a proposition
    fn extract_from_prop(&mut self, prop: &LogicalForm) {
        match prop {
            LogicalForm::Eq { ty: _, lhs, rhs } | LogicalForm::Neq { ty: _, lhs, rhs } => {
                self.extract_from_term(lhs);
                self.extract_from_term(rhs);
            }
            LogicalForm::Lt { ty: _, lhs, rhs }
            | LogicalForm::Le { ty: _, lhs, rhs }
            | LogicalForm::Gt { ty: _, lhs, rhs }
            | LogicalForm::Ge { ty: _, lhs, rhs } => {
                self.extract_from_term(lhs);
                self.extract_from_term(rhs);
            }
            LogicalForm::And(p, q)
            | LogicalForm::Or(p, q)
            | LogicalForm::Implies(p, q)
            | LogicalForm::Iff(p, q) => {
                self.extract_from_expr(p);
                self.extract_from_expr(q);
            }
            LogicalForm::Not(p) => {
                self.extract_from_expr(p);
            }
            LogicalForm::Forall {
                binder_type, body, ..
            }
            | LogicalForm::Exists {
                binder_type, body, ..
            } => {
                self.extract_from_term(binder_type);
                self.extract_from_expr(body);
            }
            LogicalForm::Atom(e) => {
                self.extract_from_term(e);
            }
            LogicalForm::True | LogicalForm::False => {}
            // Arithmetic: extract from operands
            LogicalForm::Add { lhs, rhs, .. }
            | LogicalForm::Sub { lhs, rhs, .. }
            | LogicalForm::Mul { lhs, rhs, .. }
            | LogicalForm::Div { lhs, rhs, .. }
            | LogicalForm::Mod { lhs, rhs, .. } => {
                self.extract_from_term(lhs);
                self.extract_from_term(rhs);
            }
            LogicalForm::Neg { inner, .. } => {
                self.extract_from_term(inner);
            }
        }
    }

    /// Extract patterns from an expression (for sub-propositions)
    fn extract_from_expr(&mut self, expr: &Expr) {
        // Try to classify as a proposition first
        // For now, treat as a term
        self.extract_from_term(expr);
    }

    /// Extract patterns from a term expression
    fn extract_from_term(&mut self, expr: &Expr) {
        match expr.kind() {
            ExprKind::App(_, _) => {
                // Collect the function and arguments
                let (head, args) = super::translate::collect_app_args(expr);

                // Extract symbol from head
                if let Some(sym) = Self::expr_to_symbol(&head) {
                    self.patterns.function_symbols.insert(sym.clone());

                    // Collect child term IDs if available
                    let mut child_ids = Vec::new();
                    let mut all_children_known = true;

                    for arg in &args {
                        if let Some(key) = ExprKey::from_expr(arg) {
                            if let Some(&tid) = self.expr_to_term.get(&key) {
                                child_ids.push(tid);
                            } else {
                                all_children_known = false;
                            }
                        } else {
                            all_children_known = false;
                        }
                    }

                    // Add ground term pattern if we know all children
                    if all_children_known && !child_ids.is_empty() {
                        self.patterns.ground_terms.push(GroundTermPattern {
                            symbol: sym,
                            arity: args.len(),
                        });
                    }
                }

                // Recursively extract from arguments
                for arg in args {
                    self.extract_from_term(&arg);
                }
            }
            ExprKind::Const(name, _) => {
                // Constants become symbols
                let sym = crate::egraph::Symbol::new(name.to_string());
                self.patterns.function_symbols.insert(sym);
            }
            // Free/bound variables, sorts, and literals are not useful as patterns
            ExprKind::FVar(_) | ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                self.extract_from_term(ty);
                self.extract_from_term(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                self.extract_from_term(ty);
                self.extract_from_term(val);
                self.extract_from_term(body);
            }
            ExprKind::Proj(_, _, base) => {
                self.extract_from_term(base);
            }
            // MData and Squash are transparent - extract from inner
            ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                self.extract_from_term(inner);
            }
            // Mode-specific expressions - no pattern extraction yet
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. }
            | ExprKind::SProp => {}
        }
    }

    /// Convert an expression head to a Symbol
    fn expr_to_symbol(expr: &Expr) -> Option<crate::egraph::Symbol> {
        match expr.kind() {
            ExprKind::Const(name, _) => Some(crate::egraph::Symbol::new(name.to_string())),
            ExprKind::FVar(fv) => Some(crate::egraph::Symbol::new(format!("fvar_{}", fv.as_u64()))),
            _ => None,
        }
    }
}

/// Scorer for goal-directed quantifier instantiation.
///
/// Combines the standard priority scoring with goal-relevance bonuses.
#[derive(Clone, Debug)]
pub(crate) struct GoalDirectedScorer {
    /// Base priority scorer
    base_scorer: QuantifierPriorityScorer,
    /// Goal patterns for relevance computation
    goal_patterns: GoalPatterns,
    /// Weight for goal relevance bonus
    goal_relevance_weight: i32,
}

impl GoalDirectedScorer {
    /// Create a new goal-directed scorer
    pub fn new(goal_patterns: GoalPatterns) -> Self {
        Self {
            base_scorer: QuantifierPriorityScorer::new(),
            goal_patterns,
            goal_relevance_weight: 5,
        }
    }

    /// Create a scorer with custom weights
    #[cfg(test)]
    pub fn with_weights(
        goal_patterns: GoalPatterns,
        base_scorer: QuantifierPriorityScorer,
        goal_relevance_weight: i32,
    ) -> Self {
        Self {
            base_scorer,
            goal_patterns,
            goal_relevance_weight,
        }
    }

    /// Score a pending forall with goal-directed bonus
    pub(super) fn score(&self, pending: &PendingForall) -> i32 {
        // Start with base priority
        let mut score = self.base_scorer.score(pending);

        // Add goal relevance bonus for each trigger
        for trigger in &pending.triggers {
            let relevance = self.goal_patterns.relevance_score(trigger);
            score += relevance * self.goal_relevance_weight;
        }

        score
    }

    /// Check if goal patterns are available
    #[cfg(test)]
    pub fn has_goal_patterns(&self) -> bool {
        !self.goal_patterns.is_empty()
    }
}
