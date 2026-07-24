// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trigger pattern extraction for E-matching
//!
//! Extracts trigger patterns from quantified formulas for E-matching-based
//! quantifier instantiation. Includes pattern scoring and selection.

mod normalize;

use clean_kernel::{Expr, ExprKind};
use normalize::{collect_trigger_app_args, deep_strip_wrappers, strip_trigger_wrappers};

use super::expr_classifier::is_theory_const_name;
use super::SmtBridge;

// ============================================================================
// Standalone trigger types
// ============================================================================

/// A candidate trigger pattern extracted from a quantified formula
#[derive(Debug, Clone)]
pub(crate) struct TriggerPattern {
    /// The expression pattern
    pub(crate) pattern: Expr,
    /// Bound variables that appear in this pattern
    pub(crate) bound_vars: Vec<u32>,
    /// Quality score (higher is better)
    pub(crate) score: i32,
}

impl TriggerPattern {
    /// Create a new trigger pattern
    pub(crate) fn new(pattern: Expr, bound_vars: Vec<u32>) -> Self {
        let normalized = deep_strip_wrappers(&pattern);
        let score = Self::compute_score(&normalized, &bound_vars);
        TriggerPattern {
            pattern: normalized,
            bound_vars,
            score,
        }
    }

    /// Compute quality score for a trigger pattern
    ///
    /// Better triggers:
    /// - Contain all bound variables (required)
    /// - Are function applications (not just variables)
    /// - Are smaller (fewer nodes)
    /// - Don't contain complex sub-patterns
    fn compute_score(pattern: &Expr, bound_vars: &[u32]) -> i32 {
        let normalized = strip_trigger_wrappers(pattern);
        let mut score = 0;

        // Penalize patterns that don't contain all bound variables
        // (This shouldn't happen if extraction is correct, but safety check)
        let vars_in_pattern = Self::collect_bvars(pattern);
        for bv in bound_vars {
            if !vars_in_pattern.contains(bv) {
                score -= 100;
            }
        }

        // Prefer function applications over variables
        if matches!(normalized.kind(), ExprKind::App(_, _)) {
            score += 10;
        }

        // Prefer smaller patterns (fewer nodes)
        let size = Self::pattern_size(pattern);
        score -= size as i32;

        // Bonus for containing constants (more selective)
        if Self::has_constant(pattern) {
            score += 5;
        }

        score
    }

    /// Collect all bound variables in an expression
    fn collect_bvars(expr: &Expr) -> Vec<u32> {
        let mut vars = Vec::new();
        Self::collect_bvars_rec(expr, &mut vars);
        vars
    }

    fn collect_bvars_rec(expr: &Expr, vars: &mut Vec<u32>) {
        crate::bridge::stack_safe(|| match expr.kind() {
            ExprKind::BVar(idx) if !vars.contains(idx) => {
                vars.push(*idx);
            }
            ExprKind::App(f, a) => {
                Self::collect_bvars_rec(f, vars);
                Self::collect_bvars_rec(a, vars);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                Self::collect_bvars_rec(ty, vars);
                Self::collect_bvars_rec(body, vars);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                Self::collect_bvars_rec(ty, vars);
                Self::collect_bvars_rec(val, vars);
                Self::collect_bvars_rec(body, vars);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                Self::collect_bvars_rec(inner, vars);
            }
            _ => {}
        })
    }

    /// Count nodes in a pattern
    fn pattern_size(expr: &Expr) -> usize {
        crate::bridge::stack_safe(|| match expr.kind() {
            ExprKind::App(f, a) => 1 + Self::pattern_size(f) + Self::pattern_size(a),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                1 + Self::pattern_size(ty) + Self::pattern_size(body)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                1 + Self::pattern_size(ty) + Self::pattern_size(val) + Self::pattern_size(body)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                Self::pattern_size(inner)
            }
            _ => 1,
        })
    }

    /// Check if pattern contains a constant (more selective)
    fn has_constant(expr: &Expr) -> bool {
        crate::bridge::stack_safe(|| match expr.kind() {
            ExprKind::Const(_, _) => true,
            ExprKind::App(f, a) => Self::has_constant(f) || Self::has_constant(a),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                Self::has_constant(ty) || Self::has_constant(body)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                Self::has_constant(ty) || Self::has_constant(val) || Self::has_constant(body)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                Self::has_constant(inner)
            }
            _ => false,
        })
    }
}

/// Extractor for trigger patterns from quantified formula bodies
struct TriggerExtractor<'a> {
    /// The bound variables we need to match
    bound_vars: &'a [u32],
}

impl<'a> TriggerExtractor<'a> {
    fn new(bound_vars: &'a [u32]) -> Self {
        TriggerExtractor { bound_vars }
    }

    /// Extract trigger patterns from an expression
    fn extract(&mut self, expr: &Expr, triggers: &mut Vec<TriggerPattern>) {
        crate::bridge::stack_safe(|| {
            let normalized = strip_trigger_wrappers(expr);
            // First, check if this expression itself is a good trigger
            if self.is_valid_trigger(normalized) {
                let vars = TriggerPattern::collect_bvars(normalized);
                // Only add if it contains at least one bound variable
                if vars.iter().any(|v| self.bound_vars.contains(v)) {
                    triggers.push(TriggerPattern::new(normalized.clone(), vars));
                }
            }

            // Then recursively explore sub-expressions
            match expr.kind() {
                ExprKind::App(f, a) => {
                    self.extract(f, triggers);
                    self.extract(a, triggers);
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    self.extract(ty, triggers);
                    self.extract(body, triggers);
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    self.extract(ty, triggers);
                    self.extract(val, triggers);
                    self.extract(body, triggers);
                }
                ExprKind::Proj(_, _, inner)
                | ExprKind::MData(_, inner)
                | ExprKind::Squash(inner) => {
                    self.extract(inner, triggers);
                }
                _ => {}
            }
        })
    }

    /// Check if an expression is a valid trigger
    ///
    /// Valid triggers are:
    /// - Function applications (most common)
    /// - Not theory symbols (those handled by theory solvers)
    /// - Not lambdas/pis (structural, not instantiatable)
    ///
    /// Theory symbol detection uses `is_theory_const_name` from the shared
    /// ExprClassifier, which is the single source of truth for recognized
    /// constant names (Eq, And, LT.lt, Add.add, HEq, etc.).
    fn is_valid_trigger(&self, expr: &Expr) -> bool {
        match strip_trigger_wrappers(expr).kind() {
            ExprKind::App(_f, _) => {
                let head = Self::get_head(expr);
                match head.kind() {
                    ExprKind::Const(name, _) => !is_theory_const_name(&name.to_string()),
                    ExprKind::FVar(_) => true,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Get the head symbol of an application chain, stripping transparent wrappers
    fn get_head(expr: &Expr) -> Expr {
        crate::bridge::stack_safe(|| {
            let mut current = expr;
            loop {
                current = strip_trigger_wrappers(current);
                match current.kind() {
                    ExprKind::App(f, _) => current = f,
                    _ => return current.clone(),
                }
            }
        })
    }
}

// ============================================================================
// SmtBridge trigger extraction methods
// ============================================================================

impl<'env> SmtBridge<'env> {
    // ========================================================================
    // Trigger Pattern Extraction for E-Matching
    // ========================================================================

    /// Extract trigger patterns from a quantified formula body
    ///
    /// Triggers are sub-terms that can be used for E-matching-based quantifier
    /// instantiation. Good triggers should:
    /// 1. Contain all bound variables
    /// 2. Be as small as possible (to avoid spurious matches)
    /// 3. Not be pure (not just variables or constants)
    ///
    /// For a formula `∀ x. P(f(x), g(x))`, good triggers would include
    /// `f(x)` and `g(x)` since they contain `x` and are function applications.
    pub(crate) fn extract_triggers(&self, body: &Expr, bound_vars: &[u32]) -> Vec<TriggerPattern> {
        let mut triggers = Vec::new();
        let mut extractor = TriggerExtractor::new(bound_vars);
        extractor.extract(body, &mut triggers);

        // Score and deduplicate triggers
        triggers.sort_by_key(|b| std::cmp::Reverse(b.score));
        triggers.dedup_by(|a, b| a.pattern == b.pattern);

        triggers
    }

    /// Extract triggers and convert to E-graph patterns
    pub(crate) fn extract_ematch_triggers(
        &self,
        body: &Expr,
        bound_vars: &[u32],
    ) -> Vec<crate::egraph::Trigger> {
        let patterns = self.extract_triggers(body, bound_vars);
        if patterns.is_empty() {
            return Vec::new();
        }

        let required_vars: Vec<String> = bound_vars.iter().map(|i| format!("?x{i}")).collect();

        // Collect all valid triggers with their scores
        let mut scored_triggers: Vec<(crate::egraph::Trigger, i32)> = Vec::new();

        // Prefer single-pattern triggers that already cover all bound variables
        for pat in &patterns {
            if let Some(trigger) = self.trigger_from_patterns(&[pat]) {
                if self.trigger_has_all_vars(&trigger, &required_vars) {
                    let score = self.score_trigger_combination(&[pat]);
                    scored_triggers.push((trigger, score));
                }
            }
        }

        // If we didn't find a single trigger covering everything, try combinations
        if scored_triggers.is_empty() && bound_vars.len() > 1 {
            // Try pairs first
            for i in 0..patterns.len() {
                for j in (i + 1)..patterns.len() {
                    let combo = [&patterns[i], &patterns[j]];
                    if let Some(trigger) = self.trigger_from_patterns(&combo) {
                        if self.trigger_has_all_vars(&trigger, &required_vars) {
                            let score = self.score_trigger_combination(&combo);
                            scored_triggers.push((trigger, score));
                        }
                    }
                }
            }

            // As a fallback, try triples for harder cases
            if scored_triggers.is_empty() {
                for i in 0..patterns.len() {
                    for j in (i + 1)..patterns.len() {
                        for k in (j + 1)..patterns.len() {
                            let combo = [&patterns[i], &patterns[j], &patterns[k]];
                            if let Some(trigger) = self.trigger_from_patterns(&combo) {
                                if self.trigger_has_all_vars(&trigger, &required_vars) {
                                    let score = self.score_trigger_combination(&combo);
                                    scored_triggers.push((trigger, score));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Sort by score (higher is better) and extract triggers
        scored_triggers.sort_by_key(|b| std::cmp::Reverse(b.1));
        let mut triggers: Vec<_> = scored_triggers.into_iter().map(|(t, _)| t).collect();

        // Fallback: keep legacy behavior if we couldn't cover all bound vars
        if triggers.is_empty() {
            for pat in &patterns {
                if let Some(pattern) = self.trigger_pattern_to_ematch_pattern(pat) {
                    triggers.push(crate::egraph::Trigger::single(pattern));
                }
            }
        }

        triggers
    }

    /// Score a combination of trigger patterns for E-matching quality.
    ///
    /// Better combinations:
    /// - Have smaller total size (fewer E-graph traversals)
    /// - Use patterns with higher individual scores
    /// - Have fewer patterns (simpler matching)
    /// - Minimize variable overlap (each pattern contributes unique variables)
    pub(crate) fn score_trigger_combination(&self, patterns: &[&TriggerPattern]) -> i32 {
        let mut score = 0;

        // Sum of individual pattern scores
        for pat in patterns {
            score += pat.score;
        }

        // Penalty for multiple patterns (prefer single-pattern triggers)
        // Each additional pattern adds matching overhead
        score -= (patterns.len() as i32 - 1) * 5;

        // Bonus for minimal pattern count that covers all vars
        if patterns.len() == 1 {
            score += 20;
        } else if patterns.len() == 2 {
            score += 10;
        }

        // Penalty for variable overlap (inefficient matching)
        // If two patterns share bound variables, that's wasteful
        let mut seen_vars: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut overlap_count = 0;
        for pat in patterns {
            for &bv in &pat.bound_vars {
                if !seen_vars.insert(bv) {
                    overlap_count += 1;
                }
            }
        }
        score -= overlap_count * 3;

        score
    }

    /// Build an E-matching trigger from one or more trigger patterns
    pub(crate) fn trigger_from_patterns(
        &self,
        patterns: &[&TriggerPattern],
    ) -> Option<crate::egraph::Trigger> {
        let mut ematch_patterns = Vec::new();
        for pat in patterns {
            ematch_patterns.push(self.trigger_pattern_to_ematch_pattern(pat)?);
        }

        if ematch_patterns.len() == 1 {
            Some(crate::egraph::Trigger::single(ematch_patterns.remove(0)))
        } else {
            Some(crate::egraph::Trigger::multi(ematch_patterns))
        }
    }

    /// Convert a TriggerPattern to an E-matching Pattern
    fn trigger_pattern_to_ematch_pattern(
        &self,
        trigger: &TriggerPattern,
    ) -> Option<crate::egraph::Pattern> {
        self.expr_to_pattern(&trigger.pattern, &trigger.bound_vars)
    }

    /// Check whether a trigger covers all required bound variables
    fn trigger_has_all_vars(
        &self,
        trigger: &crate::egraph::Trigger,
        required_vars: &[String],
    ) -> bool {
        let vars = trigger.variables();
        required_vars.iter().all(|req| vars.contains(req))
    }

    /// Convert an expression to an E-matching pattern
    ///
    /// The `_bound_vars` parameter is passed through recursion for potential
    /// future use in distinguishing between different bound variables.
    #[allow(clippy::only_used_in_recursion)]
    fn expr_to_pattern(&self, expr: &Expr, _bound_vars: &[u32]) -> Option<crate::egraph::Pattern> {
        crate::bridge::stack_safe(|| match strip_trigger_wrappers(expr).kind() {
            ExprKind::BVar(idx) => {
                // Bound variable becomes a pattern variable
                let var_name = format!("?x{idx}");
                Some(crate::egraph::Pattern::var(var_name))
            }
            ExprKind::FVar(fv) => {
                // Free variable becomes a constant pattern
                let name = format!("fvar_{}", fv.as_u64());
                Some(crate::egraph::Pattern::constant(name))
            }
            ExprKind::Const(name, _) => {
                // Constant becomes a constant pattern
                Some(crate::egraph::Pattern::constant(name.to_string()))
            }
            ExprKind::App(_func, _arg) => {
                // Application: recursively convert
                // Collect all arguments and the head symbol
                let (head, args) = collect_trigger_app_args(expr);
                let head_name = match head.kind() {
                    ExprKind::Const(name, _) => name.to_string(),
                    ExprKind::FVar(fv) => format!("fvar_{}", fv.as_u64()),
                    _ => return None, // Only handle function applications with known heads
                };

                let mut arg_patterns = Vec::new();
                for arg in args {
                    arg_patterns.push(self.expr_to_pattern(arg, _bound_vars)?);
                }

                Some(crate::egraph::Pattern::app(head_name, arg_patterns))
            }
            ExprKind::Lit(lit) => {
                // Literal becomes a constant
                let name = match &lit {
                    clean_kernel::Literal::Nat(n) => format!("nat_{n}"),
                    clean_kernel::Literal::String(s) => format!("str_{s}"),
                };
                Some(crate::egraph::Pattern::constant(name))
            }
            _ => None, // Lambda, Pi, Let, Sort not convertible to patterns
        })
    }
}
