// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E-matching for quantifier instantiation in E-graphs.

use super::{EClassId, EGraph, Symbol};
use std::collections::HashMap;

/// A pattern for E-matching
///
/// Patterns are used to find substitutions in an E-graph that make a pattern
/// term match some e-class. This is the core of trigger-based quantifier
/// instantiation in SMT solvers.
///
/// # Example
///
/// Pattern `f(?x, ?y)` matches `f(a, b)` with substitution `{?x → a, ?y → b}`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    /// Pattern variable `?x` - matches any e-class
    Var(String),
    /// Constant/function symbol with pattern children
    App(Symbol, Vec<Pattern>),
}

impl Pattern {
    /// Create a pattern variable
    pub fn var(name: impl Into<String>) -> Self {
        Pattern::Var(name.into())
    }

    /// Create an application pattern
    pub fn app(symbol: impl Into<Symbol>, children: Vec<Pattern>) -> Self {
        Pattern::App(symbol.into(), children)
    }

    /// Create a constant pattern (0-ary application)
    pub fn constant(name: impl Into<Symbol>) -> Self {
        Pattern::App(name.into(), vec![])
    }

    /// Collect all pattern variables in this pattern
    pub fn variables(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_vars(&mut vars);
        vars
    }

    fn collect_vars(&self, vars: &mut Vec<String>) {
        match self {
            Pattern::Var(name) => {
                if !vars.contains(name) {
                    vars.push(name.clone());
                }
            }
            Pattern::App(_, children) => {
                for child in children {
                    child.collect_vars(vars);
                }
            }
        }
    }
}

/// A substitution mapping pattern variables to e-class IDs
#[derive(Clone, Debug, Default)]
pub struct Substitution {
    /// Mapping from variable name to e-class ID
    bindings: HashMap<String, EClassId>,
}

impl Substitution {
    /// Create an empty substitution
    pub fn new() -> Self {
        Substitution {
            bindings: HashMap::new(),
        }
    }

    /// Get the binding for a variable
    pub fn get(&self, var: &str) -> Option<EClassId> {
        self.bindings.get(var).copied()
    }

    /// Set the binding for a variable
    /// Returns false if the variable is already bound to a different class
    pub fn bind(&mut self, var: &str, class: EClassId) -> bool {
        if let Some(&existing) = self.bindings.get(var) {
            existing == class
        } else {
            self.bindings.insert(var.to_string(), class);
            true
        }
    }

    /// Check if a variable is bound
    pub fn is_bound(&self, var: &str) -> bool {
        self.bindings.contains_key(var)
    }

    /// Get all bindings
    pub fn bindings(&self) -> &HashMap<String, EClassId> {
        &self.bindings
    }

    /// Get the number of bindings
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if the substitution is empty
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

/// E-matching engine for pattern matching in E-graphs
///
/// This implements the classic E-matching algorithm from SMT solvers like Z3.
/// Given a pattern with variables, it finds all substitutions that make the
/// pattern equal to some e-class in the graph.
pub struct EMatcher<'a> {
    egraph: &'a EGraph,
}

impl<'a> EMatcher<'a> {
    /// Create a new E-matcher for the given e-graph
    pub fn new(egraph: &'a EGraph) -> Self {
        EMatcher { egraph }
    }

    /// Find all substitutions that make the pattern match some e-class
    pub fn find_matches(&self, pattern: &Pattern) -> Vec<(EClassId, Substitution)> {
        let mut matches = Vec::new();

        // Try matching against every e-class in the graph
        for &root_id in self.egraph.classes.keys() {
            let canonical = self.egraph.find_const(root_id);
            // Only try each canonical representative once
            if canonical == root_id {
                let mut subst = Substitution::new();
                if self.match_pattern(pattern, canonical, &mut subst) {
                    matches.push((canonical, subst));
                }
            }
        }

        matches
    }

    /// Try to match a pattern against a specific e-class
    pub fn match_against(&self, pattern: &Pattern, target: EClassId) -> Option<Substitution> {
        let mut subst = Substitution::new();
        if self.match_pattern(pattern, self.egraph.find_const(target), &mut subst) {
            Some(subst)
        } else {
            None
        }
    }

    /// Core matching algorithm
    fn match_pattern(&self, pattern: &Pattern, class: EClassId, subst: &mut Substitution) -> bool {
        let class = self.egraph.find_const(class);

        match pattern {
            Pattern::Var(name) => {
                // Pattern variable: either bind it or check consistency
                subst.bind(name, class)
            }
            Pattern::App(symbol, children) => {
                // Application pattern: find a matching e-node in the class
                if let Some(eclass) = self.egraph.classes.get(&class) {
                    for node in &eclass.nodes {
                        if node.symbol == *symbol && node.children.len() == children.len() {
                            // Try to match all children
                            let mut local_subst = subst.clone();
                            let mut all_match = true;

                            for (pat_child, &node_child) in
                                children.iter().zip(node.children.iter())
                            {
                                if !self.match_pattern(pat_child, node_child, &mut local_subst) {
                                    all_match = false;
                                    break;
                                }
                            }

                            if all_match {
                                // Commit the local substitution
                                *subst = local_subst;
                                return true;
                            }
                        }
                    }
                }
                false
            }
        }
    }

    /// Find all matches for a multi-pattern (conjunction of patterns)
    pub fn find_multi_matches(&self, patterns: &[Pattern]) -> Vec<Substitution> {
        if patterns.is_empty() {
            return vec![Substitution::new()];
        }

        // Start with matches for the first pattern
        let first_matches = self.find_matches(&patterns[0]);
        if patterns.len() == 1 {
            return first_matches.into_iter().map(|(_, s)| s).collect();
        }

        // Filter and extend with remaining patterns
        let mut results = Vec::new();
        for (_, subst) in first_matches {
            if self.extend_multi_match(&patterns[1..], subst, &mut results) {
                // Continue collecting all matches
            }
        }

        results
    }

    /// Extend a partial substitution with remaining patterns
    fn extend_multi_match(
        &self,
        patterns: &[Pattern],
        subst: Substitution,
        results: &mut Vec<Substitution>,
    ) -> bool {
        if patterns.is_empty() {
            results.push(subst);
            return true;
        }

        let pattern = &patterns[0];
        let remaining = &patterns[1..];

        // Find matches for this pattern that are consistent with current substitution
        let matches = self.find_matches(pattern);
        let mut found_any = false;

        for (_, new_subst) in matches {
            // Check if new substitution is compatible with existing one
            let mut combined = subst.clone();
            let mut compatible = true;

            for (var, class) in new_subst.bindings() {
                if !combined.bind(var, *class) {
                    compatible = false;
                    break;
                }
            }

            if compatible {
                found_any = true;
                self.extend_multi_match(remaining, combined, results);
            }
        }

        found_any
    }
}

/// A trigger pattern for quantifier instantiation
///
/// Triggers are patterns that, when matched, indicate a useful instantiation
/// of a quantified formula.
#[derive(Clone, Debug)]
pub struct Trigger {
    /// The pattern(s) that must match (multi-trigger if > 1)
    pub patterns: Vec<Pattern>,
}

impl Trigger {
    /// Create a single-pattern trigger
    pub fn single(pattern: Pattern) -> Self {
        Trigger {
            patterns: vec![pattern],
        }
    }

    /// Create a multi-pattern trigger
    pub fn multi(patterns: Vec<Pattern>) -> Self {
        Trigger { patterns }
    }

    /// Get all variables bound by this trigger
    pub fn variables(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for p in &self.patterns {
            for v in p.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars
    }
}
