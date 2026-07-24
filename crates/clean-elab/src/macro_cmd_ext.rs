// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended macro command analysis: expansion tracing, hygiene validation,
//! dependency graphs, template extraction, and optimization hints.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use crate::macro_cmd::{
    expand_macro, MacroDef, MacroError, MacroPatternPart, MacroRegistry, MacroScoping,
};
use clean_parser::SurfaceExpr;

#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum MacroAnalysisError {
    #[error("expansion trace failed for macro '{name}': {source}")]
    ExpansionFailed {
        name: String,
        #[source]
        source: MacroError,
    },
    #[error("macro '{name}' exceeded max expansion depth {max_depth}")]
    DepthExceeded { name: String, max_depth: usize },
    #[error("cycle detected in macro dependencies: {cycle:?}")]
    CycleDetected { cycle: Vec<String> },
    #[error("hygiene violation in macro '{macro_name}': {detail}")]
    HygieneViolation { macro_name: String, detail: String },
}

#[derive(Debug, Clone)]
pub(crate) struct ExpansionStep {
    pub(crate) macro_name: String,
    pub(crate) arg_count: usize,
    pub(crate) result: SurfaceExpr,
    pub(crate) depth: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct ExpansionTrace {
    pub(crate) steps: Vec<ExpansionStep>,
    pub(crate) final_expr: SurfaceExpr,
    pub(crate) max_depth: usize,
}

/// Expand a macro with full tracing of each step.
pub(crate) fn traced_expand(
    registry: &MacroRegistry,
    name: &str,
    args: &[SurfaceExpr],
) -> Result<ExpansionTrace, MacroAnalysisError> {
    let result =
        expand_macro(registry, name, args).map_err(|e| MacroAnalysisError::ExpansionFailed {
            name: name.to_owned(),
            source: e,
        })?;
    let step = ExpansionStep {
        macro_name: name.to_owned(),
        arg_count: args.len(),
        result: result.clone(),
        depth: 0,
    };
    Ok(ExpansionTrace {
        steps: vec![step],
        final_expr: result,
        max_depth: 0,
    })
}

/// Expand with depth-limited recursive tracing through chained macros.
pub(crate) fn traced_expand_recursive(
    registry: &MacroRegistry,
    name: &str,
    args: &[SurfaceExpr],
    max_depth: usize,
) -> Result<ExpansionTrace, MacroAnalysisError> {
    let mut steps = Vec::new();
    let final_expr = trace_step(registry, name, args, 0, max_depth, &mut steps)?;
    let max_reached = steps.iter().map(|s| s.depth).max().unwrap_or(0);
    Ok(ExpansionTrace {
        steps,
        final_expr,
        max_depth: max_reached,
    })
}

fn trace_step(
    registry: &MacroRegistry,
    name: &str,
    args: &[SurfaceExpr],
    depth: usize,
    max_depth: usize,
    steps: &mut Vec<ExpansionStep>,
) -> Result<SurfaceExpr, MacroAnalysisError> {
    if depth > max_depth {
        return Err(MacroAnalysisError::DepthExceeded {
            name: name.to_owned(),
            max_depth,
        });
    }
    let result =
        expand_macro(registry, name, args).map_err(|e| MacroAnalysisError::ExpansionFailed {
            name: name.to_owned(),
            source: e,
        })?;
    steps.push(ExpansionStep {
        macro_name: name.to_owned(),
        arg_count: args.len(),
        result: result.clone(),
        depth,
    });
    if let Some(inner_name) = extract_head_name(&result) {
        if registry.is_registered(&inner_name) && inner_name != name {
            let inner_args = extract_app_args(&result);
            return trace_step(
                registry,
                &inner_name,
                &inner_args,
                depth + 1,
                max_depth,
                steps,
            );
        }
    }
    Ok(result)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum MacroPattern {
    Terminal,
    SelfRecursive,
    DelegatesToOther,
    Identity,
}

#[must_use]
pub(crate) fn classify_macro(registry: &MacroRegistry, def: &MacroDef) -> MacroPattern {
    let names = collect_names(&def.expansion_template);
    if names.is_empty() {
        return if matches!(&def.expansion_template, SurfaceExpr::Hole(_)) {
            MacroPattern::Identity
        } else {
            MacroPattern::Terminal
        };
    }
    if names.contains(&def.name) {
        return MacroPattern::SelfRecursive;
    }
    if names.iter().any(|n| registry.is_registered(n)) {
        return MacroPattern::DelegatesToOther;
    }
    MacroPattern::Terminal
}

#[must_use]
pub(crate) fn classify_all(registry: &MacroRegistry) -> BTreeMap<String, MacroPattern> {
    registry
        .all_macros()
        .map(|d| (d.name.clone(), classify_macro(registry, d)))
        .collect()
}

// =============================================================================
// Hygiene validation
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HygieneIssue {
    pub(crate) macro_name: String,
    pub(crate) detail: String,
    pub(crate) severity: HygieneSeverity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub(crate) enum HygieneSeverity {
    Info,
    Warning,
    Error,
}

const COMMON_LEAN_NAMES: &[&str] = &[
    "Nat", "Bool", "Type", "Prop", "Sort", "True", "False", "And", "Or", "Not", "Eq", "HEq",
    "Unit", "PUnit", "Empty", "List", "Option", "String",
];

#[must_use]
pub(crate) fn validate_hygiene(registry: &MacroRegistry, def: &MacroDef) -> Vec<HygieneIssue> {
    let _ = registry; // available for cross-macro checks in future
    let mut issues = Vec::new();
    let template_names = collect_names(&def.expansion_template);

    if template_names.contains(&def.name) {
        issues.push(HygieneIssue {
            macro_name: def.name.clone(),
            detail: format!(
                "template references its own name '{}', risking infinite expansion",
                def.name
            ),
            severity: HygieneSeverity::Warning,
        });
    }
    for name in &template_names {
        if COMMON_LEAN_NAMES.contains(&name.as_str()) {
            issues.push(HygieneIssue {
                macro_name: def.name.clone(),
                detail: format!("template references common name '{name}'"),
                severity: HygieneSeverity::Info,
            });
        }
    }
    let pattern_idents = count_pattern_idents(&def.pattern);
    let holes = count_holes(&def.expansion_template);
    if holes > pattern_idents {
        issues.push(HygieneIssue {
            macro_name: def.name.clone(),
            detail: format!("template has {holes} hole(s) but pattern has only {pattern_idents} expression slot(s)"),
            severity: HygieneSeverity::Error,
        });
    }
    issues
}

#[must_use]
pub(crate) fn validate_all_hygiene(registry: &MacroRegistry) -> Vec<HygieneIssue> {
    registry
        .all_macros()
        .flat_map(|d| validate_hygiene(registry, d))
        .collect()
}

// =============================================================================
// Expansion statistics
// =============================================================================

#[derive(Debug, Clone, Default)]
pub(crate) struct ExpansionStats {
    pub(crate) expansion_counts: HashMap<String, usize>,
    pub(crate) max_depths: HashMap<String, usize>,
    pub(crate) output_sizes: HashMap<String, usize>,
}

impl ExpansionStats {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn record(&mut self, trace: &ExpansionTrace) {
        for step in &trace.steps {
            *self
                .expansion_counts
                .entry(step.macro_name.clone())
                .or_insert(0) += 1;
            let d = self.max_depths.entry(step.macro_name.clone()).or_insert(0);
            if step.depth > *d {
                *d = step.depth;
            }
        }
        if let Some(first) = trace.steps.first() {
            *self
                .output_sizes
                .entry(first.macro_name.clone())
                .or_insert(0) += expr_node_count(&trace.final_expr);
        }
    }

    #[must_use]
    pub(crate) fn total_expansions(&self) -> usize {
        self.expansion_counts.values().sum()
    }

    #[must_use]
    pub(crate) fn count_for(&self, name: &str) -> usize {
        self.expansion_counts.get(name).copied().unwrap_or(0)
    }

    #[must_use]
    pub(crate) fn max_depth_for(&self, name: &str) -> usize {
        self.max_depths.get(name).copied().unwrap_or(0)
    }

    pub(crate) fn reset(&mut self) {
        self.expansion_counts.clear();
        self.max_depths.clear();
        self.output_sizes.clear();
    }
}

// =============================================================================
// Macro dependency graph
// =============================================================================

#[derive(Debug, Clone)]
pub(crate) struct MacroDependencyGraph {
    pub(crate) edges: BTreeMap<String, BTreeSet<String>>,
    pub(crate) reverse_edges: BTreeMap<String, BTreeSet<String>>,
}

impl MacroDependencyGraph {
    #[must_use]
    pub(crate) fn build(registry: &MacroRegistry) -> Self {
        let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut reverse_edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for def in registry.all_macros() {
            let mut deps = BTreeSet::new();
            for name in collect_names(&def.expansion_template) {
                if registry.is_registered(&name) && name != def.name {
                    deps.insert(name.clone());
                    reverse_edges
                        .entry(name)
                        .or_default()
                        .insert(def.name.clone());
                }
            }
            edges.insert(def.name.clone(), deps);
        }
        for def in registry.all_macros() {
            edges.entry(def.name.clone()).or_default();
            reverse_edges.entry(def.name.clone()).or_default();
        }
        Self {
            edges,
            reverse_edges,
        }
    }

    #[must_use]
    pub(crate) fn dependencies_of(&self, name: &str) -> BTreeSet<String> {
        self.edges.get(name).cloned().unwrap_or_default()
    }

    #[must_use]
    pub(crate) fn dependents_of(&self, name: &str) -> BTreeSet<String> {
        self.reverse_edges.get(name).cloned().unwrap_or_default()
    }

    #[must_use]
    pub(crate) fn leaves(&self) -> BTreeSet<String> {
        self.edges
            .iter()
            .filter(|(_, d)| d.is_empty())
            .map(|(n, _)| n.clone())
            .collect()
    }

    #[must_use]
    pub(crate) fn roots(&self) -> BTreeSet<String> {
        self.reverse_edges
            .iter()
            .filter(|(_, d)| d.is_empty())
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// Detect cycles via BFS from each node.
    #[must_use]
    pub(crate) fn detect_cycle(&self) -> Option<Vec<String>> {
        for start in self.edges.keys() {
            let mut visited = HashSet::new();
            let mut queue = VecDeque::new();
            let mut parent: HashMap<String, String> = HashMap::new();
            queue.push_back(start.clone());
            visited.insert(start.clone());
            while let Some(current) = queue.pop_front() {
                for dep in self.edges.get(&current).into_iter().flatten() {
                    if dep == start && !parent.is_empty() {
                        let mut cycle = vec![start.clone()];
                        let mut node = current.clone();
                        while node != *start {
                            cycle.push(node.clone());
                            node = parent.get(&node).cloned().unwrap_or_default();
                        }
                        cycle.push(start.clone());
                        cycle.reverse();
                        return Some(cycle);
                    }
                    if visited.insert(dep.clone()) {
                        parent.insert(dep.clone(), current.clone());
                        queue.push_back(dep.clone());
                    }
                }
            }
        }
        None
    }

    /// Compute a topological ordering. Returns `None` if cycles exist.
    #[must_use]
    pub(crate) fn topological_order(&self) -> Option<Vec<String>> {
        let mut in_deg: BTreeMap<String, usize> = BTreeMap::new();
        for (name, deps) in &self.edges {
            in_deg.entry(name.clone()).or_insert(0);
            for dep in deps {
                *in_deg.entry(dep.clone()).or_insert(0) += 1;
            }
        }
        let mut queue: VecDeque<String> = in_deg
            .iter()
            .filter(|(_, &d)| d == 0)
            .map(|(n, _)| n.clone())
            .collect();
        let mut result = Vec::new();
        while let Some(node) = queue.pop_front() {
            result.push(node.clone());
            for dep in self.edges.get(&node).into_iter().flatten() {
                if let Some(d) = in_deg.get_mut(dep) {
                    *d = d.saturating_sub(1);
                    if *d == 0 {
                        queue.push_back(dep.clone());
                    }
                }
            }
        }
        if result.len() == self.edges.len() {
            Some(result)
        } else {
            None
        }
    }
}

// =============================================================================
// Template extraction
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TemplateDescription {
    pub(crate) name: String,
    pub(crate) structure: String,
    pub(crate) parameters: Vec<String>,
    pub(crate) scoping: MacroScoping,
}

#[must_use]
pub(crate) fn extract_template(def: &MacroDef) -> TemplateDescription {
    let parameters: Vec<String> = def
        .pattern
        .iter()
        .enumerate()
        .filter_map(|(i, part)| match part {
            MacroPatternPart::Expr => Some(format!("expr_{i}")),
            MacroPatternPart::Ident => Some(format!("ident_{i}")),
            MacroPatternPart::OptionalExpr => Some(format!("opt_expr_{i}")),
            MacroPatternPart::SepByExpr(sep) => Some(format!("list_{i}(sep='{sep}')")),
            MacroPatternPart::Keyword(_) => None,
        })
        .collect();
    TemplateDescription {
        name: def.name.clone(),
        structure: describe_template(&def.expansion_template),
        parameters,
        scoping: def.scoping,
    }
}

#[must_use]
pub(crate) fn extract_all_templates(registry: &MacroRegistry) -> Vec<TemplateDescription> {
    registry.all_macros().map(extract_template).collect()
}

// =============================================================================
// Optimization hints
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OptimizationHint {
    pub(crate) macro_name: String,
    pub(crate) suggestion: String,
    pub(crate) kind: OptimizationKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum OptimizationKind {
    Inline,
    MergeDelegate,
    UnusedPattern,
    Simplify,
}

#[must_use]
pub(crate) fn suggest_optimizations(registry: &MacroRegistry) -> Vec<OptimizationHint> {
    let mut hints = Vec::new();
    let dep_graph = MacroDependencyGraph::build(registry);
    for def in registry.all_macros() {
        if matches!(&def.expansion_template, SurfaceExpr::Hole(_))
            && def.pattern.len() == 1
            && matches!(def.pattern[0], MacroPatternPart::Expr)
        {
            hints.push(OptimizationHint {
                macro_name: def.name.clone(),
                suggestion: "identity macro (hole template); consider removing".to_owned(),
                kind: OptimizationKind::Inline,
            });
        }
        let deps = dep_graph.dependencies_of(&def.name);
        if deps.len() == 1 {
            let target = deps.iter().next().unwrap_or(&def.name);
            hints.push(OptimizationHint {
                macro_name: def.name.clone(),
                suggestion: format!("delegates to '{target}'; consider merging"),
                kind: OptimizationKind::MergeDelegate,
            });
        }
        if !def.pattern.is_empty()
            && def
                .pattern
                .iter()
                .all(|p| matches!(p, MacroPatternPart::Keyword(_)))
        {
            hints.push(OptimizationHint {
                macro_name: def.name.clone(),
                suggestion: "keyword-only pattern; simplify to zero-arity".to_owned(),
                kind: OptimizationKind::Simplify,
            });
        }
    }
    hints
}

// =============================================================================
// Helpers
// =============================================================================

fn collect_names(expr: &SurfaceExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_names_inner(expr, &mut names);
    names
}

fn collect_names_inner(expr: &SurfaceExpr, out: &mut HashSet<String>) {
    match expr {
        SurfaceExpr::Ident(_, n) => {
            out.insert(n.clone());
        }
        SurfaceExpr::App(_, f, args) => {
            collect_names_inner(f, out);
            for a in args {
                collect_names_inner(&a.expr, out);
            }
        }
        SurfaceExpr::Lambda(_, _, b) | SurfaceExpr::Pi(_, _, b) => collect_names_inner(b, out),
        SurfaceExpr::Arrow(_, l, r) | SurfaceExpr::Let(_, _, l, r) => {
            collect_names_inner(l, out);
            collect_names_inner(r, out);
        }
        SurfaceExpr::Paren(_, i) | SurfaceExpr::Ascription(_, i, _) => collect_names_inner(i, out),
        _ => {}
    }
}

fn count_pattern_idents(pattern: &[MacroPatternPart]) -> usize {
    pattern
        .iter()
        .filter(|p| matches!(p, MacroPatternPart::Expr | MacroPatternPart::Ident))
        .count()
}

fn count_holes(expr: &SurfaceExpr) -> usize {
    match expr {
        SurfaceExpr::Hole(_) => 1,
        SurfaceExpr::App(_, f, a) => {
            count_holes(f) + a.iter().map(|x| count_holes(&x.expr)).sum::<usize>()
        }
        SurfaceExpr::Paren(_, i) => count_holes(i),
        SurfaceExpr::Lambda(_, _, b) | SurfaceExpr::Pi(_, _, b) => count_holes(b),
        SurfaceExpr::Arrow(_, l, r) | SurfaceExpr::Let(_, _, l, r) => {
            count_holes(l) + count_holes(r)
        }
        _ => 0,
    }
}

fn extract_head_name(expr: &SurfaceExpr) -> Option<String> {
    match expr {
        SurfaceExpr::Ident(_, n) => Some(n.clone()),
        SurfaceExpr::App(_, f, _) => extract_head_name(f),
        SurfaceExpr::Paren(_, i) => extract_head_name(i),
        _ => None,
    }
}

fn extract_app_args(expr: &SurfaceExpr) -> Vec<SurfaceExpr> {
    match expr {
        SurfaceExpr::App(_, _, a) => a.iter().map(|x| x.expr.clone()).collect(),
        _ => vec![],
    }
}

fn expr_node_count(expr: &SurfaceExpr) -> usize {
    match expr {
        SurfaceExpr::App(_, f, a) => {
            1 + expr_node_count(f) + a.iter().map(|x| expr_node_count(&x.expr)).sum::<usize>()
        }
        SurfaceExpr::Lambda(_, _, b) | SurfaceExpr::Pi(_, _, b) => 1 + expr_node_count(b),
        SurfaceExpr::Arrow(_, l, r) | SurfaceExpr::Let(_, _, l, r) => {
            1 + expr_node_count(l) + expr_node_count(r)
        }
        SurfaceExpr::Paren(_, i) | SurfaceExpr::Ascription(_, i, _) => 1 + expr_node_count(i),
        _ => 1,
    }
}

fn describe_template(expr: &SurfaceExpr) -> String {
    match expr {
        SurfaceExpr::Ident(_, n) => format!("ident({n})"),
        SurfaceExpr::Hole(_) => "hole".to_owned(),
        SurfaceExpr::App(_, f, a) => format!("app({}, {} args)", describe_template(f), a.len()),
        SurfaceExpr::Lambda(_, _, _) => "lambda".to_owned(),
        SurfaceExpr::Pi(_, _, _) => "pi".to_owned(),
        SurfaceExpr::Arrow(_, _, _) => "arrow".to_owned(),
        SurfaceExpr::Let(_, _, _, _) => "let".to_owned(),
        SurfaceExpr::Paren(_, i) => describe_template(i),
        SurfaceExpr::Lit(_, _) => "literal".to_owned(),
        _ => "other".to_owned(),
    }
}
