// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended variable command analysis: usage tracking, redundancy detection,
//! type dependency analysis, statistics, scope impact, and batch validation.

use std::collections::{HashMap, HashSet};

use clean_kernel::expr::visitor::ExprVisitor;
use clean_kernel::expr::{BinderInfo, ExprKind, LevelVec};
use clean_kernel::name::Name;
use clean_kernel::Expr;
use thiserror::Error;

use crate::variable_cmd::VariableDecl;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from extended variable command analysis.
#[derive(Debug, Error)]
pub(crate) enum VariableCmdExtError {
    #[error("duplicate variable name: '{0}'")]
    DuplicateName(String),
    #[error("cycle in type dependencies: {0}")]
    DependencyCycle(String),
    #[error("unresolved type reference: '{0}' in type of '{1}'")]
    UnresolvedTypeRef(String, String),
    #[error("binder info conflict for '{name}': {existing:?} vs {incoming:?}")]
    BinderConflict {
        name: String,
        existing: BinderInfo,
        incoming: BinderInfo,
    },
}

// ---------------------------------------------------------------------------
// Usage tracking
// ---------------------------------------------------------------------------

/// Tracks which declared variables are referenced in expression bodies.
#[derive(Debug, Clone)]
pub(crate) struct VariableUsageTracker {
    usage: HashMap<String, HashSet<String>>,
    tracked: HashSet<String>,
}

impl VariableUsageTracker {
    /// Create a tracker pre-populated with variable names from declarations.
    #[must_use]
    pub(crate) fn new(decls: &[VariableDecl]) -> Self {
        let mut tracked = HashSet::new();
        let mut usage = HashMap::new();
        for decl in decls {
            for name in &decl.names {
                let s = name.to_string();
                tracked.insert(s.clone());
                usage.insert(s, HashSet::new());
            }
        }
        Self { usage, tracked }
    }

    /// Record that `expr` (from definition `def_name`) references some variables.
    pub(crate) fn record_usage(&mut self, def_name: &str, expr: &Expr) {
        let referenced = collect_const_name_strings(expr);
        for name in &referenced {
            if self.tracked.contains(name) {
                self.usage
                    .entry(name.clone())
                    .or_default()
                    .insert(def_name.to_owned());
            }
        }
    }

    /// Variable names never referenced by any recorded definition.
    #[must_use]
    pub(crate) fn unused_variables(&self) -> Vec<String> {
        let mut r: Vec<String> = self
            .usage
            .iter()
            .filter(|(_, defs)| defs.is_empty())
            .map(|(name, _)| name.clone())
            .collect();
        r.sort();
        r
    }

    /// Variable names referenced at least once.
    #[must_use]
    pub(crate) fn used_variables(&self) -> Vec<String> {
        let mut r: Vec<String> = self
            .usage
            .iter()
            .filter(|(_, defs)| !defs.is_empty())
            .map(|(name, _)| name.clone())
            .collect();
        r.sort();
        r
    }

    /// How many definitions reference a particular variable.
    #[must_use]
    pub(crate) fn reference_count(&self, var_name: &str) -> usize {
        self.usage.get(var_name).map_or(0, HashSet::len)
    }

    /// Which definitions reference a particular variable.
    #[must_use]
    pub(crate) fn referencing_defs(&self, var_name: &str) -> Vec<String> {
        let mut r: Vec<String> = self
            .usage
            .get(var_name)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default();
        r.sort();
        r
    }

    /// Whether a specific variable is tracked.
    #[must_use]
    pub(crate) fn is_tracked(&self, var_name: &str) -> bool {
        self.tracked.contains(var_name)
    }
}

// ---------------------------------------------------------------------------
// Type dependency analysis
// ---------------------------------------------------------------------------

/// Compute a valid declaration order via topological sort on type dependencies.
///
/// If variable `b`'s type references variable `a`, then `a` must come first.
pub(crate) fn compute_declaration_order(
    decls: &[VariableDecl],
) -> Result<Vec<String>, VariableCmdExtError> {
    let all_names: HashSet<String> = decls
        .iter()
        .flat_map(|d| d.names.iter().map(|n| n.to_string()))
        .collect();

    let mut deps: HashMap<String, HashSet<String>> = HashMap::new();
    for decl in decls {
        let type_deps: HashSet<String> = collect_const_name_strings(&decl.type_)
            .into_iter()
            .filter(|r| all_names.contains(r))
            .collect();
        for name in &decl.names {
            deps.insert(name.to_string(), type_deps.clone());
        }
    }

    // Kahn's algorithm
    let mut remaining: HashMap<String, HashSet<String>> = deps;
    let mut order = Vec::new();
    let mut queue: Vec<String> = remaining
        .iter()
        .filter(|(_, d)| d.is_empty())
        .map(|(n, _)| n.clone())
        .collect();
    queue.sort();

    while let Some(name) = queue.pop() {
        order.push(name.clone());
        for (other, other_deps) in &mut remaining {
            if other_deps.remove(&name) && other_deps.is_empty() && !order.contains(other) {
                queue.push(other.clone());
                queue.sort();
            }
        }
    }

    if order.len() != all_names.len() {
        let rest: Vec<String> = all_names
            .iter()
            .filter(|n| !order.contains(n))
            .cloned()
            .collect();
        return Err(VariableCmdExtError::DependencyCycle(rest.join(", ")));
    }
    Ok(order)
}

/// Direct type dependencies of a declaration, filtered to `known_vars`.
#[must_use]
pub(crate) fn type_dependencies(
    decl: &VariableDecl,
    known_vars: &HashSet<String>,
) -> HashSet<String> {
    collect_const_name_strings(&decl.type_)
        .into_iter()
        .filter(|r| known_vars.contains(r))
        .collect()
}

// ---------------------------------------------------------------------------
// Redundancy detection
// ---------------------------------------------------------------------------

/// A redundancy finding from analyzing variable declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RedundancyKind {
    Shadow {
        name: String,
        first_binder: BinderInfo,
        second_binder: BinderInfo,
    },
    ExactDuplicate {
        name: String,
    },
    Mergeable {
        names: Vec<String>,
        binder_info: BinderInfo,
    },
}

/// Detect shadows, exact duplicates, and mergeable declarations.
#[must_use]
pub(crate) fn detect_redundancies(decls: &[VariableDecl]) -> Vec<RedundancyKind> {
    let mut findings = Vec::new();
    let mut seen: HashMap<String, (BinderInfo, String)> = HashMap::new();
    for decl in decls {
        let type_str = format!("{}", decl.type_);
        for name in &decl.names {
            let ns = name.to_string();
            if let Some((prev_bi, prev_type)) = seen.get(&ns) {
                if *prev_bi == decl.binder_info && *prev_type == type_str {
                    findings.push(RedundancyKind::ExactDuplicate { name: ns.clone() });
                } else {
                    findings.push(RedundancyKind::Shadow {
                        name: ns.clone(),
                        first_binder: *prev_bi,
                        second_binder: decl.binder_info,
                    });
                }
            }
            seen.insert(ns, (decl.binder_info, type_str.clone()));
        }
    }
    // Mergeable: same type + binder from separate single-name declarations
    let mut groups: HashMap<(String, BinderInfo), Vec<String>> = HashMap::new();
    for decl in decls {
        let ts = format!("{}", decl.type_);
        for name in &decl.names {
            groups
                .entry((ts.clone(), decl.binder_info))
                .or_default()
                .push(name.to_string());
        }
    }
    for ((_, bi), names) in &groups {
        if names.len() > 1 {
            let from_separate = decls.iter().any(|d| {
                d.binder_info == *bi
                    && d.names.len() == 1
                    && names.contains(&d.names[0].to_string())
            });
            if from_separate {
                findings.push(RedundancyKind::Mergeable {
                    names: names.clone(),
                    binder_info: *bi,
                });
            }
        }
    }
    findings
}

// ---------------------------------------------------------------------------
// Variable statistics
// ---------------------------------------------------------------------------

/// Statistics about a set of variable declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VariableStatistics {
    pub(crate) total_count: usize,
    pub(crate) by_binder: HashMap<BinderInfo, usize>,
    pub(crate) distinct_types: usize,
    pub(crate) avg_type_complexity: usize,
    pub(crate) max_type_complexity: usize,
    pub(crate) multi_name_decls: usize,
}

/// Compute statistics over a set of variable declarations.
#[must_use]
pub(crate) fn compute_statistics(decls: &[VariableDecl]) -> VariableStatistics {
    let (mut total, mut total_cx, mut max_cx, mut multi) = (0usize, 0usize, 0usize, 0usize);
    let mut by_binder: HashMap<BinderInfo, usize> = HashMap::new();
    let mut type_strs: HashSet<String> = HashSet::new();

    for decl in decls {
        let n = decl.names.len();
        total += n;
        *by_binder.entry(decl.binder_info).or_insert(0) += n;
        type_strs.insert(format!("{}", decl.type_));
        let cx = expr_node_count(&decl.type_);
        total_cx += cx * n;
        if cx > max_cx {
            max_cx = cx;
        }
        if n > 1 {
            multi += 1;
        }
    }
    VariableStatistics {
        total_count: total,
        by_binder,
        distinct_types: type_strs.len(),
        avg_type_complexity: total_cx.checked_div(total).unwrap_or(0),
        max_type_complexity: max_cx,
        multi_name_decls: multi,
    }
}

// ---------------------------------------------------------------------------
// Scope impact analysis
// ---------------------------------------------------------------------------

/// How a variable affects the elaboration scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopeImpact {
    pub(crate) name: String,
    pub(crate) adds_implicit_arg: bool,
    pub(crate) adds_instance_arg: bool,
    pub(crate) type_references: Vec<String>,
    pub(crate) binder_depth_contribution: usize,
}

/// Analyze the scope impact of each variable in a declaration set.
#[must_use]
pub(crate) fn analyze_scope_impact(decls: &[VariableDecl]) -> Vec<ScopeImpact> {
    let all: HashSet<String> = decls
        .iter()
        .flat_map(|d| d.names.iter().map(|n| n.to_string()))
        .collect();
    let mut results = Vec::new();
    for decl in decls {
        let refs: Vec<String> = collect_const_name_strings(&decl.type_)
            .into_iter()
            .filter(|r| all.contains(r))
            .collect();
        let depth = 1 + refs.len();
        for name in &decl.names {
            results.push(ScopeImpact {
                name: name.to_string(),
                adds_implicit_arg: matches!(
                    decl.binder_info,
                    BinderInfo::Implicit | BinderInfo::StrictImplicit
                ),
                adds_instance_arg: decl.binder_info == BinderInfo::InstImplicit,
                type_references: refs.clone(),
                binder_depth_contribution: depth,
            });
        }
    }
    results
}

// ---------------------------------------------------------------------------
// Batch validation
// ---------------------------------------------------------------------------

/// Validate declarations for consistency (no duplicates, conflicts, or cycles).
pub(crate) fn validate_batch(decls: &[VariableDecl]) -> Result<(), VariableCmdExtError> {
    let mut seen: HashMap<String, BinderInfo> = HashMap::new();
    for decl in decls {
        for name in &decl.names {
            let s = name.to_string();
            if let Some(existing_bi) = seen.get(&s) {
                if *existing_bi != decl.binder_info {
                    return Err(VariableCmdExtError::BinderConflict {
                        name: s,
                        existing: *existing_bi,
                        incoming: decl.binder_info,
                    });
                }
                return Err(VariableCmdExtError::DuplicateName(s));
            }
            seen.insert(s, decl.binder_info);
        }
    }
    compute_declaration_order(decls)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Variable suggestions
// ---------------------------------------------------------------------------

/// A suggestion for improving a variable declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VariableSuggestion {
    MakeImplicit { name: String },
    MakeInstance { name: String, class_name: String },
    RemoveUnused { name: String },
    MergeDeclarations { names: Vec<String> },
}

/// Generate suggestions based on usage patterns.
#[must_use]
pub(crate) fn suggest_improvements(
    decls: &[VariableDecl],
    tracker: &VariableUsageTracker,
) -> Vec<VariableSuggestion> {
    let mut sug = Vec::new();
    for name in tracker.unused_variables() {
        sug.push(VariableSuggestion::RemoveUnused { name });
    }
    for decl in decls {
        if decl.binder_info == BinderInfo::Default && decl.type_.is_sort() {
            for name in &decl.names {
                let ns = name.to_string();
                if tracker.reference_count(&ns) > 0 {
                    sug.push(VariableSuggestion::MakeImplicit { name: ns });
                }
            }
        }
        if decl.binder_info == BinderInfo::Default && decl.type_.is_app() {
            if let Some(cn) = extract_head_const_name(&decl.type_) {
                for name in &decl.names {
                    sug.push(VariableSuggestion::MakeInstance {
                        name: name.to_string(),
                        class_name: cn.clone(),
                    });
                }
            }
        }
    }
    let mut groups: HashMap<(String, BinderInfo), Vec<String>> = HashMap::new();
    for decl in decls {
        if decl.names.len() == 1 {
            groups
                .entry((format!("{}", decl.type_), decl.binder_info))
                .or_default()
                .push(decl.names[0].to_string());
        }
    }
    for names in groups.values() {
        if names.len() > 1 {
            sug.push(VariableSuggestion::MergeDeclarations {
                names: names.clone(),
            });
        }
    }
    sug
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Count AST nodes in an expression (type complexity metric).
#[must_use]
pub(crate) fn expr_node_count(expr: &Expr) -> usize {
    match expr.kind() {
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Lit(_)
        | ExprKind::Const(_, _) => 1,
        ExprKind::App(f, a) => 1 + expr_node_count(f) + expr_node_count(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            1 + expr_node_count(ty) + expr_node_count(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            1 + expr_node_count(ty) + expr_node_count(val) + expr_node_count(body)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => 1 + expr_node_count(e),
        _ => 1,
    }
}

struct ConstNameStringCollector {
    names: HashSet<String>,
}

impl ExprVisitor for ConstNameStringCollector {
    type Result = ();
    fn combine(&self, _a: (), _b: ()) {}
    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.names.insert(name.to_string());
    }
}

fn collect_const_name_strings(expr: &Expr) -> HashSet<String> {
    let mut c = ConstNameStringCollector {
        names: HashSet::new(),
    };
    c.visit_expr(expr);
    c.names
}

/// Extract the head constant name from an application chain.
fn extract_head_const_name(expr: &Expr) -> Option<String> {
    match expr.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        ExprKind::App(f, _) => extract_head_const_name(f),
        _ => None,
    }
}
