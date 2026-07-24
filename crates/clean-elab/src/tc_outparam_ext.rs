// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended type class `outParam` analysis: inference, hierarchy tracking,
//! validation, diagnostics, and statistics.
//!
//! Extends [`super::tc_outparam`] with:
//! - **Inference**: automatically classify parameters as input/output by
//!   analyzing instance patterns (which positions vary across instances).
//! - **Hierarchy**: track outParam relationships across parent/child class
//!   hierarchies (e.g., `HAdd` extends `Add`).
//! - **Validation**: verify that output parameters are uniquely determined
//!   by the input parameters across all registered instances.
//! - **Diagnostics**: human-readable explanations of why each parameter
//!   was classified as input or output.
//! - **Statistics**: summary reporting over an entire `InstanceTable`.
//!
//! Reference: Lean 4 `src/Lean/Meta/SynthInstance.lean`,
//! `src/Lean/Meta/Instances.lean`.

use std::collections::HashSet;

use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;

use crate::instances::{extract_class_app, InstanceTable};

// =============================================================================
// Parameter classification
// =============================================================================

/// How a parameter position was classified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ParamRole {
    /// Input: provided by the caller; instances must match it.
    Input,
    /// Output: determined by the instance; caller leaves it as a metavariable.
    Output,
    /// Semi-output: can be inferred from context or the instance.
    SemiOutput,
}

/// Detailed classification of one parameter position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParamClassification {
    /// 0-based parameter index.
    pub(crate) index: usize,
    /// Assigned role.
    pub(crate) role: ParamRole,
    /// Human-readable reason for the classification.
    pub(crate) reason: String,
}

/// Full classification result for a class.
#[derive(Debug, Clone)]
pub(crate) struct ClassParamProfile {
    /// Class name.
    pub(crate) class_name: Name,
    /// Number of parameters.
    pub(crate) num_params: usize,
    /// Per-parameter classification.
    pub(crate) params: Vec<ParamClassification>,
}

// =============================================================================
// Inference
// =============================================================================

/// Infer parameter roles for a class by analyzing registered instances.
///
/// Strategy: for each parameter position, collect the set of distinct
/// argument expressions across all instances. If every instance uses the
/// same expression at a position, it is likely an output (constant
/// across instances). If instances vary at a position, callers must
/// supply it (input). Annotated `outParam`/`semiOutParam` from the
/// `InstanceTable` override the heuristic.
#[must_use]
pub(crate) fn infer_param_roles(
    class_name: &Name,
    instances: &InstanceTable,
) -> Option<ClassParamProfile> {
    let class_info = instances.get_class(class_name)?;
    let num_params = class_info.num_params;
    let registered_out: HashSet<usize> = class_info.out_params.iter().copied().collect();
    let registered_semi: HashSet<usize> = class_info.semi_out_params.iter().copied().collect();

    let candidates = instances.get_instances(class_name);

    // Collect per-position argument sets from instance types.
    let mut position_values: Vec<HashSet<String>> = vec![HashSet::new(); num_params];
    for inst in candidates {
        if let Some((_name, args)) = extract_class_app(&inst.type_) {
            for (i, arg) in args.iter().enumerate() {
                if i < num_params {
                    position_values[i].insert(format!("{arg:?}"));
                }
            }
        }
    }

    let mut params = Vec::with_capacity(num_params);
    for (i, values) in position_values.iter().enumerate() {
        let (role, reason) = if registered_out.contains(&i) {
            (ParamRole::Output, "annotated outParam".to_owned())
        } else if registered_semi.contains(&i) {
            (ParamRole::SemiOutput, "annotated semiOutParam".to_owned())
        } else if candidates.is_empty() {
            (ParamRole::Input, "no instances registered".to_owned())
        } else {
            let distinct = values.len();
            if distinct <= 1 {
                (
                    ParamRole::Output,
                    format!(
                        "inferred output: all {n} instances agree",
                        n = candidates.len()
                    ),
                )
            } else {
                (
                    ParamRole::Input,
                    format!("inferred input: {distinct} distinct values across instances"),
                )
            }
        };
        params.push(ParamClassification {
            index: i,
            role,
            reason,
        });
    }

    Some(ClassParamProfile {
        class_name: class_name.clone(),
        num_params,
        params,
    })
}

// =============================================================================
// Multi-class hierarchy analysis
// =============================================================================

/// Relationship between outParam positions of two related classes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OutParamRelation {
    /// Parent class name.
    pub(crate) parent: Name,
    /// Child class name.
    pub(crate) child: Name,
    /// Indices that are output in both parent and child.
    pub(crate) shared_out_indices: Vec<usize>,
    /// Indices that are output in parent but input in child.
    pub(crate) parent_only_out: Vec<usize>,
    /// Indices that are output in child but input in parent.
    pub(crate) child_only_out: Vec<usize>,
}

/// Analyze outParam relationships between a parent and child class.
///
/// Compares parameter roles: overlapping positions are compared by role.
/// Only considers positions up to `min(parent.num_params, child.num_params)`.
#[must_use]
pub(crate) fn analyze_hierarchy_outparams(
    parent_name: &Name,
    child_name: &Name,
    instances: &InstanceTable,
) -> Option<OutParamRelation> {
    let parent_info = instances.get_class(parent_name)?;
    let child_info = instances.get_class(child_name)?;

    let parent_out: HashSet<usize> = parent_info.out_params.iter().copied().collect();
    let child_out: HashSet<usize> = child_info.out_params.iter().copied().collect();

    let max_idx = parent_info.num_params.min(child_info.num_params);
    let mut shared = Vec::new();
    let mut parent_only = Vec::new();
    let mut child_only = Vec::new();

    for i in 0..max_idx {
        let in_parent = parent_out.contains(&i);
        let in_child = child_out.contains(&i);
        match (in_parent, in_child) {
            (true, true) => shared.push(i),
            (true, false) => parent_only.push(i),
            (false, true) => child_only.push(i),
            (false, false) => {}
        }
    }

    Some(OutParamRelation {
        parent: parent_name.clone(),
        child: child_name.clone(),
        shared_out_indices: shared,
        parent_only_out: parent_only,
        child_only_out: child_only,
    })
}

// =============================================================================
// Validation
// =============================================================================

/// Validation result for a class's outParam uniqueness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValidationResult {
    /// All output parameters are uniquely determined by inputs.
    Valid,
    /// Some output positions have conflicting values for the same inputs.
    Conflict {
        /// Parameter indices that are ambiguous.
        conflicting_indices: Vec<usize>,
        /// Instance names that conflict.
        conflicting_instances: Vec<(Name, Name)>,
    },
    /// Class not registered.
    NotRegistered,
}

/// Validate that output parameters are uniquely determined by input
/// parameters.
///
/// For each pair of instances, if they agree on all non-outParam positions,
/// they must also agree on all outParam positions.
#[must_use]
pub(crate) fn validate_outparam_uniqueness(
    class_name: &Name,
    instances: &InstanceTable,
) -> ValidationResult {
    let Some(class_info) = instances.get_class(class_name) else {
        return ValidationResult::NotRegistered;
    };

    let out_set: HashSet<usize> = class_info.out_params.iter().copied().collect();
    let candidates = instances.get_instances(class_name);
    if candidates.len() < 2 {
        return ValidationResult::Valid;
    }

    let parsed: Vec<(Name, Vec<Expr>)> = candidates
        .iter()
        .filter_map(|inst| {
            extract_class_app(&inst.type_).map(|(_, args)| (inst.name.clone(), args))
        })
        .collect();

    let mut conflicting_indices = HashSet::new();
    let mut conflicting_pairs: Vec<(Name, Name)> = Vec::new();

    for i in 0..parsed.len() {
        for j in (i + 1)..parsed.len() {
            let (ref na, ref aa) = parsed[i];
            let (ref nb, ref ab) = parsed[j];
            if aa.len() != ab.len() {
                continue;
            }
            let inputs_agree = aa
                .iter()
                .zip(ab.iter())
                .enumerate()
                .all(|(idx, (a, b))| out_set.contains(&idx) || expr_structural_eq(a, b));

            if inputs_agree {
                for &idx in &class_info.out_params {
                    if let (Some(a), Some(b)) = (aa.get(idx), ab.get(idx)) {
                        if !expr_structural_eq(a, b) {
                            conflicting_indices.insert(idx);
                            conflicting_pairs.push((na.clone(), nb.clone()));
                        }
                    }
                }
            }
        }
    }

    if conflicting_indices.is_empty() {
        ValidationResult::Valid
    } else {
        let mut sorted: Vec<usize> = conflicting_indices.into_iter().collect();
        sorted.sort_unstable();
        ValidationResult::Conflict {
            conflicting_indices: sorted,
            conflicting_instances: conflicting_pairs,
        }
    }
}

/// Conservative structural expression equality (mirrors tc_outparam private fn).
fn expr_structural_eq(a: &Expr, b: &Expr) -> bool {
    match (a.kind(), b.kind()) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
        (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            expr_structural_eq(f1, f2) && expr_structural_eq(a1, a2)
        }
        (ExprKind::Lam(bi1, ty1, b1), ExprKind::Lam(bi2, ty2, b2))
        | (ExprKind::Pi(bi1, ty1, b1), ExprKind::Pi(bi2, ty2, b2)) => {
            bi1 == bi2 && expr_structural_eq(ty1, ty2) && expr_structural_eq(b1, b2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        _ => false,
    }
}

// =============================================================================
// Diagnostics
// =============================================================================

/// A single diagnostic entry explaining one parameter's classification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParamDiagnostic {
    pub(crate) index: usize,
    pub(crate) role: ParamRole,
    pub(crate) explanation: String,
}

/// Produce diagnostics explaining every parameter classification for a class.
#[must_use]
pub(crate) fn diagnose_params(
    class_name: &Name,
    instances: &InstanceTable,
) -> Vec<ParamDiagnostic> {
    let Some(profile) = infer_param_roles(class_name, instances) else {
        return Vec::new();
    };
    profile
        .params
        .into_iter()
        .map(|pc| ParamDiagnostic {
            index: pc.index,
            role: pc.role,
            explanation: format!(
                "param[{}] of `{}`: {} ({})",
                pc.index,
                class_name,
                match pc.role {
                    ParamRole::Input => "INPUT",
                    ParamRole::Output => "OUTPUT",
                    ParamRole::SemiOutput => "SEMI-OUTPUT",
                },
                pc.reason,
            ),
        })
        .collect()
}

/// Format a full diagnostic report for a class as a multi-line string.
#[must_use]
pub(crate) fn format_diagnostic_report(class_name: &Name, instances: &InstanceTable) -> String {
    let diagnostics = diagnose_params(class_name, instances);
    if diagnostics.is_empty() {
        return format!("Class `{class_name}` is not registered or has no parameters.");
    }
    let mut lines = vec![format!("OutParam diagnostic for `{class_name}`:")];
    for d in &diagnostics {
        lines.push(format!("  {}", d.explanation));
    }
    match validate_outparam_uniqueness(class_name, instances) {
        ValidationResult::Valid => {
            lines.push("  Validation: OK (all outputs uniquely determined)".to_owned());
        }
        ValidationResult::Conflict {
            ref conflicting_indices,
            ..
        } => {
            lines.push(format!(
                "  Validation: CONFLICT at indices {:?}",
                conflicting_indices,
            ));
        }
        ValidationResult::NotRegistered => {
            lines.push("  Validation: class not registered".to_owned());
        }
    }
    lines.join("\n")
}

// =============================================================================
// Statistics
// =============================================================================

/// Aggregate statistics over all classes in an `InstanceTable`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct OutParamStats {
    pub(crate) total_classes: usize,
    pub(crate) classes_with_outparams: usize,
    pub(crate) classes_with_semi_outparams: usize,
    pub(crate) total_outparam_positions: usize,
    pub(crate) total_semi_outparam_positions: usize,
    pub(crate) valid_classes: usize,
    pub(crate) conflicting_classes: usize,
}

/// Compute statistics over all classes in the given `InstanceTable`.
#[must_use]
pub(crate) fn compute_stats(instances: &InstanceTable) -> OutParamStats {
    let mut stats = OutParamStats::default();
    for ci in instances.classes() {
        stats.total_classes += 1;
        if !ci.out_params.is_empty() {
            stats.classes_with_outparams += 1;
        }
        if !ci.semi_out_params.is_empty() {
            stats.classes_with_semi_outparams += 1;
        }
        stats.total_outparam_positions += ci.out_params.len();
        stats.total_semi_outparam_positions += ci.semi_out_params.len();
        match validate_outparam_uniqueness(&ci.name, instances) {
            ValidationResult::Valid => stats.valid_classes += 1,
            ValidationResult::Conflict { .. } => stats.conflicting_classes += 1,
            ValidationResult::NotRegistered => {}
        }
    }
    stats
}

/// Format statistics as a human-readable summary string.
#[must_use]
pub(crate) fn format_stats(stats: &OutParamStats) -> String {
    format!(
        "OutParam Statistics:\n\
         \x20 Classes: {} total, {} with outParams, {} with semiOutParams\n\
         \x20 Positions: {} outParam, {} semiOutParam\n\
         \x20 Validation: {} valid, {} conflicting",
        stats.total_classes,
        stats.classes_with_outparams,
        stats.classes_with_semi_outparams,
        stats.total_outparam_positions,
        stats.total_semi_outparam_positions,
        stats.valid_classes,
        stats.conflicting_classes,
    )
}

// =============================================================================
// Resolver integration helpers
// =============================================================================

/// Check whether a class has any output parameters (outParam or semi).
#[must_use]
pub(crate) fn has_any_out_params(class_name: &Name, instances: &InstanceTable) -> bool {
    instances
        .get_class(class_name)
        .map(|info| !info.out_params.is_empty() || !info.semi_out_params.is_empty())
        .unwrap_or(false)
}

/// Collect the names of all classes that have outParam positions.
#[must_use]
pub(crate) fn classes_with_outparams(instances: &InstanceTable) -> Vec<Name> {
    instances
        .classes()
        .filter(|info| !info.out_params.is_empty())
        .map(|info| info.name.clone())
        .collect()
}

/// Collect the names of all classes that have semi-outParam positions.
#[must_use]
pub(crate) fn classes_with_semi_outparams(instances: &InstanceTable) -> Vec<Name> {
    instances
        .classes()
        .filter(|info| !info.semi_out_params.is_empty())
        .map(|info| info.name.clone())
        .collect()
}

/// Count the total number of input parameters for a class.
#[must_use]
pub(crate) fn count_input_params(class_name: &Name, instances: &InstanceTable) -> usize {
    let Some(info) = instances.get_class(class_name) else {
        return 0;
    };
    let out_set: HashSet<usize> = info
        .out_params
        .iter()
        .chain(info.semi_out_params.iter())
        .copied()
        .collect();
    (0..info.num_params)
        .filter(|i| !out_set.contains(i))
        .count()
}

#[cfg(test)]
#[path = "tc_outparam_ext_tests.rs"]
mod tests;
