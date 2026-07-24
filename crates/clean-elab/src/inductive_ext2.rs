// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended inductive type analysis (phase 2).
//!
//! Constructor classification, recursion scheme detection, universe constraint
//! analysis, eliminator shape prediction, size metrics, positivity summaries,
//! and pattern match completeness prediction. Operates on `InductiveSpec` /
//! `MutualInductiveSpec` from `inductive_ext`. Pure analysis, no elaboration.

use clean_kernel::inductive::mentions_name;
use clean_kernel::{Expr, ExprKind, Level, Name};

use crate::inductive_ext::{
    check_strict_positivity, extract_universe_from_type, is_prop_type, ConstructorSpec,
    InductiveSpec, MutualInductiveSpec, PositivityViolation,
};

/// Errors from extended inductive analysis.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum InductiveAnalysisError {
    #[error("inductive type `{name}` has no constructors")]
    NoConstructors { name: Name },
    #[error(
        "cannot classify field `{field}` of constructor `{ctor}`: unrecognized type structure"
    )]
    UnclassifiableField { ctor: Name, field: Name },
    #[error("mutual inductive block is empty")]
    EmptyMutualBlock,
}

/// Classification of a constructor by its structural properties.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstructorClassification {
    pub(crate) name: Name,
    pub(crate) arity: usize,
    pub(crate) recursive_field_count: usize,
    pub(crate) higher_order_recursive_count: usize,
    pub(crate) recursive_field_indices: Vec<usize>,
    pub(crate) index_pattern: IndexPattern,
}

/// Index pattern in a constructor's return type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IndexPattern {
    None,
    AllVariables,
    HasConstructorIndices,
    Mixed,
}

/// Classify a constructor within the context of its parent inductive type.
pub(crate) fn classify_constructor(
    ctor: &ConstructorSpec,
    ind_name: &Name,
) -> ConstructorClassification {
    let mut recursive_field_indices = Vec::new();
    let mut higher_order_recursive_count = 0;
    for (idx, (_, field_ty, _)) in ctor.fields.iter().enumerate() {
        if mentions_name(field_ty, ind_name) {
            recursive_field_indices.push(idx);
            if is_higher_order_recursive(field_ty, ind_name) {
                higher_order_recursive_count += 1;
            }
        }
    }
    ConstructorClassification {
        name: ctor.name.clone(),
        arity: ctor.fields.len(),
        recursive_field_count: recursive_field_indices.len(),
        higher_order_recursive_count,
        recursive_field_indices,
        index_pattern: classify_index_pattern(&ctor.type_, ind_name),
    }
}

/// Classify all constructors in an inductive spec.
pub(crate) fn classify_all_constructors(spec: &InductiveSpec) -> Vec<ConstructorClassification> {
    spec.ctors
        .iter()
        .map(|c| classify_constructor(c, &spec.name))
        .collect()
}

/// Check whether a field type is higher-order recursive (Pi domain is itself
/// a function type, codomain mentions the inductive).
fn is_higher_order_recursive(ty: &Expr, ind_name: &Name) -> bool {
    match ty.kind() {
        ExprKind::Pi(_, domain, body) => {
            if !mentions_name(domain, ind_name) && mentions_name(body, ind_name) {
                matches!(domain.kind(), ExprKind::Pi(..))
                    || is_higher_order_recursive(body, ind_name)
            } else {
                is_higher_order_recursive(body, ind_name)
            }
        }
        _ => false,
    }
}

/// Classify the index pattern of a constructor return type.
fn classify_index_pattern(ctor_type: &Expr, _ind_name: &Name) -> IndexPattern {
    let mut current = ctor_type;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        current = body;
    }
    let args = current.get_app_args();
    if args.is_empty() {
        return IndexPattern::None;
    }
    let (mut has_var, mut has_ctor) = (false, false);
    for arg in &args {
        match arg.kind() {
            ExprKind::BVar(_) | ExprKind::FVar(_) => has_var = true,
            ExprKind::App(..) | ExprKind::Const(..) => {
                if arg.get_app_args().is_empty() {
                    has_var = true;
                } else {
                    has_ctor = true;
                }
            }
            _ => has_ctor = true,
        }
    }
    match (has_var, has_ctor) {
        (false, false) => IndexPattern::None,
        (true, false) => IndexPattern::AllVariables,
        (false, true) => IndexPattern::HasConstructorIndices,
        (true, true) => IndexPattern::Mixed,
    }
}

/// Detected recursion scheme of an inductive type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RecursionScheme {
    NonRecursive,
    ListLike,
    NatLike,
    TreeLike,
    HigherOrder,
    Mutual,
    Nested,
    GeneralRecursive,
}

/// Detect the recursion scheme of an inductive spec.
pub(crate) fn detect_recursion_scheme(spec: &InductiveSpec) -> RecursionScheme {
    if spec.is_nested {
        return RecursionScheme::Nested;
    }
    if !spec.is_recursive {
        return RecursionScheme::NonRecursive;
    }

    let cls = classify_all_constructors(spec);
    let base: Vec<_> = cls
        .iter()
        .filter(|c| c.recursive_field_count == 0)
        .collect();
    let rec: Vec<_> = cls.iter().filter(|c| c.recursive_field_count > 0).collect();

    if rec.iter().any(|c| c.higher_order_recursive_count > 0) {
        return RecursionScheme::HigherOrder;
    }
    if rec.iter().any(|c| c.recursive_field_count >= 2) {
        return RecursionScheme::TreeLike;
    }
    if base.len() == 1
        && rec.len() == 1
        && base[0].arity == 0
        && rec[0].arity == 1
        && rec[0].recursive_field_count == 1
    {
        return RecursionScheme::NatLike;
    }
    if base.len() == 1 && rec.len() == 1 && rec[0].recursive_field_count == 1 {
        return RecursionScheme::ListLike;
    }
    RecursionScheme::GeneralRecursive
}

/// Detect the recursion scheme for each type in a mutual block.
pub(crate) fn detect_mutual_recursion_scheme(
    spec: &MutualInductiveSpec,
) -> Vec<(Name, RecursionScheme)> {
    if spec.inductives.len() <= 1 {
        return spec
            .inductives
            .iter()
            .map(|i| (i.name.clone(), detect_recursion_scheme(i)))
            .collect();
    }
    spec.inductives
        .iter()
        .map(|i| (i.name.clone(), RecursionScheme::Mutual))
        .collect()
}

/// Summary of universe constraints imposed by an inductive type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UniverseConstraintSummary {
    pub(crate) result_universe: Level,
    pub(crate) is_prop: bool,
    pub(crate) has_type_valued_fields: bool,
    pub(crate) universe_param_count: usize,
    pub(crate) is_small_eliminator: bool,
}

/// Analyze universe constraints for an inductive spec.
pub(crate) fn analyze_universe_constraints(spec: &InductiveSpec) -> UniverseConstraintSummary {
    let result_universe = extract_universe_from_type(&spec.type_);
    let is_prop = is_prop_type(&spec.type_);
    let mut has_type_valued_fields = false;
    let mut param_names = std::collections::HashSet::new();
    for ctor in &spec.ctors {
        for (_, field_ty, _) in &ctor.fields {
            let field_level = extract_universe_from_type(field_ty);
            if !field_level.is_zero() {
                has_type_valued_fields = true;
            }
            collect_universe_params(&field_level, &mut param_names);
        }
    }
    collect_universe_params(&result_universe, &mut param_names);
    let is_small_eliminator = is_prop && (spec.ctors.len() <= 1 || !has_type_valued_fields);
    UniverseConstraintSummary {
        result_universe,
        is_prop,
        has_type_valued_fields,
        universe_param_count: param_names.len(),
        is_small_eliminator,
    }
}

fn collect_universe_params(level: &Level, names: &mut std::collections::HashSet<Name>) {
    match level {
        Level::Zero => {}
        Level::Succ(inner) => collect_universe_params(inner, names),
        Level::Max(l1, l2) | Level::IMax(l1, l2) => {
            collect_universe_params(l1, names);
            collect_universe_params(l2, names);
        }
        Level::Param(name) => {
            names.insert(name.clone());
        }
    }
}

/// Predicted shape of the eliminator (recursor / casesOn) for a type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EliminatorShape {
    pub(crate) motive_count: usize,
    pub(crate) minor_premise_count: usize,
    pub(crate) target_count: usize,
    pub(crate) is_large_eliminator: bool,
    pub(crate) total_binder_count: usize,
}

/// Predict the eliminator shape for an inductive spec.
pub(crate) fn predict_eliminator_shape(spec: &InductiveSpec) -> EliminatorShape {
    let is_prop = is_prop_type(&spec.type_);
    let has_type_valued_fields = spec.ctors.iter().any(|ctor| {
        ctor.fields
            .iter()
            .any(|(_, ty, _)| !extract_universe_from_type(ty).is_zero())
    });
    let is_large_eliminator = !is_prop || (spec.ctors.len() <= 1 && !has_type_valued_fields);
    let minor_premise_count = spec.ctors.len();
    let total_binder_count = spec.params.len() + 1 + minor_premise_count + spec.indices.len() + 1;
    EliminatorShape {
        motive_count: 1,
        minor_premise_count,
        target_count: 1,
        is_large_eliminator,
        total_binder_count,
    }
}

/// Size metrics for an inductive type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InductiveSizeMetrics {
    pub(crate) constructor_count: usize,
    pub(crate) total_field_count: usize,
    pub(crate) max_constructor_arity: usize,
    pub(crate) param_count: usize,
    pub(crate) index_count: usize,
    pub(crate) max_field_depth: usize,
    pub(crate) total_recursive_fields: usize,
}

/// Compute size metrics for an inductive spec.
pub(crate) fn compute_size_metrics(spec: &InductiveSpec) -> InductiveSizeMetrics {
    let mut max_field_depth = 0;
    let mut total_recursive_fields = 0;
    for ctor in &spec.ctors {
        for (_, field_ty, is_rec) in &ctor.fields {
            let depth = pi_nesting_depth(field_ty);
            if depth > max_field_depth {
                max_field_depth = depth;
            }
            if *is_rec {
                total_recursive_fields += 1;
            }
        }
    }
    InductiveSizeMetrics {
        constructor_count: spec.ctors.len(),
        total_field_count: spec.ctors.iter().map(|c| c.fields.len()).sum(),
        max_constructor_arity: spec.ctors.iter().map(|c| c.fields.len()).max().unwrap_or(0),
        param_count: spec.params.len(),
        index_count: spec.indices.len(),
        max_field_depth,
        total_recursive_fields,
    }
}

fn pi_nesting_depth(ty: &Expr) -> usize {
    let (mut depth, mut current) = (0, ty);
    while let ExprKind::Pi(_, _, body) = current.kind() {
        depth += 1;
        current = body;
    }
    depth
}

/// Positivity analysis result for one parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ParameterPositivity {
    Unused,
    StrictlyPositive,
    Negative(PositivityViolation),
}

/// Summary of positivity checking across all constructors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PositivitySummary {
    pub(crate) passes: bool,
    pub(crate) param_positivity: Vec<(Name, ParameterPositivity)>,
    pub(crate) self_positivity: ParameterPositivity,
}

/// Summarize positivity checking for an inductive spec.
pub(crate) fn summarize_positivity(spec: &InductiveSpec) -> PositivitySummary {
    let passes = check_strict_positivity(spec).is_ok();
    let self_positivity = if !spec.is_recursive {
        ParameterPositivity::Unused
    } else if passes {
        ParameterPositivity::StrictlyPositive
    } else {
        ParameterPositivity::Negative(check_strict_positivity(spec).unwrap_err().violation)
    };
    let param_positivity = spec
        .params
        .iter()
        .map(|(param_name, _)| {
            let mentioned = spec.ctors.iter().any(|ctor| {
                ctor.fields
                    .iter()
                    .any(|(_, ty, _)| mentions_name(ty, param_name))
            });
            if !mentioned {
                (param_name.clone(), ParameterPositivity::Unused)
            } else {
                let has_neg = spec.ctors.iter().any(|ctor| {
                    ctor.fields
                        .iter()
                        .any(|(_, ty, _)| has_negative_in_field(param_name, ty))
                });
                if has_neg {
                    (
                        param_name.clone(),
                        ParameterPositivity::Negative(PositivityViolation::NegativeOccurrence),
                    )
                } else {
                    (param_name.clone(), ParameterPositivity::StrictlyPositive)
                }
            }
        })
        .collect();
    PositivitySummary {
        passes,
        param_positivity,
        self_positivity,
    }
}

fn has_negative_in_field(name: &Name, ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::Pi(_, domain, body) => {
            mentions_name(domain, name) || has_negative_in_field(name, body)
        }
        _ => false,
    }
}

/// Pattern match completeness prediction for a type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternMatchInfo {
    pub(crate) case_count: usize,
    pub(crate) needs_default: bool,
    pub(crate) is_empty: bool,
    pub(crate) is_irrefutable: bool,
    pub(crate) constructor_names: Vec<Name>,
}

/// Predict pattern match completeness information for an inductive spec.
pub(crate) fn predict_pattern_match_info(spec: &InductiveSpec) -> PatternMatchInfo {
    let case_count = spec.ctors.len();
    PatternMatchInfo {
        case_count,
        needs_default: false,
        is_empty: case_count == 0,
        is_irrefutable: case_count == 1,
        constructor_names: spec.ctors.iter().map(|c| c.name.clone()).collect(),
    }
}

/// Full analysis report for an inductive type.
#[derive(Debug, Clone)]
pub(crate) struct InductiveAnalysisReport {
    pub(crate) name: Name,
    pub(crate) constructor_classifications: Vec<ConstructorClassification>,
    pub(crate) recursion_scheme: RecursionScheme,
    pub(crate) universe_constraints: UniverseConstraintSummary,
    pub(crate) eliminator_shape: EliminatorShape,
    pub(crate) size_metrics: InductiveSizeMetrics,
    pub(crate) positivity_summary: PositivitySummary,
    pub(crate) pattern_match_info: PatternMatchInfo,
}

/// Run all analyses on an inductive spec.
pub(crate) fn analyze_inductive(spec: &InductiveSpec) -> InductiveAnalysisReport {
    InductiveAnalysisReport {
        name: spec.name.clone(),
        constructor_classifications: classify_all_constructors(spec),
        recursion_scheme: detect_recursion_scheme(spec),
        universe_constraints: analyze_universe_constraints(spec),
        eliminator_shape: predict_eliminator_shape(spec),
        size_metrics: compute_size_metrics(spec),
        positivity_summary: summarize_positivity(spec),
        pattern_match_info: predict_pattern_match_info(spec),
    }
}

/// Run analysis on each type in a mutual inductive block.
pub(crate) fn analyze_mutual_inductive(
    spec: &MutualInductiveSpec,
) -> Result<Vec<InductiveAnalysisReport>, InductiveAnalysisError> {
    if spec.inductives.is_empty() {
        return Err(InductiveAnalysisError::EmptyMutualBlock);
    }
    Ok(spec.inductives.iter().map(analyze_inductive).collect())
}
