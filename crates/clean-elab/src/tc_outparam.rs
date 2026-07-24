// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type class `outParam` handling for instance resolution.
//!
//! In Lean 4, `outParam` marks type class parameters that should be determined
//! by the instance rather than the caller. Critical for heterogeneous operators
//! like `HAdd`, `HMul`, `OfNat`.
//!
//! When resolving `HAdd Nat Nat ?γ`, the resolver finds `instHAddNatNat :
//! HAdd Nat Nat Nat` and assigns `?γ := Nat`.
//!
//! Reference: Lean 4 `src/Lean/Meta/SynthInstance.lean`

use crate::instances::{extract_class_app, InstanceInfo, InstanceTable};
use clean_kernel::expr::{BinderData, BinderInfo, Expr, ExprKind};
use clean_kernel::name::Name;
use clean_kernel::Environment;
use thiserror::Error;

/// Describes an outParam position in a type class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OutParamInfo {
    /// Parameter index (0-based among the class parameters)
    pub(crate) index: usize,
    /// Parameter name (for diagnostics)
    pub(crate) name: Name,
    /// Whether this is a semi-outParam (can be inferred but not required)
    pub(crate) is_semi: bool,
}

/// Configuration for outParam resolution behavior.
#[derive(Debug, Clone)]
pub(crate) struct OutParamConfig {
    /// Maximum depth for recursive outParam resolution.
    pub(crate) max_depth: usize,
    /// Whether to try `@[default_instance]` when outParam is ambiguous.
    pub(crate) allow_default_instances: bool,
    /// Whether semi-outParam resolution is enabled.
    pub(crate) semi_outparam_enabled: bool,
}

impl Default for OutParamConfig {
    fn default() -> Self {
        Self {
            max_depth: 32,
            allow_default_instances: true,
            semi_outparam_enabled: true,
        }
    }
}

/// Result of outParam resolution for a single class application.
#[derive(Debug, Clone)]
pub(crate) enum OutParamResult {
    /// All outParams resolved. Contains `(index, resolved_expr)` pairs.
    Resolved(Vec<(usize, Expr)>),
    /// Multiple instances match non-outParam args with conflicting outParams.
    Ambiguous(Vec<Name>),
    /// Resolution failed with a structured error.
    Failed(OutParamError),
}

/// Errors specific to outParam resolution.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum OutParamError {
    #[error("Class `{0}` is not registered")]
    UnregisteredClass(Name),
    #[error("No instance matches non-outParam args for class `{0}`")]
    NoMatchingInstance(Name),
    #[error("OutParam unification failed for instance `{instance}` at index {index}")]
    UnificationFailed { instance: Name, index: usize },
    #[error("OutParam resolution exceeded max depth ({0})")]
    MaxDepthExceeded(usize),
    #[error("Goal type is not a class application")]
    NotClassApplication,
}

/// OutParam resolver for type class instance resolution.
///
/// Stateless resolver operating on `InstanceTable` and `Environment`.
pub(crate) struct OutParamResolver<'a> {
    env: &'a Environment,
    config: OutParamConfig,
}

impl<'a> OutParamResolver<'a> {
    pub(crate) fn new(env: &'a Environment, config: OutParamConfig) -> Self {
        Self { env, config }
    }

    pub(crate) fn with_defaults(env: &'a Environment) -> Self {
        Self::new(env, OutParamConfig::default())
    }

    /// Detect outParam positions for a type class from the InstanceTable or
    /// kernel environment's class registry.
    pub(crate) fn detect_out_params(
        &self,
        class_name: &Name,
        instances: &InstanceTable,
    ) -> Vec<OutParamInfo> {
        if let Some(class_info) = instances.get_class(class_name) {
            return self
                .collect_out_param_infos(&class_info.out_params, &class_info.semi_out_params);
        }
        if let Some(kernel_info) = self.env.get_class_info(class_name) {
            return self
                .collect_out_param_infos(&kernel_info.out_params, &kernel_info.semi_out_params);
        }
        Vec::new()
    }

    /// Detect outParam positions by scanning a class type's Pi-binder chain.
    ///
    /// `outParam` is represented as `App (Const "outParam") T` wrapping the
    /// parameter type at the kernel level.
    pub(crate) fn detect_out_params_from_type(&self, class_type: &Expr) -> Vec<OutParamInfo> {
        let mut result = Vec::new();
        let mut current = class_type;
        let mut index = 0;

        while let ExprKind::Pi(_bd, ty, body) = current.kind() {
            if is_out_param_type(ty) {
                result.push(OutParamInfo {
                    index,
                    name: Name::from_string(&format!("param_{index}")),
                    is_semi: false,
                });
            } else if is_semi_out_param_type(ty) {
                result.push(OutParamInfo {
                    index,
                    name: Name::from_string(&format!("param_{index}")),
                    is_semi: true,
                });
            }
            index += 1;
            current = body.as_ref();
        }
        result
    }

    /// Resolve outParams for a class application given candidate instances.
    pub(crate) fn resolve_out_params(
        &self,
        class_name: &Name,
        goal_args: &[Expr],
        instances: &InstanceTable,
        depth: usize,
    ) -> OutParamResult {
        if depth > self.config.max_depth {
            return OutParamResult::Failed(OutParamError::MaxDepthExceeded(self.config.max_depth));
        }

        let out_param_indices = self.detect_out_params(class_name, instances);
        if out_param_indices.is_empty() {
            return OutParamResult::Resolved(Vec::new());
        }

        let candidates = instances.get_instances(class_name);
        if candidates.is_empty() {
            return OutParamResult::Failed(OutParamError::NoMatchingInstance(class_name.clone()));
        }

        let out_indices: std::collections::HashSet<usize> =
            out_param_indices.iter().map(|info| info.index).collect();

        let mut matching: Vec<(&InstanceInfo, Vec<(usize, Expr)>)> = Vec::new();
        for candidate in candidates {
            if let Some(solutions) =
                self.try_match_non_outparams(candidate, goal_args, &out_indices)
            {
                matching.push((candidate, solutions));
            }
        }

        match matching.len() {
            0 => {
                if self.config.allow_default_instances {
                    if let Some(default_name) = self.select_default_instance(class_name) {
                        for candidate in candidates {
                            if candidate.name == default_name {
                                if let Some(solutions) =
                                    self.try_match_non_outparams(candidate, goal_args, &out_indices)
                                {
                                    return OutParamResult::Resolved(solutions);
                                }
                            }
                        }
                    }
                }
                OutParamResult::Failed(OutParamError::NoMatchingInstance(class_name.clone()))
            }
            1 => {
                let solutions = matching
                    .into_iter()
                    .next()
                    .map(|(_, s)| s)
                    .unwrap_or_default();
                OutParamResult::Resolved(solutions)
            }
            _ => self.resolve_ambiguity(matching),
        }
    }

    /// Select a default instance for a class from the kernel environment.
    pub(crate) fn select_default_instance(&self, class_name: &Name) -> Option<Name> {
        self.env
            .get_class_instances(class_name)
            .iter()
            .find(|inst| self.env.is_default_instance(&inst.name))
            .map(|inst| inst.name.clone())
    }

    /// Propagate resolved outParam solutions into a goal argument vector.
    #[must_use]
    pub(crate) fn propagate_solutions(
        &self,
        goal_args: &[Expr],
        solutions: &[(usize, Expr)],
    ) -> Vec<Expr> {
        let mut result = goal_args.to_vec();
        for (index, expr) in solutions {
            if *index < result.len() {
                result[*index] = expr.clone();
            }
        }
        result
    }

    // -- Internal helpers --

    /// Build OutParamInfo list from out_params and semi_out_params index vecs.
    fn collect_out_param_infos(
        &self,
        out_params: &[usize],
        semi_out_params: &[usize],
    ) -> Vec<OutParamInfo> {
        let mut result: Vec<OutParamInfo> = out_params
            .iter()
            .map(|&index| OutParamInfo {
                index,
                name: Name::from_string(&format!("out_{index}")),
                is_semi: false,
            })
            .collect();

        if self.config.semi_outparam_enabled {
            result.extend(semi_out_params.iter().map(|&index| OutParamInfo {
                index,
                name: Name::from_string(&format!("semi_out_{index}")),
                is_semi: true,
            }));
        }
        result.sort_by_key(|p| p.index);
        result
    }

    /// Try to match an instance against goal args, ignoring outParam positions.
    /// Returns outParam solutions if non-outParam args match structurally.
    fn try_match_non_outparams(
        &self,
        candidate: &InstanceInfo,
        goal_args: &[Expr],
        out_indices: &std::collections::HashSet<usize>,
    ) -> Option<Vec<(usize, Expr)>> {
        let (_, inst_args) = extract_class_app(&candidate.type_)?;
        if inst_args.len() != goal_args.len() {
            return None;
        }

        for (i, (inst_arg, goal_arg)) in inst_args.iter().zip(goal_args.iter()).enumerate() {
            if out_indices.contains(&i) {
                continue;
            }
            if !structural_eq(inst_arg, goal_arg) {
                return None;
            }
        }

        let solutions: Vec<(usize, Expr)> = out_indices
            .iter()
            .filter_map(|&idx| inst_args.get(idx).map(|expr| (idx, expr.clone())))
            .collect();
        Some(solutions)
    }

    /// Check if multiple matches agree on outParam values; return Resolved or Ambiguous.
    fn resolve_ambiguity(
        &self,
        matching: Vec<(&InstanceInfo, Vec<(usize, Expr)>)>,
    ) -> OutParamResult {
        let first_solutions = &matching[0].1;
        let all_agree = matching[1..].iter().all(|(_, solutions)| {
            solutions.len() == first_solutions.len()
                && solutions
                    .iter()
                    .zip(first_solutions.iter())
                    .all(|((ia, ea), (ib, eb))| ia == ib && structural_eq(ea, eb))
        });

        if all_agree {
            let solutions = matching
                .into_iter()
                .next()
                .map(|(_, s)| s)
                .unwrap_or_default();
            OutParamResult::Resolved(solutions)
        } else {
            let names: Vec<Name> = matching.iter().map(|(inst, _)| inst.name.clone()).collect();
            OutParamResult::Ambiguous(names)
        }
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// Check if a type expression is `@outParam T`.
pub(crate) fn is_out_param_type(ty: &Expr) -> bool {
    if let ExprKind::App(func, _) = ty.kind() {
        if let ExprKind::Const(name, _) = func.kind() {
            let s = name.to_string();
            return s == "outParam" || s == "Lean.outParam";
        }
    }
    false
}

/// Check if a type expression is `@semiOutParam T`.
pub(crate) fn is_semi_out_param_type(ty: &Expr) -> bool {
    if let ExprKind::App(func, _) = ty.kind() {
        if let ExprKind::Const(name, _) = func.kind() {
            let s = name.to_string();
            return s == "semiOutParam" || s == "Lean.semiOutParam";
        }
    }
    false
}

/// Unwrap an `outParam`/`semiOutParam` wrapper, returning the inner type.
pub(crate) fn unwrap_out_param(ty: &Expr) -> Option<&Expr> {
    if let ExprKind::App(func, inner) = ty.kind() {
        if let ExprKind::Const(name, _) = func.kind() {
            let s = name.to_string();
            if s == "outParam"
                || s == "Lean.outParam"
                || s == "semiOutParam"
                || s == "Lean.semiOutParam"
            {
                return Some(inner.as_ref());
            }
        }
    }
    None
}

/// Check if a binder has InstImplicit info (instance implicit `[x : T]`).
pub(crate) fn is_inst_implicit_binder(bd: &BinderData) -> bool {
    bd.info == BinderInfo::InstImplicit
}

/// Conservative structural equality for expressions (no alpha-equiv or WHNF).
fn structural_eq(a: &Expr, b: &Expr) -> bool {
    match (a.kind(), b.kind()) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
        (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            structural_eq(f1, f2) && structural_eq(a1, a2)
        }
        (ExprKind::Lam(bi1, ty1, body1), ExprKind::Lam(bi2, ty2, body2))
        | (ExprKind::Pi(bi1, ty1, body1), ExprKind::Pi(bi2, ty2, body2)) => {
            bi1 == bi2 && structural_eq(ty1, ty2) && structural_eq(body1, body2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        _ => false,
    }
}

/// Count outParam positions for a class.
pub(crate) fn count_out_params(class_name: &Name, instances: &InstanceTable) -> usize {
    instances
        .get_class(class_name)
        .map(|info| info.out_params.len())
        .unwrap_or(0)
}

/// Check whether any goal argument at an outParam position is an FVar
/// (potential unresolved metavariable).
pub(crate) fn has_unresolved_out_params(
    class_name: &Name,
    goal_args: &[Expr],
    instances: &InstanceTable,
) -> bool {
    let Some(class_info) = instances.get_class(class_name) else {
        return false;
    };
    class_info.out_params.iter().any(|&idx| {
        goal_args
            .get(idx)
            .map(|arg| matches!(arg.kind(), ExprKind::FVar(_)))
            .unwrap_or(false)
    })
}

#[cfg(test)]
#[path = "tc_outparam_tests.rs"]
mod tests;
