// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended auto-bound parameter handling for the elaborator.
//!
//! Provides auto-bound implicit detection, instance implicit insertion,
//! strict implicit handling, default value parameters, named argument
//! resolution, out-parameter detection, universe auto-binding, parameter
//! ordering validation, and statistics tracking.
//!
//! Reference: Lean 4 `src/Lean/Elab/Binders.lean`, `src/Lean/Elab/Term.lean`.

use std::collections::{HashMap, HashSet};

use clean_kernel::expr::BinderInfo;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

/// Errors specific to extended auto-bound parameter processing.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum AutoParamError {
    #[error("unknown named argument '{name}'")]
    UnknownNamedArg { name: String },
    #[error("duplicate named argument '{name}'")]
    DuplicateNamedArg { name: String },
    #[error("parameter ordering violation: {reason}")]
    OrderingViolation { reason: String },
    #[error("default value for '{param}' references unbound variable '{var}'")]
    DefaultValueUnbound { param: String, var: String },
    #[error("cyclic dependency in default values involving '{param}'")]
    CyclicDefault { param: String },
}

/// Classification of a parameter's binding mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ParamKind {
    Explicit,
    Implicit,
    StrictImplicit,
    InstanceImplicit,
}

impl From<BinderInfo> for ParamKind {
    fn from(bi: BinderInfo) -> Self {
        match bi {
            BinderInfo::Default => Self::Explicit,
            BinderInfo::Implicit => Self::Implicit,
            BinderInfo::StrictImplicit => Self::StrictImplicit,
            BinderInfo::InstImplicit => Self::InstanceImplicit,
        }
    }
}

impl From<ParamKind> for BinderInfo {
    fn from(pk: ParamKind) -> Self {
        match pk {
            ParamKind::Explicit => Self::Default,
            ParamKind::Implicit => Self::Implicit,
            ParamKind::StrictImplicit => Self::StrictImplicit,
            ParamKind::InstanceImplicit => Self::InstImplicit,
        }
    }
}

/// A single parameter descriptor with full metadata.
#[derive(Debug, Clone)]
pub(crate) struct ParamDesc {
    pub name: Name,
    pub type_expr: Expr,
    pub kind: ParamKind,
    pub default_value: Option<Expr>,
    pub is_auto_bound: bool,
    pub is_out_param: bool,
}

/// A resolved named argument mapping a parameter name to a value expression.
#[derive(Debug, Clone)]
pub(crate) struct NamedArgResolution {
    pub param_name: Name,
    pub param_index: usize,
    pub value: Expr,
}

/// Well-known typeclass names that trigger instance implicit insertion.
const KNOWN_TYPECLASSES: &[&str] = &[
    "Decidable",
    "DecidableEq",
    "DecidablePred",
    "BEq",
    "Hashable",
    "Repr",
    "ToString",
    "Inhabited",
    "Nonempty",
    "Zero",
    "One",
    "OfNat",
    "Add",
    "Sub",
    "Mul",
    "Div",
    "Mod",
    "Neg",
    "HPow",
    "HAdd",
    "HSub",
    "HMul",
    "HDiv",
    "HMod",
    "HAnd",
    "HOr",
    "HXor",
    "Monad",
    "Functor",
    "Applicative",
    "Pure",
    "Bind",
    "LT",
    "LE",
    "Ord",
    "Append",
    "Membership",
    "GetElem",
    "SetElem",
    "Stream",
    "ForIn",
    "ToFormat",
    "Coe",
    "CoeSort",
    "CoeFun",
    "Fintype",
    "CommRing",
    "Field",
    "LinearOrder",
];

/// Check if a name refers to a known typeclass.
#[must_use]
pub(crate) fn is_known_typeclass(name: &str) -> bool {
    KNOWN_TYPECLASSES.contains(&name)
}

/// Scan an expression for typeclass applications, returning `(class_name, args)`.
#[must_use]
pub(crate) fn detect_instance_implicits(expr: &Expr) -> Vec<(String, Vec<Expr>)> {
    let mut results = Vec::new();
    detect_instance_inner(expr, &mut results, 0, 32);
    results
}

fn detect_instance_inner(
    expr: &Expr,
    results: &mut Vec<(String, Vec<Expr>)>,
    depth: usize,
    max_depth: usize,
) {
    if depth >= max_depth {
        return;
    }
    match expr.kind() {
        ExprKind::App(func, arg) => {
            let mut args = vec![(**arg).clone()];
            let mut head = &**func;
            while let ExprKind::App(f, a) = head.kind() {
                args.push((**a).clone());
                head = f;
            }
            args.reverse();
            if let ExprKind::Const(name, _) = head.kind() {
                let s = format!("{}", name);
                if is_known_typeclass(&s) {
                    results.push((s, args));
                }
            }
            detect_instance_inner(func, results, depth + 1, max_depth);
            detect_instance_inner(arg, results, depth + 1, max_depth);
        }
        ExprKind::Pi(_bd, ty, body) | ExprKind::Lam(_bd, ty, body) => {
            detect_instance_inner(ty, results, depth + 1, max_depth);
            detect_instance_inner(body, results, depth + 1, max_depth);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            detect_instance_inner(ty, results, depth + 1, max_depth);
            detect_instance_inner(val, results, depth + 1, max_depth);
            detect_instance_inner(body, results, depth + 1, max_depth);
        }
        _ => {}
    }
}

/// Check whether a strict implicit (`{{x : T}}`) should be inserted at `current_index`.
/// Only inserted when a later explicit argument exists.
#[must_use]
pub(crate) fn should_insert_strict_implicit(params: &[ParamDesc], current_index: usize) -> bool {
    params[current_index + 1..]
        .iter()
        .any(|p| p.kind == ParamKind::Explicit)
}

/// Resolve default values for unsupplied parameters.
#[must_use]
pub(crate) fn resolve_defaults(
    params: &[ParamDesc],
    supplied: &HashSet<usize>,
) -> Vec<(usize, Expr)> {
    params
        .iter()
        .enumerate()
        .filter_map(|(i, p)| {
            if !supplied.contains(&i) {
                p.default_value.as_ref().map(|dv| (i, dv.clone()))
            } else {
                None
            }
        })
        .collect()
}

/// Validate default values do not forward-reference later parameters.
pub(crate) fn validate_defaults(params: &[ParamDesc]) -> Result<(), AutoParamError> {
    let idx: HashMap<&Name, usize> = params
        .iter()
        .enumerate()
        .map(|(i, p)| (&p.name, i))
        .collect();
    for (i, param) in params.iter().enumerate() {
        if let Some(ref dv) = param.default_value {
            for free_name in &collect_const_names(dv) {
                if let Some(&j) = idx.get(free_name) {
                    if j > i {
                        return Err(AutoParamError::DefaultValueUnbound {
                            param: format!("{}", param.name),
                            var: format!("{}", free_name),
                        });
                    }
                }
            }
        }
    }
    Ok(())
}

/// Resolve named arguments `(name := value)` to parameter positions.
pub(crate) fn resolve_named_args(
    params: &[ParamDesc],
    named_args: &[(Name, Expr)],
) -> Result<Vec<NamedArgResolution>, AutoParamError> {
    let mut seen = HashSet::new();
    let mut results = Vec::with_capacity(named_args.len());
    for (arg_name, value) in named_args {
        let s = format!("{}", arg_name);
        if !seen.insert(s.clone()) {
            return Err(AutoParamError::DuplicateNamedArg { name: s });
        }
        let position = params
            .iter()
            .position(|p| p.name == *arg_name)
            .ok_or(AutoParamError::UnknownNamedArg { name: s })?;
        results.push(NamedArgResolution {
            param_name: arg_name.clone(),
            param_index: position,
            value: value.clone(),
        });
    }
    Ok(results)
}

/// Detect out-parameters: params whose name appears in the return type as a Const.
#[must_use]
pub(crate) fn detect_out_params(params: &[ParamDesc], return_type: &Expr) -> Vec<usize> {
    let ret_consts = collect_const_names(return_type);
    let ret_set: HashSet<&Name> = ret_consts.iter().collect();
    params
        .iter()
        .enumerate()
        .filter(|(_, p)| ret_set.contains(&p.name))
        .map(|(i, _)| i)
        .collect()
}

/// Scan an expression for undeclared universe level parameters.
#[must_use]
pub(crate) fn collect_universe_params(expr: &Expr, declared: &[Name]) -> Vec<Name> {
    let decl_set: HashSet<&Name> = declared.iter().collect();
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    collect_univ_inner(expr, &decl_set, &mut found, &mut seen, 0, 64);
    found
}

fn collect_univ_inner(
    expr: &Expr,
    declared: &HashSet<&Name>,
    found: &mut Vec<Name>,
    seen: &mut HashSet<Name>,
    depth: usize,
    max_depth: usize,
) {
    if depth >= max_depth {
        return;
    }
    match expr.kind() {
        ExprKind::Sort(level) => collect_level_params(level, declared, found, seen),
        ExprKind::Const(_, levels) => {
            for level in levels.iter() {
                collect_level_params(level, declared, found, seen);
            }
        }
        ExprKind::App(f, a) => {
            collect_univ_inner(f, declared, found, seen, depth + 1, max_depth);
            collect_univ_inner(a, declared, found, seen, depth + 1, max_depth);
        }
        ExprKind::Pi(_, ty, body) | ExprKind::Lam(_, ty, body) => {
            collect_univ_inner(ty, declared, found, seen, depth + 1, max_depth);
            collect_univ_inner(body, declared, found, seen, depth + 1, max_depth);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_univ_inner(ty, declared, found, seen, depth + 1, max_depth);
            collect_univ_inner(val, declared, found, seen, depth + 1, max_depth);
            collect_univ_inner(body, declared, found, seen, depth + 1, max_depth);
        }
        _ => {}
    }
}

fn collect_level_params(
    level: &Level,
    declared: &HashSet<&Name>,
    found: &mut Vec<Name>,
    seen: &mut HashSet<Name>,
) {
    match level {
        Level::Param(name) => {
            if !declared.contains(name) && seen.insert(name.clone()) {
                found.push(name.clone());
            }
        }
        Level::Succ(inner) => collect_level_params(inner, declared, found, seen),
        Level::Max(a, b) | Level::IMax(a, b) => {
            collect_level_params(a, declared, found, seen);
            collect_level_params(b, declared, found, seen);
        }
        Level::Zero => {}
    }
}

/// Validate parameter ordering: implicit/instance before explicit (unless auto-bound).
pub(crate) fn validate_param_ordering(params: &[ParamDesc]) -> Result<(), AutoParamError> {
    let mut seen_explicit = false;
    for param in params {
        match param.kind {
            ParamKind::Explicit => {
                seen_explicit = true;
            }
            ParamKind::Implicit | ParamKind::StrictImplicit => {
                if seen_explicit && !param.is_auto_bound {
                    return Err(AutoParamError::OrderingViolation {
                        reason: format!(
                            "implicit parameter '{}' appears after explicit parameter",
                            param.name
                        ),
                    });
                }
            }
            ParamKind::InstanceImplicit => {
                if seen_explicit && !param.is_auto_bound {
                    return Err(AutoParamError::OrderingViolation {
                        reason: format!(
                            "instance implicit '{}' appears after explicit parameter",
                            param.name
                        ),
                    });
                }
            }
        }
    }
    Ok(())
}

/// Statistics for auto-bound parameter processing.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AutoParamStats {
    pub implicit_type_params: u32,
    pub instance_implicits: u32,
    pub strict_implicits: u32,
    pub defaults_applied: u32,
    pub named_args_resolved: u32,
    pub out_params_detected: u32,
    pub universe_params: u32,
}

impl AutoParamStats {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn total_insertions(&self) -> u32 {
        self.implicit_type_params
            + self.instance_implicits
            + self.strict_implicits
            + self.defaults_applied
            + self.named_args_resolved
            + self.out_params_detected
            + self.universe_params
    }

    pub(crate) fn merge(&mut self, other: &Self) {
        self.implicit_type_params += other.implicit_type_params;
        self.instance_implicits += other.instance_implicits;
        self.strict_implicits += other.strict_implicits;
        self.defaults_applied += other.defaults_applied;
        self.named_args_resolved += other.named_args_resolved;
        self.out_params_detected += other.out_params_detected;
        self.universe_params += other.universe_params;
    }
}

/// Main entry point: validate ordering, resolve named args, apply defaults,
/// detect out-params, and collect stats.
pub(crate) fn process_params(
    params: &mut [ParamDesc],
    named_args: &[(Name, Expr)],
    return_type: Option<&Expr>,
) -> Result<AutoParamStats, AutoParamError> {
    let mut stats = AutoParamStats::new();
    validate_param_ordering(params)?;
    validate_defaults(params)?;

    let resolved = resolve_named_args(params, named_args)?;
    stats.named_args_resolved = resolved.len() as u32;

    if let Some(ret_ty) = return_type {
        let out_indices = detect_out_params(params, ret_ty);
        stats.out_params_detected = out_indices.len() as u32;
        for idx in out_indices {
            params[idx].is_out_param = true;
        }
    }

    let supplied: HashSet<usize> = resolved.iter().map(|r| r.param_index).collect();
    stats.defaults_applied = resolve_defaults(params, &supplied).len() as u32;

    for param in params.iter() {
        match param.kind {
            ParamKind::Implicit if param.is_auto_bound => {
                stats.implicit_type_params += 1;
            }
            ParamKind::StrictImplicit => {
                stats.strict_implicits += 1;
            }
            ParamKind::InstanceImplicit => {
                stats.instance_implicits += 1;
            }
            _ => {}
        }
    }
    Ok(stats)
}

/// Collect all `Const` names from an expression (for dependency analysis).
fn collect_const_names(expr: &Expr) -> Vec<Name> {
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    collect_const_inner(expr, &mut found, &mut seen, 0, 32);
    found
}

fn collect_const_inner(
    expr: &Expr,
    found: &mut Vec<Name>,
    seen: &mut HashSet<Name>,
    depth: usize,
    max_depth: usize,
) {
    if depth >= max_depth {
        return;
    }
    match expr.kind() {
        ExprKind::Const(name, _) if seen.insert(name.clone()) => {
            found.push(name.clone());
        }
        ExprKind::App(f, a) => {
            collect_const_inner(f, found, seen, depth + 1, max_depth);
            collect_const_inner(a, found, seen, depth + 1, max_depth);
        }
        ExprKind::Pi(_, ty, body) | ExprKind::Lam(_, ty, body) => {
            collect_const_inner(ty, found, seen, depth + 1, max_depth);
            collect_const_inner(body, found, seen, depth + 1, max_depth);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_const_inner(ty, found, seen, depth + 1, max_depth);
            collect_const_inner(val, found, seen, depth + 1, max_depth);
            collect_const_inner(body, found, seen, depth + 1, max_depth);
        }
        _ => {}
    }
}
