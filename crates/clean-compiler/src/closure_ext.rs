// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended closure-environment analysis for LCNF closure conversion.
//!
//! This module adds conservative analysis and debug helpers for the closure
//! environments produced by [`crate::closure`]. It focuses on capture shape,
//! layout estimation, escape behavior, optimization hints, and pretty-printing.
use crate::closure::{CaptureMode, CapturedVar, ClosureConvertResult, ClosureEnv};
use crate::lcnf::{Alt, Arg, Code, FunDecl, LetValue, Param};
use clean_kernel::expr::{ExprKind, ZFCSetExpr};
use clean_kernel::{Expr, FVarId, Name};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
/// Configuration for closure analysis and hint generation.
#[derive(Clone, Debug)]
pub(crate) struct ClosureAnalysisConfig {
    pub(crate) inline_capture_limit: usize,
    pub(crate) inline_body_node_limit: usize,
    pub(crate) pointer_size: usize,
    pub(crate) pointer_alignment: usize,
    pub(crate) enable_dead_capture_elimination: bool,
}
impl Default for ClosureAnalysisConfig {
    fn default() -> Self {
        Self {
            inline_capture_limit: 2,
            inline_body_node_limit: 16,
            pointer_size: 8,
            pointer_alignment: 8,
            enable_dead_capture_elimination: true,
        }
    }
}

/// Aggregate statistics for a single closure environment.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ClosureStats {
    pub(crate) capture_count: usize,
    pub(crate) by_value_captures: usize,
    pub(crate) by_ref_captures: usize,
    pub(crate) scalar_captures: usize,
    pub(crate) object_captures: usize,
    pub(crate) erased_captures: usize,
    pub(crate) unknown_captures: usize,
    pub(crate) environment_size: usize,
    pub(crate) alignment: usize,
    pub(crate) max_field_offset: usize,
    pub(crate) closure_depth: usize,
}
/// Best-effort capture classification from debug names and mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CaptureClassification {
    Scalar,
    Object,
    Erased,
    Unknown,
}
/// Conservative escape analysis result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EscapeStatus {
    Local,
    Escaping,
    Unknown,
}
/// Optimization hints derived from static closure analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClosureOptHint {
    InlineCandidate,
    ConstantClosure,
    HasDeadCaptures,
    NoHint,
}

/// Estimated layout of a closure environment payload.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ClosureLayout {
    pub(crate) size: usize,
    pub(crate) alignment: usize,
    pub(crate) header_size: usize,
    pub(crate) field_offsets: HashMap<FVarId, usize>,
}

/// Summarize one closure environment.
#[must_use]
pub(crate) fn analyze_closure_env(env: &ClosureEnv) -> ClosureStats {
    let mut stats = ClosureStats {
        capture_count: env.capture_count(),
        ..ClosureStats::default()
    };
    for capture in env.iter() {
        match capture.capture_mode {
            CaptureMode::ByValue => stats.by_value_captures += 1,
            CaptureMode::ByRef => stats.by_ref_captures += 1,
        }
        match classify_capture(capture) {
            CaptureClassification::Scalar => stats.scalar_captures += 1,
            CaptureClassification::Object => stats.object_captures += 1,
            CaptureClassification::Erased => stats.erased_captures += 1,
            CaptureClassification::Unknown => stats.unknown_captures += 1,
        }
    }
    let layout = compute_closure_layout(env);
    stats.environment_size = layout.size;
    stats.alignment = layout.alignment;
    stats.max_field_offset = layout.field_offsets.values().copied().max().unwrap_or(0);
    stats
}

/// Classify each capture in an environment.
#[must_use]
pub(crate) fn classify_captures(env: &ClosureEnv) -> Vec<(FVarId, CaptureClassification)> {
    env.iter()
        .map(|capture| (capture.fvar_id, classify_capture(capture)))
        .collect()
}

/// Determine whether a closure escapes its defining scope.
#[must_use]
pub(crate) fn detect_escape_status(
    env: &ClosureEnv,
    result: &ClosureConvertResult,
) -> EscapeStatus {
    if find_matching_fun_decl(result, env).is_none() {
        return EscapeStatus::Unknown;
    }
    let scan = scan_escapes(&result.code, env.body_fvar);
    if scan.escapes {
        EscapeStatus::Escaping
    } else if scan.ambiguous {
        EscapeStatus::Unknown
    } else {
        EscapeStatus::Local
    }
}

/// Compute optimization hints for a single closure.
#[must_use]
pub(crate) fn compute_optimization_hints(
    env: &ClosureEnv,
    result: &ClosureConvertResult,
    config: &ClosureAnalysisConfig,
) -> Vec<ClosureOptHint> {
    let pruned = if config.enable_dead_capture_elimination {
        eliminate_dead_captures(env, result)
    } else {
        env.clone()
    };
    let mut hints = Vec::new();
    if pruned.capture_count() < env.capture_count() {
        hints.push(ClosureOptHint::HasDeadCaptures);
    }
    if pruned.capture_count() == 0 {
        hints.push(ClosureOptHint::ConstantClosure);
    }
    if let Some(fun_decl) = find_matching_fun_decl(result, env) {
        let body_nodes = count_code_nodes(&fun_decl.body);
        if detect_escape_status(env, result) == EscapeStatus::Local
            && pruned.capture_count() <= config.inline_capture_limit
            && body_nodes <= config.inline_body_node_limit
        {
            hints.push(ClosureOptHint::InlineCandidate);
        }
    }
    if hints.is_empty() {
        hints.push(ClosureOptHint::NoHint);
    }
    hints
}

/// Remove captures unused by the converted closure body.
#[must_use]
pub(crate) fn eliminate_dead_captures(
    env: &ClosureEnv,
    result: &ClosureConvertResult,
) -> ClosureEnv {
    let live = live_capture_ids(env, result);
    let captures = env
        .captures
        .iter()
        .filter(|capture| live.contains(&capture.fvar_id))
        .enumerate()
        .map(|(index, capture)| CapturedVar {
            fvar_id: capture.fvar_id,
            name: capture.name.clone(),
            index,
            capture_mode: capture.capture_mode.clone(),
        })
        .collect();
    ClosureEnv {
        captures,
        body_fvar: env.body_fvar,
        param_count: env.param_count,
    }
}

/// Estimate the in-memory layout of an environment.
#[must_use]
pub(crate) fn compute_closure_layout(env: &ClosureEnv) -> ClosureLayout {
    let config = ClosureAnalysisConfig::default();
    let pointer_size = config.pointer_size.max(1);
    let alignment = config.pointer_alignment.max(1);
    let mut offset = pointer_size;
    let mut field_offsets = HashMap::new();
    for capture in env.iter() {
        if classify_capture(capture) == CaptureClassification::Erased {
            continue;
        }
        offset = align_up(offset, alignment);
        field_offsets.insert(capture.fvar_id, offset);
        offset += pointer_size;
    }
    ClosureLayout {
        size: align_up(offset, alignment),
        alignment,
        header_size: pointer_size,
        field_offsets,
    }
}

/// Pretty-print a closure environment for debugging.
#[must_use]
pub(crate) fn pretty_print_env(env: &ClosureEnv) -> String {
    let layout = compute_closure_layout(env);
    let classes: HashMap<FVarId, CaptureClassification> =
        classify_captures(env).into_iter().collect();
    let mut out = String::new();
    let _ = writeln!(
        out,
        "closure _x{} params={} captures={} size={} align={}",
        env.body_fvar.as_u64(),
        env.param_count,
        env.capture_count(),
        layout.size,
        layout.alignment
    );
    for capture in env.iter() {
        let class = classes
            .get(&capture.fvar_id)
            .copied()
            .unwrap_or(CaptureClassification::Unknown);
        let offset = layout
            .field_offsets
            .get(&capture.fvar_id)
            .map(|value| value.to_string())
            .unwrap_or_else(|| String::from("erased"));
        let name_ref: &Name = &capture.name;
        let name = if name_ref.is_anon() {
            String::from("[anonymous]")
        } else {
            name_ref.to_string()
        };
        let _ = writeln!(
            out,
            "  [{}] _x{} {} mode={:?} class={:?} offset={}",
            capture.index,
            capture.fvar_id.as_u64(),
            name,
            capture.capture_mode,
            class,
            offset
        );
    }
    out
}

/// Analyze all closures in a conversion result.
#[must_use]
pub(crate) fn analyze_all_closures(result: &ClosureConvertResult) -> Vec<ClosureStats> {
    let depths = collect_depths(&result.code);
    result
        .closures
        .iter()
        .map(|env| {
            let mut stats = analyze_closure_env(env);
            stats.closure_depth = depths.get(&env.body_fvar).copied().unwrap_or(0);
            stats
        })
        .collect()
}

/// Compute lexical nesting depth for one closure.
#[must_use]
pub(crate) fn compute_closure_depth(env: &ClosureEnv, result: &ClosureConvertResult) -> usize {
    collect_depths(&result.code)
        .get(&env.body_fvar)
        .copied()
        .unwrap_or(0)
}

/// Detect closures that become constant after dead-capture elimination.
#[must_use]
pub(crate) fn detect_constant_closures(result: &ClosureConvertResult) -> Vec<FVarId> {
    result
        .closures
        .iter()
        .filter(|env| eliminate_dead_captures(env, result).capture_count() == 0)
        .map(|env| env.body_fvar)
        .collect()
}

#[derive(Default)]
struct EscapeScan {
    escapes: bool,
    ambiguous: bool,
}

#[must_use]
fn classify_capture(capture: &CapturedVar) -> CaptureClassification {
    if capture.name.is_anon() {
        return CaptureClassification::Unknown;
    }
    let component = capture
        .name
        .last_component()
        .unwrap_or_else(|| String::from("[anonymous]"));
    if matches!(component.as_str(), "_" | "proof" | "inst" | "type") {
        return CaptureClassification::Erased;
    }
    if matches!(
        component.as_str(),
        "i" | "j" | "k" | "n" | "idx" | "len" | "size" | "tag" | "arity" | "depth" | "offset"
    ) || component.ends_with("_idx")
        || component.ends_with("_len")
        || component.ends_with("_size")
    {
        return CaptureClassification::Scalar;
    }
    match capture.capture_mode {
        CaptureMode::ByRef | CaptureMode::ByValue => CaptureClassification::Object,
    }
}

#[must_use]
fn align_up(value: usize, alignment: usize) -> usize {
    let alignment = alignment.max(1);
    let remainder = value % alignment;
    if remainder == 0 {
        value
    } else {
        value + (alignment - remainder)
    }
}

#[must_use]
fn find_matching_fun_decl<'a>(
    result: &'a ClosureConvertResult,
    env: &ClosureEnv,
) -> Option<&'a FunDecl> {
    let fun_decl = find_fun_decl(&result.code, env.body_fvar)?;
    let split_at = env.capture_count().min(fun_decl.params.len());
    let (capture_params, declared_params): (&[Param], &[Param]) =
        fun_decl.params.split_at(split_at);
    if capture_params.len() == env.capture_count()
        && declared_params.len() == env.param_count
        && capture_params
            .iter()
            .zip(&env.captures)
            .all(|(param, capture)| param.fvar_id == capture.fvar_id)
    {
        Some(fun_decl)
    } else {
        None
    }
}

#[must_use]
fn find_fun_decl(code: &Code, target: FVarId) -> Option<&FunDecl> {
    match code {
        Code::Let(_, body) => find_fun_decl(body, target),
        Code::Fun(fun_decl, body) => {
            if fun_decl.fvar_id == target {
                Some(fun_decl)
            } else {
                find_fun_decl(&fun_decl.body, target).or_else(|| find_fun_decl(body, target))
            }
        }
        Code::JoinPoint(fun_decl, body) => {
            find_fun_decl(&fun_decl.body, target).or_else(|| find_fun_decl(body, target))
        }
        Code::Cases(cases) => cases.alts.iter().find_map(|alt| match alt {
            Alt::Ctor { body, .. } | Alt::Default(body) => find_fun_decl(body, target),
        }),
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => None,
    }
}

#[must_use]
fn live_capture_ids(env: &ClosureEnv, result: &ClosureConvertResult) -> HashSet<FVarId> {
    let Some(fun_decl) = find_matching_fun_decl(result, env) else {
        return env.iter().map(|capture| capture.fvar_id).collect();
    };
    env.iter()
        .filter(|capture| code_refs_fvar(&fun_decl.body, capture.fvar_id))
        .map(|capture| capture.fvar_id)
        .collect()
}

#[must_use]
fn code_refs_fvar(code: &Code, target: FVarId) -> bool {
    match code {
        Code::Let(decl, body) => {
            value_refs_fvar(&decl.value, target)
                || expr_refs_fvar(&decl.ty, target)
                || code_refs_fvar(body, target)
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            fun_decl
                .params
                .iter()
                .any(|param| expr_refs_fvar(&param.ty, target))
                || expr_refs_fvar(&fun_decl.ty, target)
                || code_refs_fvar(&fun_decl.body, target)
                || code_refs_fvar(body, target)
        }
        Code::Cases(cases) => {
            cases.scrutinee == target
                || expr_refs_fvar(&cases.result_type, target)
                || cases.alts.iter().any(|alt| match alt {
                    Alt::Ctor { params, body, .. } => {
                        params.iter().any(|param| expr_refs_fvar(&param.ty, target))
                            || code_refs_fvar(body, target)
                    }
                    Alt::Default(body) => code_refs_fvar(body, target),
                })
        }
        Code::Jmp { jp, args } => {
            *jp == target || args.iter().any(|arg| arg_refs_fvar(arg, target))
        }
        Code::Return(fvar) => *fvar == target,
        Code::Unreachable(expr) => expr_refs_fvar(expr, target),
    }
}

#[must_use]
fn value_refs_fvar(value: &LetValue, target: FVarId) -> bool {
    match value {
        LetValue::Lit(_) | LetValue::Erased => false,
        LetValue::Proj { structure, .. } => *structure == target,
        LetValue::FVar { fvar, args } => {
            *fvar == target || args.iter().any(|arg| arg_refs_fvar(arg, target))
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            args.iter().any(|arg| arg_refs_fvar(arg, target))
        }
        LetValue::Reuse { slot, args, .. } => {
            *slot == target || args.iter().any(|arg| arg_refs_fvar(arg, target))
        }
    }
}

#[must_use]
fn arg_refs_fvar(arg: &Arg, target: FVarId) -> bool {
    match arg {
        Arg::FVar(fvar) => *fvar == target,
        Arg::Type(expr) => expr_refs_fvar(expr, target),
        Arg::Erased | Arg::Index(_) => false,
    }
}

#[must_use]
fn expr_refs_fvar(expr: &Expr, target: FVarId) -> bool {
    match expr.kind() {
        ExprKind::FVar(fvar) => *fvar == target,
        ExprKind::App(fun, arg) => expr_refs_fvar(fun, target) || expr_refs_fvar(arg, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_refs_fvar(ty, target) || expr_refs_fvar(body, target)
        }
        ExprKind::Let(_, ty, value, body, _) => {
            expr_refs_fvar(ty, target)
                || expr_refs_fvar(value, target)
                || expr_refs_fvar(body, target)
        }
        ExprKind::MData(_, inner)
        | ExprKind::Proj(_, _, inner)
        | ExprKind::Squash(inner)
        | ExprKind::CubicalPathLam { body: inner } => expr_refs_fvar(inner, target),
        ExprKind::CubicalPathApp { path, arg }
        | ExprKind::ZFCMem {
            element: path,
            set: arg,
        } => expr_refs_fvar(path, target) || expr_refs_fvar(arg, target),
        ExprKind::CubicalPath { ty, left, right }
        | ExprKind::CubicalTransp {
            ty,
            phi: left,
            base: right,
        } => {
            expr_refs_fvar(ty, target)
                || expr_refs_fvar(left, target)
                || expr_refs_fvar(right, target)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            expr_refs_fvar(ty, target)
                || expr_refs_fvar(phi, target)
                || expr_refs_fvar(u, target)
                || expr_refs_fvar(base, target)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            expr_refs_fvar(domain, target) || expr_refs_fvar(pred, target)
        }
        ExprKind::ZFCSet(zfc) => match zfc {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => false,
            ZFCSetExpr::Singleton(inner)
            | ZFCSetExpr::Union(inner)
            | ZFCSetExpr::PowerSet(inner)
            | ZFCSetExpr::Choice(inner) => expr_refs_fvar(inner, target),
            ZFCSetExpr::Pair(a, b)
            | ZFCSetExpr::Separation { set: a, pred: b }
            | ZFCSetExpr::Replacement { set: a, func: b } => {
                expr_refs_fvar(a, target) || expr_refs_fvar(b, target)
            }
        },
        _ => false,
    }
}

#[must_use]
fn scan_escapes(code: &Code, target: FVarId) -> EscapeScan {
    match code {
        Code::Let(decl, body) => merge_scans(
            scan_value_escapes(&decl.value, target),
            scan_escapes(body, target),
        ),
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => merge_scans(
            scan_escapes(&fun_decl.body, target),
            scan_escapes(body, target),
        ),
        Code::Cases(cases) => cases.alts.iter().fold(
            EscapeScan {
                escapes: cases.scrutinee == target,
                ambiguous: false,
            },
            |scan, alt| {
                merge_scans(
                    scan,
                    match alt {
                        Alt::Ctor { body, .. } | Alt::Default(body) => scan_escapes(body, target),
                    },
                )
            },
        ),
        Code::Jmp { jp, args } => EscapeScan {
            escapes: args
                .iter()
                .any(|arg| matches!(arg, Arg::FVar(fvar) if *fvar == target)),
            ambiguous: *jp == target,
        },
        Code::Return(fvar) => EscapeScan {
            escapes: *fvar == target,
            ambiguous: false,
        },
        Code::Unreachable(_) => EscapeScan::default(),
    }
}

#[must_use]
fn scan_value_escapes(value: &LetValue, target: FVarId) -> EscapeScan {
    match value {
        LetValue::Lit(_) | LetValue::Erased => EscapeScan::default(),
        LetValue::FVar { args, .. } => EscapeScan {
            escapes: args
                .iter()
                .any(|arg| matches!(arg, Arg::FVar(id) if *id == target)),
            ambiguous: false,
        },
        LetValue::Proj { structure, .. } => EscapeScan {
            escapes: *structure == target,
            ambiguous: false,
        },
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => EscapeScan {
            escapes: args
                .iter()
                .any(|arg| matches!(arg, Arg::FVar(fvar) if *fvar == target)),
            ambiguous: false,
        },
        LetValue::Reuse { slot, args, .. } => EscapeScan {
            escapes: *slot == target
                || args
                    .iter()
                    .any(|arg| matches!(arg, Arg::FVar(fvar) if *fvar == target)),
            ambiguous: false,
        },
    }
}

#[must_use]
fn merge_scans(left: EscapeScan, right: EscapeScan) -> EscapeScan {
    EscapeScan {
        escapes: left.escapes || right.escapes,
        ambiguous: left.ambiguous || right.ambiguous,
    }
}

#[must_use]
fn count_code_nodes(code: &Code) -> usize {
    match code {
        Code::Let(_, body) => 1 + count_code_nodes(body),
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            1 + count_code_nodes(&fun_decl.body) + count_code_nodes(body)
        }
        Code::Cases(cases) => {
            1 + cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor { body, .. } | Alt::Default(body) => count_code_nodes(body),
                })
                .sum::<usize>()
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 1,
    }
}

#[must_use]
fn collect_depths(code: &Code) -> HashMap<FVarId, usize> {
    let mut out = HashMap::new();
    fill_depths(code, 0, &mut out);
    out
}

fn fill_depths(code: &Code, depth: usize, out: &mut HashMap<FVarId, usize>) {
    match code {
        Code::Let(_, body) => fill_depths(body, depth, out),
        Code::Fun(fun_decl, body) => {
            let next = depth + 1;
            out.insert(fun_decl.fvar_id, next);
            fill_depths(&fun_decl.body, next, out);
            fill_depths(body, depth, out);
        }
        Code::JoinPoint(fun_decl, body) => {
            fill_depths(&fun_decl.body, depth, out);
            fill_depths(body, depth, out);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } | Alt::Default(body) => fill_depths(body, depth, out),
                }
            }
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}
