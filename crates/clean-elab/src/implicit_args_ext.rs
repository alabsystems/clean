// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended implicit argument insertion for the Lean 5 elaborator.
//!
//! Builds on `implicit_args.rs` with: strict implicit insertion, instance
//! implicit resolution, auto-bound detection, optional argument defaults,
//! named argument support, postponement, out-param deferral, trace, and
//! eta expansion for implicit lambdas.
//!
//! Reference: lean4-ref/src/library/elaborator/app.cpp

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#![allow(dead_code)]
use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, Name};

use crate::error::ElabError;
use crate::implicit_args::{is_implicit_binder_info, ImplicitConfig};
use crate::meta::MetaCtx;

/// A single entry in the implicit argument trace log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TraceEntry {
    pub(crate) position: usize,
    pub(crate) action: TraceAction,
    pub(crate) binder_info: BinderInfo,
}

/// Action taken for an implicit argument position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TraceAction {
    InsertedMeta,
    InsertedInstance,
    NamedArgFilled,
    DefaultUsed,
    StrictSkipped,
    Postponed,
    OutParamDeferred,
    ExplicitConsumed,
}

/// Accumulated trace for one implicit-insertion pass.
#[derive(Debug, Clone, Default)]
pub(crate) struct ImplicitTrace {
    pub(crate) entries: Vec<TraceEntry>,
}

impl ImplicitTrace {
    pub(crate) fn record(&mut self, position: usize, action: TraceAction, binder_info: BinderInfo) {
        self.entries.push(TraceEntry {
            position,
            action,
            binder_info,
        });
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Extended configuration adding optional-arg, postponement, and out-param knobs.
#[derive(Debug, Clone)]
pub(crate) struct ExtImplicitConfig {
    pub(crate) base: ImplicitConfig,
    pub(crate) fill_optional_defaults: bool,
    pub(crate) allow_postponement: bool,
    pub(crate) defer_out_params: bool,
    pub(crate) tracing: bool,
}

impl Default for ExtImplicitConfig {
    fn default() -> Self {
        Self {
            base: ImplicitConfig::default(),
            fill_optional_defaults: true,
            allow_postponement: true,
            defer_out_params: true,
            tracing: false,
        }
    }
}

/// An optional argument with a default value: `(x : A := default)`.
#[derive(Debug, Clone)]
pub(crate) struct OptionalArg {
    pub(crate) name: Name,
    pub(crate) default_val: Expr,
}

/// An out-param implicit deferred for later resolution.
#[derive(Debug, Clone)]
pub(crate) struct DeferredOutParam {
    pub(crate) position: usize,
    pub(crate) meta_expr: Expr,
    pub(crate) param_type: Expr,
}

/// An implicit whose resolution was postponed (incomplete type info).
#[derive(Debug, Clone)]
pub(crate) struct PostponedImplicit {
    pub(crate) position: usize,
    pub(crate) meta_expr: Expr,
    pub(crate) expected_type: Expr,
    pub(crate) binder_info: BinderInfo,
}

/// Result of an extended implicit analysis pass.
#[derive(Debug, Clone)]
pub(crate) struct ExtImplicitAnalysis {
    pub(crate) all_args: Vec<Expr>,
    pub(crate) instance_goals: Vec<(Name, Expr)>,
    pub(crate) deferred_out_params: Vec<DeferredOutParam>,
    pub(crate) postponed: Vec<PostponedImplicit>,
    pub(crate) trace: ImplicitTrace,
}

/// Check if a name looks like a universe variable (`u`, `v`, `w`, `u1` ...).
pub(crate) fn is_universe_variable_name(name: &Name) -> bool {
    let s = format!("{name}");
    if s.is_empty() {
        return false;
    }
    let base = s.trim_end_matches(|c: char| c.is_ascii_digit() || "₁₂₃".contains(c));
    matches!(base, "u" | "v" | "w")
}

/// Check if a name looks like a type variable (`α`, `β`, `γ`, single uppercase).
pub(crate) fn is_type_variable_name(name: &Name) -> bool {
    let s = format!("{name}");
    if s.is_empty() {
        return false;
    }
    let first = s
        .chars()
        .next()
        .expect("invariant: non-empty checked above");
    matches!(first, 'α' | 'β' | 'γ' | 'δ' | 'ε' | 'ζ' | 'η' | 'θ')
        || (s.len() == 1 && first.is_ascii_uppercase())
}

/// Classification of auto-bound implicits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AutoBoundKind {
    Universe,
    TypeVar,
}

/// Identify auto-bound implicit candidates in an expression.
pub(crate) fn detect_auto_bound_implicits(expr: &Expr) -> Vec<(Name, AutoBoundKind)> {
    let mut result = Vec::new();
    collect_free_names(expr, &mut result);
    result.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
    result.dedup_by(|a, b| format!("{}", a.0) == format!("{}", b.0));
    result
}

fn collect_free_names(expr: &Expr, out: &mut Vec<(Name, AutoBoundKind)>) {
    match expr.kind() {
        ExprKind::Const(name, _) => {
            if is_universe_variable_name(name) {
                out.push((name.clone(), AutoBoundKind::Universe));
            } else if is_type_variable_name(name) {
                out.push((name.clone(), AutoBoundKind::TypeVar));
            }
        }
        ExprKind::App(f, a) => {
            collect_free_names(f, out);
            collect_free_names(a, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_free_names(ty, out);
            collect_free_names(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_free_names(ty, out);
            collect_free_names(val, out);
            collect_free_names(body, out);
        }
        _ => {}
    }
}

/// Resolve a named argument with fallback to string-based matching.
pub(crate) fn resolve_named_arg_ext<'a>(
    name: &Name,
    named_args: &'a [(Name, Expr)],
) -> Option<&'a Expr> {
    if let Some((_, e)) = named_args.iter().find(|(n, _)| n == name) {
        return Some(e);
    }
    let name_str = format!("{name}");
    named_args
        .iter()
        .find(|(n, _)| format!("{n}") == name_str)
        .map(|(_, e)| e)
}

/// Strict implicit insertion check (extended with named-arg awareness).
pub(crate) fn should_insert_strict_ext(
    remaining_explicit_count: usize,
    named_explicit_count: usize,
) -> bool {
    remaining_explicit_count + named_explicit_count > 0
}

/// Check if a type expression contains unresolved metavariables (FVars).
pub(crate) fn type_has_unresolved_metas(ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::FVar(_) => true,
        ExprKind::App(f, a) => type_has_unresolved_metas(f) || type_has_unresolved_metas(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            type_has_unresolved_metas(t) || type_has_unresolved_metas(b)
        }
        _ => false,
    }
}

/// Eta-expand a function to expose implicit parameters as lambda binders.
///
/// Given `f : {A : Type} -> A -> B`, produces `fun {A : Type} => f A`.
/// Only expands leading implicit/instance/strict binders.
pub(crate) fn eta_expand_implicits(
    fn_expr: &Expr,
    fn_type: &Expr,
    meta_ctx: &mut MetaCtx<'_>,
) -> Expr {
    let mut binders: Vec<(BinderData, Expr)> = Vec::new();
    let mut current_type = fn_type.clone();
    loop {
        match current_type.kind() {
            ExprKind::Pi(bd, arg_ty, body_ty) if is_implicit_binder_info(bd.info) => {
                binders.push((*bd, arg_ty.as_ref().clone()));
                current_type = body_ty.as_ref().clone();
            }
            _ => break,
        }
    }
    if binders.is_empty() {
        return fn_expr.clone();
    }
    let n = binders.len();
    let mut inner = fn_expr.clone();
    for i in 0..n {
        let _ = meta_ctx;
        inner = Expr::app(inner, Expr::bvar((n - 1 - i) as u32));
    }
    for (bd, ty) in binders.into_iter().rev() {
        inner = Expr::lam(bd, ty, inner);
    }
    inner
}

/// Perform extended implicit argument insertion.
pub(crate) fn insert_implicits_ext(
    fn_expr: Expr,
    fn_type: &Expr,
    explicit_args: &[Expr],
    named_args: &[(Name, Expr)],
    optional_args: &[OptionalArg],
    out_param_names: &[Name],
    meta_ctx: &mut MetaCtx<'_>,
    config: &ExtImplicitConfig,
) -> Result<ExtImplicitAnalysis, ElabError> {
    let mut result_expr = fn_expr;
    let mut all_args: Vec<Expr> = Vec::new();
    let mut instance_goals: Vec<(Name, Expr)> = Vec::new();
    let mut deferred_out_params: Vec<DeferredOutParam> = Vec::new();
    let mut postponed: Vec<PostponedImplicit> = Vec::new();
    let mut trace = ImplicitTrace::default();
    let mut current_type = fn_type.clone();
    let mut explicit_idx = 0;
    let mut position = 0;
    let max_depth = config.base.max_implicit_depth;
    let mut stopped_before_type_exhausted = false;

    while position < max_depth {
        let (bd, arg_ty_owned, body_ty_owned) = match current_type.kind() {
            ExprKind::Pi(bd, arg_ty, body_ty) => {
                (*bd, arg_ty.as_ref().clone(), body_ty.as_ref().clone())
            }
            _ => break,
        };
        let binder_name = binder_name_at_position(position);

        match bd.info {
            BinderInfo::Default => {
                if let Some(val) = resolve_named_arg_ext(&binder_name, named_args) {
                    push_arg(&mut result_expr, &mut all_args, val.clone());
                    maybe_trace(
                        config,
                        &mut trace,
                        position,
                        TraceAction::NamedArgFilled,
                        bd.info,
                    );
                    current_type = body_ty_owned.instantiate(val);
                    position += 1;
                    continue;
                }
                if explicit_idx >= explicit_args.len() {
                    if config.fill_optional_defaults {
                        if let Some(opt) = optional_args.iter().find(|o| o.name == binder_name) {
                            let arg = opt.default_val.clone();
                            push_arg(&mut result_expr, &mut all_args, arg.clone());
                            maybe_trace(
                                config,
                                &mut trace,
                                position,
                                TraceAction::DefaultUsed,
                                bd.info,
                            );
                            current_type = body_ty_owned.instantiate(&arg);
                            position += 1;
                            continue;
                        }
                    }
                    stopped_before_type_exhausted = true;
                    break;
                }
                let arg = explicit_args[explicit_idx].clone();
                explicit_idx += 1;
                push_arg(&mut result_expr, &mut all_args, arg.clone());
                maybe_trace(
                    config,
                    &mut trace,
                    position,
                    TraceAction::ExplicitConsumed,
                    bd.info,
                );
                current_type = body_ty_owned.instantiate(&arg);
            }
            BinderInfo::Implicit if config.base.insert_implicit => {
                if let Some(val) = resolve_named_arg_ext(&binder_name, named_args) {
                    push_arg(&mut result_expr, &mut all_args, val.clone());
                    maybe_trace(
                        config,
                        &mut trace,
                        position,
                        TraceAction::NamedArgFilled,
                        bd.info,
                    );
                    current_type = body_ty_owned.instantiate(val);
                    position += 1;
                    continue;
                }
                if config.defer_out_params && out_param_names.contains(&binder_name) {
                    let meta = meta_ctx.fresh_meta(arg_ty_owned.clone());
                    push_arg(&mut result_expr, &mut all_args, meta.clone());
                    deferred_out_params.push(DeferredOutParam {
                        position,
                        meta_expr: meta,
                        param_type: arg_ty_owned,
                    });
                    maybe_trace(
                        config,
                        &mut trace,
                        position,
                        TraceAction::OutParamDeferred,
                        bd.info,
                    );
                    current_type = body_ty_owned;
                    position += 1;
                    continue;
                }
                if config.allow_postponement && type_has_unresolved_metas(&arg_ty_owned) {
                    let meta = meta_ctx.fresh_meta(arg_ty_owned.clone());
                    push_arg(&mut result_expr, &mut all_args, meta.clone());
                    postponed.push(PostponedImplicit {
                        position,
                        meta_expr: meta,
                        expected_type: arg_ty_owned,
                        binder_info: bd.info,
                    });
                    maybe_trace(
                        config,
                        &mut trace,
                        position,
                        TraceAction::Postponed,
                        bd.info,
                    );
                    current_type = body_ty_owned;
                    position += 1;
                    continue;
                }
                let meta = meta_ctx.fresh_meta(arg_ty_owned);
                push_arg(&mut result_expr, &mut all_args, meta.clone());
                maybe_trace(
                    config,
                    &mut trace,
                    position,
                    TraceAction::InsertedMeta,
                    bd.info,
                );
                current_type = body_ty_owned.instantiate(&meta);
            }
            BinderInfo::InstImplicit if config.base.insert_instance => {
                if let Some(val) = resolve_named_arg_ext(&binder_name, named_args) {
                    push_arg(&mut result_expr, &mut all_args, val.clone());
                    maybe_trace(
                        config,
                        &mut trace,
                        position,
                        TraceAction::NamedArgFilled,
                        bd.info,
                    );
                    current_type = body_ty_owned.instantiate(val);
                    position += 1;
                    continue;
                }
                let meta = meta_ctx.fresh_meta(arg_ty_owned.clone());
                instance_goals.push((binder_name, arg_ty_owned));
                push_arg(&mut result_expr, &mut all_args, meta.clone());
                maybe_trace(
                    config,
                    &mut trace,
                    position,
                    TraceAction::InsertedInstance,
                    bd.info,
                );
                current_type = body_ty_owned.instantiate(&meta);
            }
            BinderInfo::StrictImplicit if config.base.insert_strict => {
                let remaining = explicit_args.len().saturating_sub(explicit_idx);
                if !should_insert_strict_ext(remaining, named_args.len()) {
                    maybe_trace(
                        config,
                        &mut trace,
                        position,
                        TraceAction::StrictSkipped,
                        bd.info,
                    );
                    stopped_before_type_exhausted = true;
                    break;
                }
                if let Some(val) = resolve_named_arg_ext(&binder_name, named_args) {
                    push_arg(&mut result_expr, &mut all_args, val.clone());
                    maybe_trace(
                        config,
                        &mut trace,
                        position,
                        TraceAction::NamedArgFilled,
                        bd.info,
                    );
                    current_type = body_ty_owned.instantiate(val);
                    position += 1;
                    continue;
                }
                let meta = meta_ctx.fresh_meta(arg_ty_owned);
                push_arg(&mut result_expr, &mut all_args, meta.clone());
                maybe_trace(
                    config,
                    &mut trace,
                    position,
                    TraceAction::InsertedMeta,
                    bd.info,
                );
                current_type = body_ty_owned.instantiate(&meta);
            }
            _ => {
                stopped_before_type_exhausted = true;
                break;
            }
        }
        position += 1;
    }

    if position >= max_depth {
        stopped_before_type_exhausted = true;
    }

    if explicit_idx < explicit_args.len() && !stopped_before_type_exhausted {
        return Err(ElabError::TooManyArguments {
            func_type: format!("{fn_type:?}"),
            remaining_args: explicit_args.len() - explicit_idx,
        });
    }

    Ok(ExtImplicitAnalysis {
        all_args,
        instance_goals,
        deferred_out_params,
        postponed,
        trace,
    })
}

fn push_arg(result_expr: &mut Expr, all_args: &mut Vec<Expr>, arg: Expr) {
    *result_expr = Expr::app(result_expr.clone(), arg.clone());
    all_args.push(arg);
}

fn maybe_trace(
    config: &ExtImplicitConfig,
    trace: &mut ImplicitTrace,
    pos: usize,
    action: TraceAction,
    info: BinderInfo,
) {
    if config.tracing {
        trace.record(pos, action, info);
    }
}

/// Synthesize a positional binder name `_argN` for position `n`.
fn binder_name_at_position(n: usize) -> Name {
    Name::from_string(&format!("_arg{n}"))
}
