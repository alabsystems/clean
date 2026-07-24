// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implicit argument insertion for function applications.
//!
//! When a user writes `f x` but `f` has type `{A : Type} -> A -> B`, the
//! elaborator must insert a metavariable for `A` before `x`. This module
//! handles:
//!
//! - `{}` implicit binders: fill with fresh metavariables
//! - `[]` instance implicit binders: fill with instance search placeholders
//! - `{{}}` strict implicit binders: only insert if later explicit args exist
//! - `(name := value)` named arguments: skip implicit positions by name
//!
//! This is a standalone utility operating on `MetaCtx`, separate from the
//! inline implicit insertion in `infer/elab_app.rs` which operates on `ElabCtx`.
//! Both share the same semantic rules per Lean 4's `addImplicitArg` /
//! `mkFreshExprMVar` pattern.
//!
//! Reference: lean4-ref/src/library/elaborator/app.cpp

use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, Name};

use crate::error::ElabError;
use crate::meta::MetaCtx;

/// Information about an implicit argument that was inserted.
#[derive(Debug, Clone)]
pub(crate) struct ImplicitArg {
    /// Position (0-based) of this argument in the full parameter list.
    pub(crate) position: usize,
    /// Binder name from the function type.
    pub(crate) name: Name,
    /// Binder info (Implicit, StrictImplicit, or InstImplicit).
    pub(crate) binder_info: BinderInfo,
    /// The expression inserted (typically a metavariable).
    pub(crate) arg_expr: Expr,
}

/// Configuration for implicit insertion behavior.
#[derive(Debug, Clone)]
pub(crate) struct ImplicitConfig {
    /// Insert metavariables for `{}` implicit binders.
    pub(crate) insert_implicit: bool,
    /// Insert instance search placeholders for `[]` binders.
    pub(crate) insert_instance: bool,
    /// Insert metavariables for `{{}}` strict implicit binders
    /// (subject to the "has later explicit args" rule).
    pub(crate) insert_strict: bool,
    /// Maximum number of implicit arguments to insert before giving up.
    /// Guards against runaway insertion on malformed types.
    pub(crate) max_implicit_depth: usize,
}

impl Default for ImplicitConfig {
    fn default() -> Self {
        Self {
            insert_implicit: true,
            insert_instance: true,
            insert_strict: true,
            max_implicit_depth: 128,
        }
    }
}

/// Result of implicit argument analysis on a function type.
#[derive(Debug, Clone)]
pub(crate) struct ImplicitAnalysis {
    /// Implicit arguments that were inserted (metavariables or instance goals).
    pub(crate) inserted: Vec<ImplicitArg>,
    /// Remaining explicit parameters: `(position, name, type)`.
    pub(crate) remaining_explicit: Vec<(usize, Name, Expr)>,
    /// Instance goals that need resolution: `(name, class_type)`.
    pub(crate) instance_goals: Vec<(Name, Expr)>,
}

/// Check if a binder requires implicit argument insertion.
#[inline]
pub(crate) fn is_implicit_binder_info(info: BinderInfo) -> bool {
    matches!(
        info,
        BinderInfo::Implicit | BinderInfo::StrictImplicit | BinderInfo::InstImplicit
    )
}

/// Count the number of leading implicit parameters in a type.
///
/// Walks the outermost Pi chain and counts consecutive implicit/instance/strict
/// binders before the first explicit binder or non-Pi type.
pub(crate) fn count_leading_implicits(type_expr: &Expr) -> usize {
    let mut count = 0;
    let mut current = type_expr;
    loop {
        match current.kind() {
            ExprKind::Pi(bd, _arg_ty, body_ty) if is_implicit_binder_info(bd.info) => {
                count += 1;
                current = body_ty.as_ref();
            }
            _ => break,
        }
    }
    count
}

/// Count the number of explicit parameters in a Pi type.
///
/// Walks the full Pi chain and counts binders with `BinderInfo::Default`.
pub(crate) fn count_explicit_params(type_expr: &Expr) -> usize {
    let mut count = 0;
    let mut current = type_expr;
    while let ExprKind::Pi(bd, _arg_ty, body_ty) = current.kind() {
        if bd.info == BinderInfo::Default {
            count += 1;
        }
        current = body_ty.as_ref();
    }
    count
}

/// Determine whether a strict implicit binder should be inserted.
///
/// Strict implicit (`{{x : T}}`) is only inserted when at least one later
/// explicit argument is provided. This prevents insertion when a function
/// is partially applied up to but not past the strict implicit.
///
/// `remaining_explicit_count` is the number of explicit arguments the caller
/// still intends to supply.
pub(crate) fn should_insert_strict(_binder: BinderData, remaining_explicit_count: usize) -> bool {
    remaining_explicit_count > 0
}

/// Look up a named argument by binder name.
///
/// Searches `named_args` for an entry matching `name` and returns the
/// associated expression if found.
pub(crate) fn resolve_named_arg<'a>(
    name: &Name,
    named_args: &'a [(Name, Expr)],
) -> Option<&'a Expr> {
    named_args.iter().find(|(n, _)| n == name).map(|(_, e)| e)
}

/// Create a metavariable for an implicit argument.
///
/// Allocates a fresh metavariable in `meta_ctx` with the given type.
pub(crate) fn make_implicit_meta(
    _name: &Name,
    type_expr: &Expr,
    meta_ctx: &mut MetaCtx<'_>,
) -> Expr {
    meta_ctx.fresh_meta(type_expr.clone())
}

/// Create a metavariable for an instance implicit argument.
///
/// Allocates a fresh metavariable for the class type. The caller is
/// responsible for scheduling actual instance resolution (via the instance
/// table or synthesis queue) for the returned metavariable's type.
pub(crate) fn make_instance_meta(
    _class_name: &Name,
    type_expr: &Expr,
    meta_ctx: &mut MetaCtx<'_>,
) -> Expr {
    meta_ctx.fresh_meta(type_expr.clone())
}

/// Analyze a function type to determine implicit argument structure.
///
/// Walks the Pi chain of `fn_type`, categorizing each binder as implicit
/// (to be filled by metavariable), instance (to be filled by instance search),
/// strict implicit (conditional on later explicit args), or explicit.
///
/// Named arguments in `named_args` are matched by binder name and consumed
/// in place of metavariable insertion.
///
/// Returns an `ImplicitAnalysis` with inserted args, remaining explicit
/// params, and instance goals.
pub(crate) fn analyze_function_type(
    fn_type: &Expr,
    explicit_arg_count: usize,
    named_args: &[(Name, Expr)],
    config: &ImplicitConfig,
    meta_ctx: &mut MetaCtx<'_>,
) -> ImplicitAnalysis {
    let mut inserted = Vec::new();
    let mut remaining_explicit = Vec::new();
    let mut instance_goals = Vec::new();
    let mut current_type = fn_type.clone();
    let mut position = 0;
    let mut depth = 0;

    // Count total explicit params to track how many remain for strict logic.
    let total_explicit = count_explicit_params(fn_type);
    let mut explicit_seen = 0;

    loop {
        if depth >= config.max_implicit_depth {
            break;
        }

        match current_type.kind() {
            ExprKind::Pi(bd, arg_ty, body_ty) => {
                let arg_ty_owned = arg_ty.as_ref().clone();
                let body_ty_owned = body_ty.as_ref().clone();
                let binder_name = extract_binder_name(&current_type);

                match bd.info {
                    BinderInfo::Default => {
                        explicit_seen += 1;
                        // Check for named arg before recording as remaining.
                        if let Some(val) = resolve_named_arg(&binder_name, named_args) {
                            // Named arg fills explicit slot -- advance type.
                            current_type = body_ty_owned.instantiate(val);
                            position += 1;
                            continue;
                        }
                        // Explicit parameter -- record it as remaining.
                        remaining_explicit.push((position, binder_name, arg_ty_owned.clone()));
                        // Cannot proceed past unfilled explicit without a value.
                        // In real elaboration the caller supplies explicit args one
                        // at a time; here we just record remaining positions.
                        current_type = body_ty_owned;
                        position += 1;
                    }

                    BinderInfo::Implicit if config.insert_implicit => {
                        let arg = if let Some(val) = resolve_named_arg(&binder_name, named_args) {
                            val.clone()
                        } else {
                            make_implicit_meta(&binder_name, &arg_ty_owned, meta_ctx)
                        };
                        inserted.push(ImplicitArg {
                            position,
                            name: binder_name,
                            binder_info: BinderInfo::Implicit,
                            arg_expr: arg.clone(),
                        });
                        current_type = body_ty_owned.instantiate(&arg);
                        position += 1;
                        depth += 1;
                    }

                    BinderInfo::InstImplicit if config.insert_instance => {
                        let arg = if let Some(val) = resolve_named_arg(&binder_name, named_args) {
                            val.clone()
                        } else {
                            let meta = make_instance_meta(&binder_name, &arg_ty_owned, meta_ctx);
                            instance_goals.push((binder_name.clone(), arg_ty_owned.clone()));
                            meta
                        };
                        inserted.push(ImplicitArg {
                            position,
                            name: binder_name,
                            binder_info: BinderInfo::InstImplicit,
                            arg_expr: arg.clone(),
                        });
                        current_type = body_ty_owned.instantiate(&arg);
                        position += 1;
                        depth += 1;
                    }

                    BinderInfo::StrictImplicit if config.insert_strict => {
                        let remaining = total_explicit.saturating_sub(explicit_seen);
                        let remaining_for_strict =
                            remaining.min(explicit_arg_count.saturating_sub(explicit_seen));
                        if !should_insert_strict(*bd, remaining_for_strict) {
                            // Strict implicit not inserted -- stop.
                            break;
                        }
                        let arg = if let Some(val) = resolve_named_arg(&binder_name, named_args) {
                            val.clone()
                        } else {
                            make_implicit_meta(&binder_name, &arg_ty_owned, meta_ctx)
                        };
                        inserted.push(ImplicitArg {
                            position,
                            name: binder_name,
                            binder_info: BinderInfo::StrictImplicit,
                            arg_expr: arg.clone(),
                        });
                        current_type = body_ty_owned.instantiate(&arg);
                        position += 1;
                        depth += 1;
                    }

                    // Binder kind disabled by config -- stop.
                    _ => break,
                }
            }
            _ => break,
        }
    }

    ImplicitAnalysis {
        inserted,
        remaining_explicit,
        instance_goals,
    }
}

/// Insert implicit arguments into a function application.
///
/// Given `fn_expr` with type `fn_type` and explicit `args`, inserts
/// metavariables for implicit parameters and applies `fn_expr` to both
/// implicit and explicit arguments in order.
///
/// Returns the fully-applied expression and the list of all arguments
/// (implicit and explicit interleaved in declaration order).
pub(crate) fn insert_implicits(
    fn_expr: Expr,
    fn_type: &Expr,
    explicit_args: &[Expr],
    meta_ctx: &mut MetaCtx<'_>,
    config: &ImplicitConfig,
) -> Result<(Expr, Vec<Expr>), ElabError> {
    let mut result = fn_expr;
    let mut all_args: Vec<Expr> = Vec::new();
    let mut current_type = fn_type.clone();
    let mut explicit_idx = 0;
    let mut depth = 0;
    let mut stopped_before_type_exhausted = false;

    loop {
        if depth >= config.max_implicit_depth {
            stopped_before_type_exhausted = true;
            break;
        }

        match current_type.kind() {
            ExprKind::Pi(bd, arg_ty, body_ty) => {
                let arg_ty_owned = arg_ty.as_ref().clone();
                let body_ty_owned = body_ty.as_ref().clone();

                match bd.info {
                    BinderInfo::Default => {
                        // Explicit binder -- consume from args.
                        if explicit_idx >= explicit_args.len() {
                            stopped_before_type_exhausted = true;
                            break; // No more explicit args to consume.
                        }
                        let arg = explicit_args[explicit_idx].clone();
                        explicit_idx += 1;
                        result = Expr::app(result, arg.clone());
                        all_args.push(arg.clone());
                        current_type = body_ty_owned.instantiate(&arg);
                    }

                    BinderInfo::Implicit if config.insert_implicit => {
                        let arg = make_implicit_meta(&Name::anon(), &arg_ty_owned, meta_ctx);
                        result = Expr::app(result, arg.clone());
                        all_args.push(arg.clone());
                        current_type = body_ty_owned.instantiate(&arg);
                        depth += 1;
                    }

                    BinderInfo::InstImplicit if config.insert_instance => {
                        let arg = make_instance_meta(&Name::anon(), &arg_ty_owned, meta_ctx);
                        result = Expr::app(result, arg.clone());
                        all_args.push(arg.clone());
                        current_type = body_ty_owned.instantiate(&arg);
                        depth += 1;
                    }

                    BinderInfo::StrictImplicit if config.insert_strict => {
                        let remaining_explicit = explicit_args.len().saturating_sub(explicit_idx);
                        if !should_insert_strict(*bd, remaining_explicit) {
                            stopped_before_type_exhausted = true;
                            break;
                        }
                        let arg = make_implicit_meta(&Name::anon(), &arg_ty_owned, meta_ctx);
                        result = Expr::app(result, arg.clone());
                        all_args.push(arg.clone());
                        current_type = body_ty_owned.instantiate(&arg);
                        depth += 1;
                    }

                    _ => {
                        stopped_before_type_exhausted = true;
                        break;
                    }
                }
            }
            _ => break,
        }
    }

    // If there are remaining explicit args that were not consumed, it means
    // the function type ran out of binders. Report over-application.
    if explicit_idx < explicit_args.len() && !stopped_before_type_exhausted {
        return Err(ElabError::TooManyArguments {
            func_type: format!("{:?}", fn_type),
            remaining_args: explicit_args.len() - explicit_idx,
        });
    }

    Ok((result, all_args))
}

/// Extract the binder name from a Pi type.
///
/// If the expression is `Pi(bd, ty, body)` and comes from Lean's named
/// binder syntax, the name is embedded in the Let's structure. For our
/// kernel the name is carried in the metadata or is anonymous. We return
/// `Name::anon()` for now; future work can thread names through BinderData.
fn extract_binder_name(expr: &Expr) -> Name {
    // Lean 4's Pi stores the binder name alongside the BinderInfo.
    // Our kernel stores BinderData (info + multiplicity) but not a name.
    // This is a known limitation. For now, return anonymous.
    let _ = expr;
    Name::anon()
}
