// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Function Inlining for L5IR
//!
//! Replaces calls to small or annotated functions with their body,
//! reducing call overhead and exposing further optimization opportunities.
//!
//! # Decision Heuristics
//!
//! A call is inlined when any of the following hold:
//!
//! 1. The callee has `InlineAttr::Always` (`@[always_inline]`)
//! 2. The callee's body is at or below `max_inline_size` IR nodes
//!    and does not have `InlineAttr::NoInline`
//! 3. The callee is called exactly once and `inline_once_used` is set
//!
//! A call is never inlined when:
//!
//! - The callee has `InlineAttr::NoInline` (`@[noinline]`)
//! - The callee is recursive (direct self-reference in body)
//! - The inline depth exceeds `max_inline_depth`
//!
//! # Modules
//!
//! - `analysis`: Size estimation, call counting, recursion detection
//! - `substitute`: Argument substitution and body splicing
//!
//! Part of #3084 - IO/FFI/Native epic.

pub(crate) mod analysis;
#[cfg(test)]
pub(crate) mod substitute;

#[cfg(test)]
use crate::ir::{IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
#[cfg(test)]
use clean_kernel::Name;
#[cfg(test)]
use std::collections::{HashMap, HashSet};

pub(crate) use analysis::max_var_id;
#[cfg(test)]
pub(crate) use analysis::{body_references_name, compute_call_counts, estimate_size, is_recursive};
#[cfg(test)]
pub(crate) use substitute::{splice_inlined, substitute_args};

// -----------------------------------------------------------------------
// Inline annotation
// -----------------------------------------------------------------------

/// Inline annotation for a declaration, corresponding to Lean 4's
/// `@[inline]`, `@[always_inline]`, and `@[noinline]` attributes.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg(test)]
pub(crate) enum InlineAttr {
    /// `@[inline]` -- hint to the inliner.
    Inline,
    /// `@[always_inline]` -- unconditionally inline regardless of size.
    Always,
    /// `@[noinline]` -- never inline this function.
    NoInline,
    /// No annotation; use size heuristics.
    None,
}

// -----------------------------------------------------------------------
// Configuration
// -----------------------------------------------------------------------

/// Configuration for the IR inlining pass.
#[derive(Clone, Debug)]
#[cfg(test)]
pub(crate) struct InlinePassConfig {
    /// Maximum IR node count for automatic inlining (default: 20).
    pub(crate) max_inline_size: usize,
    /// Maximum recursive inline depth (default: 3).
    pub(crate) max_inline_depth: usize,
    /// Respect `InlineAttr` annotations on declarations (default: true).
    pub(crate) respect_annotations: bool,
    /// Inline functions called exactly once regardless of size (default: true).
    pub(crate) inline_once_used: bool,
}

#[cfg(test)]
impl Default for InlinePassConfig {
    fn default() -> Self {
        Self {
            max_inline_size: 20,
            max_inline_depth: 3,
            respect_annotations: true,
            inline_once_used: true,
        }
    }
}

// -----------------------------------------------------------------------
// Inline decision
// -----------------------------------------------------------------------

/// The inlining decision for a particular function.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg(test)]
pub(crate) enum InlineDecision {
    /// Inline unconditionally (`@[always_inline]`).
    Always,
    /// Inline because the function is small or annotated `@[inline]`.
    Yes,
    /// Do not inline (`@[noinline]` or too large).
    No,
    /// Inline because the function is called exactly once.
    OnceOnly,
}

// -----------------------------------------------------------------------
// Statistics
// -----------------------------------------------------------------------

/// Statistics collected during an inlining pass.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct InlineStats {
    /// Number of call sites that were inlined.
    pub(crate) inlined_calls: usize,
    /// Calls skipped due to `@[noinline]`.
    pub(crate) skipped_noinline: usize,
    /// Calls skipped because the callee was too large.
    pub(crate) skipped_too_large: usize,
    /// Calls skipped because the callee is recursive.
    pub(crate) skipped_recursive: usize,
}

// -----------------------------------------------------------------------
// Inline decision logic
// -----------------------------------------------------------------------

/// Decide whether a function should be inlined at its call sites.
#[cfg(test)]
pub(crate) fn should_inline(
    decl: &IRDecl,
    attr: &InlineAttr,
    call_count: usize,
    config: &InlinePassConfig,
) -> InlineDecision {
    if is_recursive(decl) {
        return InlineDecision::No;
    }
    if config.respect_annotations {
        match attr {
            InlineAttr::Always => return InlineDecision::Always,
            InlineAttr::NoInline => return InlineDecision::No,
            InlineAttr::Inline => return InlineDecision::Yes,
            InlineAttr::None => {}
        }
    }
    if config.inline_once_used && call_count == 1 {
        return InlineDecision::OnceOnly;
    }
    if estimate_size(&decl.body) <= config.max_inline_size {
        InlineDecision::Yes
    } else {
        InlineDecision::No
    }
}

// -----------------------------------------------------------------------
// Inline call-site traversal
// -----------------------------------------------------------------------

/// Traverse `body`, inlining eligible call sites. Returns `(new_body, changed)`.
#[cfg(test)]
pub(crate) fn inline_call_in_body(
    body: &IRBody,
    env: &HashMap<Name, IRDecl>,
    attrs: &HashMap<Name, InlineAttr>,
    call_counts: &HashMap<Name, usize>,
    recursive_fns: &HashSet<Name>,
    config: &InlinePassConfig,
    depth: usize,
    stats: &mut InlineStats,
) -> (IRBody, bool) {
    if depth > config.max_inline_depth {
        return (body.clone(), false);
    }
    match body {
        IRBody::VDecl {
            var,
            ty,
            value: IRExpr::Apply { fn_id, args },
            rest,
        } => try_inline_apply(
            *var,
            ty,
            fn_id,
            args,
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
            body,
        ),
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (new_rest, changed) = inline_call_in_body(
                rest,
                env,
                attrs,
                call_counts,
                recursive_fns,
                config,
                depth,
                stats,
            );
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(new_rest),
                },
                changed,
            )
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let (new_jp, c1) = inline_call_in_body(
                jp_body,
                env,
                attrs,
                call_counts,
                recursive_fns,
                config,
                depth,
                stats,
            );
            let (new_rest, c2) = inline_call_in_body(
                rest,
                env,
                attrs,
                call_counts,
                recursive_fns,
                config,
                depth,
                stats,
            );
            (
                IRBody::JDecl {
                    jp: *jp,
                    params: params.clone(),
                    body: Box::new(new_jp),
                    rest: Box::new(new_rest),
                },
                c1 || c2,
            )
        }
        IRBody::Inc { var, n, rest } => wrap_rest(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
            |r| IRBody::Inc {
                var: *var,
                n: *n,
                rest: Box::new(r),
            },
        ),
        IRBody::Dec { var, rest } => wrap_rest(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
            |r| IRBody::Dec {
                var: *var,
                rest: Box::new(r),
            },
        ),
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => wrap_rest(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
            |r| IRBody::Set {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(r),
            },
        ),
        IRBody::SetTag { var, tag, rest } => wrap_rest(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
            |r| IRBody::SetTag {
                var: *var,
                tag: *tag,
                rest: Box::new(r),
            },
        ),
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => wrap_rest(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
            |r| IRBody::USet {
                var: *var,
                idx: *idx,
                value: *value,
                rest: Box::new(r),
            },
        ),
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => wrap_rest(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
            |r| IRBody::SSet {
                var: *var,
                n: *n,
                offset: *offset,
                value: *value,
                ty: ty.clone(),
                rest: Box::new(r),
            },
        ),
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let mut any_changed = false;
            let new_alts: Vec<IRAlt> = alts
                .iter()
                .map(|alt| {
                    let (new_body, c) = inline_call_in_body(
                        &alt.body,
                        env,
                        attrs,
                        call_counts,
                        recursive_fns,
                        config,
                        depth,
                        stats,
                    );
                    any_changed |= c;
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(new_body),
                    }
                })
                .collect();
            let new_default = default.as_ref().map(|d| {
                let (new_d, c) = inline_call_in_body(
                    d,
                    env,
                    attrs,
                    call_counts,
                    recursive_fns,
                    config,
                    depth,
                    stats,
                );
                any_changed |= c;
                Box::new(new_d)
            });
            (
                IRBody::Case {
                    scrutinee: *scrutinee,
                    alts: new_alts,
                    default: new_default,
                },
                any_changed,
            )
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => (body.clone(), false),
    }
}

/// Helper: recurse into `rest`, then wrap the result.
#[cfg(test)]
fn wrap_rest(
    rest: &IRBody,
    env: &HashMap<Name, IRDecl>,
    attrs: &HashMap<Name, InlineAttr>,
    call_counts: &HashMap<Name, usize>,
    recursive_fns: &HashSet<Name>,
    config: &InlinePassConfig,
    depth: usize,
    stats: &mut InlineStats,
    wrap: impl FnOnce(IRBody) -> IRBody,
) -> (IRBody, bool) {
    let (new_rest, changed) = inline_call_in_body(
        rest,
        env,
        attrs,
        call_counts,
        recursive_fns,
        config,
        depth,
        stats,
    );
    (wrap(new_rest), changed)
}

/// Handle a VDecl whose value is Apply -- decide whether to inline.
#[cfg(test)]
fn try_inline_apply(
    var: VarId,
    ty: &IRType,
    fn_id: &crate::ir::FnId,
    args: &[IRArg],
    rest: &IRBody,
    env: &HashMap<Name, IRDecl>,
    attrs: &HashMap<Name, InlineAttr>,
    call_counts: &HashMap<Name, usize>,
    recursive_fns: &HashSet<Name>,
    config: &InlinePassConfig,
    depth: usize,
    stats: &mut InlineStats,
    original_body: &IRBody,
) -> (IRBody, bool) {
    let callee_name = &fn_id.0;
    let Some(callee) = env.get(callee_name) else {
        // Unknown callee -- continue traversal in rest
        let (new_rest, changed) = inline_call_in_body(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
        );
        return (
            IRBody::VDecl {
                var,
                ty: ty.clone(),
                value: IRExpr::Apply {
                    fn_id: fn_id.clone(),
                    args: args.to_vec(),
                },
                rest: Box::new(new_rest),
            },
            changed,
        );
    };

    if recursive_fns.contains(callee_name) {
        stats.skipped_recursive += 1;
        let (new_rest, changed) = inline_call_in_body(
            rest,
            env,
            attrs,
            call_counts,
            recursive_fns,
            config,
            depth,
            stats,
        );
        return (
            IRBody::VDecl {
                var,
                ty: ty.clone(),
                value: IRExpr::Apply {
                    fn_id: fn_id.clone(),
                    args: args.to_vec(),
                },
                rest: Box::new(new_rest),
            },
            changed,
        );
    }

    let attr = attrs.get(callee_name).unwrap_or(&InlineAttr::None);
    let count = call_counts.get(callee_name).copied().unwrap_or(0);
    let decision = should_inline(callee, attr, count, config);

    match decision {
        InlineDecision::No => {
            if attr == &InlineAttr::NoInline {
                stats.skipped_noinline += 1;
            } else {
                stats.skipped_too_large += 1;
            }
            let (new_rest, changed) = inline_call_in_body(
                rest,
                env,
                attrs,
                call_counts,
                recursive_fns,
                config,
                depth,
                stats,
            );
            (
                IRBody::VDecl {
                    var,
                    ty: ty.clone(),
                    value: IRExpr::Apply {
                        fn_id: fn_id.clone(),
                        args: args.to_vec(),
                    },
                    rest: Box::new(new_rest),
                },
                changed,
            )
        }
        InlineDecision::Always | InlineDecision::Yes | InlineDecision::OnceOnly => {
            let max_caller = max_var_id(original_body);
            let max_callee = max_var_id(&callee.body);
            let offset = max_caller + max_callee + 1;

            let inlined = substitute_args(&callee.body, &callee.params, args, offset);
            let spliced = splice_inlined(inlined, var, ty.clone(), rest);
            stats.inlined_calls += 1;

            let (final_body, _) = inline_call_in_body(
                &spliced,
                env,
                attrs,
                call_counts,
                recursive_fns,
                config,
                depth + 1,
                stats,
            );
            (final_body, true)
        }
    }
}

// -----------------------------------------------------------------------
// Top-level pass
// -----------------------------------------------------------------------

/// Run the full inlining pass on a set of IR declarations.
///
/// Builds a function environment, computes call counts, detects recursive
/// functions, and inlines eligible call sites across all declaration bodies.
#[must_use]
#[cfg(test)]
pub(crate) fn run_inline_pass(
    decls: &[IRDecl],
    attrs: &HashMap<Name, InlineAttr>,
    config: &InlinePassConfig,
) -> (Vec<IRDecl>, InlineStats) {
    let mut stats = InlineStats::default();

    let env: HashMap<Name, IRDecl> = decls.iter().map(|d| (d.name.clone(), d.clone())).collect();

    let call_counts = compute_call_counts(decls);

    let recursive_fns: HashSet<Name> = decls
        .iter()
        .filter(|d| is_recursive(d))
        .map(|d| d.name.clone())
        .collect();

    let result: Vec<IRDecl> = decls
        .iter()
        .map(|decl| {
            let (new_body, _) = inline_call_in_body(
                &decl.body,
                &env,
                attrs,
                &call_counts,
                &recursive_fns,
                config,
                0,
                &mut stats,
            );
            IRDecl {
                name: decl.name.clone(),
                params: decl.params.clone(),
                return_type: decl.return_type.clone(),
                body: new_body,
            }
        })
        .collect();

    (result, stats)
}

#[cfg(test)]
#[path = "../inline_pass_tests.rs"]
mod tests;
