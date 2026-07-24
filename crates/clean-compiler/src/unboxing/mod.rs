// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unboxing Optimization Pass
//!
//! Eliminates unnecessary box/unbox operations on scalar values in L5IR.
//! Runs after the explicit boxing pass to remove redundant conversions
//! that boxing conservatively inserts.
//!
//! # Optimizations
//!
//! 1. **Box/unbox elimination** — `unbox(box(x))` => `x`
//! 2. **Unbox/box elimination** — `box(unbox(x))` => `x` (when types match)
//! 3. **Unboxed arithmetic** — `unbox(Nat.add(box(a), box(b)))` => `a + b`
//! 4. **Unboxed comparison** — `unbox(Nat.decLt(box(a), box(b)))` => `a < b`
//! 5. **Type flow analysis** — track concrete types to detect more candidates
//! 6. **Return type specialization** — unbox return when all callers expect scalar
//!
//! # Pipeline Position
//!
//! Runs after `explicit_boxing` and before RC insertion. The boxing pass
//! conservatively inserts box/unbox at every type boundary; this pass
//! removes the ones that are provably unnecessary.
//!
//! Part of Epic #3084 — IO/FFI/Native.

pub(crate) mod rules;

#[cfg(test)]
#[path = "../unboxing_tests.rs"]
mod tests;

use std::collections::HashMap;

use crate::ir::{IRAlt, IRBody, IRDecl, IRExpr, IRType, VarId};

use rules::optimize_vdecl;

/// Configuration for the unboxing optimization pass.
#[derive(Debug, Clone)]
pub struct UnboxingConfig {
    /// Eliminate `unbox(box(x))` and `box(unbox(x))` pairs.
    pub eliminate_box_unbox_pairs: bool,
    /// Replace boxed arithmetic (Nat.add, etc.) with direct operations.
    pub unbox_arithmetic: bool,
    /// Replace boxed comparisons (Nat.decLt, etc.) with direct comparisons.
    pub unbox_comparisons: bool,
    /// Enable type flow analysis for deeper optimization.
    pub enable_type_flow: bool,
    /// Specialize return types when all callers expect unboxed values.
    pub specialize_returns: bool,
}

impl Default for UnboxingConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl UnboxingConfig {
    /// All optimizations enabled (recommended default).
    #[must_use]
    pub fn new() -> Self {
        Self {
            eliminate_box_unbox_pairs: true,
            unbox_arithmetic: true,
            unbox_comparisons: true,
            enable_type_flow: true,
            specialize_returns: true,
        }
    }

    /// No optimizations (pass-through).
    #[must_use]
    pub fn disabled() -> Self {
        Self {
            eliminate_box_unbox_pairs: false,
            unbox_arithmetic: false,
            unbox_comparisons: false,
            enable_type_flow: false,
            specialize_returns: false,
        }
    }
}

/// Statistics collected during unboxing.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UnboxingStats {
    /// Number of box/unbox pairs eliminated.
    pub pairs_eliminated: u32,
    /// Number of arithmetic operations unboxed.
    pub arithmetic_unboxed: u32,
    /// Number of comparison operations unboxed.
    pub comparisons_unboxed: u32,
    /// Number of return types specialized.
    pub returns_specialized: u32,
    /// Total declarations processed.
    pub decls_processed: u32,
}

/// Context for the unboxing pass, tracking variable definitions and types.
pub(crate) struct UnboxingContext<'a> {
    /// Maps variable to the expression it was bound to.
    pub(crate) var_defs: HashMap<VarId, IRExpr>,
    /// Maps variable to its declared type.
    pub(crate) var_types: HashMap<VarId, IRType>,
    /// Configuration.
    pub(crate) config: &'a UnboxingConfig,
    /// Accumulated statistics.
    pub(crate) stats: UnboxingStats,
}

impl<'a> UnboxingContext<'a> {
    fn new(config: &'a UnboxingConfig) -> Self {
        Self {
            var_defs: HashMap::new(),
            var_types: HashMap::new(),
            config,
            stats: UnboxingStats::default(),
        }
    }

    pub(crate) fn record_var(&mut self, var: VarId, ty: &IRType, value: &IRExpr) {
        self.var_types.insert(var, ty.clone());
        self.var_defs.insert(var, value.clone());
    }

    pub(crate) fn get_def(&self, var: VarId) -> Option<&IRExpr> {
        self.var_defs.get(&var)
    }
}

/// Apply unboxing optimization to a set of declarations.
///
/// Returns the optimized declarations and statistics.
#[must_use]
pub fn unbox_decls(decls: &[IRDecl], config: &UnboxingConfig) -> (Vec<IRDecl>, UnboxingStats) {
    let return_expectations = if config.specialize_returns {
        analyze_return_expectations(decls)
    } else {
        HashMap::new()
    };

    let mut total_stats = UnboxingStats::default();
    let mut result = Vec::with_capacity(decls.len());

    for decl in decls {
        let (optimized, stats) = unbox_decl(decl, config, &return_expectations);
        total_stats.pairs_eliminated += stats.pairs_eliminated;
        total_stats.arithmetic_unboxed += stats.arithmetic_unboxed;
        total_stats.comparisons_unboxed += stats.comparisons_unboxed;
        total_stats.returns_specialized += stats.returns_specialized;
        total_stats.decls_processed += 1;
        result.push(optimized);
    }

    (result, total_stats)
}

/// Apply unboxing optimization to a single declaration.
#[must_use]
pub fn unbox_decl(
    decl: &IRDecl,
    config: &UnboxingConfig,
    return_expectations: &HashMap<String, IRType>,
) -> (IRDecl, UnboxingStats) {
    let mut ctx = UnboxingContext::new(config);

    for (var, ty) in &decl.params {
        ctx.var_types.insert(*var, ty.clone());
    }

    let body = optimize_body(&decl.body, &mut ctx);

    let return_type = if config.specialize_returns {
        let name_str = format!("{}", decl.name);
        if let Some(expected) = return_expectations.get(&name_str) {
            if decl.return_type == IRType::Object && expected.is_scalar() {
                ctx.stats.returns_specialized += 1;
                expected.clone()
            } else {
                decl.return_type.clone()
            }
        } else {
            decl.return_type.clone()
        }
    } else {
        decl.return_type.clone()
    };

    let optimized = IRDecl {
        name: decl.name.clone(),
        params: decl.params.clone(),
        return_type,
        body,
    };

    let stats = ctx.stats.clone();
    (optimized, stats)
}

/// Convenience: apply unboxing with default config.
#[must_use]
pub fn unbox_decls_default(decls: &[IRDecl]) -> (Vec<IRDecl>, UnboxingStats) {
    unbox_decls(decls, &UnboxingConfig::new())
}

/// Check if a declaration is an unboxing candidate (has box/unbox operations).
#[must_use]
pub fn is_unboxing_candidate(decl: &IRDecl) -> bool {
    body_has_box_unbox(&decl.body)
}

/// Count the total number of box and unbox operations in a declaration.
#[must_use]
pub fn count_box_unbox_ops(decl: &IRDecl) -> (u32, u32) {
    let mut boxes = 0u32;
    let mut unboxes = 0u32;
    count_box_unbox_in_body(&decl.body, &mut boxes, &mut unboxes);
    (boxes, unboxes)
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Core optimization: transform an IR body, eliminating unnecessary box/unbox.
fn optimize_body(body: &IRBody, ctx: &mut UnboxingContext) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (opt_ty, opt_value) = optimize_vdecl(*var, ty, value, ctx);
            ctx.record_var(*var, &opt_ty, &opt_value);
            let rest = optimize_body(rest, ctx);
            IRBody::VDecl {
                var: *var,
                ty: opt_ty,
                value: opt_value,
                rest: Box::new(rest),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            for (v, t) in params {
                ctx.var_types.insert(*v, t.clone());
            }
            IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(optimize_body(jp_body, ctx)),
                rest: Box::new(optimize_body(rest, ctx)),
            }
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => optimize_case(*scrutinee, alts, default, ctx),
        _ => optimize_body_passthrough(body, ctx),
    }
}

/// Handle Case bodies — recurse into all alternatives and default.
fn optimize_case(
    scrutinee: VarId,
    alts: &[IRAlt],
    default: &Option<Box<IRBody>>,
    ctx: &mut UnboxingContext,
) -> IRBody {
    let alts = alts
        .iter()
        .map(|a| IRAlt {
            ctor: a.ctor.clone(),
            body: Box::new(optimize_body(&a.body, ctx)),
        })
        .collect();
    let default = default.as_ref().map(|d| Box::new(optimize_body(d, ctx)));
    IRBody::Case {
        scrutinee,
        alts,
        default,
    }
}

/// Handle body variants that pass through unchanged (only recurse into rest).
fn optimize_body_passthrough(body: &IRBody, ctx: &mut UnboxingContext) -> IRBody {
    match body {
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(optimize_body(rest, ctx)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(optimize_body(rest, ctx)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(optimize_body(rest, ctx)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(optimize_body(rest, ctx)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(optimize_body(rest, ctx)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: Box::new(optimize_body(rest, ctx)),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
        // The remaining variants are dispatched by `optimize_body` before this
        // helper is ever called, so they never reach here. Enumerating them
        // explicitly (instead of a catch-all `_`) keeps the match exhaustive:
        // if `IRBody` gains a variant, the compiler forces it to be classified
        // here rather than silently routing it into a runtime panic.
        IRBody::VDecl { .. } | IRBody::JDecl { .. } | IRBody::Case { .. } => {
            unreachable!("non-passthrough variant in optimize_body_passthrough")
        }
    }
}

/// Analyze all call sites to determine if return values are always unboxed.
fn analyze_return_expectations(decls: &[IRDecl]) -> HashMap<String, IRType> {
    let mut expectations: HashMap<String, Option<IRType>> = HashMap::new();
    for decl in decls {
        collect_call_return_expectations(&decl.body, &mut expectations);
    }
    expectations
        .into_iter()
        .filter_map(|(name, ty)| ty.map(|t| (name, t)))
        .collect()
}

fn collect_call_return_expectations(
    body: &IRBody,
    expectations: &mut HashMap<String, Option<IRType>>,
) {
    match body {
        IRBody::VDecl {
            value: IRExpr::Apply { fn_id, .. },
            rest,
            ..
        } => {
            let fn_name = format!("{}", fn_id.0);
            expectations.entry(fn_name).or_insert(None);
            collect_call_return_expectations(rest, expectations);
        }
        IRBody::VDecl { rest, .. } => {
            collect_call_return_expectations(rest, expectations);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_call_return_expectations(body, expectations);
            collect_call_return_expectations(rest, expectations);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_call_return_expectations(rest, expectations);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_call_return_expectations(&alt.body, expectations);
            }
            if let Some(d) = default {
                collect_call_return_expectations(d, expectations);
            }
        }
        IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => {}
    }
}

fn body_has_box_unbox(body: &IRBody) -> bool {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            matches!(value, IRExpr::Box { .. } | IRExpr::Unbox { .. }) || body_has_box_unbox(rest)
        }
        IRBody::JDecl { body, rest, .. } => body_has_box_unbox(body) || body_has_box_unbox(rest),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => body_has_box_unbox(rest),
        IRBody::Case { alts, default, .. } => {
            alts.iter().any(|a| body_has_box_unbox(&a.body))
                || default.as_ref().is_some_and(|d| body_has_box_unbox(d))
        }
        IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => false,
    }
}

fn count_box_unbox_in_body(body: &IRBody, boxes: &mut u32, unboxes: &mut u32) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Box { .. } => *boxes += 1,
                IRExpr::Unbox { .. } => *unboxes += 1,
                _ => {}
            }
            count_box_unbox_in_body(rest, boxes, unboxes);
        }
        IRBody::JDecl { body, rest, .. } => {
            count_box_unbox_in_body(body, boxes, unboxes);
            count_box_unbox_in_body(rest, boxes, unboxes);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            count_box_unbox_in_body(rest, boxes, unboxes);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                count_box_unbox_in_body(&alt.body, boxes, unboxes);
            }
            if let Some(d) = default {
                count_box_unbox_in_body(d, boxes, unboxes);
            }
        }
        IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => {}
    }
}
