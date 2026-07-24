// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5IR Closure Conversion Pass
//!
//! Converts PartialApply/ClosureApply in L5IR into explicit closure objects.
//! Counterpart of `closure.rs` (LCNF level) for the low-level IR.
//!
//! Pipeline: `L5CNF -> to_ir -> closure_convert -> borrow_infer -> boxing -> RC -> emit`
//!
//! Part of #3084 - Runtime closure support.

use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use std::collections::HashMap;

// ════════════════════════════════════════════════════════════════════════════
// Environment Layout
// ════════════════════════════════════════════════════════════════════════════

/// A single captured variable in a closure environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IRCapture {
    pub(crate) var: VarId,
    pub(crate) env_index: u32,
    pub(crate) ty: IRType,
}

/// Layout of a closure environment object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClosureLayout {
    pub(crate) fn_id: FnId,
    pub(crate) arity: u16,
    pub(crate) captures: Vec<IRCapture>,
}

impl ClosureLayout {
    #[must_use]
    pub(crate) fn capture_count(&self) -> usize {
        self.captures.len()
    }

    #[must_use]
    pub(crate) fn remaining_arity(&self) -> u16 {
        self.arity.saturating_sub(self.captures.len() as u16)
    }

    /// Build CtorInfo for the closure object (tag 0, all captures boxed).
    #[must_use]
    pub(crate) fn ctor_info(&self) -> CtorInfo {
        CtorInfo {
            name: Name::from_string(&format!("_closure.{}", self.fn_id.0)),
            tag: 0,
            num_scalars: 0,
            num_objects: self.captures.len() as u32,
            field_types: self.captures.iter().map(|c| c.ty.boxed()).collect(),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Statistics and Output
// ════════════════════════════════════════════════════════════════════════════

/// Statistics collected during closure conversion.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ClosureConvertStats {
    pub(crate) closures_created: u32,
    pub(crate) total_captures: u32,
    pub(crate) closure_applies_lowered: u32,
    pub(crate) functions_hoisted: u32,
}

/// Result of running closure conversion on declarations.
#[derive(Clone, Debug)]
pub(crate) struct ClosureConvertOutput {
    pub(crate) decls: Vec<IRDecl>,
    pub(crate) hoisted: Vec<IRDecl>,
    pub(crate) stats: ClosureConvertStats,
}

/// Internal state for the conversion pass.
struct ConvertState {
    type_env: HashMap<VarId, IRType>,
    stats: ClosureConvertStats,
    hoisted: Vec<IRDecl>,
}

impl ConvertState {
    fn new() -> Self {
        Self {
            type_env: HashMap::new(),
            stats: ClosureConvertStats::default(),
            hoisted: Vec::new(),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Entry Points
// ════════════════════════════════════════════════════════════════════════════

/// Run closure conversion on a slice of IR declarations.
#[must_use]
pub(crate) fn closure_convert_decls(decls: &[IRDecl]) -> ClosureConvertOutput {
    let mut state = ConvertState::new();
    let converted = decls.iter().map(|d| convert_decl(d, &mut state)).collect();
    ClosureConvertOutput {
        decls: converted,
        hoisted: state.hoisted,
        stats: state.stats,
    }
}

/// Run closure conversion on a single IR declaration.
#[must_use]
pub(crate) fn closure_convert_decl(decl: &IRDecl) -> ClosureConvertOutput {
    closure_convert_decls(std::slice::from_ref(decl))
}

fn convert_decl(decl: &IRDecl, state: &mut ConvertState) -> IRDecl {
    for (v, ty) in &decl.params {
        state.type_env.insert(*v, ty.clone());
    }
    IRDecl {
        name: decl.name.clone(),
        params: decl.params.clone(),
        return_type: decl.return_type.clone(),
        body: convert_body(&decl.body, state),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Body Conversion (split into binding/control helpers for size)
// ════════════════════════════════════════════════════════════════════════════

/// Recursively convert an IRBody, lowering PartialApply and ClosureApply.
fn convert_body(body: &IRBody, state: &mut ConvertState) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            state.type_env.insert(*var, ty.clone());
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: convert_expr(value, state),
                rest: Box::new(convert_body(rest, state)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            for (v, ty) in params {
                state.type_env.insert(*v, ty.clone());
            }
            IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(convert_body(jp_body, state)),
                rest: Box::new(convert_body(rest, state)),
            }
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => convert_case(*scrutinee, alts, default.as_deref(), state),
        _ => convert_passthrough(body, state),
    }
}

/// Convert case bodies.
fn convert_case(
    scrutinee: VarId,
    alts: &[IRAlt],
    default: Option<&IRBody>,
    state: &mut ConvertState,
) -> IRBody {
    let new_alts = alts
        .iter()
        .map(|alt| IRAlt {
            ctor: alt.ctor.clone(),
            body: Box::new(convert_body(&alt.body, state)),
        })
        .collect();
    IRBody::Case {
        scrutinee,
        alts: new_alts,
        default: default.map(|d| Box::new(convert_body(d, state))),
    }
}

/// Handle body variants that only recurse into `rest` (no expr to convert).
fn convert_passthrough(body: &IRBody, state: &mut ConvertState) -> IRBody {
    match body {
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(convert_body(rest, state)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(convert_body(rest, state)),
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
            rest: Box::new(convert_body(rest, state)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(convert_body(rest, state)),
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
            rest: Box::new(convert_body(rest, state)),
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
            rest: Box::new(convert_body(rest, state)),
        },
        // Terminals
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
        // VDecl, JDecl, Case handled in convert_body
        _ => body.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Expression Conversion
// ════════════════════════════════════════════════════════════════════════════

/// Convert an IRExpr, handling PartialApply and ClosureApply.
fn convert_expr(expr: &IRExpr, state: &mut ConvertState) -> IRExpr {
    match expr {
        IRExpr::PartialApply { fn_id, arity, args } => {
            convert_partial_apply(fn_id, *arity, args, expr, state)
        }
        IRExpr::ClosureApply { closure, args } => {
            state.stats.closure_applies_lowered += 1;
            IRExpr::ClosureApply {
                closure: closure.clone(),
                args: args.clone(),
            }
        }
        _ => expr.clone(),
    }
}

/// Lower a PartialApply to either a hoisted reference or a closure Ctor.
fn convert_partial_apply(
    fn_id: &FnId,
    arity: u16,
    args: &[IRArg],
    original: &IRExpr,
    state: &mut ConvertState,
) -> IRExpr {
    let captures: Vec<IRCapture> = args
        .iter()
        .enumerate()
        .filter_map(|(i, arg)| {
            if let IRArg::Var(v) = arg {
                let ty = state.type_env.get(v).cloned().unwrap_or(IRType::Object);
                Some(IRCapture {
                    var: *v,
                    env_index: i as u32,
                    ty,
                })
            } else {
                None
            }
        })
        .collect();

    let layout = ClosureLayout {
        fn_id: fn_id.clone(),
        arity,
        captures,
    };

    if layout.capture_count() == 0 {
        state.stats.functions_hoisted += 1;
        return original.clone();
    }

    state.stats.closures_created += 1;
    state.stats.total_captures += layout.capture_count() as u32;

    let ctor_info = layout.ctor_info();
    let ctor_args = layout.captures.iter().map(|c| IRArg::Var(c.var)).collect();
    IRExpr::Ctor {
        info: ctor_info,
        args: ctor_args,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Closure Hoisting
// ════════════════════════════════════════════════════════════════════════════

/// Identify PartialApply with zero captures that can be hoisted.
#[must_use]
pub(crate) fn find_hoistable_closures(decls: &[IRDecl]) -> Vec<FnId> {
    let mut hoistable = Vec::new();
    for decl in decls {
        find_hoistable_in_body(&decl.body, &mut hoistable);
    }
    hoistable
}

fn find_hoistable_in_body(body: &IRBody, out: &mut Vec<FnId>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::PartialApply { fn_id, args, .. } = value {
                if args.is_empty() {
                    out.push(fn_id.clone());
                }
            }
            find_hoistable_in_body(rest, out);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            find_hoistable_in_body(jp, out);
            find_hoistable_in_body(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            find_hoistable_in_body(rest, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                find_hoistable_in_body(&alt.body, out);
            }
            if let Some(def) = default {
                find_hoistable_in_body(def, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Counting Utilities
// ════════════════════════════════════════════════════════════════════════════

/// Count total PartialApply sites in declarations.
#[must_use]
pub(crate) fn count_partial_applies(decls: &[IRDecl]) -> u32 {
    count_expr_sites(decls, |e| matches!(e, IRExpr::PartialApply { .. }))
}

/// Count total ClosureApply sites in declarations.
#[must_use]
pub(crate) fn count_closure_applies(decls: &[IRDecl]) -> u32 {
    count_expr_sites(decls, |e| matches!(e, IRExpr::ClosureApply { .. }))
}

fn count_expr_sites(decls: &[IRDecl], pred: fn(&IRExpr) -> bool) -> u32 {
    decls.iter().map(|d| count_in_body(&d.body, pred)).sum()
}

fn count_in_body(body: &IRBody, pred: fn(&IRExpr) -> bool) -> u32 {
    match body {
        IRBody::VDecl { value, rest, .. } => u32::from(pred(value)) + count_in_body(rest, pred),
        IRBody::JDecl { body: jp, rest, .. } => count_in_body(jp, pred) + count_in_body(rest, pred),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => count_in_body(rest, pred),
        IRBody::Case { alts, default, .. } => {
            let mut n: u32 = alts.iter().map(|a| count_in_body(&a.body, pred)).sum();
            if let Some(def) = default {
                n += count_in_body(def, pred);
            }
            n
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 0,
    }
}

#[cfg(test)]
#[path = "closure_convert_tests.rs"]
mod tests;
