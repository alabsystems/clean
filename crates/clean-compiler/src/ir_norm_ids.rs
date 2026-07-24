// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NormIds — Normalize variable IDs in L5IR to sequential numbering.
//!
//! This pass rewrites all `VarId` and `JoinPointId` values in an IR declaration
//! so that they use sequential numbering (0, 1, 2, ...) assigned in definition
//! order (parameters first, then body in left-to-right traversal order).
//!
//! The output is deterministic and comparable: two structurally identical IR
//! declarations will produce identical normalized forms regardless of the
//! original variable numbering.
//!
//! `FnId` values are global function names and are left unchanged — they
//! reference external declarations, not local bindings.
//!
//! # Reference
//!
//! Based on Lean 4's `src/Lean/Compiler/IR/NormIds.lean`
//! (Leonardo de Moura, Microsoft, 2019).
//!
//! Part of #1032 — IR ID normalization.

use crate::ir::{IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use std::collections::HashMap;

/// State for the normalization pass.
///
/// Tracks the next sequential ID to assign and the mapping from old IDs
/// to their normalized counterparts. Both `VarId` and `JoinPointId` share
/// a single counter, matching Lean 4's design where both use the same
/// `Index` namespace.
struct NormState {
    next_id: u32,
    map: HashMap<u32, u32>,
}

impl NormState {
    fn new() -> Self {
        Self {
            next_id: 0,
            map: HashMap::new(),
        }
    }

    /// Bind a VarId, assigning it the next sequential ID.
    fn bind_var(&mut self, v: VarId) -> VarId {
        let id = self.next_id;
        self.next_id += 1;
        self.map.insert(v.0, id);
        VarId(id)
    }

    /// Bind a JoinPointId, assigning it the next sequential ID.
    fn bind_jp(&mut self, jp: JoinPointId) -> JoinPointId {
        let id = self.next_id;
        self.next_id += 1;
        self.map.insert(jp.0, id);
        JoinPointId(id)
    }

    /// Look up a VarId in the renaming map. Returns the original if not found.
    fn norm_var(&self, v: VarId) -> VarId {
        VarId(self.map.get(&v.0).copied().unwrap_or(v.0))
    }

    /// Look up a JoinPointId in the renaming map. Returns the original if not found.
    fn norm_jp(&self, jp: JoinPointId) -> JoinPointId {
        JoinPointId(self.map.get(&jp.0).copied().unwrap_or(jp.0))
    }
}

// ─── Argument normalization ─────────────────────────────────────────────

fn norm_arg(state: &NormState, arg: &IRArg) -> IRArg {
    match arg {
        IRArg::Var(v) => IRArg::Var(state.norm_var(*v)),
        IRArg::Erased => IRArg::Erased,
    }
}

fn norm_args(state: &NormState, args: &[IRArg]) -> Vec<IRArg> {
    args.iter().map(|a| norm_arg(state, a)).collect()
}

// ─── Expression normalization ───────────────────────────────────────────

fn norm_expr(state: &NormState, expr: &IRExpr) -> IRExpr {
    match expr {
        IRExpr::Ctor { info, args } => IRExpr::Ctor {
            info: info.clone(),
            args: norm_args(state, args),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: norm_arg(state, arg),
        },
        IRExpr::Tag(arg) => IRExpr::Tag(norm_arg(state, arg)),
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: ty.clone(),
            arg: norm_arg(state, arg),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: norm_arg(state, arg),
        },
        IRExpr::Lit(lit) => IRExpr::Lit(lit.clone()),
        IRExpr::Apply { fn_id, args } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: norm_args(state, args),
        },
        IRExpr::PartialApply { fn_id, arity, args } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: norm_args(state, args),
        },
        IRExpr::ClosureApply { closure, args } => IRExpr::ClosureApply {
            closure: norm_arg(state, closure),
            args: norm_args(state, args),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: state.norm_var(*var),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: state.norm_var(*var),
            ty: ty.clone(),
        },
        IRExpr::IsShared(v) => IRExpr::IsShared(state.norm_var(*v)),
        IRExpr::String(s) => IRExpr::String(s.clone()),
        IRExpr::Reset(v) => IRExpr::Reset(state.norm_var(*v)),
        IRExpr::Reuse { var, ctor, args } => IRExpr::Reuse {
            var: state.norm_var(*var),
            ctor: ctor.clone(),
            args: norm_args(state, args),
        },
    }
}

// ─── Body normalization ─────────────────────────────────────────────────

fn norm_vdecl(
    state: &mut NormState,
    var: VarId,
    ty: &IRType,
    value: &IRExpr,
    rest: &IRBody,
) -> IRBody {
    let new_value = norm_expr(state, value);
    let new_var = state.bind_var(var);
    IRBody::VDecl {
        var: new_var,
        ty: ty.clone(),
        value: new_value,
        rest: Box::new(norm_body(state, rest)),
    }
}

fn norm_jdecl(
    state: &mut NormState,
    jp: JoinPointId,
    params: &[(VarId, IRType)],
    jp_body: &IRBody,
    rest: &IRBody,
) -> IRBody {
    let new_params: Vec<_> = params
        .iter()
        .map(|(v, ty)| (state.bind_var(*v), ty.clone()))
        .collect();
    let new_jp_body = norm_body(state, jp_body);
    let new_jp = state.bind_jp(jp);
    IRBody::JDecl {
        jp: new_jp,
        params: new_params,
        body: Box::new(new_jp_body),
        rest: Box::new(norm_body(state, rest)),
    }
}

fn norm_body(state: &mut NormState, body: &IRBody) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => norm_vdecl(state, *var, ty, value, rest),
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => norm_jdecl(state, *jp, params, jp_body, rest),
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: state.norm_var(*var),
            n: *n,
            rest: Box::new(norm_body(state, rest)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: state.norm_var(*var),
            rest: Box::new(norm_body(state, rest)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: state.norm_var(*var),
            idx: *idx,
            value: state.norm_var(*value),
            rest: Box::new(norm_body(state, rest)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: state.norm_var(*var),
            tag: *tag,
            rest: Box::new(norm_body(state, rest)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: state.norm_var(*var),
            idx: *idx,
            value: state.norm_var(*value),
            rest: Box::new(norm_body(state, rest)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: state.norm_var(*var),
            n: *n,
            offset: *offset,
            value: state.norm_var(*value),
            ty: ty.clone(),
            rest: Box::new(norm_body(state, rest)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: state.norm_var(*scrutinee),
            alts: alts.iter().map(|alt| norm_alt(state, alt)).collect(),
            default: default.as_ref().map(|d| Box::new(norm_body(state, d))),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: state.norm_jp(*jp),
            args: norm_args(state, args),
        },
        IRBody::Ret(arg) => IRBody::Ret(norm_arg(state, arg)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

fn norm_alt(state: &mut NormState, alt: &IRAlt) -> IRAlt {
    IRAlt {
        ctor: alt.ctor.clone(),
        body: Box::new(norm_body(state, &alt.body)),
    }
}

// ─── Public API ─────────────────────────────────────────────────────────

/// Normalize all variable and join-point IDs in a declaration to sequential
/// numbering starting from 0.
///
/// Parameters are numbered first in declaration order, then body bindings
/// in left-to-right traversal order. `FnId` references (global function
/// names) are left unchanged.
///
/// # Example
///
/// ```text
/// // Before: params x100, x200; body uses x300
/// // After:  params x0, x1; body uses x2
/// let normalized = normalize_ids(&decl);
/// ```
#[must_use]
pub fn normalize_ids(decl: &IRDecl) -> IRDecl {
    let mut state = NormState::new();

    // Bind parameters first, in declaration order.
    let new_params: Vec<_> = decl
        .params
        .iter()
        .map(|(v, ty)| (state.bind_var(*v), ty.clone()))
        .collect();

    let new_body = norm_body(&mut state, &decl.body);

    IRDecl {
        name: decl.name.clone(),
        params: new_params,
        return_type: decl.return_type.clone(),
        body: new_body,
    }
}

/// Check whether all variable and join-point IDs in a declaration are unique.
///
/// Returns `true` if no two binding sites share the same raw ID value.
/// This is a precondition for several IR passes and a postcondition of
/// `normalize_ids`.
#[must_use]
pub fn has_unique_ids(decl: &IRDecl) -> bool {
    let mut seen = std::collections::HashSet::new();
    for (v, _) in &decl.params {
        if !seen.insert(v.0) {
            return false;
        }
    }
    body_unique_ids(&decl.body, &mut seen)
}

fn body_unique_ids(body: &IRBody, seen: &mut std::collections::HashSet<u32>) -> bool {
    match body {
        IRBody::VDecl { var, rest, .. } => seen.insert(var.0) && body_unique_ids(rest, seen),
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            for (v, _) in params {
                if !seen.insert(v.0) {
                    return false;
                }
            }
            seen.insert(jp.0) && body_unique_ids(jp_body, seen) && body_unique_ids(rest, seen)
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => body_unique_ids(rest, seen),
        IRBody::Case { alts, default, .. } => {
            alts.iter().all(|alt| body_unique_ids(&alt.body, seen))
                && default.as_ref().is_none_or(|d| body_unique_ids(d, seen))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => true,
    }
}
