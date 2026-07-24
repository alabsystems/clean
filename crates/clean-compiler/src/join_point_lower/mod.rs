// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Join Point Lowering Pass
//!
//! Transforms L5IR join points (JDecl/Jmp) into loop-based control flow
//! compatible with Rust emission. Since Rust has no `goto`, join points
//! are lowered to labeled blocks and loops.
//!
//! # Strategy
//!
//! Join points in L5IR are structurally scoped: each JDecl's body is only
//! reachable from Jmp within the same function's scope (confirmed by
//! ir_checker.rs scope enforcement). This enables labeled-loop lowering
//! (Option A from #1888).
//!
//! ## Lowering Pattern
//!
//! ```text
//! JDecl { jp0, params: [(v, T)], body, rest }
//! ```
//! becomes:
//! ```text
//! let mut v: T;
//! '_jp0_init: {
//!     <lowered rest>
//!     // Jmp { jp0, [a] } → v = a; break '_jp0_init;
//! }
//! '_jp0: loop {
//!     <lowered body>
//!     // Jmp { jp0, [a] } → v = a; continue '_jp0;
//!     break '_jp0;
//! }
//! ```
//!
//! Nested join points work because `break '_jpN_init` exits all enclosing
//! structures up to the targeted labeled block.
//!
//! Part of #1888 - Join point lowering for Rust backend.

#[cfg(test)]
mod tests;

use std::collections::HashMap;

use crate::ir::{CtorInfo, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use clean_kernel::Name;

// ── Lowered IR types ────────────────────────────────────────────────

/// Lowered IR body for Rust emission.
///
/// Mirrors `IRBody` but replaces JDecl/Jmp with loop-based control flow.
#[derive(Clone, Debug)]
pub enum LoweredBody {
    /// Variable declaration: `let x: T = e; rest`.
    VDecl {
        var: VarId,
        ty: IRType,
        value: IRExpr,
        rest: Box<LoweredBody>,
    },
    /// Increment reference count.
    Inc {
        var: VarId,
        n: u32,
        rest: Box<LoweredBody>,
    },
    /// Decrement reference count.
    Dec { var: VarId, rest: Box<LoweredBody> },
    /// Mutable object field set.
    Set {
        var: VarId,
        idx: u32,
        value: VarId,
        rest: Box<LoweredBody>,
    },
    /// Set constructor tag.
    SetTag {
        var: VarId,
        tag: u32,
        rest: Box<LoweredBody>,
    },
    /// Store USize value at position in object.
    USet {
        var: VarId,
        idx: u32,
        value: VarId,
        rest: Box<LoweredBody>,
    },
    /// Store scalar value at position in object.
    SSet {
        var: VarId,
        n: u32,
        offset: u32,
        value: VarId,
        ty: IRType,
        rest: Box<LoweredBody>,
    },
    /// Case analysis.
    Case {
        scrutinee: VarId,
        alts: Vec<LoweredAlt>,
        default: Option<Box<LoweredBody>>,
    },
    /// Return value.
    Ret(IRArg),
    /// Unreachable code.
    Unreachable,

    /// Lowered join point: labeled-block init + labeled-loop body.
    ///
    /// Emits as:
    /// ```text
    /// let mut param_var: T;  // for each param
    /// '_jpN_init: { <init> }
    /// '_jpN: loop { <body>; break '_jpN; }
    /// ```
    JoinPoint {
        jp: JoinPointId,
        params: Vec<(VarId, IRType)>,
        /// Code that runs before JP body (was "rest" in JDecl).
        init: Box<LoweredBody>,
        /// JP body that runs on each entry.
        body: Box<LoweredBody>,
    },

    /// Jump from init block: assign args, break out of init.
    JumpBreak {
        jp: JoinPointId,
        assignments: Vec<(VarId, IRArg)>,
    },

    /// Jump from body (re-entry): assign args, continue loop.
    JumpContinue {
        jp: JoinPointId,
        assignments: Vec<(VarId, IRArg)>,
    },
}

impl LoweredBody {
    /// Returns true if this body always terminates (return, unreachable, jump)
    /// and never falls through to the next statement.
    pub fn is_terminating(&self) -> bool {
        match self {
            LoweredBody::Ret(_) | LoweredBody::Unreachable => true,
            LoweredBody::JumpBreak { .. } | LoweredBody::JumpContinue { .. } => true,
            LoweredBody::VDecl { rest, .. }
            | LoweredBody::Inc { rest, .. }
            | LoweredBody::Dec { rest, .. }
            | LoweredBody::Set { rest, .. }
            | LoweredBody::SetTag { rest, .. }
            | LoweredBody::USet { rest, .. }
            | LoweredBody::SSet { rest, .. } => rest.is_terminating(),
            LoweredBody::Case { alts, default, .. } => {
                let alts_terminate = alts.iter().all(|alt| alt.body.is_terminating());
                // No default means exhaustive coverage — all constructors handled by alts.
                let default_terminates = default.as_ref().is_none_or(|d| d.is_terminating());
                alts_terminate && default_terminates
            }
            LoweredBody::JoinPoint { .. } => false,
        }
    }
}

/// Lowered case alternative.
#[derive(Clone, Debug)]
pub struct LoweredAlt {
    pub ctor: CtorInfo,
    pub body: Box<LoweredBody>,
}

/// Lowered function declaration.
#[derive(Clone, Debug)]
pub struct LoweredDecl {
    pub name: Name,
    pub params: Vec<(VarId, IRType)>,
    pub return_type: IRType,
    pub body: LoweredBody,
}

// ── Lowering context ────────────────────────────────────────────────

/// Whether a Jmp is in the init or body subtree of its target JP.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum JpLocation {
    Init,
    Body,
}

/// Info about a visible join point during lowering.
#[derive(Clone, Debug)]
struct JpInfo {
    params: Vec<(VarId, IRType)>,
    location: JpLocation,
}

/// Context for the lowering traversal.
struct LowerCtx {
    jp_info: HashMap<JoinPointId, JpInfo>,
}

impl LowerCtx {
    fn new() -> Self {
        Self {
            jp_info: HashMap::new(),
        }
    }
}

// ── Public API ──────────────────────────────────────────────────────

/// Lower join points in an IR declaration.
#[must_use]
pub fn lower_decl(decl: &IRDecl) -> LoweredDecl {
    let mut ctx = LowerCtx::new();
    LoweredDecl {
        name: decl.name.clone(),
        params: decl.params.clone(),
        return_type: decl.return_type.clone(),
        body: lower_body(&decl.body, &mut ctx),
    }
}

/// Lower join points in multiple declarations.
#[must_use]
pub fn lower_decls(decls: &[IRDecl]) -> Vec<LoweredDecl> {
    decls.iter().map(lower_decl).collect()
}

// ── Lowering logic ──────────────────────────────────────────────────

/// Lower an IR body, replacing JDecl/Jmp with loop-based constructs.
fn lower_body(body: &IRBody, ctx: &mut LowerCtx) -> LoweredBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => LoweredBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(lower_body(rest, ctx)),
        },
        IRBody::Inc { var, n, rest } => LoweredBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(lower_body(rest, ctx)),
        },
        IRBody::Dec { var, rest } => LoweredBody::Dec {
            var: *var,
            rest: Box::new(lower_body(rest, ctx)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => LoweredBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(lower_body(rest, ctx)),
        },
        IRBody::SetTag { var, tag, rest } => LoweredBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(lower_body(rest, ctx)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => LoweredBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(lower_body(rest, ctx)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => LoweredBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: Box::new(lower_body(rest, ctx)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => lower_case(*scrutinee, alts, default, ctx),
        IRBody::Ret(arg) => LoweredBody::Ret(arg.clone()),
        IRBody::Unreachable => LoweredBody::Unreachable,
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => lower_jdecl(*jp, params, jp_body, rest, ctx),
        IRBody::Jmp { jp, args } => lower_jmp(*jp, args, ctx),
    }
}

/// Lower a Case node.
fn lower_case(
    scrutinee: VarId,
    alts: &[crate::ir::IRAlt],
    default: &Option<Box<IRBody>>,
    ctx: &mut LowerCtx,
) -> LoweredBody {
    LoweredBody::Case {
        scrutinee,
        alts: alts
            .iter()
            .map(|alt| LoweredAlt {
                ctor: alt.ctor.clone(),
                body: Box::new(lower_body(&alt.body, ctx)),
            })
            .collect(),
        default: default.as_ref().map(|d| Box::new(lower_body(d, ctx))),
    }
}

/// Lower a JDecl into a JoinPoint with init block and body loop.
fn lower_jdecl(
    jp: JoinPointId,
    params: &[(VarId, IRType)],
    jp_body: &IRBody,
    rest: &IRBody,
    ctx: &mut LowerCtx,
) -> LoweredBody {
    // Register JP with Init location for lowering rest.
    ctx.jp_info.insert(
        jp,
        JpInfo {
            params: params.to_vec(),
            location: JpLocation::Init,
        },
    );
    let init = lower_body(rest, ctx);

    // Switch to Body location for lowering JP body.
    if let Some(info) = ctx.jp_info.get_mut(&jp) {
        info.location = JpLocation::Body;
    }
    let body = lower_body(jp_body, ctx);

    ctx.jp_info.remove(&jp);

    LoweredBody::JoinPoint {
        jp,
        params: params.to_vec(),
        init: Box::new(init),
        body: Box::new(body),
    }
}

/// Lower a Jmp into JumpBreak (from init) or JumpContinue (from body).
fn lower_jmp(jp: JoinPointId, args: &[IRArg], ctx: &LowerCtx) -> LoweredBody {
    let info = ctx
        .jp_info
        .get(&jp)
        .expect("Jmp to undefined join point (IR checker should catch this)");

    let assignments: Vec<(VarId, IRArg)> = info
        .params
        .iter()
        .zip(args.iter())
        .map(|((var, _ty), arg)| (*var, arg.clone()))
        .collect();

    match info.location {
        JpLocation::Init => LoweredBody::JumpBreak { jp, assignments },
        JpLocation::Body => LoweredBody::JumpContinue { jp, assignments },
    }
}
