// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! D transform: depth-first search for last use of scrutinee.
//!
//! Matches Lean 4's `D` and `D.go` in `ResetReuse.lean:186-246`.
//! Also contains helper functions: classify_use, is_fvar_live_in,
//! value_stores_var, value_references_var.
//!
//! Part of #963 - Compiler IR infrastructure.

use super::s_transform::try_s;
use super::FVarIdAllocator;
use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetValue};
use crate::rc::borrow::{BorrowMap, Ownership};
use clean_kernel::{Environment, FVarId, Name};
use std::collections::HashSet;

/// Three-way classification of how a variable is used in a let-binding.
///
/// Matches Lean 4's `UseClassification` in `ResetReuse.lean:130-142`.
/// This is critical for correct D-transform behavior:
/// - `OwnedArg`: variable is consumed (passed as owned arg) → D returns alive=true
/// - `Other`: variable is used but not consumed (e.g. projection) → D applies S to continuation only
/// - `None`: variable is not used → D continues searching
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum UseClassification {
    /// Variable is passed as an owned argument to a function call.
    OwnedArg,
    /// Variable is used but not consumed (projection, borrowed parameter).
    Other,
    /// Variable is not used in this instruction.
    None,
}

/// Immutable context for D-transform search.
///
/// Bundles the parameters that remain constant throughout a D/S search
/// for a given scrutinee in a case branch.
pub(super) struct DCtx<'a> {
    /// The scrutinee variable we're searching for.
    pub x: FVarId,
    /// Number of fields in the source constructor.
    pub n: usize,
    /// Name of the source constructor.
    pub source_ctor: &'a Name,
    /// Whether cross-family reuse is enabled.
    pub cross_family: bool,
    /// Borrow annotations for function parameters.
    pub borrow_map: &'a BorrowMap,
    /// Kernel environment for constructor layout lookup (cross-family mode).
    pub env: Option<&'a Environment>,
}

/// Check if FVarId `x` is referenced (live) anywhere in `code`.
///
/// Matches Lean 4's `Code.isFVarLiveIn` — returns true if `x` appears
/// in any use position (args, scrutinee, return value, jmp args).
pub(super) fn is_fvar_live_in(code: &Code, x: FVarId) -> bool {
    match code {
        Code::Let(decl, body) => value_references_var(&decl.value, x) || is_fvar_live_in(body, x),
        Code::Fun(fun_decl, body) => is_fvar_live_in(&fun_decl.body, x) || is_fvar_live_in(body, x),
        Code::JoinPoint(jp_decl, body) => {
            is_fvar_live_in(&jp_decl.body, x) || is_fvar_live_in(body, x)
        }
        Code::Cases(cases) => {
            cases.scrutinee == x
                || cases.alts.iter().any(|alt| match alt {
                    Alt::Ctor { body, .. } => is_fvar_live_in(body, x),
                    Alt::Default(body) => is_fvar_live_in(body, x),
                })
        }
        Code::Jmp { args, .. } => args.iter().any(|a| matches!(a, Arg::FVar(f) if *f == x)),
        Code::Return(fvar) => *fvar == x,
        Code::Unreachable(_) => false,
    }
}

/// Check if a LetValue references (uses) the variable in any position.
fn value_references_var(value: &LetValue, x: FVarId) -> bool {
    match value {
        LetValue::Proj { structure, .. } => *structure == x,
        LetValue::Const { args, .. }
        | LetValue::FVar { args, .. }
        | LetValue::Ctor { args, .. }
        | LetValue::Reuse { args, .. } => args.iter().any(|a| matches!(a, Arg::FVar(f) if *f == x)),
        LetValue::Lit(_) | LetValue::Erased => false,
    }
}

/// Check if a let-value stores the variable in a constructor.
pub(super) fn value_stores_var(value: &LetValue, x: FVarId) -> bool {
    match value {
        LetValue::Ctor { args, .. } => args
            .iter()
            .any(|arg| matches!(arg, Arg::FVar(f) if *f == x)),
        _ => false,
    }
}

/// Classify how variable `x` is used in a let-value.
///
/// Matches Lean 4's `classifyUse` in `ResetReuse.lean:147-177`.
///
/// Bug 22 fix: accepts `borrow_map` to check whether call arguments are
/// borrowed. When param.borrow is true, classification downgrades from
/// OwnedArg to Other, matching Lean 4 ResetReuse.lean:147-167.
pub(super) fn classify_use(
    value: &LetValue,
    x: FVarId,
    borrow_map: &BorrowMap,
) -> UseClassification {
    match value {
        LetValue::Proj { structure, .. } => {
            if *structure == x {
                UseClassification::Other
            } else {
                UseClassification::None
            }
        }
        // Function calls: check borrow info per argument position.
        // (Lean 4: ResetReuse.lean:147-167)
        LetValue::Const { name, args, .. } => {
            let borrow_info = borrow_map.get(name);
            let mut result = UseClassification::None;
            for (i, arg) in args.iter().enumerate() {
                if matches!(arg, Arg::FVar(f) if *f == x) {
                    let is_borrowed = borrow_info
                        .and_then(|b| b.params.get(i))
                        .is_some_and(|o| *o == Ownership::Borrowed);
                    result = match (result, is_borrowed) {
                        (UseClassification::OwnedArg, true) => UseClassification::Other,
                        (UseClassification::None, true) => UseClassification::Other,
                        (UseClassification::None, false) => UseClassification::OwnedArg,
                        (r, _) => r,
                    };
                }
            }
            result
        }
        // Indirect calls via FVar: no static callee name, so no borrow info.
        // Conservative: treat as OwnedArg if x appears in args.
        LetValue::FVar { args, .. } => {
            if args
                .iter()
                .any(|arg| matches!(arg, Arg::FVar(f) if *f == x))
            {
                UseClassification::OwnedArg
            } else {
                UseClassification::None
            }
        }
        LetValue::Ctor { args, .. } => {
            if args
                .iter()
                .any(|arg| matches!(arg, Arg::FVar(f) if *f == x))
            {
                UseClassification::Other
            } else {
                UseClassification::None
            }
        }
        LetValue::Reuse { args, slot, .. } => {
            if *slot == x || args.iter().any(|a| matches!(a, Arg::FVar(f) if *f == x)) {
                UseClassification::Other
            } else {
                UseClassification::None
            }
        }
        LetValue::Lit(_) | LetValue::Erased => UseClassification::None,
    }
}

/// D: Depth-first search for last use of scrutinee x.
///
/// Outer wrapper: calls `d_go` to find where x is dead, then calls S there.
/// Matches Lean 4's `D` in `ResetReuse.lean:186-191`.
pub(super) fn d_transform(
    ctx: &DCtx<'_>,
    code: &Code,
    already_found: &mut HashSet<FVarId>,
    alloc: &mut FVarIdAllocator,
) -> Code {
    let (c, alive) = d_go(ctx, code, already_found, alloc);
    if alive {
        c
    } else {
        // x is dead — invoke S to find reuse opportunities
        let (s_result, _) = try_s(
            ctx.x,
            ctx.n,
            ctx.source_ctor,
            &c,
            already_found,
            ctx.cross_family,
            alloc,
            ctx.env,
        );
        s_result
    }
}

/// D inner: depth-first search returning (code, alive).
///
/// Returns (transformed_code, alive) where alive=true means x is still live.
/// Matches Lean 4's `D.go` in `ResetReuse.lean:202-245`.
pub(super) fn d_go(
    ctx: &DCtx<'_>,
    code: &Code,
    already_found: &mut HashSet<FVarId>,
    alloc: &mut FVarIdAllocator,
) -> (Code, bool) {
    match code {
        Code::Let(decl, body) => {
            if value_stores_var(&decl.value, ctx.x) {
                return (code.clone(), true);
            }

            let (new_body, found) = d_go(ctx, body, already_found, alloc);

            if found {
                return (Code::Let(decl.clone(), Box::new(new_body)), true);
            }

            // (Lean 4: ResetReuse.lean:235-242)
            match classify_use(&decl.value, ctx.x, ctx.borrow_map) {
                UseClassification::OwnedArg => (Code::Let(decl.clone(), Box::new(new_body)), true),
                UseClassification::Other => {
                    let s_body = try_s(
                        ctx.x,
                        ctx.n,
                        ctx.source_ctor,
                        &new_body,
                        already_found,
                        ctx.cross_family,
                        alloc,
                        ctx.env,
                    );
                    (Code::Let(decl.clone(), Box::new(s_body.0)), true)
                }
                UseClassification::None => (Code::Let(decl.clone(), Box::new(new_body)), false),
            }
        }

        // Bug 4 fix: Cases checks liveness and propagates found correctly.
        // (Lean 4: ResetReuse.lean:204-210)
        Code::Cases(cases) => {
            if is_fvar_live_in(code, ctx.x) {
                let new_alts: Vec<Alt> = cases
                    .alts
                    .iter()
                    .map(|alt| match alt {
                        Alt::Ctor {
                            ctor_name,
                            params,
                            body,
                        } => {
                            let new_body = d_transform(ctx, body, already_found, alloc);
                            Alt::Ctor {
                                ctor_name: ctor_name.clone(),
                                params: params.clone(),
                                body: Box::new(new_body),
                            }
                        }
                        Alt::Default(body) => {
                            let new_body = d_transform(ctx, body, already_found, alloc);
                            Alt::Default(Box::new(new_body))
                        }
                    })
                    .collect();

                (
                    Code::Cases(Cases {
                        type_name: cases.type_name.clone(),
                        result_type: cases.result_type.clone(),
                        scrutinee: cases.scrutinee,
                        alts: new_alts,
                    }),
                    true,
                )
            } else {
                (code.clone(), false)
            }
        }

        Code::Fun(fun_decl, body) => {
            let (new_body, found) = d_go(ctx, body, already_found, alloc);
            (Code::Fun(fun_decl.clone(), Box::new(new_body)), found)
        }

        // Bug 3 fix: JoinPoint recurses into BOTH jp body and continuation.
        // (Lean 4: ResetReuse.lean:211-220)
        Code::JoinPoint(jp_decl, body) => {
            let (new_cont, found) = d_go(ctx, body, already_found, alloc);
            let (new_jp_body, _) = d_go(ctx, &jp_decl.body, already_found, alloc);
            let new_decl = FunDecl {
                fvar_id: jp_decl.fvar_id,
                name: jp_decl.name.clone(),
                params: jp_decl.params.clone(),
                ty: jp_decl.ty.clone(),
                body: Box::new(new_jp_body),
            };
            (Code::JoinPoint(new_decl, Box::new(new_cont)), found)
        }

        // Bug 5 fix: Terminals check liveness instead of unconditionally calling S.
        // (Lean 4: ResetReuse.lean:243-244)
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => {
            let alive = is_fvar_live_in(code, ctx.x);
            (code.clone(), alive)
        }
    }
}
