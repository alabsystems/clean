// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! S transform: substitute compatible constructors with reuse.
//!
//! Matches Lean 4's `S` in `ResetReuse.lean:81-123`.
//! Also contains try_s (reset insertion wrapper) and
//! is_compatible_ctor / get_ctor_family helpers.
//!
//! Part of #963 - Compiler IR infrastructure.

use super::FVarIdAllocator;
use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue};
use crate::rc::pseudo_op;
use crate::to_ir::types::expr_to_ir_type;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};
use std::collections::HashSet;

/// Try S transformation; insert reset if successful.
pub(super) fn try_s(
    x: FVarId,
    n: usize,
    source_ctor: &Name,
    code: &Code,
    already_found: &mut HashSet<FVarId>,
    cross_family: bool,
    alloc: &mut FVarIdAllocator,
    env: Option<&Environment>,
) -> (Code, bool) {
    let w = alloc.fresh().expect("FVarId allocation overflow");

    if let Some(reused_code) = s_transform(w, n, source_ctor, code, cross_family, env) {
        already_found.insert(x);

        // Insert: let w := reset x; reused_code
        let reset_code = Code::Let(
            LetDecl::new(
                w,
                pseudo_op::NAME_RESET.clone(),
                Expr::const_str("_"), // Type erased
                LetValue::Const {
                    name: pseudo_op::NAME_RESET.clone(),
                    levels: vec![],
                    args: vec![Arg::FVar(x)],
                },
            ),
            Box::new(reused_code),
        );

        (reset_code, true)
    } else {
        (code.clone(), false)
    }
}

/// S: Substitute compatible constructor with reuse.
pub(super) fn s_transform(
    w: FVarId,
    n: usize,
    source_ctor: &Name,
    code: &Code,
    cross_family: bool,
    env: Option<&Environment>,
) -> Option<Code> {
    match code {
        Code::Let(decl, body) => {
            // Check if this is a compatible constructor
            if let LetValue::Ctor { name, levels, args } = &decl.value {
                if args.len() == n && is_compatible_ctor(source_ctor, name, cross_family, env) {
                    // Replace with reuse - use LetValue::Reuse for proper ctor metadata
                    // Part of #1104: preserve constructor identity for slow path conversion
                    let new_value = LetValue::Reuse {
                        slot: w,
                        ctor_name: name.clone(),
                        levels: levels.clone(),
                        args: args.clone(),
                    };

                    return Some(Code::Let(
                        LetDecl {
                            fvar_id: decl.fvar_id,
                            name: decl.name.clone(),
                            ty: decl.ty.clone(),
                            value: new_value,
                        },
                        body.clone(),
                    ));
                }
            }

            // Recurse into body
            s_transform(w, n, source_ctor, body, cross_family, env)
                .map(|new_body| Code::Let(decl.clone(), Box::new(new_body)))
        }

        Code::Fun(fun_decl, body) => s_transform(w, n, source_ctor, body, cross_family, env)
            .map(|new_body| Code::Fun(fun_decl.clone(), Box::new(new_body))),

        Code::JoinPoint(jp_decl, body) => {
            // Lean 4: try JP body first, then continuation (ResetReuse.lean:108-113)
            if let Some(new_jp_body) =
                s_transform(w, n, source_ctor, &jp_decl.body, cross_family, env)
            {
                let new_decl = FunDecl {
                    fvar_id: jp_decl.fvar_id,
                    name: jp_decl.name.clone(),
                    params: jp_decl.params.clone(),
                    ty: jp_decl.ty.clone(),
                    body: Box::new(new_jp_body),
                };
                Some(Code::JoinPoint(new_decl, body.clone()))
            } else {
                s_transform(w, n, source_ctor, body, cross_family, env)
                    .map(|new_body| Code::JoinPoint(jp_decl.clone(), Box::new(new_body)))
            }
        }

        // Bug 7 fix: S recurses into case alternatives.
        // (Lean 4: ResetReuse.lean:114-119)
        Code::Cases(cases) => {
            let mut any_changed = false;
            let new_alts: Vec<Alt> = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => {
                        if let Some(new_body) =
                            s_transform(w, n, source_ctor, body, cross_family, env)
                        {
                            any_changed = true;
                            Alt::Ctor {
                                ctor_name: ctor_name.clone(),
                                params: params.clone(),
                                body: Box::new(new_body),
                            }
                        } else {
                            alt.clone()
                        }
                    }
                    Alt::Default(body) => {
                        if let Some(new_body) =
                            s_transform(w, n, source_ctor, body, cross_family, env)
                        {
                            any_changed = true;
                            Alt::Default(Box::new(new_body))
                        } else {
                            alt.clone()
                        }
                    }
                })
                .collect();

            if any_changed {
                Some(Code::Cases(Cases {
                    type_name: cases.type_name.clone(),
                    result_type: cases.result_type.clone(),
                    scrutinee: cases.scrutinee,
                    alts: new_alts,
                }))
            } else {
                None
            }
        }

        // Terminals: no substitution possible
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => None,
    }
}

/// Constructor layout for reuse compatibility comparison.
///
/// Matches Lean 4's `mayReuse` check: two constructors are layout-compatible
/// if they have the same number of object fields and the same scalar storage
/// size. This ensures the reset memory slot has the correct shape for reuse.
#[derive(Debug, PartialEq, Eq)]
struct CtorLayout {
    /// Number of heap-allocated (object/RC) fields.
    num_objects: u32,
    /// Total byte size of all scalar fields.
    scalar_size: u32,
}

/// Extract constructor layout from Environment.
///
/// Uses `strip_pi` to walk the constructor's Pi-type and `expr_to_ir_type`
/// to classify each field as object or scalar. Returns `None` if the
/// constructor is not found in the environment.
fn get_ctor_layout(name: &Name, env: &Environment) -> Option<CtorLayout> {
    let ctor_val = env.get_constructor(name)?;
    let after_params = clean_kernel::inductive::strip_pi(&ctor_val.type_, ctor_val.num_params);
    let mut num_objects: u32 = 0;
    let mut scalar_size: u32 = 0;
    let mut current = after_params;
    for _ in 0..ctor_val.num_fields {
        match current.kind() {
            ExprKind::Pi(_, domain, body) => {
                let ir_type = expr_to_ir_type(domain).ok()?;
                if ir_type.is_scalar() {
                    scalar_size += ir_type.scalar_byte_size();
                } else if ir_type.is_object() {
                    num_objects += 1;
                }
                // Erased/Void fields have no runtime representation
                current = body;
            }
            _ => {
                // Fewer Pi binders than expected — can't determine remaining
                // field types. Break rather than over-counting as Object.
                break;
            }
        }
    }
    Some(CtorLayout {
        num_objects,
        scalar_size,
    })
}

/// Check if two constructors are compatible for reuse.
///
/// Same-name constructors are always compatible. For cross-family reuse,
/// compares actual constructor layouts (num_objects, scalar_size) when
/// Environment is available, matching Lean 4's `mayReuse`. Returns `false`
/// when env is unavailable (conservative — layout info is required for
/// cross-family soundness). Part of #2082.
pub(super) fn is_compatible_ctor(
    source: &Name,
    target: &Name,
    cross_family: bool,
    env: Option<&Environment>,
) -> bool {
    if source == target {
        return true;
    }

    if !cross_family {
        return false;
    }

    // Cross-family: compare actual constructor layouts when env is available.
    // Lean 4 mayReuse: c1.size == c2.size && c1.usize == c2.usize && c1.ssize == c2.ssize
    // Note: scalar_size lumps USize with other scalars (correct on 64-bit;
    // Lean 4 tracks usize separately for 32-bit portability).
    match env {
        Some(env) => match (get_ctor_layout(source, env), get_ctor_layout(target, env)) {
            (Some(src_layout), Some(tgt_layout)) => src_layout == tgt_layout,
            // Constructor not found in env — be conservative.
            _ => false,
        },
        // Without env, cross-family reuse is unsound: name-prefix matching
        // cannot distinguish constructors with different layouts (e.g.,
        // List.cons has 2 fields, List.nil has 0). Conservative: reject.
        // Part of #2082.
        None => false,
    }
}

/// Get the constructor family (type name) from a constructor name.
///
/// No longer used in production after #2082 removed the name-prefix fallback
/// from `is_compatible_ctor`. Retained for test coverage of the helper.
#[cfg(test)]
pub(super) fn get_ctor_family(ctor: &Name) -> String {
    let s = ctor.to_string();
    // Strip the last component (constructor name) to get the type
    if let Some(idx) = s.rfind('.') {
        s[..idx].to_string()
    } else {
        s
    }
}
