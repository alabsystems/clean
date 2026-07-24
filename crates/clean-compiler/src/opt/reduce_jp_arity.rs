// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ReduceJpArity - Remove unused join point parameters
//!
//! If a join point parameter is never referenced in the body, both the
//! parameter and the corresponding argument at every `Jmp` site can be
//! removed. This reduces closure size and avoids passing dead values
//! through the control-flow graph.
//!
//! Based on Lean 4's `Lean.Compiler.LCNF.ReduceJpArity`.
//!
//! # Algorithm
//!
//! 1. Collect all FVarIds referenced in the join point body (free variables).
//! 2. For each parameter, check if its FVarId appears in the collected set.
//! 3. Build a mask of which parameter positions to keep.
//! 4. Rewrite the join point with only the kept parameters.
//! 5. Rewrite every `Jmp` targeting this join point, removing arguments
//!    at positions that were eliminated.
//!
//! The pass recurses into the entire Code tree, processing each
//! `JoinPoint` from the inside out.
//!
//! # Example
//!
//! Before:
//! ```text
//! jp loop (x : Nat) (unused : Nat) (y : Nat) : Nat :=
//!   let _1 := Nat.add x y
//!   return _1
//! cases n of
//!   | zero => jmp loop 0 99 1
//!   | succ k => jmp loop k 99 2
//! ```
//!
//! After:
//! ```text
//! jp loop (x : Nat) (y : Nat) : Nat :=
//!   let _1 := Nat.add x y
//!   return _1
//! cases n of
//!   | zero => jmp loop 0 1
//!   | succ k => jmp loop k 2
//! ```
//!
//! Part of #1088 - ReduceJpArity compiler pass.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetValue, Param};
use clean_kernel::FVarId;
use std::collections::{HashMap, HashSet};

/// Collect all FVarIds referenced in a Code tree.
///
/// This walks the entire code block and records every FVarId that appears
/// in any position (arguments, scrutinees, return values, let-value
/// references, jump targets, etc.).
fn collect_used_fvars(code: &Code, used: &mut HashSet<FVarId>) {
    match code {
        Code::Let(decl, body) => {
            collect_used_fvars_in_let_value(&decl.value, used);
            collect_used_fvars(body, used);
        }
        Code::Fun(fdecl, body) | Code::JoinPoint(fdecl, body) => {
            collect_used_fvars(&fdecl.body, used);
            collect_used_fvars(body, used);
        }
        Code::Cases(cases) => {
            used.insert(cases.scrutinee);
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => collect_used_fvars(body, used),
                    Alt::Default(body) => collect_used_fvars(body, used),
                }
            }
        }
        Code::Jmp { jp, args } => {
            used.insert(*jp);
            for arg in args {
                if let Arg::FVar(id) = arg {
                    used.insert(*id);
                }
            }
        }
        Code::Return(fvar) => {
            used.insert(*fvar);
        }
        Code::Unreachable(_) => {}
    }
}

/// Collect FVarIds referenced in a LetValue.
fn collect_used_fvars_in_let_value(value: &LetValue, used: &mut HashSet<FVarId>) {
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => {
            used.insert(*structure);
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                if let Arg::FVar(id) = arg {
                    used.insert(*id);
                }
            }
        }
        LetValue::FVar { fvar, args } => {
            used.insert(*fvar);
            for arg in args {
                if let Arg::FVar(id) = arg {
                    used.insert(*id);
                }
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            used.insert(*slot);
            for arg in args {
                if let Arg::FVar(id) = arg {
                    used.insert(*id);
                }
            }
        }
    }
}

/// Compute which parameters of a join point are actually used in its body.
///
/// Returns a bitmask (Vec<bool>) where `true` means the parameter at that
/// index is used and should be kept.
fn compute_keep_mask(params: &[Param], body: &Code) -> Vec<bool> {
    let mut used = HashSet::new();
    collect_used_fvars(body, &mut used);
    params.iter().map(|p| used.contains(&p.fvar_id)).collect()
}

/// Filter parameters according to a keep mask.
fn filter_params(params: &[Param], mask: &[bool]) -> Vec<Param> {
    params
        .iter()
        .zip(mask.iter())
        .filter(|(_, &keep)| keep)
        .map(|(p, _)| p.clone())
        .collect()
}

/// Filter arguments according to a keep mask.
fn filter_args(args: &[Arg], mask: &[bool]) -> Vec<Arg> {
    args.iter()
        .zip(mask.iter())
        .filter(|(_, &keep)| keep)
        .map(|(a, _)| a.clone())
        .collect()
}

/// Reduce join point arity in a Code block.
///
/// Processes the tree bottom-up: inner join points are reduced before
/// outer ones. For each `JoinPoint`, computes the keep mask, rewrites
/// the declaration, then rewrites all `Jmp` sites in the continuation.
pub fn reduce_jp_arity_in_code(code: &Code) -> Code {
    // First pass: recursively process all sub-expressions.
    // Then handle JoinPoint nodes at this level.
    reduce_impl(code, &HashMap::new())
}

/// Internal recursive implementation.
///
/// `masks` maps join point FVarIds to their keep masks. When we enter
/// a JoinPoint scope we add its mask so that Jmp sites deeper in the
/// continuation can be rewritten.
/// Reduce a single JoinPoint node: compute keep mask, rewrite decl, recurse continuation.
fn reduce_join_point(fdecl: &FunDecl, body: &Code, masks: &HashMap<FVarId, Vec<bool>>) -> Code {
    let processed_jp_body = reduce_impl(&fdecl.body, masks);
    let mask = compute_keep_mask(&fdecl.params, &processed_jp_body);
    let all_used = mask.iter().all(|&k| k);

    let (new_fdecl, new_masks) = if all_used {
        let new_fdecl = FunDecl {
            fvar_id: fdecl.fvar_id,
            name: fdecl.name.clone(),
            params: fdecl.params.clone(),
            ty: fdecl.ty.clone(),
            body: Box::new(processed_jp_body),
        };
        (new_fdecl, masks.clone())
    } else {
        let new_params = filter_params(&fdecl.params, &mask);
        let new_fdecl = FunDecl {
            fvar_id: fdecl.fvar_id,
            name: fdecl.name.clone(),
            params: new_params,
            ty: fdecl.ty.clone(),
            body: Box::new(processed_jp_body),
        };
        let mut new_masks = masks.clone();
        new_masks.insert(fdecl.fvar_id, mask);
        (new_fdecl, new_masks)
    };

    let new_body = reduce_impl(body, &new_masks);
    Code::JoinPoint(new_fdecl, Box::new(new_body))
}

fn reduce_impl(code: &Code, masks: &HashMap<FVarId, Vec<bool>>) -> Code {
    match code {
        Code::Let(decl, body) => Code::Let(decl.clone(), Box::new(reduce_impl(body, masks))),
        Code::Fun(fdecl, body) => {
            let new_fun_body = reduce_impl(&fdecl.body, masks);
            let new_fdecl = FunDecl {
                fvar_id: fdecl.fvar_id,
                name: fdecl.name.clone(),
                params: fdecl.params.clone(),
                ty: fdecl.ty.clone(),
                body: Box::new(new_fun_body),
            };
            Code::Fun(new_fdecl, Box::new(reduce_impl(body, masks)))
        }
        Code::JoinPoint(fdecl, body) => reduce_join_point(fdecl, body, masks),
        Code::Cases(cases) => {
            let new_alts = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => Alt::Ctor {
                        ctor_name: ctor_name.clone(),
                        params: params.clone(),
                        body: Box::new(reduce_impl(body, masks)),
                    },
                    Alt::Default(body) => Alt::Default(Box::new(reduce_impl(body, masks))),
                })
                .collect();
            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }
        Code::Jmp { jp, args } => {
            if let Some(mask) = masks.get(jp) {
                Code::Jmp {
                    jp: *jp,
                    args: filter_args(args, mask),
                }
            } else {
                code.clone()
            }
        }
        Code::Return(_) | Code::Unreachable(_) => code.clone(),
    }
}

/// Reduce join point arity in a top-level declaration.
pub fn reduce_jp_arity(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(reduce_jp_arity_in_code(code))),
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body: new_body,
        recursive: decl.recursive,
    }
}
