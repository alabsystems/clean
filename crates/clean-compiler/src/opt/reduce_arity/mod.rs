// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ReduceArity - Remove top-level function parameters that are always passed
//! the same argument at every call site.
//!
//! Based on Lean 4's `Lean.Compiler.LCNF.ReduceArity`.
//!
//! # Algorithm
//!
//! 1. **Collect used parameters**: Walk the function body, tracking which
//!    parameters are actually referenced. For recursive self-calls, a parameter
//!    that is always passed back as itself (pass-through) is NOT considered used.
//! 2. **Build keep mask**: A `Vec<bool>` where `true` means the parameter at
//!    that index is used and must be kept.
//! 3. **Create auxiliary declaration**: If any parameters are unused, create
//!    `f._redArg` containing the original body with only the used parameters.
//!    Self-recursive calls are rewritten to target `f._redArg`.
//! 4. **Rewrite original declaration**: The original `f` becomes a thin wrapper
//!    that calls `f._redArg` with only the used arguments. This wrapper will
//!    be inlined away in a subsequent simp pass.
//!
//! # Example
//!
//! Before:
//! ```text
//! def f (x y : Nat) : Nat :=
//!   let _1 := Nat.add x x
//!   let _2 := Nat.mul _1 _1
//!   _2
//! ```
//!
//! After:
//! ```text
//! def f._redArg (x : Nat) : Nat :=
//!   let _1 := Nat.add x x
//!   let _2 := Nat.mul _1 _1
//!   _2
//! def f (x y : Nat) : Nat :=
//!   let _3 := f._redArg x
//!   _3
//! ```
//!
//! Part of #1050 - ReduceArity compiler pass.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{FVarId, Name};
use std::collections::HashSet;

/// Collect FVarIds that are "used" in a declaration body.
///
/// A parameter is considered "used" if:
/// - It appears in the body in any non-self-call position, OR
/// - In a self-recursive call, the argument at that position is NOT the
///   parameter itself (i.e., a different value is passed).
///
/// A parameter is "unused" only if it never appears except as a pass-through
/// in self-recursive calls.
fn collect_used_params(decl_name: &Name, params: &[Param], code: &Code) -> HashSet<FVarId> {
    let param_set: HashSet<FVarId> = params.iter().map(|p| p.fvar_id).collect();
    let mut used = HashSet::new();

    visit_code_for_used(decl_name, params, &param_set, code, &mut used);
    used
}

/// Mark an FVarId as used if it is one of the declaration's parameters.
fn mark_if_param(fvar: FVarId, param_set: &HashSet<FVarId>, used: &mut HashSet<FVarId>) {
    if param_set.contains(&fvar) {
        used.insert(fvar);
    }
}

/// Mark FVarIds referenced in an Arg as used (if they are parameters).
fn mark_arg(arg: &Arg, param_set: &HashSet<FVarId>, used: &mut HashSet<FVarId>) {
    if let Arg::FVar(id) = arg {
        mark_if_param(*id, param_set, used);
    }
}

/// Visit a LetValue, collecting used parameter references.
///
/// Special-cases self-recursive calls: when the callee is the declaration
/// itself, a parameter passed at its own position is a pass-through and
/// does NOT count as a use. Any non-matching argument or over/under-
/// application arguments are counted normally.
fn visit_let_value(
    decl_name: &Name,
    params: &[Param],
    param_set: &HashSet<FVarId>,
    value: &LetValue,
    used: &mut HashSet<FVarId>,
) {
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => {
            mark_if_param(*structure, param_set, used);
        }
        LetValue::Const { name, args, .. } if name == decl_name => {
            // Self-recursive call: skip pass-through arguments.
            for (i, arg) in args.iter().enumerate() {
                if let Arg::FVar(fvar) = arg {
                    if i < params.len() && *fvar == params[i].fvar_id {
                        // Pass-through: same param at same position, skip.
                        continue;
                    }
                }
                mark_arg(arg, param_set, used);
            }
            // Over-application: args beyond param count always count.
            // (Already handled by the loop above since i >= params.len().)
            // Partial application: missing params are considered used.
            for param in params.iter().skip(args.len()) {
                used.insert(param.fvar_id);
            }
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                mark_arg(arg, param_set, used);
            }
        }
        LetValue::FVar { fvar, args } => {
            mark_if_param(*fvar, param_set, used);
            for arg in args {
                mark_arg(arg, param_set, used);
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            mark_if_param(*slot, param_set, used);
            for arg in args {
                mark_arg(arg, param_set, used);
            }
        }
    }
}

/// Recursively walk a Code tree, collecting used-parameter references.
fn visit_code_for_used(
    decl_name: &Name,
    params: &[Param],
    param_set: &HashSet<FVarId>,
    code: &Code,
    used: &mut HashSet<FVarId>,
) {
    match code {
        Code::Let(decl, body) => {
            visit_let_value(decl_name, params, param_set, &decl.value, used);
            visit_code_for_used(decl_name, params, param_set, body, used);
        }
        Code::Fun(fdecl, body) | Code::JoinPoint(fdecl, body) => {
            visit_code_for_used(decl_name, params, param_set, &fdecl.body, used);
            visit_code_for_used(decl_name, params, param_set, body, used);
        }
        Code::Cases(cases) => {
            mark_if_param(cases.scrutinee, param_set, used);
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => {
                        visit_code_for_used(decl_name, params, param_set, body, used);
                    }
                    Alt::Default(body) => {
                        visit_code_for_used(decl_name, params, param_set, body, used);
                    }
                }
            }
        }
        Code::Jmp { jp, args } => {
            mark_if_param(*jp, param_set, used);
            for arg in args {
                mark_arg(arg, param_set, used);
            }
        }
        Code::Return(fvar) => {
            mark_if_param(*fvar, param_set, used);
        }
        Code::Unreachable(_) => {}
    }
}

/// Rewrite self-recursive calls inside the auxiliary body to target
/// `aux_name` with only the kept arguments.
fn rewrite_self_calls(decl_name: &Name, aux_name: &Name, mask: &[bool], code: &Code) -> Code {
    match code {
        Code::Let(decl, body) => {
            let new_value = rewrite_let_value(decl_name, aux_name, mask, &decl.value);
            let new_decl = LetDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                ty: decl.ty.clone(),
                value: new_value,
            };
            Code::Let(
                new_decl,
                Box::new(rewrite_self_calls(decl_name, aux_name, mask, body)),
            )
        }
        Code::Fun(fdecl, body) => {
            let new_fbody = rewrite_self_calls(decl_name, aux_name, mask, &fdecl.body);
            let new_fdecl = FunDecl {
                fvar_id: fdecl.fvar_id,
                name: fdecl.name.clone(),
                params: fdecl.params.clone(),
                ty: fdecl.ty.clone(),
                body: Box::new(new_fbody),
            };
            Code::Fun(
                new_fdecl,
                Box::new(rewrite_self_calls(decl_name, aux_name, mask, body)),
            )
        }
        Code::JoinPoint(fdecl, body) => {
            let new_fbody = rewrite_self_calls(decl_name, aux_name, mask, &fdecl.body);
            let new_fdecl = FunDecl {
                fvar_id: fdecl.fvar_id,
                name: fdecl.name.clone(),
                params: fdecl.params.clone(),
                ty: fdecl.ty.clone(),
                body: Box::new(new_fbody),
            };
            Code::JoinPoint(
                new_fdecl,
                Box::new(rewrite_self_calls(decl_name, aux_name, mask, body)),
            )
        }
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
                        body: Box::new(rewrite_self_calls(decl_name, aux_name, mask, body)),
                    },
                    Alt::Default(body) => Alt::Default(Box::new(rewrite_self_calls(
                        decl_name, aux_name, mask, body,
                    ))),
                })
                .collect();
            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => code.clone(),
    }
}

/// Rewrite a LetValue, changing self-calls to target the auxiliary declaration
/// with only the kept arguments.
fn rewrite_let_value(
    decl_name: &Name,
    aux_name: &Name,
    mask: &[bool],
    value: &LetValue,
) -> LetValue {
    match value {
        LetValue::Const { name, levels, args } if name == decl_name => {
            let filtered_args = filter_args_by_mask(args, mask);
            LetValue::Const {
                name: aux_name.clone(),
                levels: levels.clone(),
                args: filtered_args,
            }
        }
        _ => value.clone(),
    }
}

/// Filter arguments according to a keep mask.
///
/// Keeps arguments at positions where `mask[i]` is true.
/// Arguments beyond the mask length are always kept (over-application).
fn filter_args_by_mask(args: &[Arg], mask: &[bool]) -> Vec<Arg> {
    args.iter()
        .enumerate()
        .filter(|(i, _)| mask.get(*i).copied().unwrap_or(true))
        .map(|(_, a)| a.clone())
        .collect()
}

/// Filter parameters according to a keep mask.
fn filter_params_by_mask(params: &[Param], mask: &[bool]) -> Vec<Param> {
    params
        .iter()
        .zip(mask.iter())
        .filter(|(_, &keep)| keep)
        .map(|(p, _)| p.clone())
        .collect()
}

/// Reduce arity of a single top-level declaration.
///
/// If some parameters are never used (except as pass-throughs in self-calls),
/// produces two declarations:
/// 1. `f._redArg` — the auxiliary with only used parameters
/// 2. `f` — a thin wrapper that calls `f._redArg`
///
/// If all parameters are used (or the decl is extern), returns the original
/// declaration unchanged.
pub fn reduce_arity(decl: &Decl) -> Vec<Decl> {
    let code = match &decl.body {
        DeclValue::Code(code) => code,
        DeclValue::Extern(_) => return vec![decl.clone()],
    };

    if decl.params.is_empty() {
        return vec![decl.clone()];
    }

    let used = collect_used_params(&decl.name, &decl.params, code);

    // If all params are used, or NO params are used, do nothing.
    // (Zero used would promote to a constant, which could execute unreachable code.)
    if used.len() == decl.params.len() || used.is_empty() {
        return vec![decl.clone()];
    }

    let mask: Vec<bool> = decl
        .params
        .iter()
        .map(|p| used.contains(&p.fvar_id))
        .collect();

    let aux_name = decl.name.clone().str("_redArg");

    // Build the auxiliary declaration (with only used params, body rewritten).
    let aux_params = filter_params_by_mask(&decl.params, &mask);
    let aux_body = rewrite_self_calls(&decl.name, &aux_name, &mask, code);
    let aux_decl = Decl {
        name: aux_name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: aux_params,
        body: DeclValue::Code(Box::new(aux_body)),
        recursive: decl.recursive,
    };

    let wrapper_decl = build_wrapper_decl(decl, &aux_name, &mask);
    vec![aux_decl, wrapper_decl]
}

/// Build a thin wrapper declaration that forwards only the kept arguments
/// to the auxiliary `aux_name` function.
///
/// The wrapper preserves the original function signature so callers do not
/// need to be rewritten. A subsequent inlining/simp pass will eliminate it.
fn build_wrapper_decl(decl: &Decl, aux_name: &Name, mask: &[bool]) -> Decl {
    let wrapper_args: Vec<Arg> = decl
        .params
        .iter()
        .zip(mask.iter())
        .filter(|(_, &keep)| keep)
        .map(|(p, _)| Arg::FVar(p.fvar_id))
        .collect();

    let result_fvar = FVarId::new(
        decl.params
            .iter()
            .map(|p| p.fvar_id.as_u64())
            .max()
            .unwrap_or(0)
            + 1000,
    );

    let let_decl = LetDecl::new(
        result_fvar,
        Name::from_string("_redArg_result"),
        decl.ty.clone(),
        LetValue::Const {
            name: aux_name.clone(),
            levels: Vec::new(),
            args: wrapper_args,
        },
    );
    let wrapper_body = Code::Let(let_decl, Box::new(Code::Return(result_fvar)));
    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body: DeclValue::Code(Box::new(wrapper_body)),
        recursive: false,
    }
}

/// Reduce arity across a batch of declarations.
///
/// Processes each declaration independently, returning the expanded list
/// (original declarations may be replaced by aux + wrapper pairs).
pub fn reduce_arity_all(decls: &[Decl]) -> Vec<Decl> {
    decls.iter().flat_map(reduce_arity).collect()
}

#[cfg(test)]
mod tests;
