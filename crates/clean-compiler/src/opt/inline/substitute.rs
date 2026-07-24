// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Substitution and splicing logic for function inlining.
//!
//! Handles replacing FVarIds in code after inlining a function call,
//! and splicing the inlined code into the continuation.

use super::{InlineContext, MAX_INLINE_STACK_DEPTH};
use crate::code_visitor::CodeFolder;
use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::FVarId;
use std::collections::HashMap;

/// Inline a function call by substituting arguments for parameters.
pub(super) fn inline_call(ctx: &mut InlineContext, fun: &FunDecl, args: &[Arg]) -> Code {
    // Build parameter -> argument substitution
    let mut subst = HashMap::new();

    for (param, arg) in fun.params.iter().zip(args.iter()) {
        if let Arg::FVar(arg_fvar) = arg {
            subst.insert(param.fvar_id, *arg_fvar);
        }
        // For Erased and Type args, we don't substitute
    }

    // Substitute in the function body
    substitute_code_with_depth(ctx, &fun.body, &subst, 0)
}

/// Substitute FVarIds in code according to a mapping.
///
/// Uses depth tracking to prevent stack overflow on deeply nested code.
fn substitute_code_with_depth(
    ctx: &mut InlineContext,
    code: &Code,
    subst: &HashMap<FVarId, FVarId>,
    depth: usize,
) -> Code {
    // Stack protection: return code unchanged if too deep
    if depth > MAX_INLINE_STACK_DEPTH {
        return code.clone();
    }
    match code {
        Code::Let(decl, body) => {
            // Create fresh FVarId for this binding
            let new_fvar = ctx.fresh_fvar();
            let mut new_subst = subst.clone();
            new_subst.insert(decl.fvar_id, new_fvar);

            let new_value = substitute_let_value(&decl.value, subst);
            let new_decl = LetDecl {
                fvar_id: new_fvar,
                name: decl.name.clone(),
                ty: decl.ty.clone(),
                value: new_value,
            };

            Code::Let(
                new_decl,
                Box::new(substitute_code_with_depth(ctx, body, &new_subst, depth + 1)),
            )
        }

        Code::Fun(fun_decl, body) => {
            let new_fvar = ctx.fresh_fvar();
            let mut new_subst = subst.clone();
            new_subst.insert(fun_decl.fvar_id, new_fvar);

            // Also create fresh FVarIds for parameters
            let mut param_subst = new_subst.clone();
            let new_params: Vec<Param> = fun_decl
                .params
                .iter()
                .map(|p| {
                    let new_param_fvar = ctx.fresh_fvar();
                    param_subst.insert(p.fvar_id, new_param_fvar);
                    Param {
                        fvar_id: new_param_fvar,
                        name: p.name.clone(),
                        ty: p.ty.clone(),
                        borrow: p.borrow,
                    }
                })
                .collect();

            let new_fun_body =
                substitute_code_with_depth(ctx, &fun_decl.body, &param_subst, depth + 1);
            let new_decl = FunDecl {
                fvar_id: new_fvar,
                name: fun_decl.name.clone(),
                params: new_params,
                ty: fun_decl.ty.clone(),
                body: Box::new(new_fun_body),
            };

            Code::Fun(
                new_decl,
                Box::new(substitute_code_with_depth(ctx, body, &new_subst, depth + 1)),
            )
        }

        Code::JoinPoint(jp_decl, body) => {
            let new_fvar = ctx.fresh_fvar();
            let mut new_subst = subst.clone();
            new_subst.insert(jp_decl.fvar_id, new_fvar);

            let mut param_subst = new_subst.clone();
            let new_params: Vec<Param> = jp_decl
                .params
                .iter()
                .map(|p| {
                    let new_param_fvar = ctx.fresh_fvar();
                    param_subst.insert(p.fvar_id, new_param_fvar);
                    Param {
                        fvar_id: new_param_fvar,
                        name: p.name.clone(),
                        ty: p.ty.clone(),
                        borrow: p.borrow,
                    }
                })
                .collect();

            let new_jp_body =
                substitute_code_with_depth(ctx, &jp_decl.body, &param_subst, depth + 1);
            let new_decl = FunDecl {
                fvar_id: new_fvar,
                name: jp_decl.name.clone(),
                params: new_params,
                ty: jp_decl.ty.clone(),
                body: Box::new(new_jp_body),
            };

            Code::JoinPoint(
                new_decl,
                Box::new(substitute_code_with_depth(ctx, body, &new_subst, depth + 1)),
            )
        }

        Code::Cases(cases) => {
            let new_scrutinee = subst
                .get(&cases.scrutinee)
                .copied()
                .unwrap_or(cases.scrutinee);
            let depth_for_alts = depth + 1;
            let new_alts = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => {
                        // Create fresh FVarIds for pattern variables
                        let mut alt_subst = subst.clone();
                        let new_params: Vec<Param> = params
                            .iter()
                            .map(|p| {
                                let new_param_fvar = ctx.fresh_fvar();
                                alt_subst.insert(p.fvar_id, new_param_fvar);
                                Param {
                                    fvar_id: new_param_fvar,
                                    name: p.name.clone(),
                                    ty: p.ty.clone(),
                                    borrow: p.borrow,
                                }
                            })
                            .collect();

                        Alt::Ctor {
                            ctor_name: ctor_name.clone(),
                            params: new_params,
                            body: Box::new(substitute_code_with_depth(
                                ctx,
                                body,
                                &alt_subst,
                                depth_for_alts,
                            )),
                        }
                    }
                    Alt::Default(body) => Alt::Default(Box::new(substitute_code_with_depth(
                        ctx,
                        body,
                        subst,
                        depth_for_alts,
                    ))),
                })
                .collect();

            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: new_scrutinee,
                alts: new_alts,
            })
        }

        Code::Jmp { jp, args } => {
            let new_jp = subst.get(jp).copied().unwrap_or(*jp);
            let new_args = args.iter().map(|a| substitute_arg(a, subst)).collect();
            Code::Jmp {
                jp: new_jp,
                args: new_args,
            }
        }

        Code::Return(fvar) => {
            let new_fvar = subst.get(fvar).copied().unwrap_or(*fvar);
            // We return the value directly - the splice will handle binding
            Code::Return(new_fvar)
        }

        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

/// Substitute FVarIds in a let-value.
fn substitute_let_value(value: &LetValue, subst: &HashMap<FVarId, FVarId>) -> LetValue {
    match value {
        LetValue::Lit(lit) => LetValue::Lit(lit.clone()),
        LetValue::Erased => LetValue::Erased,
        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => LetValue::Proj {
            type_name: type_name.clone(),
            idx: *idx,
            structure: subst.get(structure).copied().unwrap_or(*structure),
        },
        LetValue::Const { name, levels, args } => LetValue::Const {
            name: name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| substitute_arg(a, subst)).collect(),
        },
        LetValue::FVar { fvar, args } => LetValue::FVar {
            fvar: subst.get(fvar).copied().unwrap_or(*fvar),
            args: args.iter().map(|a| substitute_arg(a, subst)).collect(),
        },
        LetValue::Ctor { name, levels, args } => LetValue::Ctor {
            name: name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| substitute_arg(a, subst)).collect(),
        },
        LetValue::Reuse {
            slot,
            ctor_name,
            levels,
            args,
        } => LetValue::Reuse {
            slot: subst.get(slot).copied().unwrap_or(*slot),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| substitute_arg(a, subst)).collect(),
        },
    }
}

/// Substitute FVarIds in an argument.
fn substitute_arg(arg: &Arg, subst: &HashMap<FVarId, FVarId>) -> Arg {
    match arg {
        Arg::FVar(fvar) => Arg::FVar(subst.get(fvar).copied().unwrap_or(*fvar)),
        Arg::Erased => Arg::Erased,
        Arg::Type(ty) => Arg::Type(ty.clone()),
        Arg::Index(idx) => Arg::Index(*idx),
    }
}

/// CodeFolder that replaces `return x` with `let result := x; continuation`.
///
/// Only overrides `fold_return`; all other Code variants use the default
/// structural recursion from `CodeFolder`.
struct SpliceFolder {
    result_var: FVarId,
    continuation: Code,
}

impl CodeFolder for SpliceFolder {
    fn fold_return(&mut self, fvar: FVarId) -> Code {
        Code::Let(
            LetDecl {
                fvar_id: self.result_var,
                name: clean_kernel::Name::anon(),
                ty: clean_kernel::Expr::const_str("_"),
                value: LetValue::FVar { fvar, args: vec![] },
            },
            Box::new(self.continuation.clone()),
        )
    }
}

/// Splice inlined code: replace `return x` with `let result := x; continuation`.
pub(super) fn splice_code(inlined: Code, result_var: FVarId, continuation: Code) -> Code {
    let mut folder = SpliceFolder {
        result_var,
        continuation,
    };
    folder.fold_code(&inlined)
}
