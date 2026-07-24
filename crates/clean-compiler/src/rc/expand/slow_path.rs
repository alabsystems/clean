// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Slow-path reuse lowering for reset/reuse expansion.

use super::is_reuse_op;
use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue};
use crate::rc::pseudo_op;

/// Convert a reuse LetValue to its constructor equivalent (slow path).
fn reuse_value_to_ctor(value: &LetValue) -> LetValue {
    match value {
        LetValue::Const { args, levels, .. } => {
            let remaining_args: Vec<Arg> = args.iter().skip(1).cloned().collect();
            LetValue::Ctor {
                name: pseudo_op::NAME_CTOR.clone(),
                levels: levels.clone(),
                args: remaining_args,
            }
        }
        LetValue::Reuse {
            ctor_name,
            levels,
            args,
            ..
        } => LetValue::Ctor {
            name: ctor_name.clone(),
            levels: levels.clone(),
            args: args.clone(),
        },
        _ => value.clone(),
    }
}

/// Rewrite reuse operations to constructor calls (slow path).
pub(crate) fn rewrite_reuse_to_ctor(code: &Code) -> Code {
    match code {
        Code::Let(decl, body) => {
            let new_value = if is_reuse_op(&decl.value) {
                reuse_value_to_ctor(&decl.value)
            } else {
                decl.value.clone()
            };

            Code::Let(
                LetDecl {
                    fvar_id: decl.fvar_id,
                    name: decl.name.clone(),
                    ty: decl.ty.clone(),
                    value: new_value,
                },
                Box::new(rewrite_reuse_to_ctor(body)),
            )
        }
        Code::Fun(fun_decl, body) => {
            let new_fun_body = rewrite_reuse_to_ctor(&fun_decl.body);
            Code::Fun(
                FunDecl {
                    body: Box::new(new_fun_body),
                    ..fun_decl.clone()
                },
                Box::new(rewrite_reuse_to_ctor(body)),
            )
        }
        Code::JoinPoint(jp_decl, body) => {
            let new_jp_body = rewrite_reuse_to_ctor(&jp_decl.body);
            Code::JoinPoint(
                FunDecl {
                    body: Box::new(new_jp_body),
                    ..jp_decl.clone()
                },
                Box::new(rewrite_reuse_to_ctor(body)),
            )
        }
        Code::Cases(cases) => {
            let new_alts: Vec<Alt> = cases
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
                        body: Box::new(rewrite_reuse_to_ctor(body)),
                    },
                    Alt::Default(body) => Alt::Default(Box::new(rewrite_reuse_to_ctor(body))),
                })
                .collect();

            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }
        Code::Jmp { jp, args } => Code::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        Code::Return(fvar) => Code::Return(*fvar),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}
