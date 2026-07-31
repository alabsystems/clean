// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core recursive traversal for the specialization pass.
//!
//! Contains `specialize_code` (single-decl) and `specialize_code_with_index`
//! (batch with declaration index), plus the `is_code_ground` analysis helper.

use super::candidate::{try_specialize_value, try_specialize_value_with_index};
use super::context::{SpecContext, SpecState};
use super::{DeclIndex, SpecConfig};
use crate::lcnf::{Alt, Cases, Code, FunDecl, LetDecl, LetValue};
use clean_kernel::FVarId;
use std::collections::HashMap;

/// Core specialization logic.
pub(crate) fn specialize_code(
    ctx: &mut SpecContext,
    state: &mut SpecState,
    code: &Code,
    config: &SpecConfig,
) -> Code {
    match code {
        Code::Let(decl, body) => {
            // Build bindings reference for ground value extraction
            let bindings_ref: HashMap<FVarId, &LetValue> =
                ctx.bindings.iter().map(|(k, v)| (*k, v)).collect();

            // Check if this let-binding is a specialization candidate
            let new_value = try_specialize_value(ctx, state, &decl.value, config, &bindings_ref);

            // Track this binding as ground if applicable
            let new_decl = LetDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                ty: decl.ty.clone(),
                value: new_value,
            };

            // Drain local specializations generated for this call site
            let local_specs: Vec<FunDecl> = state.pending_local_specs.drain(..).collect();
            for spec in &local_specs {
                ctx.scope.insert(spec.fvar_id);
                ctx.local_funs.insert(spec.fvar_id, spec.clone());
            }

            ctx.with_let_decl(&new_decl);

            let new_body = specialize_code(ctx, state, body, config);

            // Wrap result with specialized local function definitions
            let mut result = Code::Let(new_decl, Box::new(new_body));
            for spec_fun in local_specs.into_iter().rev() {
                result = Code::Fun(spec_fun, Box::new(result));
            }
            result
        }

        Code::Fun(fun_decl, body) => {
            // Save context, process function body
            let saved_scope = ctx.scope.clone();
            let saved_ground = ctx.ground.clone();

            // Add function params to scope (not ground)
            for param in &fun_decl.params {
                ctx.scope.insert(param.fvar_id);
            }

            let new_fun_body = specialize_code(ctx, state, &fun_decl.body, config);

            // Restore context
            ctx.scope = saved_scope;
            ctx.ground = saved_ground;

            // Add function to scope
            ctx.scope.insert(fun_decl.fvar_id);
            // Local functions are ground if their free vars are ground
            let is_ground = is_code_ground(ctx, &new_fun_body);
            if is_ground {
                ctx.ground.insert(fun_decl.fvar_id);
            }

            let new_fun_decl = FunDecl {
                fvar_id: fun_decl.fvar_id,
                name: fun_decl.name.clone(),
                params: fun_decl.params.clone(),
                ty: fun_decl.ty.clone(),
                body: Box::new(new_fun_body),
            };

            // Track local function definition for FVar specialization
            ctx.local_funs
                .insert(fun_decl.fvar_id, new_fun_decl.clone());

            let new_body = specialize_code(ctx, state, body, config);
            Code::Fun(new_fun_decl, Box::new(new_body))
        }

        Code::JoinPoint(jp_decl, body) => {
            // Similar to Fun - save/restore context, track groundness
            let saved_scope = ctx.scope.clone();
            let saved_ground = ctx.ground.clone();

            for param in &jp_decl.params {
                ctx.scope.insert(param.fvar_id);
            }

            let new_jp_body = specialize_code(ctx, state, &jp_decl.body, config);

            ctx.scope = saved_scope;
            ctx.ground = saved_ground;

            // Add join point to scope and check if it's ground
            ctx.scope.insert(jp_decl.fvar_id);
            let is_ground = is_code_ground(ctx, &new_jp_body);
            if is_ground {
                ctx.ground.insert(jp_decl.fvar_id);
            }

            let new_jp_decl = FunDecl {
                fvar_id: jp_decl.fvar_id,
                name: jp_decl.name.clone(),
                params: jp_decl.params.clone(),
                ty: jp_decl.ty.clone(),
                body: Box::new(new_jp_body),
            };

            let new_body = specialize_code(ctx, state, body, config);
            Code::JoinPoint(new_jp_decl, Box::new(new_body))
        }

        Code::Cases(cases) => {
            let saved_scope = ctx.scope.clone();
            let saved_ground = ctx.ground.clone();

            let new_alts = cases
                .alts
                .iter()
                .map(|alt| {
                    // Restore context for each alternative
                    ctx.scope = saved_scope.clone();
                    ctx.ground = saved_ground.clone();

                    match alt {
                        Alt::Ctor {
                            ctor_name,
                            params,
                            body,
                        } => {
                            // Add constructor params to scope (not ground)
                            for param in params {
                                ctx.scope.insert(param.fvar_id);
                            }
                            Alt::Ctor {
                                ctor_name: ctor_name.clone(),
                                params: params.clone(),
                                body: Box::new(specialize_code(ctx, state, body, config)),
                            }
                        }
                        Alt::Default(body) => {
                            Alt::Default(Box::new(specialize_code(ctx, state, body, config)))
                        }
                    }
                })
                .collect();

            // Restore context
            ctx.scope = saved_scope;
            ctx.ground = saved_ground;

            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                scrutinee: cases.scrutinee,
                result_type: cases.result_type.clone(),
                alts: new_alts,
            })
        }

        // Terminals - unchanged
        Code::Jmp { jp, args } => Code::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        Code::Return(fvar) => Code::Return(*fvar),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

/// Core specialization logic with declaration index for generating specialized decls.
pub(crate) fn specialize_code_with_index(
    ctx: &mut SpecContext,
    state: &mut SpecState,
    code: &Code,
    config: &SpecConfig,
    decl_index: &DeclIndex<'_>,
) -> Code {
    match code {
        Code::Let(decl, body) => {
            let bindings_ref: HashMap<FVarId, &LetValue> =
                ctx.bindings.iter().map(|(k, v)| (*k, v)).collect();

            let new_value = try_specialize_value_with_index(
                ctx,
                state,
                &decl.value,
                config,
                &bindings_ref,
                decl_index,
            );

            let new_decl = LetDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                ty: decl.ty.clone(),
                value: new_value,
            };

            // Drain local specializations generated for this call site
            let local_specs: Vec<FunDecl> = state.pending_local_specs.drain(..).collect();
            for spec in &local_specs {
                ctx.scope.insert(spec.fvar_id);
                ctx.local_funs.insert(spec.fvar_id, spec.clone());
            }

            ctx.with_let_decl(&new_decl);
            let new_body = specialize_code_with_index(ctx, state, body, config, decl_index);

            // Wrap result with specialized local function definitions
            let mut result = Code::Let(new_decl, Box::new(new_body));
            for spec_fun in local_specs.into_iter().rev() {
                result = Code::Fun(spec_fun, Box::new(result));
            }
            result
        }

        Code::Fun(fun_decl, body) => {
            let saved_scope = ctx.scope.clone();
            let saved_ground = ctx.ground.clone();

            for param in &fun_decl.params {
                ctx.scope.insert(param.fvar_id);
            }
            let new_fun_body =
                specialize_code_with_index(ctx, state, &fun_decl.body, config, decl_index);

            ctx.scope = saved_scope;
            ctx.ground = saved_ground;

            ctx.scope.insert(fun_decl.fvar_id);
            let is_ground = is_code_ground(ctx, &new_fun_body);
            if is_ground {
                ctx.ground.insert(fun_decl.fvar_id);
            }

            let new_fun_decl = FunDecl {
                fvar_id: fun_decl.fvar_id,
                name: fun_decl.name.clone(),
                params: fun_decl.params.clone(),
                ty: fun_decl.ty.clone(),
                body: Box::new(new_fun_body),
            };

            // Track local function definition for FVar specialization
            ctx.local_funs
                .insert(fun_decl.fvar_id, new_fun_decl.clone());

            let new_body = specialize_code_with_index(ctx, state, body, config, decl_index);
            Code::Fun(new_fun_decl, Box::new(new_body))
        }

        Code::JoinPoint(jp_decl, body) => {
            let saved_scope = ctx.scope.clone();
            let saved_ground = ctx.ground.clone();

            for param in &jp_decl.params {
                ctx.scope.insert(param.fvar_id);
            }
            let new_jp_body =
                specialize_code_with_index(ctx, state, &jp_decl.body, config, decl_index);

            ctx.scope = saved_scope;
            ctx.ground = saved_ground;

            // Add join point to scope and track groundness
            ctx.scope.insert(jp_decl.fvar_id);
            let is_ground = is_code_ground(ctx, &new_jp_body);
            if is_ground {
                ctx.ground.insert(jp_decl.fvar_id);
            }

            let new_jp_decl = FunDecl {
                fvar_id: jp_decl.fvar_id,
                name: jp_decl.name.clone(),
                params: jp_decl.params.clone(),
                ty: jp_decl.ty.clone(),
                body: Box::new(new_jp_body),
            };
            let new_body = specialize_code_with_index(ctx, state, body, config, decl_index);
            Code::JoinPoint(new_jp_decl, Box::new(new_body))
        }

        Code::Cases(cases) => {
            let saved_scope = ctx.scope.clone();
            let saved_ground = ctx.ground.clone();
            let new_alts = cases
                .alts
                .iter()
                .map(|alt| {
                    ctx.scope = saved_scope.clone();
                    ctx.ground = saved_ground.clone();
                    match alt {
                        Alt::Ctor {
                            ctor_name,
                            params,
                            body,
                        } => {
                            for param in params {
                                ctx.scope.insert(param.fvar_id);
                            }
                            Alt::Ctor {
                                ctor_name: ctor_name.clone(),
                                params: params.clone(),
                                body: Box::new(specialize_code_with_index(
                                    ctx, state, body, config, decl_index,
                                )),
                            }
                        }
                        Alt::Default(body) => Alt::Default(Box::new(specialize_code_with_index(
                            ctx, state, body, config, decl_index,
                        ))),
                    }
                })
                .collect();
            ctx.scope = saved_scope;
            ctx.ground = saved_ground;
            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                scrutinee: cases.scrutinee,
                result_type: cases.result_type.clone(),
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

/// Check if code only references ground FVars.
pub(crate) fn is_code_ground(ctx: &SpecContext, code: &Code) -> bool {
    match code {
        Code::Let(decl, body) => ctx.is_value_ground(&decl.value) && is_code_ground(ctx, body),
        Code::Fun(_, body) | Code::JoinPoint(_, body) => is_code_ground(ctx, body),
        Code::Cases(cases) => {
            ctx.is_fvar_ground(cases.scrutinee)
                && cases.alts.iter().all(|alt| match alt {
                    Alt::Ctor { body, .. } => is_code_ground(ctx, body),
                    Alt::Default(body) => is_code_ground(ctx, body),
                })
        }
        Code::Jmp { jp, args } => {
            ctx.is_fvar_ground(*jp) && args.iter().all(|arg| ctx.is_arg_ground(arg))
        }
        Code::Return(fvar) => ctx.is_fvar_ground(*fvar),
        Code::Unreachable(_) => true,
    }
}
