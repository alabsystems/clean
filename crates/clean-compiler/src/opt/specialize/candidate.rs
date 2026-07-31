// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Specialization candidate detection and specialized declaration generation.
//!
//! Contains the logic to identify specialization-worthy call sites, build
//! cache keys, and generate specialized function declarations.

use super::context::{GroundValue, LocalSpecKey, SpecCacheKey, SpecContext, SpecKey, SpecState};
use super::substitute::{substitute_ground_in_code, wrap_with_ground_bindings};
use super::{DeclIndex, SpecConfig};
use crate::lcnf::{Arg, Code, Decl, DeclValue, FunDecl, LetValue, Param};
use clean_kernel::{FVarId, Literal, Name};
use std::collections::HashMap;

/// Build a SpecKey for an argument.
///
/// If the argument is ground, returns `SpecKey::Ground` with the value.
/// Otherwise returns `SpecKey::Erased`.
pub(crate) fn arg_to_spec_key(
    ctx: &SpecContext,
    arg: &Arg,
    bindings: &HashMap<FVarId, &LetValue>,
) -> SpecKey {
    match arg {
        Arg::FVar(fvar) if ctx.ground.contains(fvar) => {
            // Try to extract the ground value from bindings
            if let Some(value) = bindings.get(fvar) {
                if let Some(gv) = let_value_to_ground(value, bindings) {
                    return SpecKey::Ground(gv);
                }
            }
            // If we can't extract the value, still mark as ground with FVar reference
            SpecKey::Ground(GroundValue::Const(Name::from_string(&format!(
                "_x{}",
                fvar.as_u64()
            ))))
        }
        Arg::Type(_) | Arg::Erased | Arg::Index(_) => SpecKey::Erased,
        Arg::FVar(_) => SpecKey::Erased,
    }
}

/// Try to convert a LetValue to a GroundValue for caching.
pub(crate) fn let_value_to_ground(
    value: &LetValue,
    bindings: &HashMap<FVarId, &LetValue>,
) -> Option<GroundValue> {
    match value {
        LetValue::Lit(lit) => {
            // Extract literal as u64 for caching
            match lit {
                Literal::Nat(n) => n.to_u64().map(GroundValue::Lit),
                Literal::String(_) => None, // Strings not cached by value
            }
        }
        LetValue::Const { name, args, .. } => {
            if args.is_empty() {
                Some(GroundValue::Const(name.clone()))
            } else {
                // Recursively collect ground args
                let mut ground_args = Vec::new();
                for arg in args {
                    match arg {
                        Arg::FVar(fvar) => {
                            let value = bindings.get(fvar)?;
                            ground_args.push(let_value_to_ground(value, bindings)?);
                        }
                        Arg::Type(_) | Arg::Erased | Arg::Index(_) => {}
                    }
                }
                Some(GroundValue::Ctor(name.clone(), ground_args))
            }
        }
        LetValue::Ctor { name, args, .. } => {
            let mut ground_args = Vec::new();
            for arg in args {
                match arg {
                    Arg::FVar(fvar) => {
                        let value = bindings.get(fvar)?;
                        ground_args.push(let_value_to_ground(value, bindings)?);
                    }
                    Arg::Type(_) | Arg::Erased | Arg::Index(_) => {}
                }
            }
            Some(GroundValue::Ctor(name.clone(), ground_args))
        }
        LetValue::Erased => None,
        LetValue::Proj { .. } | LetValue::FVar { .. } | LetValue::Reuse { .. } => None,
    }
}

/// Build a specialization cache key from a call site.
pub(crate) fn build_spec_key(
    ctx: &SpecContext,
    fn_name: &Name,
    args: &[Arg],
    bindings: &HashMap<FVarId, &LetValue>,
) -> SpecCacheKey {
    let ground_args: Vec<SpecKey> = args
        .iter()
        .map(|arg| arg_to_spec_key(ctx, arg, bindings))
        .collect();

    SpecCacheKey {
        original: fn_name.clone(),
        ground_args,
    }
}

/// Build a specialization cache key for a local function call.
fn build_local_spec_key(
    ctx: &SpecContext,
    fvar: FVarId,
    args: &[Arg],
    bindings: &HashMap<FVarId, &LetValue>,
) -> LocalSpecKey {
    let ground_args: Vec<SpecKey> = args
        .iter()
        .map(|arg| arg_to_spec_key(ctx, arg, bindings))
        .collect();

    LocalSpecKey {
        original_fvar: fvar,
        ground_args,
    }
}

/// Check if a call has any ground arguments worth specializing.
pub(crate) fn has_specializable_ground_args(ctx: &SpecContext, args: &[Arg]) -> bool {
    args.iter().any(|arg| {
        if let Arg::FVar(fvar) = arg {
            ctx.ground.contains(fvar)
        } else {
            false
        }
    })
}

/// Filter arguments to keep only non-ground (erased) ones after specialization.
fn filter_remaining_args(args: &[Arg], ground_args: &[SpecKey]) -> Vec<Arg> {
    args.iter()
        .zip(ground_args.iter())
        .filter_map(|(arg, sk)| {
            if matches!(sk, SpecKey::Erased) {
                Some(arg.clone())
            } else {
                None
            }
        })
        .collect()
}

/// Try to specialize a let-value (function application).
///
/// This function checks if a function call has ground arguments that
/// make it a specialization candidate. Currently identifies candidates
/// but actual declaration generation requires full environment access.
pub(crate) fn try_specialize_value(
    ctx: &SpecContext,
    state: &mut SpecState,
    value: &LetValue,
    config: &SpecConfig,
    bindings: &HashMap<FVarId, &LetValue>,
) -> LetValue {
    match value {
        LetValue::Const { name, levels, args } => {
            if !config.specialize_instances || args.is_empty() {
                return value.clone();
            }

            // Check if any arguments are ground instances
            if !has_specializable_ground_args(ctx, args) {
                return value.clone();
            }

            // Build specialization key
            let key = build_spec_key(ctx, name, args, bindings);

            // Check if any args are actually ground (not all erased)
            let has_ground = key
                .ground_args
                .iter()
                .any(|k| matches!(k, SpecKey::Ground(_)));
            if !has_ground {
                return value.clone();
            }

            // Check cache for existing specialization
            if let Some(spec_name) = state.lookup_cache(&key) {
                return LetValue::Const {
                    name: spec_name.clone(),
                    levels: levels.clone(),
                    args: filter_remaining_args(args, &key.ground_args),
                };
            }

            // Generate new specialized name and cache it
            // Note: actual declaration generation requires access to the original
            // declaration, which we don't have here. For now, we just record
            // that specialization was requested.
            let spec_name = state.gen_spec_name(name, &ctx.decl_name);
            state.cache_spec(key, spec_name);

            // Return original - the specialized decl will be generated
            // in a separate pass with full environment access
            value.clone()
        }
        LetValue::FVar { fvar, args } => {
            specialize_local_fvar_call(ctx, state, *fvar, args, config, bindings)
                .unwrap_or_else(|| value.clone())
        }
        _ => value.clone(),
    }
}

/// Specialize a local function (FVar) call with ground arguments.
///
/// Looks up the local function definition, builds a specialized copy with
/// ground params substituted, and returns the rewritten call. Returns `None`
/// if specialization is not applicable.
fn specialize_local_fvar_call(
    ctx: &SpecContext,
    state: &mut SpecState,
    fvar: FVarId,
    args: &[Arg],
    config: &SpecConfig,
    bindings: &HashMap<FVarId, &LetValue>,
) -> Option<LetValue> {
    if !config.specialize_instances || args.is_empty() {
        return None;
    }

    if !has_specializable_ground_args(ctx, args) {
        return None;
    }

    // Look up local function definition
    let fun_decl = ctx.local_funs.get(&fvar)?.clone();

    // Build spec key
    let key = build_local_spec_key(ctx, fvar, args, bindings);
    let has_ground = key
        .ground_args
        .iter()
        .any(|k| matches!(k, SpecKey::Ground(_)));
    if !has_ground {
        return None;
    }

    // Check cache for existing specialization
    if let Some(&spec_fvar) = state.local_spec_cache.get(&key) {
        return Some(LetValue::FVar {
            fvar: spec_fvar,
            args: filter_remaining_args(args, &key.ground_args),
        });
    }

    // Generate specialized local function
    let spec_name = state.gen_spec_name(&fun_decl.name, &ctx.decl_name);
    let spec_fvar_id = state.gen_spec_fvar();

    // Build new params (remove ground) and substitution map
    let param_count = fun_decl.params.len().min(args.len());
    let mut new_params = Vec::new();
    let mut substitutions: HashMap<FVarId, LetValue> = HashMap::new();

    for (param, (arg, spec_key)) in fun_decl.params[..param_count]
        .iter()
        .zip(args[..param_count].iter().zip(key.ground_args.iter()))
    {
        if matches!(spec_key, SpecKey::Ground(_)) {
            if let Arg::FVar(arg_fvar) = arg {
                if let Some(binding) = bindings.get(arg_fvar) {
                    substitutions.insert(param.fvar_id, (*binding).clone());
                }
            }
        } else {
            new_params.push(param.clone());
        }
    }
    // Keep any extra params beyond the args
    if fun_decl.params.len() > args.len() {
        new_params.extend(fun_decl.params[args.len()..].iter().cloned());
    }

    let new_body = substitute_ground_in_code(&fun_decl.body, &substitutions);

    // Wrap body with let bindings for ground params so that all references
    // to the removed parameter FVarIds remain valid — substitute_ground_in_code
    // only handles LetValue::FVar but misses Arg::FVar in Const/Ctor/Jmp args
    // and Code::Return. Part of #1954 Bug 3.
    let wrapped_body = wrap_with_ground_bindings(
        new_body,
        &fun_decl.params[..param_count],
        &key.ground_args,
        &substitutions,
    );

    let spec_fun = FunDecl {
        fvar_id: spec_fvar_id,
        name: spec_name,
        params: new_params,
        ty: fun_decl.ty.clone(),
        body: Box::new(wrapped_body),
    };

    state.pending_local_specs.push(spec_fun);
    state.local_spec_cache.insert(key.clone(), spec_fvar_id);

    Some(LetValue::FVar {
        fvar: spec_fvar_id,
        args: filter_remaining_args(args, &key.ground_args),
    })
}

/// Try to specialize a let-value with access to the declaration index.
pub(crate) fn try_specialize_value_with_index(
    ctx: &SpecContext,
    state: &mut SpecState,
    value: &LetValue,
    config: &SpecConfig,
    bindings: &HashMap<FVarId, &LetValue>,
    decl_index: &DeclIndex<'_>,
) -> LetValue {
    match value {
        LetValue::Const { name, levels, args } => {
            if !config.specialize_instances || args.is_empty() {
                return value.clone();
            }

            if !has_specializable_ground_args(ctx, args) {
                return value.clone();
            }

            let key = build_spec_key(ctx, name, args, bindings);
            let has_ground = key
                .ground_args
                .iter()
                .any(|k| matches!(k, SpecKey::Ground(_)));
            if !has_ground {
                return value.clone();
            }

            // Check cache for existing specialization
            if let Some(spec_name) = state.lookup_cache(&key) {
                return LetValue::Const {
                    name: spec_name.clone(),
                    levels: levels.clone(),
                    args: filter_remaining_args(args, &key.ground_args),
                };
            }

            // Try to get the original declaration and create a specialized version
            if let Some(target_decl) = decl_index.get(name) {
                if let DeclValue::Code(target_code) = &target_decl.body {
                    let spec_name = state.gen_spec_name(name, &ctx.decl_name);

                    // Collect ground argument values
                    let ground_values: Vec<Option<LetValue>> = args
                        .iter()
                        .zip(key.ground_args.iter())
                        .map(|(arg, spec_key)| {
                            if matches!(spec_key, SpecKey::Ground(_)) {
                                if let Arg::FVar(fvar) = arg {
                                    bindings.get(fvar).cloned().cloned()
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        })
                        .collect();

                    // Create the specialized declaration
                    if let Some(spec_decl) = create_specialized_decl(
                        target_decl,
                        &spec_name,
                        &key.ground_args,
                        &ground_values,
                        target_code,
                    ) {
                        state.generated_decls.push(spec_decl);
                    }

                    state.cache_spec(key.clone(), spec_name.clone());

                    // Rewrite call to use specialized version
                    return LetValue::Const {
                        name: spec_name,
                        levels: levels.clone(),
                        args: filter_remaining_args(args, &key.ground_args),
                    };
                }
            }

            value.clone()
        }
        LetValue::FVar { fvar, args } => {
            specialize_local_fvar_call(ctx, state, *fvar, args, config, bindings)
                .unwrap_or_else(|| value.clone())
        }
        _ => value.clone(),
    }
}

/// Create a specialized declaration by substituting ground arguments.
pub(crate) fn create_specialized_decl(
    original: &Decl,
    spec_name: &Name,
    ground_args: &[SpecKey],
    ground_values: &[Option<LetValue>],
    original_code: &Code,
) -> Option<Decl> {
    // Build parameter list: keep non-ground params, drop ground ones
    let new_params: Vec<Param> = original
        .params
        .iter()
        .zip(ground_args.iter())
        .filter_map(|(param, key)| {
            if matches!(key, SpecKey::Erased) {
                Some(param.clone())
            } else {
                None
            }
        })
        .collect();

    // Build substitution map: ground params -> their values
    let mut substitutions: HashMap<FVarId, LetValue> = HashMap::new();
    for (param, (key, value)) in original
        .params
        .iter()
        .zip(ground_args.iter().zip(ground_values.iter()))
    {
        if matches!(key, SpecKey::Ground(_)) {
            if let Some(v) = value {
                substitutions.insert(param.fvar_id, v.clone());
            }
        }
    }

    // Substitute ground parameters in the body
    let new_body = substitute_ground_in_code(original_code, &substitutions);

    // Wrap body with let bindings for ground params — same fix as local
    // specialization. Part of #1954 Bug 3.
    let wrapped_body =
        wrap_with_ground_bindings(new_body, &original.params, ground_args, &substitutions);

    Some(Decl {
        name: spec_name.clone(),
        level_params: original.level_params.clone(),
        ty: original.ty.clone(),
        params: new_params,
        body: DeclValue::Code(Box::new(wrapped_body)),
        recursive: original.recursive,
    })
}
