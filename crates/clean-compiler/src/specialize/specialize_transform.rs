// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IR body transformation functions for the specialization pass.
//!
//! Contains:
//! - Type environment construction
//! - Call site collection
//! - Specialized body generation (type substitution)
//! - Call site rewriting
//! - Name generation helpers

use super::{resolve_arg_type, SpecKey};
use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

/// Type environment: maps VarId -> known concrete IRType.
pub(crate) type TypeEnv = HashMap<VarId, IRType>;

/// A collected call site with known concrete type arguments.
#[derive(Clone, Debug)]
pub(crate) struct CallSite {
    /// The specialization key for deduplication.
    pub(crate) key: SpecKey,
}

// ═══════════════════════════════════════════════════════════════════════════
// Type Environment
// ═══════════════════════════════════════════════════════════════════════════

/// Build a type environment from a declaration's params and VDecls.
pub(crate) fn build_type_env(decl: &IRDecl) -> TypeEnv {
    let mut env = HashMap::new();
    for (var, ty) in &decl.params {
        env.insert(*var, ty.clone());
    }
    collect_types_from_body(&decl.body, &mut env);
    env
}

/// Walk the body to collect type information from VDecl bindings.
fn collect_types_from_body(body: &IRBody, env: &mut TypeEnv) {
    match body {
        IRBody::VDecl { var, ty, rest, .. } => {
            env.insert(*var, ty.clone());
            collect_types_from_body(rest, env);
        }
        IRBody::JDecl {
            params, body, rest, ..
        } => {
            for (var, ty) in params {
                env.insert(*var, ty.clone());
            }
            collect_types_from_body(body, env);
            collect_types_from_body(rest, env);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_types_from_body(rest, env);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_types_from_body(&alt.body, env);
            }
            if let Some(d) = default {
                collect_types_from_body(d, env);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Call Site Collection
// ═══════════════════════════════════════════════════════════════════════════

/// Collect call sites from a body that target candidate functions.
pub(crate) fn collect_call_sites(
    body: &IRBody,
    env: &TypeEnv,
    candidates: &HashSet<Name>,
    sites: &mut Vec<CallSite>,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, args } = value {
                if candidates.contains(&fn_id.0) {
                    let type_args: Vec<Option<IRType>> = args
                        .iter()
                        .map(|arg| resolve_arg_type(arg, env).filter(|t| t.is_scalar()))
                        .collect();

                    if type_args.iter().any(|t| t.is_some()) {
                        sites.push(CallSite {
                            key: SpecKey {
                                fn_name: fn_id.0.clone(),
                                type_args,
                            },
                        });
                    }
                }
            }
            collect_call_sites(rest, env, candidates, sites);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_call_sites(body, env, candidates, sites);
            collect_call_sites(rest, env, candidates, sites);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_call_sites(rest, env, candidates, sites);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_call_sites(&alt.body, env, candidates, sites);
            }
            if let Some(d) = default {
                collect_call_sites(d, env, candidates, sites);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Name Generation
// ═══════════════════════════════════════════════════════════════════════════

/// Generate a specialized name for a function + type arguments.
pub(crate) fn specialized_name(fn_name: &Name, type_args: &[Option<IRType>]) -> Name {
    let suffix: String = type_args
        .iter()
        .map(|t| match t {
            Some(ty) => ir_type_suffix(ty),
            None => "_".to_string(),
        })
        .collect::<Vec<_>>()
        .join("_");
    Name::append(fn_name, &format!("_spec_{suffix}"))
}

/// Short suffix string for an IRType (used in mangled names and hashing).
pub(crate) fn ir_type_suffix(ty: &IRType) -> String {
    match ty {
        IRType::Bool => "b".to_string(),
        IRType::UInt8 => "u8".to_string(),
        IRType::UInt16 => "u16".to_string(),
        IRType::UInt32 => "u32".to_string(),
        IRType::UInt64 => "u64".to_string(),
        IRType::USize => "us".to_string(),
        IRType::Float32 => "f32".to_string(),
        IRType::Float64 => "f64".to_string(),
        IRType::Object => "obj".to_string(),
        IRType::TObject => "tobj".to_string(),
        IRType::Erased => "e".to_string(),
        IRType::Void => "v".to_string(),
        IRType::Struct(_) => "st".to_string(),
        IRType::Union(_) => "un".to_string(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Body Specialization
// ═══════════════════════════════════════════════════════════════════════════

/// Specialize a function body by replacing Object types with concrete types.
///
/// For each variable in `param_map`, replace occurrences of its original
/// type with the mapped concrete type in VDecl, JDecl, and expressions.
pub(crate) fn specialize_body(body: &IRBody, param_map: &HashMap<VarId, IRType>) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let new_ty = param_map.get(var).cloned().unwrap_or_else(|| ty.clone());
            let new_value = specialize_expr(value, param_map);
            IRBody::VDecl {
                var: *var,
                ty: new_ty,
                value: new_value,
                rest: Box::new(specialize_body(rest, param_map)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let new_params: Vec<(VarId, IRType)> = params
                .iter()
                .map(|(v, t)| (*v, param_map.get(v).cloned().unwrap_or_else(|| t.clone())))
                .collect();
            IRBody::JDecl {
                jp: *jp,
                params: new_params,
                body: Box::new(specialize_body(jp_body, param_map)),
                rest: Box::new(specialize_body(rest, param_map)),
            }
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(specialize_body(rest, param_map)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(specialize_body(rest, param_map)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(specialize_body(rest, param_map)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(specialize_body(rest, param_map)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(specialize_body(rest, param_map)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: Box::new(specialize_body(rest, param_map)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let new_alts: Vec<IRAlt> = alts
                .iter()
                .map(|alt| IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(specialize_body(&alt.body, param_map)),
                })
                .collect();
            IRBody::Case {
                scrutinee: *scrutinee,
                alts: new_alts,
                default: default
                    .as_ref()
                    .map(|d| Box::new(specialize_body(d, param_map))),
            }
        }
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

/// Specialize an expression (handle Box/Unbox/Proj type substitution).
fn specialize_expr(expr: &IRExpr, param_map: &HashMap<VarId, IRType>) -> IRExpr {
    match expr {
        IRExpr::Box { ty, arg } => {
            let resolved = match arg {
                IRArg::Var(v) => param_map.get(v).cloned().unwrap_or_else(|| ty.clone()),
                _ => ty.clone(),
            };
            IRExpr::Box {
                ty: resolved,
                arg: arg.clone(),
            }
        }
        IRExpr::Unbox { ty, arg } => {
            let resolved = match arg {
                IRArg::Var(v) => param_map.get(v).cloned().unwrap_or_else(|| ty.clone()),
                _ => ty.clone(),
            };
            IRExpr::Unbox {
                ty: resolved,
                arg: arg.clone(),
            }
        }
        IRExpr::Proj { idx, ty, arg } => {
            let resolved = match arg {
                IRArg::Var(v) => param_map.get(v).cloned().unwrap_or_else(|| ty.clone()),
                _ => ty.clone(),
            };
            IRExpr::Proj {
                idx: *idx,
                ty: resolved,
                arg: arg.clone(),
            }
        }
        other => other.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Call Site Rewriting
// ═══════════════════════════════════════════════════════════════════════════

/// Rewrite call sites in a body to use specialized functions.
pub(crate) fn rewrite_call_sites(
    body: &IRBody,
    env: &TypeEnv,
    rewrites: &HashMap<SpecKey, Name>,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let new_value = rewrite_expr(value, env, rewrites);
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: new_value,
                rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(rewrite_call_sites(jp_body, env, rewrites)),
            rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: Box::new(rewrite_call_sites(rest, env, rewrites)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let new_alts: Vec<IRAlt> = alts
                .iter()
                .map(|alt| IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(rewrite_call_sites(&alt.body, env, rewrites)),
                })
                .collect();
            IRBody::Case {
                scrutinee: *scrutinee,
                alts: new_alts,
                default: default
                    .as_ref()
                    .map(|d| Box::new(rewrite_call_sites(d, env, rewrites))),
            }
        }
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

/// Rewrite a single expression, replacing Apply targets as needed.
fn rewrite_expr(expr: &IRExpr, env: &TypeEnv, rewrites: &HashMap<SpecKey, Name>) -> IRExpr {
    if let IRExpr::Apply { fn_id, args } = expr {
        let type_args: Vec<Option<IRType>> = args
            .iter()
            .map(|arg| resolve_arg_type(arg, env).filter(|t| t.is_scalar()))
            .collect();

        if type_args.iter().any(|t| t.is_some()) {
            let key = SpecKey {
                fn_name: fn_id.0.clone(),
                type_args,
            };
            if let Some(spec_name) = rewrites.get(&key) {
                return IRExpr::Apply {
                    fn_id: FnId(spec_name.clone()),
                    args: args.clone(),
                };
            }
        }
    }
    expr.clone()
}
