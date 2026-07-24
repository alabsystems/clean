// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended closure-conversion helpers for L5IR.
//!
//! Provides configurable optimizations layered on top of the base closure
//! conversion pass: small-closure inlining, invariant-closure hoisting, and
//! optional defunctionalization.

use crate::closure_convert_ext_rewrite as rw;
use crate::closure_convert_fva::find_max_var_id;
use crate::ir::{CtorInfo, FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

/// Configuration for extended closure-conversion optimizations.
#[derive(Clone, Debug)]
pub(crate) struct ClosureConvertExtConfig {
    pub(crate) inline_small_closures: bool,
    pub(crate) small_closure_threshold: usize,
    pub(crate) defunctionalize: bool,
    pub(crate) hoist_invariant_closures: bool,
}

impl Default for ClosureConvertExtConfig {
    fn default() -> Self {
        Self {
            inline_small_closures: true,
            small_closure_threshold: 5,
            defunctionalize: false,
            hoist_invariant_closures: true,
        }
    }
}

/// Statistics collected by [`convert_closures_ext`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ClosureConvertExtStats {
    pub(crate) closures_converted: usize,
    pub(crate) closures_inlined: usize,
    pub(crate) closures_hoisted: usize,
    pub(crate) defunctionalized: usize,
    pub(crate) paps_generated: usize,
    pub(crate) mutual_groups: usize,
}

/// Summary information for a discovered closure binding.
#[derive(Clone, Debug)]
pub(crate) struct ClosureInfo {
    pub(crate) var: VarId,
    pub(crate) captured: Vec<VarId>,
    pub(crate) arity: usize,
    pub(crate) body_size: usize,
}

/// Internal representation of a `PartialApply` binding site.
#[derive(Clone, Debug)]
pub(crate) struct ClosureBinding {
    pub(crate) fn_id: FnId,
    pub(crate) arity: usize,
    pub(crate) captured_args: Vec<IRArg>,
}

/// Run the extended closure-conversion heuristics in place.
pub(crate) fn convert_closures_ext(
    decls: &mut Vec<IRDecl>,
    config: &ClosureConvertExtConfig,
) -> ClosureConvertExtStats {
    let mut stats = ClosureConvertExtStats::default();
    let fn_map: HashMap<FnId, IRDecl> = decls
        .iter()
        .cloned()
        .map(|decl| (FnId(decl.name.clone()), decl))
        .collect();
    let mut generated = Vec::new();
    let mut next_fresh = find_max_var_id(decls).saturating_add(1);

    for decl in decls.iter_mut() {
        let original_infos = identify_closures(&decl.body);
        stats.closures_converted += original_infos.len();

        let mutual = detect_mutual_groups(&decl.body);
        stats.mutual_groups += mutual.len();

        if config.inline_small_closures {
            run_inline_phase(
                decl,
                &original_infos,
                config,
                &fn_map,
                &mut next_fresh,
                &mut stats,
            );
        }
        if config.hoist_invariant_closures {
            run_hoist_phase(decl, &mut generated, &mut stats);
        }
        if config.defunctionalize {
            run_defunctionalize_phase(decl, &mut generated, &mut stats);
        }
        run_pap_phase(decl, &fn_map, &mut generated, &mut stats);
    }

    decls.extend(generated);
    stats
}

/// Run [`convert_closures_ext`] with the default configuration.
pub(crate) fn convert_closures_ext_default(decls: &mut Vec<IRDecl>) -> ClosureConvertExtStats {
    convert_closures_ext(decls, &ClosureConvertExtConfig::default())
}

/// Find `PartialApply`-backed closure bindings inside a body.
pub(crate) fn identify_closures(body: &IRBody) -> Vec<ClosureInfo> {
    let mut infos = Vec::new();
    collect_closure_infos(body, &mut infos);
    infos
}

/// Decide whether a discovered closure is below the small-closure threshold.
pub(crate) fn is_small_closure(info: &ClosureInfo, threshold: usize) -> bool {
    info.body_size <= threshold
}

/// Inline closure applications that reference `closure_var`.
pub(crate) fn inline_closure_at_call_site(
    body: &mut IRBody,
    closure_var: VarId,
    closure_body: &IRBody,
) -> bool {
    let (rewritten, changed) = rw::inline_thunk_calls(body, closure_var, closure_body);
    *body = rewritten;
    changed
}

/// Hoist an invariant `PartialApply` into a new top-level wrapper declaration.
pub(crate) fn hoist_invariant_closure(decl: &mut IRDecl, closure_var: VarId) -> Option<IRDecl> {
    let bindings = collect_bindings(&decl.body);
    let binding = bindings.get(&closure_var)?.clone();
    if !binding.captured_args.is_empty() {
        return None;
    }
    if !closure_var_uses_are_exact_calls(&decl.body, closure_var, binding.arity) {
        return None;
    }

    let hoisted_name = Name::from_string(&format!("{}._closure{}", decl.name, closure_var.0));
    let hoisted = make_hoisted_wrapper(&hoisted_name, &binding);
    let (body, removed, rewritten) =
        rw::remove_binding_and_rewrite_calls(&decl.body, closure_var, &hoisted_name, binding.arity);
    if removed && rewritten {
        decl.body = body;
        Some(hoisted)
    } else {
        None
    }
}

/// Build a defunctionalized apply wrapper and its environment type.
pub(crate) fn defunctionalize_closure(closure_info: &ClosureInfo) -> (IRDecl, IRType) {
    let env_ty = IRType::Struct(vec![IRType::Object; closure_info.captured.len()]);
    let remaining = closure_info
        .arity
        .saturating_sub(closure_info.captured.len());
    let mut params = Vec::with_capacity(remaining + 1);
    params.push((VarId(0), env_ty.clone()));
    for i in 0..remaining {
        params.push((VarId(i as u32 + 1), IRType::Object));
    }
    (
        IRDecl {
            name: Name::from_string(&format!("_closure.defun.apply.{}", closure_info.var.0)),
            params,
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(VarId(0))),
        },
        env_ty,
    )
}

/// A group of mutually-recursive closures that share a combined environment.
#[derive(Clone, Debug)]
pub(crate) struct MutualGroup {
    pub(crate) members: Vec<VarId>,
    pub(crate) shared_captures: Vec<VarId>,
}

/// Detect groups of mutually-recursive closure bindings in a body.
///
/// Two closures are mutually recursive if either captures the other's VarId
/// as a free variable. Returns groups of 2+ closures that reference each other.
pub(crate) fn detect_mutual_groups(body: &IRBody) -> Vec<MutualGroup> {
    let infos = identify_closures(body);
    let closure_vars: HashSet<VarId> = infos.iter().map(|i| i.var).collect();
    let mut groups: Vec<MutualGroup> = Vec::new();
    let mut visited: HashSet<VarId> = HashSet::new();
    for info in &infos {
        if visited.contains(&info.var) {
            continue;
        }
        let refs_other: Vec<VarId> = info
            .captured
            .iter()
            .filter(|v| closure_vars.contains(v) && **v != info.var)
            .copied()
            .collect();
        if refs_other.is_empty() {
            continue;
        }
        let mut members = vec![info.var];
        members.extend(&refs_other);
        let all_captures: HashSet<VarId> = members
            .iter()
            .flat_map(|m| infos.iter().find(|i| i.var == *m))
            .flat_map(|i| i.captured.iter().copied())
            .filter(|v| !members.contains(v))
            .collect();
        for m in &members {
            visited.insert(*m);
        }
        groups.push(MutualGroup {
            members,
            shared_captures: all_captures.into_iter().collect(),
        });
    }
    groups
}

/// Generate a PAP wrapper for an under-saturated call site.
/// Creates `f._pap_K` that accepts K args and returns a PartialApply closure.
pub(crate) fn generate_pap_wrapper(
    fn_id: &FnId,
    full_arity: usize,
    applied_count: usize,
) -> Option<IRDecl> {
    if applied_count >= full_arity || applied_count == 0 {
        return None;
    }
    let wrapper_name = Name::from_string(&format!("{}._pap_{}", fn_id.0, applied_count));
    let params: Vec<(VarId, IRType)> = (0..applied_count)
        .map(|i| (VarId(i as u32), IRType::Object))
        .collect();
    let result_var = VarId(applied_count as u32);
    let captured_args: Vec<IRArg> = params.iter().map(|(v, _)| IRArg::Var(*v)).collect();
    Some(IRDecl {
        name: wrapper_name,
        params,
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: result_var,
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id.clone(),
                arity: full_arity as u16,
                args: captured_args,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(result_var))),
        },
    })
}

fn run_inline_phase(
    decl: &mut IRDecl,
    original_infos: &[ClosureInfo],
    config: &ClosureConvertExtConfig,
    fn_map: &HashMap<FnId, IRDecl>,
    next_fresh: &mut u32,
    stats: &mut ClosureConvertExtStats,
) {
    let bindings = collect_bindings(&decl.body);
    for info in original_infos
        .iter()
        .filter(|i| is_small_closure(i, config.small_closure_threshold))
    {
        let Some(binding) = bindings.get(&info.var) else {
            continue;
        };
        let changed = try_inline_or_lower(decl, info.var, binding, fn_map, next_fresh);
        if changed {
            stats.closures_inlined += 1;
        }
    }
}

fn try_inline_or_lower(
    decl: &mut IRDecl,
    var: VarId,
    binding: &ClosureBinding,
    fn_map: &HashMap<FnId, IRDecl>,
    next_fresh: &mut u32,
) -> bool {
    if let Some(callee) = fn_map.get(&binding.fn_id) {
        let (body, count) =
            rw::inline_bound_closure_calls(&decl.body, var, binding, callee, next_fresh);
        if count > 0 {
            decl.body = body;
            return true;
        }
    }
    let (body, lowered) = rw::lower_exact_closure_calls_to_apply(
        &decl.body,
        var,
        &binding.fn_id,
        &binding.captured_args,
        binding.arity,
    );
    decl.body = body;
    lowered
}

fn run_hoist_phase(
    decl: &mut IRDecl,
    generated: &mut Vec<IRDecl>,
    stats: &mut ClosureConvertExtStats,
) {
    let closure_vars: Vec<VarId> = identify_closures(&decl.body)
        .into_iter()
        .map(|info| info.var)
        .collect();
    for closure_var in closure_vars {
        if let Some(hoisted) = hoist_invariant_closure(decl, closure_var) {
            generated.push(hoisted);
            stats.closures_hoisted += 1;
        }
    }
}

fn run_pap_phase(
    decl: &IRDecl,
    fn_map: &HashMap<FnId, IRDecl>,
    generated: &mut Vec<IRDecl>,
    stats: &mut ClosureConvertExtStats,
) {
    let bindings = collect_bindings(&decl.body);
    for binding in bindings.values() {
        let applied = binding.captured_args.len();
        if applied > 0 && applied < binding.arity && fn_map.contains_key(&binding.fn_id) {
            if let Some(pap) = generate_pap_wrapper(&binding.fn_id, binding.arity, applied) {
                let pap_name = FnId(pap.name.clone());
                if !generated.iter().any(|d| FnId(d.name.clone()) == pap_name) {
                    generated.push(pap);
                    stats.paps_generated += 1;
                }
            }
        }
    }
}

fn run_defunctionalize_phase(
    decl: &mut IRDecl,
    generated: &mut Vec<IRDecl>,
    stats: &mut ClosureConvertExtStats,
) {
    let infos = identify_closures(&decl.body);
    let bindings = collect_bindings(&decl.body);
    for info in infos {
        let Some(binding) = bindings.get(&info.var) else {
            continue;
        };
        let remaining_arity = binding.arity.saturating_sub(info.captured.len());
        if !closure_var_uses_are_exact_calls(&decl.body, info.var, remaining_arity) {
            continue;
        }
        let (mut apply_decl, env_ty) = defunctionalize_closure(&info);
        apply_decl.body = rw::build_defunctionalized_apply_body(&apply_decl, binding, &info);
        let env_ctor = env_ctor_info(info.var, &env_ty);
        let (body, changed) =
            rw::defunctionalize_body(&decl.body, info.var, binding, &apply_decl, &env_ctor);
        if changed {
            decl.body = body;
            generated.push(apply_decl);
            stats.defunctionalized += 1;
        }
    }
}

pub(crate) fn body_size(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { rest, .. } => 1 + body_size(rest),
        IRBody::JDecl { body, rest, .. } => 1 + body_size(body) + body_size(rest),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + body_size(rest),
        IRBody::Case { alts, default, .. } => {
            1 + alts.iter().map(|alt| body_size(&alt.body)).sum::<usize>()
                + default.as_ref().map_or(0, |body| body_size(body))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

/// Walk body visiting each PartialApply VDecl.
fn walk_partial_applies(body: &IRBody, f: &mut impl FnMut(VarId, &FnId, u16, &[IRArg], &IRBody)) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if let IRExpr::PartialApply { fn_id, arity, args } = value {
                f(*var, fn_id, *arity, args, rest);
            }
            walk_partial_applies(rest, f);
        }
        IRBody::JDecl { body: b, rest, .. } => {
            walk_partial_applies(b, f);
            walk_partial_applies(rest, f);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => walk_partial_applies(rest, f),
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                walk_partial_applies(&a.body, f);
            }
            if let Some(d) = default {
                walk_partial_applies(d, f);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn collect_closure_infos(body: &IRBody, out: &mut Vec<ClosureInfo>) {
    walk_partial_applies(body, &mut |var, _, arity, args, rest| {
        out.push(ClosureInfo {
            var,
            captured: args
                .iter()
                .filter_map(|a| match a {
                    IRArg::Var(v) => Some(*v),
                    IRArg::Erased => None,
                })
                .collect(),
            arity: arity as usize,
            body_size: body_size(rest),
        });
    });
}

pub(crate) fn collect_bindings(body: &IRBody) -> HashMap<VarId, ClosureBinding> {
    let mut out = HashMap::new();
    walk_partial_applies(body, &mut |var, fn_id, arity, args, _| {
        out.insert(
            var,
            ClosureBinding {
                fn_id: fn_id.clone(),
                arity: arity as usize,
                captured_args: args.to_vec(),
            },
        );
    });
    out
}

fn closure_var_uses_are_exact_calls(body: &IRBody, cv: VarId, remaining: usize) -> bool {
    let arg_has = |a: &IRArg| matches!(a, IRArg::Var(v) if *v == cv);
    let args_have = |args: &[IRArg]| args.iter().any(&arg_has);
    let expr_ok = |e: &IRExpr| -> bool {
        match e {
            IRExpr::ClosureApply {
                closure: IRArg::Var(v),
                args,
            } if *v == cv => args.len() == remaining && !args_have(args),
            IRExpr::Ctor { args, .. }
            | IRExpr::Apply { args, .. }
            | IRExpr::PartialApply { args, .. } => !args_have(args),
            IRExpr::Proj { arg, .. }
            | IRExpr::Tag(arg)
            | IRExpr::Box { arg, .. }
            | IRExpr::Unbox { arg, .. } => !arg_has(arg),
            IRExpr::ClosureApply { closure, args } => !arg_has(closure) && !args_have(args),
            IRExpr::UProj { var, .. }
            | IRExpr::SProj { var, .. }
            | IRExpr::IsShared(var)
            | IRExpr::Reset(var) => *var != cv,
            IRExpr::Reuse { var, args, .. } => *var != cv && !args_have(args),
            IRExpr::Lit(_) | IRExpr::String(_) => true,
        }
    };
    match body {
        IRBody::VDecl { value, rest, .. } => {
            expr_ok(value) && closure_var_uses_are_exact_calls(rest, cv, remaining)
        }
        IRBody::JDecl { body, rest, .. } => {
            closure_var_uses_are_exact_calls(body, cv, remaining)
                && closure_var_uses_are_exact_calls(rest, cv, remaining)
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => closure_var_uses_are_exact_calls(rest, cv, remaining),
        IRBody::Case { alts, default, .. } => {
            alts.iter()
                .all(|a| closure_var_uses_are_exact_calls(&a.body, cv, remaining))
                && default
                    .as_ref()
                    .is_none_or(|b| closure_var_uses_are_exact_calls(b, cv, remaining))
        }
        IRBody::Jmp { args, .. } => !args_have(args),
        IRBody::Ret(arg) => !arg_has(arg),
        IRBody::Unreachable => true,
    }
}

fn make_hoisted_wrapper(name: &Name, binding: &ClosureBinding) -> IRDecl {
    let params: Vec<(VarId, IRType)> = (0..binding.arity)
        .map(|i| (VarId(i as u32), IRType::Object))
        .collect();
    let result = VarId(binding.arity as u32);
    IRDecl {
        name: name.clone(),
        params: params.clone(),
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: result,
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: binding.fn_id.clone(),
                args: params.iter().map(|(v, _)| IRArg::Var(*v)).collect(),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(result))),
        },
    }
}

fn env_ctor_info(closure_var: VarId, env_ty: &IRType) -> CtorInfo {
    let field_types = match env_ty {
        IRType::Struct(fields) => fields.clone(),
        _ => Vec::new(),
    };
    CtorInfo {
        name: Name::from_string(&format!("_closure.defun.env.{}", closure_var.0)),
        tag: 0,
        num_scalars: 0,
        num_objects: field_types.iter().filter(|ty| ty.is_object()).count() as u32,
        field_types,
    }
}
