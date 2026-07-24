// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Extended function specialization for Lean 5 L5IR.
//! Adds cost-guided, depth-limited, partially polymorphic specialization on
//! top of the base IR specializer by aggregating concrete call-site patterns.
use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use crate::specialize::{
    build_type_env, collect_call_sites, find_candidates, resolve_arg_type, specialize_body,
    specialized_name, CallSite, SpecKey, SpecializeConfig, TypeEnv,
};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Clone, Debug)]
pub(crate) struct SpecializeExtConfig {
    pub(crate) base: SpecializeConfig,
    pub(crate) max_specialization_depth: usize,
    pub(crate) max_specialized_args_per_call: usize,
    pub(crate) min_call_count: usize,
    pub(crate) max_code_size_increase: usize,
    pub(crate) min_speedup_factor: f64,
    pub(crate) enable_partial_specialization: bool,
}
impl Default for SpecializeExtConfig {
    fn default() -> Self {
        Self {
            base: SpecializeConfig::default(),
            max_specialization_depth: 2,
            max_specialized_args_per_call: 2,
            min_call_count: 1,
            max_code_size_increase: 96,
            min_speedup_factor: 1.15,
            enable_partial_specialization: true,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct SpecializeExtStats {
    pub(crate) candidates_found: usize,
    pub(crate) call_sites_analyzed: usize,
    pub(crate) call_patterns_observed: usize,
    pub(crate) specializations_generated: usize,
    pub(crate) partial_specializations: usize,
    pub(crate) rewritten_decls: usize,
    pub(crate) cache_hits: usize,
    pub(crate) profitable_rejections: usize,
    pub(crate) depth_rejections: usize,
    pub(crate) limit_rejections: usize,
    pub(crate) errors: usize,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct CallSiteInfo {
    pub(crate) call_count: usize,
    pub(crate) argument_type_patterns: Vec<Vec<Option<IRType>>>,
}
impl CallSiteInfo {
    pub(crate) fn observe(&mut self, pattern: Vec<Option<IRType>>) {
        self.call_count += 1;
        if !self.argument_type_patterns.iter().any(|p| p == &pattern) {
            self.argument_type_patterns.push(pattern);
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct SpecializationCost {
    pub(crate) estimated_code_size_increase: usize,
    pub(crate) estimated_speedup_factor: f64,
}
impl SpecializationCost {
    #[must_use]
    pub(crate) fn is_profitable(&self) -> bool {
        self.estimated_speedup_factor >= 1.10
            && self.estimated_speedup_factor * 24.0 >= self.estimated_code_size_increase as f64
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct SpecializationCache {
    entries: HashMap<SpecKey, Name>,
}
impl SpecializationCache {
    pub(crate) fn get(&self, key: &SpecKey) -> Option<&Name> {
        self.entries.get(key)
    }
    pub(crate) fn insert(&mut self, key: SpecKey, name: Name) {
        self.entries.insert(key, name);
    }
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
    fn rewrites(&self) -> &HashMap<SpecKey, Name> {
        &self.entries
    }
}

#[derive(Debug, Error)]
pub(crate) enum SpecializeExtError {
    #[error("specialization depth {depth} exceeds max depth {max_depth} for {fn_name:?}")]
    DepthLimitExceeded {
        fn_name: Name,
        depth: usize,
        max_depth: usize,
    },
    #[error("missing declaration for specialization target {0:?}")]
    MissingDeclaration(Name),
    #[error(
        "specialization key arity mismatch for {fn_name:?}: expected {expected}, got {actual}"
    )]
    ArityMismatch {
        fn_name: Name,
        expected: usize,
        actual: usize,
    },
    #[error("specialization for {0:?} keeps all parameters polymorphic")]
    EmptySpecialization(Name),
}

#[must_use]
pub(crate) fn run_extended_specialization(
    decls: &[IRDecl],
    config: &SpecializeExtConfig,
) -> (Vec<IRDecl>, SpecializeExtStats) {
    let mut stats = SpecializeExtStats::default();
    let candidates = find_candidates(decls, &config.base);
    stats.candidates_found = candidates.len();
    if candidates.is_empty() {
        return (decls.to_vec(), stats);
    }
    let originals: HashMap<Name, IRDecl> = decls
        .iter()
        .cloned()
        .map(|decl| (decl.name.clone(), decl))
        .collect();
    let mut cache = SpecializationCache::default();
    let mut per_fn_count = HashMap::<Name, usize>::new();
    let mut generated = Vec::new();
    let mut worklist: Vec<(IRDecl, usize)> = decls.iter().cloned().map(|d| (d, 0)).collect();
    let mut i = 0;
    while i < worklist.len() {
        let (decl, depth) = worklist[i].clone();
        i += 1;
        let env = build_type_env(&decl);
        let mut raw_sites: Vec<CallSite> = Vec::new();
        collect_call_sites(&decl.body, &env, &candidates, &mut raw_sites);
        stats.call_sites_analyzed += raw_sites.len();
        let mut infos = HashMap::<Name, CallSiteInfo>::new();
        let mut counts = HashMap::<SpecKey, usize>::new();
        collect_call_site_info(
            &decl.body,
            &env,
            &candidates,
            &originals,
            config,
            &mut infos,
            &mut counts,
        );
        stats.call_patterns_observed += counts.len();
        let mut ordered: Vec<_> = counts.into_iter().collect();
        ordered.sort_by_key(|(key, _)| {
            format!("{:?}", specialized_name(&key.fn_name, &key.type_args))
        });
        for (key, count) in ordered {
            if cache.get(&key).is_some() {
                stats.cache_hits += 1;
                continue;
            }
            if per_fn_count.get(&key.fn_name).copied().unwrap_or(0)
                >= config.base.max_specializations_per_fn
                || cache.len() >= config.base.max_total_specializations
            {
                stats.limit_rejections += 1;
                continue;
            }
            match try_create_specialization(
                &key,
                count,
                depth + 1,
                infos.get(&key.fn_name),
                &originals,
                config,
            ) {
                Ok(Some((new_decl, partial))) => {
                    cache.insert(key.clone(), new_decl.name.clone());
                    *per_fn_count.entry(key.fn_name.clone()).or_insert(0) += 1;
                    worklist.push((new_decl.clone(), depth + 1));
                    generated.push(new_decl);
                    stats.specializations_generated += 1;
                    if partial {
                        stats.partial_specializations += 1;
                    }
                }
                Ok(None) => stats.profitable_rejections += 1,
                Err(SpecializeExtError::DepthLimitExceeded { .. }) => stats.depth_rejections += 1,
                Err(_) => stats.errors += 1,
            }
        }
    }
    let mut out = Vec::with_capacity(decls.len() + generated.len());
    for decl in decls.iter().chain(generated.iter()) {
        let (decl, changed) = rewrite_decl_calls(decl, cache.rewrites());
        if changed {
            stats.rewritten_decls += 1;
        }
        out.push(decl);
    }
    (out, stats)
}

fn try_create_specialization(
    key: &SpecKey,
    call_count: usize,
    depth: usize,
    info: Option<&CallSiteInfo>,
    originals: &HashMap<Name, IRDecl>,
    config: &SpecializeExtConfig,
) -> Result<Option<(IRDecl, bool)>, SpecializeExtError> {
    if depth > config.max_specialization_depth {
        return Err(SpecializeExtError::DepthLimitExceeded {
            fn_name: key.fn_name.clone(),
            depth,
            max_depth: config.max_specialization_depth,
        });
    }
    let original = originals
        .get(&key.fn_name)
        .ok_or_else(|| SpecializeExtError::MissingDeclaration(key.fn_name.clone()))?;
    let cost = estimate_specialization_cost(
        original,
        key,
        call_count,
        &info.cloned().unwrap_or_default(),
    );
    if call_count < config.min_call_count
        || cost.estimated_code_size_increase > config.max_code_size_increase
        || cost.estimated_speedup_factor < config.min_speedup_factor
        || !cost.is_profitable()
    {
        return Ok(None);
    }
    let decl = build_specialized_decl(original, key)?;
    let total_poly = original
        .params
        .iter()
        .filter(|(_, ty)| *ty == IRType::Object)
        .count();
    Ok(Some((
        decl,
        key.type_args.iter().flatten().count() < total_poly,
    )))
}

fn build_specialized_decl(original: &IRDecl, key: &SpecKey) -> Result<IRDecl, SpecializeExtError> {
    if key.type_args.len() != original.params.len() {
        return Err(SpecializeExtError::ArityMismatch {
            fn_name: key.fn_name.clone(),
            expected: original.params.len(),
            actual: key.type_args.len(),
        });
    }
    let mut param_map = HashMap::<VarId, IRType>::new();
    let params = original
        .params
        .iter()
        .zip(key.type_args.iter())
        .map(|((var, orig_ty), spec_ty)| match (orig_ty, spec_ty) {
            (IRType::Object, Some(ty)) => {
                param_map.insert(*var, ty.clone());
                (*var, ty.clone())
            }
            _ => (*var, orig_ty.clone()),
        })
        .collect();
    if param_map.is_empty() {
        return Err(SpecializeExtError::EmptySpecialization(key.fn_name.clone()));
    }
    Ok(IRDecl {
        name: specialized_name(&key.fn_name, &key.type_args),
        params,
        return_type: original.return_type.clone(),
        body: specialize_body(&original.body, &param_map),
    })
}

fn collect_call_site_info(
    body: &IRBody,
    env: &TypeEnv,
    candidates: &HashSet<Name>,
    originals: &HashMap<Name, IRDecl>,
    config: &SpecializeExtConfig,
    infos: &mut HashMap<Name, CallSiteInfo>,
    counts: &mut HashMap<SpecKey, usize>,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, args } = value {
                if candidates.contains(&fn_id.0) {
                    let pattern: Vec<Option<IRType>> =
                        args.iter().map(|arg| resolve_arg_type(arg, env)).collect();
                    infos
                        .entry(fn_id.0.clone())
                        .or_default()
                        .observe(pattern.clone());
                    if let Some(target) = originals.get(&fn_id.0) {
                        for key in expand_partial_keys(&fn_id.0, &target.params, &pattern, config) {
                            *counts.entry(key).or_insert(0) += 1;
                        }
                    }
                }
            }
            collect_call_site_info(rest, env, candidates, originals, config, infos, counts);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_call_site_info(body, env, candidates, originals, config, infos, counts);
            collect_call_site_info(rest, env, candidates, originals, config, infos, counts);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_call_site_info(rest, env, candidates, originals, config, infos, counts)
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_call_site_info(
                    &alt.body, env, candidates, originals, config, infos, counts,
                );
            }
            if let Some(default) = default {
                collect_call_site_info(default, env, candidates, originals, config, infos, counts);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn expand_partial_keys(
    fn_name: &Name,
    params: &[(VarId, IRType)],
    pattern: &[Option<IRType>],
    config: &SpecializeExtConfig,
) -> Vec<SpecKey> {
    if params.len() != pattern.len() {
        return Vec::new();
    }
    let concrete: Vec<(usize, IRType)> = params
        .iter()
        .zip(pattern.iter())
        .enumerate()
        .filter_map(|(i, ((_, param_ty), arg_ty))| match (param_ty, arg_ty) {
            (IRType::Object, Some(ty)) if is_specializable_concrete_type(ty) => {
                Some((i, ty.clone()))
            }
            _ => None,
        })
        .collect();
    if concrete.is_empty() {
        return Vec::new();
    }
    let max_args = concrete
        .len()
        .min(config.max_specialized_args_per_call.max(1));
    let sizes: Vec<usize> = if config.enable_partial_specialization {
        (1..=max_args).collect()
    } else {
        vec![concrete.len()]
    };
    let mut out = Vec::new();
    for size in sizes {
        let mut picks = Vec::new();
        collect_key_subsets(
            fn_name,
            params.len(),
            &concrete,
            size,
            0,
            &mut picks,
            &mut out,
        );
    }
    out
}

fn collect_key_subsets(
    fn_name: &Name,
    arity: usize,
    concrete: &[(usize, IRType)],
    remaining: usize,
    start: usize,
    picks: &mut Vec<(usize, IRType)>,
    out: &mut Vec<SpecKey>,
) {
    if remaining == 0 {
        let mut type_args = vec![None; arity];
        for (i, ty) in picks.iter() {
            type_args[*i] = Some(ty.clone());
        }
        out.push(SpecKey {
            fn_name: fn_name.clone(),
            type_args,
        });
        return;
    }
    for idx in start..=concrete.len() - remaining {
        picks.push(concrete[idx].clone());
        collect_key_subsets(fn_name, arity, concrete, remaining - 1, idx + 1, picks, out);
        picks.pop();
    }
}

fn estimate_specialization_cost(
    decl: &IRDecl,
    key: &SpecKey,
    call_count: usize,
    info: &CallSiteInfo,
) -> SpecializationCost {
    let specialized = key.type_args.iter().flatten().count();
    let scalar_specialized = key
        .type_args
        .iter()
        .flatten()
        .filter(|ty| ty.is_scalar())
        .count();
    let object_specialized = specialized.saturating_sub(scalar_specialized);
    let complexity = body_complexity(&decl.body);
    let pattern_pressure = info.argument_type_patterns.len().saturating_sub(1);
    SpecializationCost {
        estimated_code_size_increase: (complexity / 4).max(1) * specialized.max(1)
            + pattern_pressure,
        estimated_speedup_factor: 1.0
            + scalar_specialized as f64 * 0.35
            + object_specialized as f64 * 0.12
            + call_count.min(info.call_count.max(1)) as f64 * 0.03,
    }
}

fn body_complexity(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { value, rest, .. } => 1 + expr_complexity(value) + body_complexity(rest),
        IRBody::JDecl { body, rest, .. } => 1 + body_complexity(body) + body_complexity(rest),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + body_complexity(rest),
        IRBody::Case { alts, default, .. } => {
            1 + alts
                .iter()
                .map(|alt| body_complexity(&alt.body))
                .sum::<usize>()
                + default.as_deref().map_or(0, body_complexity)
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}
fn expr_complexity(expr: &IRExpr) -> usize {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. }
        | IRExpr::ClosureApply { args, .. }
        | IRExpr::Reuse { args, .. } => 1 + args.len(),
        _ => 1,
    }
}
fn is_specializable_concrete_type(ty: &IRType) -> bool {
    !matches!(ty, IRType::Object | IRType::Erased | IRType::Void)
}

fn rewrite_decl_calls(decl: &IRDecl, rewrites: &HashMap<SpecKey, Name>) -> (IRDecl, bool) {
    let env = build_type_env(decl);
    let (body, changed) = rewrite_body_calls(&decl.body, &env, rewrites);
    (
        IRDecl {
            name: decl.name.clone(),
            params: decl.params.clone(),
            return_type: decl.return_type.clone(),
            body,
        },
        changed,
    )
}

fn rewrite_body_calls(
    body: &IRBody,
    env: &TypeEnv,
    rewrites: &HashMap<SpecKey, Name>,
) -> (IRBody, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (value, c1) = rewrite_expr_call(value, env, rewrites);
            let (rest, c2) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value,
                    rest: Box::new(rest),
                },
                c1 || c2,
            )
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            let (body, c1) = rewrite_body_calls(body, env, rewrites);
            let (rest, c2) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::JDecl {
                    jp: *jp,
                    params: params.clone(),
                    body: Box::new(body),
                    rest: Box::new(rest),
                },
                c1 || c2,
            )
        }
        IRBody::Inc { var, n, rest } => {
            let (rest, changed) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(rest),
                },
                changed,
            )
        }
        IRBody::Dec { var, rest } => {
            let (rest, changed) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(rest),
                },
                changed,
            )
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, changed) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::Set {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                changed,
            )
        }
        IRBody::SetTag { var, tag, rest } => {
            let (rest, changed) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::SetTag {
                    var: *var,
                    tag: *tag,
                    rest: Box::new(rest),
                },
                changed,
            )
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, changed) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::USet {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                changed,
            )
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => {
            let (rest, changed) = rewrite_body_calls(rest, env, rewrites);
            (
                IRBody::SSet {
                    var: *var,
                    n: *n,
                    offset: *offset,
                    value: *value,
                    ty: ty.clone(),
                    rest: Box::new(rest),
                },
                changed,
            )
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let mut changed = false;
            let alts: Vec<IRAlt> = alts
                .iter()
                .map(|alt| {
                    let (body, c) = rewrite_body_calls(&alt.body, env, rewrites);
                    changed |= c;
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(body),
                    }
                })
                .collect();
            let default = if let Some(default) = default {
                let (body, c) = rewrite_body_calls(default, env, rewrites);
                changed |= c;
                Some(Box::new(body))
            } else {
                None
            };
            (
                IRBody::Case {
                    scrutinee: *scrutinee,
                    alts,
                    default,
                },
                changed,
            )
        }
        IRBody::Jmp { jp, args } => (
            IRBody::Jmp {
                jp: *jp,
                args: args.clone(),
            },
            false,
        ),
        IRBody::Ret(arg) => (IRBody::Ret(arg.clone()), false),
        IRBody::Unreachable => (IRBody::Unreachable, false),
    }
}

fn rewrite_expr_call(
    expr: &IRExpr,
    env: &TypeEnv,
    rewrites: &HashMap<SpecKey, Name>,
) -> (IRExpr, bool) {
    if let IRExpr::Apply { fn_id, args } = expr {
        if let Some(name) = best_specialized_target(fn_id, args, env, rewrites) {
            return (
                IRExpr::Apply {
                    fn_id: FnId(name),
                    args: args.clone(),
                },
                true,
            );
        }
    }
    (expr.clone(), false)
}

fn best_specialized_target(
    fn_id: &FnId,
    args: &[IRArg],
    env: &TypeEnv,
    rewrites: &HashMap<SpecKey, Name>,
) -> Option<Name> {
    let resolved: Vec<Option<IRType>> = args.iter().map(|arg| resolve_arg_type(arg, env)).collect();
    let mut best: Option<(usize, String, Name)> = None;
    for (key, name) in rewrites {
        if key.fn_name != fn_id.0 || key.type_args.len() != resolved.len() {
            continue;
        }
        let mut matches = true;
        for (want, have) in key.type_args.iter().zip(resolved.iter()) {
            if let Some(want_ty) = want {
                if have.as_ref() != Some(want_ty) {
                    matches = false;
                    break;
                }
            }
        }
        if matches {
            let rank = key.type_args.iter().flatten().count();
            let tie = format!("{:?}", name);
            match &best {
                Some((best_rank, best_tie, _))
                    if *best_rank > rank || (*best_rank == rank && best_tie <= &tie) => {}
                _ => best = Some((rank, tie, name.clone())),
            }
        }
    }
    best.map(|(_, _, name)| name)
}
