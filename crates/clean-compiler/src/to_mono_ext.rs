// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended monomorphization for the Lean 5 compiler.
//!
//! Aggressive type erasure, monomorphization specialization, type class evidence
//! erasure, erased type representation, caching, recursive type handling,
//! statistics tracking, and polymorphic closure handling.
//!
//! Part of #3083 — Extensibility: Lean 4 replacement compiler infrastructure.

use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

/// Configuration for extended monomorphization.
#[derive(Debug, Clone)]
pub(crate) struct MonoExtConfig {
    pub(crate) max_specializations_per_fn: usize,
    pub(crate) max_total_specializations: usize,
    pub(crate) max_recursion_depth: usize,
    pub(crate) erase_type_class_evidence: bool,
    pub(crate) monomorphize_closures: bool,
}

impl Default for MonoExtConfig {
    fn default() -> Self {
        Self {
            max_specializations_per_fn: 8,
            max_total_specializations: 256,
            max_recursion_depth: 16,
            erase_type_class_evidence: true,
            monomorphize_closures: true,
        }
    }
}

/// Statistics from extended monomorphization.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct MonoExtStats {
    pub(crate) types_erased: usize,
    pub(crate) specializations_created: usize,
    pub(crate) cache_hits: usize,
    pub(crate) evidence_erased: usize,
    pub(crate) closures_monomorphized: usize,
    pub(crate) recursive_truncations: usize,
    pub(crate) decls_processed: usize,
    pub(crate) decls_rewritten: usize,
}

/// Unique key for a monomorphized instance.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct MonoKey {
    pub(crate) fn_name: Name,
    pub(crate) type_args: Vec<IRType>,
}

/// Cache for monomorphized function instances.
#[derive(Clone, Debug, Default)]
pub(crate) struct MonoCache {
    entries: HashMap<MonoKey, Name>,
}

impl MonoCache {
    pub(crate) fn get(&self, key: &MonoKey) -> Option<&Name> {
        self.entries.get(key)
    }
    pub(crate) fn insert(&mut self, key: MonoKey, name: Name) {
        self.entries.insert(key, name);
    }
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Type Erasure
// ═══════════════════════════════════════════════════════════════════════════

/// Check if a parameter represents type class evidence (dictionary).
pub(crate) fn is_type_class_evidence(name: &Name, ty: &IRType) -> bool {
    if *ty != IRType::Object {
        return false;
    }
    let s = format!("{name:?}");
    s.contains("_inst") || s.contains("_tc") || s.contains("_dict")
}

/// Erase type arguments from a parameter list. Returns (params, erased_count).
pub(crate) fn erase_type_args(
    params: &[(VarId, IRType)],
    fn_name: &Name,
    erase_evidence: bool,
) -> (Vec<(VarId, IRType)>, usize) {
    let mut erased_count = 0;
    let result = params
        .iter()
        .map(|(var, ty)| {
            if *ty == IRType::Erased || *ty == IRType::Void {
                erased_count += 1;
                (*var, IRType::Object)
            } else if erase_evidence && is_type_class_evidence(fn_name, ty) {
                erased_count += 1;
                (*var, IRType::Erased)
            } else {
                (*var, ty.clone())
            }
        })
        .collect();
    (result, erased_count)
}

/// Map erased IR types to `Object` for uniform runtime representation.
pub(crate) fn erased_type_repr(ty: &IRType) -> IRType {
    match ty {
        IRType::Erased | IRType::Void => IRType::Object,
        IRType::Struct(f) => IRType::Struct(f.iter().map(erased_type_repr).collect()),
        IRType::Union(v) => IRType::Union(v.iter().map(erased_type_repr).collect()),
        other => other.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Recursive Type Tracking
// ═══════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug, Default)]
pub(crate) struct RecursionTracker {
    expanding: HashMap<Name, usize>,
}

impl RecursionTracker {
    pub(crate) fn enter(&mut self, name: &Name, max_depth: usize) -> bool {
        let depth = self.expanding.entry(name.clone()).or_insert(0);
        if *depth >= max_depth {
            return false;
        }
        *depth += 1;
        true
    }
    pub(crate) fn leave(&mut self, name: &Name) {
        if let Some(d) = self.expanding.get_mut(name) {
            *d = d.saturating_sub(1);
            if *d == 0 {
                self.expanding.remove(name);
            }
        }
    }
    pub(crate) fn is_expanding(&self, name: &Name) -> bool {
        self.expanding.get(name).copied().unwrap_or(0) > 0
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Specialization
// ═══════════════════════════════════════════════════════════════════════════

/// Build a specialized name by appending type suffixes.
pub(crate) fn mono_specialized_name(base: &Name, types: &[IRType]) -> Name {
    let suffix: String = types
        .iter()
        .map(|ty| match ty {
            IRType::Bool => "_b",
            IRType::UInt8 => "_u8",
            IRType::UInt16 => "_u16",
            IRType::UInt32 => "_u32",
            IRType::UInt64 => "_u64",
            IRType::USize => "_us",
            IRType::Float32 => "_f32",
            IRType::Float64 => "_f64",
            IRType::Object => "_o",
            IRType::TObject => "_to",
            IRType::Erased => "_e",
            IRType::Void => "_v",
            IRType::Struct(_) => "_s",
            IRType::Union(_) => "_un",
        })
        .collect();
    Name::append(base, &format!("_mono{suffix}"))
}

/// Create a specialized copy of a declaration with concrete types substituted.
pub(crate) fn specialize_decl(original: &IRDecl, concrete: &[IRType]) -> Option<IRDecl> {
    if concrete.len() != original.params.len() {
        return None;
    }
    let mut type_map: HashMap<VarId, IRType> = HashMap::new();
    let params: Vec<_> = original
        .params
        .iter()
        .zip(concrete.iter())
        .map(|((v, orig), c)| {
            if *orig == IRType::Object && *c != IRType::Object {
                type_map.insert(*v, c.clone());
                (*v, c.clone())
            } else {
                (*v, orig.clone())
            }
        })
        .collect();
    if type_map.is_empty() {
        return None;
    }
    Some(IRDecl {
        name: mono_specialized_name(&original.name, concrete),
        params,
        return_type: original.return_type.clone(),
        body: subst_body(&original.body, &type_map),
    })
}

fn subst_body(body: &IRBody, m: &HashMap<VarId, IRType>) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: m.get(var).cloned().unwrap_or_else(|| ty.clone()),
            value: subst_expr(value, m),
            rest: Box::new(subst_body(rest, m)),
        },
        IRBody::JDecl {
            jp,
            params,
            body: jb,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params
                .iter()
                .map(|(v, t)| (*v, m.get(v).cloned().unwrap_or_else(|| t.clone())))
                .collect(),
            body: Box::new(subst_body(jb, m)),
            rest: Box::new(subst_body(rest, m)),
        },
        _ => map_body_rest(body, |r| subst_body(r, m)),
    }
}

fn subst_expr(expr: &IRExpr, m: &HashMap<VarId, IRType>) -> IRExpr {
    let resolve = |arg: &IRArg, ty: &IRType| -> IRType {
        if let IRArg::Var(v) = arg {
            m.get(v).cloned().unwrap_or_else(|| ty.clone())
        } else {
            ty.clone()
        }
    };
    match expr {
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: resolve(arg, ty),
            arg: arg.clone(),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: resolve(arg, ty),
            arg: arg.clone(),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: resolve(arg, ty),
            arg: arg.clone(),
        },
        other => other.clone(),
    }
}

/// Structural traversal helper: recursively transform the "rest" continuation.
fn map_body_rest(body: &IRBody, f: impl Fn(&IRBody) -> IRBody) -> IRBody {
    match body {
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(f(rest)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(f(rest)),
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
            rest: Box::new(f(rest)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(f(rest)),
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
            rest: Box::new(f(rest)),
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
            rest: Box::new(f(rest)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: *scrutinee,
            alts: alts
                .iter()
                .map(|alt| IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(f(&alt.body)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(f(d))),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
        // VDecl and JDecl handled by callers directly.
        IRBody::VDecl { .. } | IRBody::JDecl { .. } => body.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Closure Monomorphization
// ═══════════════════════════════════════════════════════════════════════════

pub(crate) fn collect_closure_type_captures(
    body: &IRBody,
    var_types: &HashMap<VarId, IRType>,
) -> HashMap<VarId, IRType> {
    let mut captures = HashMap::new();
    closure_caps_inner(body, var_types, &mut captures);
    captures
}

fn closure_caps_inner(
    body: &IRBody,
    vt: &HashMap<VarId, IRType>,
    caps: &mut HashMap<VarId, IRType>,
) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::PartialApply { args, .. } | IRExpr::ClosureApply { args, .. } = value {
                for arg in args {
                    if let IRArg::Var(v) = arg {
                        if let Some(c) = vt.get(v) {
                            if c.is_scalar() {
                                caps.insert(*v, c.clone());
                            }
                        }
                    }
                }
            }
            let mut vt2 = vt.clone();
            vt2.insert(*var, ty.clone());
            closure_caps_inner(rest, &vt2, caps);
        }
        IRBody::JDecl { body: jb, rest, .. } => {
            closure_caps_inner(jb, vt, caps);
            closure_caps_inner(rest, vt, caps);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                closure_caps_inner(&a.body, vt, caps);
            }
            if let Some(d) = default {
                closure_caps_inner(d, vt, caps);
            }
        }
        _ => {
            if let Some(r) = body_rest(body) {
                closure_caps_inner(r, vt, caps);
            }
        }
    }
}

/// Extract the `rest` continuation from single-continuation body variants.
fn body_rest(body: &IRBody) -> Option<&IRBody> {
    match body {
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => Some(rest),
        _ => None,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Top-Level Entry Point
// ═══════════════════════════════════════════════════════════════════════════

#[must_use]
pub(crate) fn run_mono_ext(
    decls: &[IRDecl],
    config: &MonoExtConfig,
) -> (Vec<IRDecl>, MonoExtStats) {
    let mut stats = MonoExtStats::default();
    let mut cache = MonoCache::default();
    let mut recursion = RecursionTracker::default();
    let mut generated: Vec<IRDecl> = Vec::new();
    let mut per_fn_count: HashMap<Name, usize> = HashMap::new();
    let decl_index: HashMap<Name, &IRDecl> = decls.iter().map(|d| (d.name.clone(), d)).collect();

    // Phase 1: Erase types, collect specialization sites.
    let mut processed: Vec<IRDecl> = Vec::with_capacity(decls.len());
    let mut call_site_types: HashMap<Name, Vec<Vec<IRType>>> = HashMap::new();

    for decl in decls {
        stats.decls_processed += 1;
        let (erased_params, erase_count) =
            erase_type_args(&decl.params, &decl.name, config.erase_type_class_evidence);
        stats.types_erased += erase_count;
        let return_type = erased_type_repr(&decl.return_type);
        if config.monomorphize_closures {
            let vt: HashMap<VarId, IRType> =
                erased_params.iter().map(|(v, t)| (*v, t.clone())).collect();
            stats.closures_monomorphized += collect_closure_type_captures(&decl.body, &vt).len();
        }
        collect_call_types(&decl.body, &decl_index, &mut call_site_types);
        processed.push(IRDecl {
            name: decl.name.clone(),
            params: erased_params,
            return_type,
            body: decl.body.clone(),
        });
    }

    // Phase 2: Create specializations.
    for (fn_name, patterns) in &call_site_types {
        let Some(original) = decl_index.get(fn_name) else {
            continue;
        };
        let mut seen: HashSet<Vec<IRType>> = HashSet::new();
        for pattern in patterns {
            if !seen.insert(pattern.clone()) {
                continue;
            }
            let key = MonoKey {
                fn_name: fn_name.clone(),
                type_args: pattern.clone(),
            };
            if cache.get(&key).is_some() {
                stats.cache_hits += 1;
                continue;
            }
            let fc = per_fn_count.entry(fn_name.clone()).or_insert(0);
            if *fc >= config.max_specializations_per_fn
                || cache.len() >= config.max_total_specializations
            {
                continue;
            }
            if !recursion.enter(fn_name, config.max_recursion_depth) {
                stats.recursive_truncations += 1;
                continue;
            }
            if let Some(sd) = specialize_decl(original, pattern) {
                cache.insert(key, sd.name.clone());
                *fc += 1;
                generated.push(sd);
                stats.specializations_created += 1;
            }
            recursion.leave(fn_name);
        }
    }

    // Phase 3: Rewrite call sites to use specialized versions.
    let rewrites = cache.entries.clone();
    let result: Vec<IRDecl> = processed
        .iter()
        .chain(generated.iter())
        .map(|decl| {
            let vt: HashMap<VarId, IRType> =
                decl.params.iter().map(|(v, t)| (*v, t.clone())).collect();
            let (new_body, changed) = rewrite_calls(&decl.body, &vt, &rewrites);
            if changed {
                stats.decls_rewritten += 1;
            }
            IRDecl {
                name: decl.name.clone(),
                params: decl.params.clone(),
                return_type: decl.return_type.clone(),
                body: new_body,
            }
        })
        .collect();

    (result, stats)
}

#[must_use]
pub(crate) fn run_mono_ext_default(decls: &[IRDecl]) -> Vec<IRDecl> {
    run_mono_ext(decls, &MonoExtConfig::default()).0
}

// ═══════════════════════════════════════════════════════════════════════════
// Call Site Collection & Rewriting
// ═══════════════════════════════════════════════════════════════════════════

fn collect_call_types(
    body: &IRBody,
    idx: &HashMap<Name, &IRDecl>,
    sites: &mut HashMap<Name, Vec<Vec<IRType>>>,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, args } = value {
                if idx.contains_key(&fn_id.0) {
                    let types: Vec<IRType> = args
                        .iter()
                        .map(|a| match a {
                            IRArg::Var(_) => IRType::Object,
                            IRArg::Erased => IRType::Erased,
                        })
                        .collect();
                    if types.iter().any(|t| *t != IRType::Object) {
                        sites.entry(fn_id.0.clone()).or_default().push(types);
                    }
                }
            }
            collect_call_types(rest, idx, sites);
        }
        IRBody::JDecl { body: jb, rest, .. } => {
            collect_call_types(jb, idx, sites);
            collect_call_types(rest, idx, sites);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                collect_call_types(&a.body, idx, sites);
            }
            if let Some(d) = default {
                collect_call_types(d, idx, sites);
            }
        }
        _ => {
            if let Some(r) = body_rest(body) {
                collect_call_types(r, idx, sites);
            }
        }
    }
}

fn rewrite_calls(
    body: &IRBody,
    vt: &HashMap<VarId, IRType>,
    rw: &HashMap<MonoKey, Name>,
) -> (IRBody, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (nv, c1) = rewrite_expr(value, vt, rw);
            let mut vt2 = vt.clone();
            vt2.insert(*var, ty.clone());
            let (nr, c2) = rewrite_calls(rest, &vt2, rw);
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: nv,
                    rest: Box::new(nr),
                },
                c1 || c2,
            )
        }
        IRBody::JDecl {
            jp,
            params,
            body: jb,
            rest,
        } => {
            let (b, c1) = rewrite_calls(jb, vt, rw);
            let (r, c2) = rewrite_calls(rest, vt, rw);
            (
                IRBody::JDecl {
                    jp: *jp,
                    params: params.clone(),
                    body: Box::new(b),
                    rest: Box::new(r),
                },
                c1 || c2,
            )
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let mut changed = false;
            let na: Vec<_> = alts
                .iter()
                .map(|a| {
                    let (b, c) = rewrite_calls(&a.body, vt, rw);
                    changed |= c;
                    IRAlt {
                        ctor: a.ctor.clone(),
                        body: Box::new(b),
                    }
                })
                .collect();
            let nd = default.as_ref().map(|d| {
                let (b, c) = rewrite_calls(d, vt, rw);
                changed |= c;
                Box::new(b)
            });
            (
                IRBody::Case {
                    scrutinee: *scrutinee,
                    alts: na,
                    default: nd,
                },
                changed,
            )
        }
        _ => {
            if let Some(r) = body_rest(body) {
                let (nr, c) = rewrite_calls(r, vt, rw);
                (set_body_rest(body, nr), c)
            } else {
                (body.clone(), false)
            }
        }
    }
}

/// Reconstruct a single-continuation body with a new `rest`.
fn set_body_rest(body: &IRBody, new_rest: IRBody) -> IRBody {
    let r = Box::new(new_rest);
    match body {
        IRBody::Inc { var, n, .. } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: r,
        },
        IRBody::Dec { var, .. } => IRBody::Dec { var: *var, rest: r },
        IRBody::Set {
            var, idx, value, ..
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: r,
        },
        IRBody::SetTag { var, tag, .. } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: r,
        },
        IRBody::USet {
            var, idx, value, ..
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: r,
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            ..
        } => IRBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: r,
        },
        _ => body.clone(),
    }
}

fn rewrite_expr(
    expr: &IRExpr,
    vt: &HashMap<VarId, IRType>,
    rw: &HashMap<MonoKey, Name>,
) -> (IRExpr, bool) {
    if let IRExpr::Apply { fn_id, args } = expr {
        let resolved: Vec<IRType> = args
            .iter()
            .map(|a| match a {
                IRArg::Var(v) => vt.get(v).cloned().unwrap_or(IRType::Object),
                IRArg::Erased => IRType::Erased,
            })
            .collect();
        let key = MonoKey {
            fn_name: fn_id.0.clone(),
            type_args: resolved,
        };
        if let Some(sn) = rw.get(&key) {
            return (
                IRExpr::Apply {
                    fn_id: FnId(sn.clone()),
                    args: args.clone(),
                },
                true,
            );
        }
    }
    (expr.clone(), false)
}
