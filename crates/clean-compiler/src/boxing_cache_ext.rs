// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended boxing cache: type-aware decisions, elimination, layout analysis.
//!
//! Part of #3083 - Compiler extensibility infrastructure.

use std::collections::HashMap;

use clean_kernel::Name;

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};

// -- Boxing decision ---------------------------------------------------------

/// Cached decision about whether a type needs boxing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BoxingDecision {
    Unboxed,
    Boxed,
    Absent,
}

/// Type-aware boxing decision cache keyed by [`IRType`].
#[derive(Clone, Debug, Default)]
pub(crate) struct BoxingDecisionCache {
    decisions: HashMap<IRType, BoxingDecision>,
    hits: u64,
    misses: u64,
}

impl BoxingDecisionCache {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn decide(&mut self, ty: &IRType) -> &BoxingDecision {
        if self.decisions.contains_key(ty) {
            self.hits += 1;
            return &self.decisions[ty];
        }
        self.misses += 1;
        let d = match ty {
            IRType::Erased | IRType::Void => BoxingDecision::Absent,
            t if t.is_scalar() => BoxingDecision::Unboxed,
            _ => BoxingDecision::Boxed,
        };
        self.decisions.entry(ty.clone()).or_insert(d)
    }

    #[must_use]
    pub(crate) fn hits(&self) -> u64 {
        self.hits
    }
    #[must_use]
    pub(crate) fn misses(&self) -> u64 {
        self.misses
    }
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.decisions.len()
    }
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.decisions.is_empty()
    }

    pub(crate) fn invalidate_all(&mut self) {
        self.decisions.clear();
        self.hits = 0;
        self.misses = 0;
    }

    pub(crate) fn invalidate(&mut self, ty: &IRType) {
        self.decisions.remove(ty);
    }
}

// -- Scalar classification ---------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ScalarClass {
    Integer,
    Float,
    NonScalar,
}

#[must_use]
pub(crate) fn classify_scalar(ty: &IRType) -> ScalarClass {
    match ty {
        IRType::Bool
        | IRType::UInt8
        | IRType::UInt16
        | IRType::UInt32
        | IRType::UInt64
        | IRType::USize => ScalarClass::Integer,
        IRType::Float32 | IRType::Float64 => ScalarClass::Float,
        _ => ScalarClass::NonScalar,
    }
}

#[must_use]
pub(crate) fn is_unboxable(ty: &IRType) -> bool {
    ty.is_scalar() || matches!(ty, IRType::Erased | IRType::Void)
}

// -- Structure layout analysis -----------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum StructLayout {
    Flat { total_bytes: u32 },
    HeapAllocated,
    Empty,
}

#[must_use]
pub(crate) fn analyze_struct_layout(fields: &[IRType]) -> StructLayout {
    if fields.is_empty() {
        return StructLayout::Empty;
    }
    let mut total = 0u32;
    for f in fields {
        if !f.is_scalar() {
            return StructLayout::HeapAllocated;
        }
        total = total.saturating_add(f.scalar_byte_size());
    }
    StructLayout::Flat { total_bytes: total }
}

// -- Unboxing opportunity detection ------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UnboxOpportunity {
    pub(crate) var: VarId,
    pub(crate) original_ty: IRType,
    pub(crate) reason: UnboxReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum UnboxReason {
    ScalarOnly,
    RedundantBoxUnbox,
    CalleeAcceptsUnboxed,
}

#[must_use]
pub(crate) fn detect_unbox_opportunities(decl: &IRDecl) -> Vec<UnboxOpportunity> {
    let mut opps = Vec::new();
    let mut boxed: HashMap<VarId, IRType> = HashMap::new();
    detect_opp_inner(&decl.body, &mut boxed, &mut opps);
    opps
}

fn detect_opp_inner(
    body: &IRBody,
    boxed: &mut HashMap<VarId, IRType>,
    opps: &mut Vec<UnboxOpportunity>,
) {
    if let IRBody::VDecl { var, value, .. } = body {
        if let IRExpr::Box { ty, .. } = value {
            boxed.insert(*var, ty.clone());
        }
        if let IRExpr::Unbox {
            ty,
            arg: IRArg::Var(src),
        } = value
        {
            if boxed.get(src) == Some(ty) {
                opps.push(UnboxOpportunity {
                    var: *src,
                    original_ty: ty.clone(),
                    reason: UnboxReason::RedundantBoxUnbox,
                });
            }
        }
    }
    for_each_child(body, |c| detect_opp_inner(c, boxed, opps));
}

// -- Boxing coercion detection -----------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Coercion {
    BoxAt { var: VarId, ty: IRType },
    UnboxAt { var: VarId, ty: IRType },
}

#[must_use]
pub(crate) fn detect_coercions(decls: &[IRDecl]) -> Vec<Coercion> {
    let sigs: HashMap<&Name, &IRDecl> = decls.iter().map(|d| (&d.name, d)).collect();
    let mut out = Vec::new();
    for decl in decls {
        detect_coerce_body(&decl.body, &sigs, &mut out);
    }
    out
}

fn detect_coerce_body(body: &IRBody, sigs: &HashMap<&Name, &IRDecl>, out: &mut Vec<Coercion>) {
    if let IRBody::VDecl {
        value: IRExpr::Apply { fn_id, args },
        ..
    } = body
    {
        if let Some(callee) = sigs.get(&fn_id.0) {
            for (i, arg) in args.iter().enumerate() {
                if let (Some((_, expected)), IRArg::Var(v)) = (callee.params.get(i), arg) {
                    if expected.is_object() {
                        out.push(Coercion::BoxAt {
                            var: *v,
                            ty: expected.clone(),
                        });
                    } else if expected.is_scalar() {
                        out.push(Coercion::UnboxAt {
                            var: *v,
                            ty: expected.clone(),
                        });
                    }
                }
            }
        }
    }
    for_each_child(body, |c| detect_coerce_body(c, sigs, out));
}

// -- Boxing through function boundaries --------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FnBoxingSig {
    pub(crate) fn_id: FnId,
    pub(crate) param_boxed: Vec<bool>,
    pub(crate) return_boxed: bool,
}

#[must_use]
pub(crate) fn build_fn_boxing_sigs(decls: &[IRDecl]) -> Vec<FnBoxingSig> {
    decls
        .iter()
        .map(|d| FnBoxingSig {
            fn_id: FnId(d.name.clone()),
            param_boxed: d.params.iter().map(|(_, ty)| ty.is_object()).collect(),
            return_boxed: d.return_type.is_object(),
        })
        .collect()
}

/// Propagate boxing requirements across call boundaries. Returns `true` if changed.
pub(crate) fn propagate_fn_boxing(decls: &[IRDecl], sigs: &mut [FnBoxingSig]) -> bool {
    let index: HashMap<Name, usize> = sigs
        .iter()
        .enumerate()
        .map(|(i, s)| (s.fn_id.0.clone(), i))
        .collect();
    let mut changed = false;
    for decl in decls {
        if let Some(&ci) = index.get(&decl.name) {
            prop_sig_body(&decl.body, &decl.params, &index, sigs, ci, &mut changed);
        }
    }
    changed
}

fn prop_sig_body(
    body: &IRBody,
    params: &[(VarId, IRType)],
    idx: &HashMap<Name, usize>,
    sigs: &mut [FnBoxingSig],
    ci: usize,
    changed: &mut bool,
) {
    if let IRBody::VDecl {
        value: IRExpr::Apply { fn_id, args },
        ..
    } = body
    {
        if let Some(&callee) = idx.get(&fn_id.0) {
            for (i, arg) in args.iter().enumerate() {
                if i < sigs[callee].param_boxed.len() && sigs[callee].param_boxed[i] {
                    if let IRArg::Var(v) = arg {
                        if let Some(pi) = params.iter().position(|(pv, _)| pv == v) {
                            if !sigs[ci].param_boxed[pi] {
                                sigs[ci].param_boxed[pi] = true;
                                *changed = true;
                            }
                        }
                    }
                }
            }
        }
    }
    for_each_child(body, |c| prop_sig_body(c, params, idx, sigs, ci, changed));
}

// -- Polymorphic boxing ------------------------------------------------------

#[must_use]
pub(crate) fn resolve_polymorphic_type(ty: &IRType) -> IRType {
    match ty {
        IRType::Erased => IRType::Object,
        IRType::Void => IRType::Void,
        other if other.is_scalar() => other.boxed(),
        other => other.clone(),
    }
}

#[must_use]
pub(crate) fn count_polymorphic_params(decl: &IRDecl) -> usize {
    decl.params
        .iter()
        .filter(|(_, ty)| matches!(ty, IRType::Erased))
        .count()
}

// -- Boxing elimination ------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct EliminationResult {
    pub(crate) pairs_eliminated: u32,
}

#[must_use]
pub(crate) fn eliminate_boxing_pairs(body: &IRBody) -> (IRBody, EliminationResult) {
    let mut boxed: HashMap<VarId, (IRType, IRArg)> = HashMap::new();
    let mut r = EliminationResult::default();
    let b = elim_inner(body, &mut boxed, &mut r);
    (b, r)
}

fn elim_inner(
    body: &IRBody,
    boxed: &mut HashMap<VarId, (IRType, IRArg)>,
    r: &mut EliminationResult,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::Box { ty: bt, arg: ba } = value {
                boxed.insert(*var, (bt.clone(), ba.clone()));
            }
            let nv = if let IRExpr::Unbox {
                ty: ut,
                arg: IRArg::Var(src),
            } = value
            {
                boxed.get(src).and_then(|(bt, orig)| {
                    if bt == ut {
                        if let IRArg::Var(ov) = orig {
                            r.pairs_eliminated += 1;
                            Some(IRExpr::Unbox {
                                ty: ut.clone(),
                                arg: IRArg::Var(*ov),
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
            } else {
                None
            };
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: nv.unwrap_or_else(|| value.clone()),
                rest: Box::new(elim_inner(rest, boxed, r)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jb,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(elim_inner(jb, boxed, r)),
            rest: Box::new(elim_inner(rest, boxed, r)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(elim_inner(rest, boxed, r)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(elim_inner(rest, boxed, r)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: *scrutinee,
            alts: alts
                .iter()
                .map(|a| crate::ir::IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(elim_inner(&a.body, boxed, r)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(elim_inner(d, boxed, r))),
        },
        other => other.clone(),
    }
}

// -- Cache invalidation / signature tracker ----------------------------------

#[derive(Clone, Debug, Default)]
pub(crate) struct SignatureTracker {
    sigs: HashMap<Name, (Vec<IRType>, IRType)>,
}

impl SignatureTracker {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn record(&mut self, decl: &IRDecl) {
        let pts: Vec<IRType> = decl.params.iter().map(|(_, ty)| ty.clone()).collect();
        self.sigs
            .insert(decl.name.clone(), (pts, decl.return_type.clone()));
    }

    #[must_use]
    pub(crate) fn has_changed(&self, decl: &IRDecl) -> bool {
        match self.sigs.get(&decl.name) {
            None => true,
            Some((ps, ret)) => {
                let cur: Vec<&IRType> = decl.params.iter().map(|(_, ty)| ty).collect();
                let stored: Vec<&IRType> = ps.iter().collect();
                cur != stored || *ret != decl.return_type
            }
        }
    }

    #[must_use]
    pub(crate) fn tracked_names(&self) -> Vec<&Name> {
        self.sigs.keys().collect()
    }
    pub(crate) fn clear(&mut self) {
        self.sigs.clear();
    }
}

// -- Statistics --------------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct BoxingCacheExtStats {
    pub(crate) decisions_cached: u64,
    pub(crate) cache_hits: u64,
    pub(crate) cache_misses: u64,
    pub(crate) pairs_eliminated: u32,
    pub(crate) coercions_detected: u32,
    pub(crate) unbox_opportunities: u32,
    pub(crate) polymorphic_params: u32,
    pub(crate) flat_structs: u32,
    pub(crate) heap_structs: u32,
}

impl BoxingCacheExtStats {
    #[must_use]
    pub(crate) fn summary(&self) -> String {
        format!(
            "cached={} hits={} misses={} elim={} coerce={} unbox_opp={} poly={} flat={} heap={}",
            self.decisions_cached,
            self.cache_hits,
            self.cache_misses,
            self.pairs_eliminated,
            self.coercions_detected,
            self.unbox_opportunities,
            self.polymorphic_params,
            self.flat_structs,
            self.heap_structs
        )
    }
}

#[must_use]
pub(crate) fn collect_ext_stats(decls: &[IRDecl]) -> BoxingCacheExtStats {
    let mut cache = BoxingDecisionCache::new();
    let mut stats = BoxingCacheExtStats::default();
    for decl in decls {
        for (_, ty) in &decl.params {
            let _ = cache.decide(ty);
        }
        let _ = cache.decide(&decl.return_type);
    }
    stats.decisions_cached = cache.len() as u64;
    stats.cache_hits = cache.hits();
    stats.cache_misses = cache.misses();
    for decl in decls {
        stats.pairs_eliminated += eliminate_boxing_pairs(&decl.body).1.pairs_eliminated;
    }
    stats.coercions_detected = detect_coercions(decls).len() as u32;
    for decl in decls {
        stats.unbox_opportunities += detect_unbox_opportunities(decl).len() as u32;
    }
    for decl in decls {
        stats.polymorphic_params += count_polymorphic_params(decl) as u32;
    }
    for decl in decls {
        count_struct_layouts(&decl.body, &mut stats);
        for (_, ty) in &decl.params {
            if let IRType::Struct(fields) = ty {
                match analyze_struct_layout(fields) {
                    StructLayout::Flat { .. } => stats.flat_structs += 1,
                    StructLayout::HeapAllocated => stats.heap_structs += 1,
                    StructLayout::Empty => {}
                }
            }
        }
    }
    stats
}

fn count_struct_layouts(body: &IRBody, stats: &mut BoxingCacheExtStats) {
    if let IRBody::VDecl {
        ty: IRType::Struct(fields),
        ..
    } = body
    {
        match analyze_struct_layout(fields) {
            StructLayout::Flat { .. } => stats.flat_structs += 1,
            StructLayout::HeapAllocated => stats.heap_structs += 1,
            StructLayout::Empty => {}
        }
    }
    for_each_child(body, |c| count_struct_layouts(c, stats));
}

// -- Utility -----------------------------------------------------------------

fn for_each_child(body: &IRBody, mut f: impl FnMut(&IRBody)) {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => f(rest),
        IRBody::JDecl { body, rest, .. } => {
            f(body);
            f(rest);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                f(&alt.body);
            }
            if let Some(d) = default {
                f(d);
            }
        }
        IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => {}
    }
}
