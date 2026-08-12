// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Reset/Reuse Memory Optimization for L5IR
//!
//! Extends the basic reset/reuse pass with multi-reset (multiple case-
//! destructured objects can each contribute a reset slot), partial reuse
//! (over-allocation is acceptable), reuse distance tracking, and field-
//! liveness filtering.
//!
//! Reference: Ullrich & de Moura, "Counting Immutable Beans", IFL 2020, S4.4.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{CtorInfo, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use std::collections::HashSet;

/// Configuration for the extended reset/reuse optimization.
#[derive(Clone, Debug)]
pub(crate) struct ResetReuseExtConfig {
    /// Max IR nodes between reset candidate and allocation site.
    pub(crate) max_reuse_distance: usize,
    /// Allow multiple reset slots per Case (one per arm).
    pub(crate) enable_multi_reset: bool,
    /// Allow reuse when source is strictly larger than target.
    pub(crate) enable_partial_reuse: bool,
    /// Reject candidates whose projected fields are still live at alloc site.
    pub(crate) track_field_liveness: bool,
}

impl Default for ResetReuseExtConfig {
    fn default() -> Self {
        Self {
            max_reuse_distance: 5,
            enable_multi_reset: true,
            enable_partial_reuse: true,
            track_field_liveness: true,
        }
    }
}

/// Statistics from an extended reset/reuse pass.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ResetReuseExtStats {
    pub(crate) resets_inserted: usize,
    pub(crate) reuses_inserted: usize,
    pub(crate) multi_resets: usize,
    pub(crate) partial_reuses: usize,
    pub(crate) candidates_rejected: usize,
}

/// A case-destructured variable that could provide a reset slot.
#[derive(Clone, Debug)]
pub(crate) struct ReuseCandidate {
    pub(crate) source_var: VarId,
    pub(crate) ctor_tag: u16,
    pub(crate) num_fields: usize,
    // Per-field layout of the slot. `is_compatible_reuse` decides on the
    // aggregate `CtorInfo` (object count + scalar size); the field-wise types
    // are what a field-level partial-reuse check will compare — 2026-07-31.
    #[allow(dead_code)]
    pub(crate) field_types: Vec<IRType>,
    pub(crate) distance_to_use: usize,
    pub(crate) ctor_info: CtorInfo,
}

/// An allocation (Ctor expression) that could be replaced with Reuse.
#[derive(Clone, Debug)]
pub(crate) struct AllocationSite {
    pub(crate) var: VarId,
    // The allocation's own shape. Matching is done through `ctor_info`, so the
    // tag/arity/field-type triple is currently write-only; it is the data a
    // tag-preserving (in-place `SetTag`-free) reuse rule needs — 2026-07-31.
    #[allow(dead_code)]
    pub(crate) ctor_tag: u16,
    #[allow(dead_code)]
    pub(crate) num_fields: usize,
    #[allow(dead_code)]
    pub(crate) field_types: Vec<IRType>,
    pub(crate) ctor_info: CtorInfo,
}

/// Check if `candidate` can provide memory for `alloc`.
pub(crate) fn is_compatible_reuse(
    candidate: &ReuseCandidate,
    alloc: &AllocationSite,
    partial: bool,
) -> bool {
    let (so, ss) = (
        candidate.ctor_info.num_objects,
        candidate.ctor_info.scalar_size(),
    );
    let (to, ts) = (alloc.ctor_info.num_objects, alloc.ctor_info.scalar_size());
    (so == to && ss == ts) || (partial && so >= to && ss >= ts)
}

/// Find all case-destructured objects that could supply a reset slot.
pub(crate) fn find_reuse_candidates(body: &IRBody) -> Vec<ReuseCandidate> {
    let mut out = Vec::new();
    find_cands(body, &mut out, 0);
    out
}

fn find_cands(body: &IRBody, out: &mut Vec<ReuseCandidate>, depth: usize) {
    match body {
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            for alt in alts {
                out.push(ReuseCandidate {
                    source_var: *scrutinee,
                    ctor_tag: alt.ctor.tag as u16,
                    num_fields: alt.ctor.field_types.len(),
                    field_types: alt.ctor.field_types.clone(),
                    distance_to_use: depth,
                    ctor_info: alt.ctor.clone(),
                });
                find_cands(&alt.body, out, depth + 1);
            }
            if let Some(d) = default {
                find_cands(d, out, depth + 1);
            }
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => find_cands(rest, out, depth + 1),
        IRBody::JDecl { body: jp, rest, .. } => {
            find_cands(jp, out, depth + 1);
            find_cands(rest, out, depth + 1);
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Find all constructor allocation sites in the body.
pub(crate) fn find_allocation_sites(body: &IRBody) -> Vec<AllocationSite> {
    let mut out = Vec::new();
    find_allocs(body, &mut out);
    out
}

fn find_allocs(body: &IRBody, out: &mut Vec<AllocationSite>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if let IRExpr::Ctor { info, .. } = value {
                out.push(AllocationSite {
                    var: *var,
                    ctor_tag: info.tag as u16,
                    num_fields: info.field_types.len(),
                    field_types: info.field_types.clone(),
                    ctor_info: info.clone(),
                });
            }
            find_allocs(rest, out);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            find_allocs(jp, out);
            find_allocs(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => find_allocs(rest, out),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                find_allocs(&alt.body, out);
            }
            if let Some(d) = default {
                find_allocs(d, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn is_exact_size_match(candidate: &ReuseCandidate, alloc: &AllocationSite) -> bool {
    candidate.ctor_info.num_objects == alloc.ctor_info.num_objects
        && candidate.ctor_info.scalar_size() == alloc.ctor_info.scalar_size()
}

fn candidate_rank(
    candidate: &ReuseCandidate,
    alloc: &AllocationSite,
    config: &ResetReuseExtConfig,
) -> (u8, usize) {
    let quality = if is_exact_size_match(candidate, alloc) {
        0
    } else if is_compatible_reuse(candidate, alloc, config.enable_partial_reuse) {
        1
    } else {
        2
    };
    (quality, candidate.distance_to_use)
}

fn candidate_is_eligible(
    candidate: &ReuseCandidate,
    alloc: &AllocationSite,
    config: &ResetReuseExtConfig,
) -> bool {
    candidate.distance_to_use <= config.max_reuse_distance
        && is_compatible_reuse(candidate, alloc, config.enable_partial_reuse)
}

/// Rank candidates by match quality, then by proximity to the allocation.
pub(crate) fn rank_candidates(
    candidates: &[ReuseCandidate],
    alloc: &AllocationSite,
    config: &ResetReuseExtConfig,
) -> Vec<usize> {
    let mut ranked: Vec<usize> = candidates
        .iter()
        .enumerate()
        .filter_map(|(ci, candidate)| candidate_is_eligible(candidate, alloc, config).then_some(ci))
        .collect();
    ranked.sort_by_key(|&ci| {
        let (quality, distance) = candidate_rank(&candidates[ci], alloc, config);
        (quality, distance, ci)
    });
    ranked
}

fn match_reuse_pairs_with_rejections(
    candidates: &[ReuseCandidate],
    allocations: &[AllocationSite],
    config: &ResetReuseExtConfig,
) -> (Vec<(usize, usize)>, usize) {
    let mut used_c: HashSet<usize> = HashSet::new();
    let mut pairs = Vec::new();
    let mut rejected = 0;

    for (ai, alloc) in allocations.iter().enumerate() {
        rejected += candidates
            .iter()
            .filter(|candidate| !candidate_is_eligible(candidate, alloc, config))
            .count();
        for ci in rank_candidates(candidates, alloc, config) {
            if used_c.contains(&ci) {
                continue;
            }
            pairs.push((ci, ai));
            used_c.insert(ci);
            break;
        }
    }

    (pairs, rejected)
}

/// Pair reuse candidates with compatible allocation sites using ranked ordering.
pub(crate) fn match_reuse_pairs(
    candidates: &[ReuseCandidate],
    allocations: &[AllocationSite],
    config: &ResetReuseExtConfig,
) -> Vec<(usize, usize)> {
    let (pairs, _) = match_reuse_pairs_with_rejections(candidates, allocations, config);
    pairs
}

fn collect_proj_vars(body: &IRBody, scr: VarId) -> HashSet<VarId> {
    let mut vars = HashSet::new();
    collect_proj(body, scr, &mut vars);
    vars
}

fn collect_proj(body: &IRBody, scr: VarId, vars: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            match value {
                IRExpr::Proj {
                    arg: IRArg::Var(s), ..
                } if *s == scr => {
                    vars.insert(*var);
                }
                IRExpr::UProj { var: s, .. } if *s == scr => {
                    vars.insert(*var);
                }
                IRExpr::SProj { var: s, .. } if *s == scr => {
                    vars.insert(*var);
                }
                _ => {}
            }
            collect_proj(rest, scr, vars);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            collect_proj(jp, scr, vars);
            collect_proj(rest, scr, vars);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_proj(rest, scr, vars);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                collect_proj(&a.body, scr, vars);
            }
            if let Some(d) = default {
                collect_proj(d, scr, vars);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn args_use_projected(args: &[IRArg], proj: &HashSet<VarId>) -> bool {
    args.iter()
        .any(|a| matches!(a, IRArg::Var(v) if proj.contains(v)))
}

fn max_var(body: &IRBody) -> u32 {
    match body {
        IRBody::VDecl { var, rest, .. } => var.0.max(max_var(rest)),
        IRBody::JDecl {
            params,
            body: jp,
            rest,
            ..
        } => {
            let p = params.iter().map(|(v, _)| v.0).max().unwrap_or(0);
            p.max(max_var(jp)).max(max_var(rest))
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => var.0.max(max_var(rest)),
        IRBody::Set {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var(rest)),
        IRBody::SetTag { var, rest, .. } => var.0.max(max_var(rest)),
        IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var(rest)),
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let a = alts.iter().map(|a| max_var(&a.body)).max().unwrap_or(0);
            let d = default.as_ref().map(|b| max_var(b)).unwrap_or(0);
            scrutinee.0.max(a).max(d)
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 0,
    }
}

/// Walk straight-line code for the first compatible Ctor to replace with Reuse.
fn try_reuse(
    body: &IRBody,
    src: &CtorInfo,
    rv: VarId,
    proj: &HashSet<VarId>,
    distance: usize,
    cfg: &ResetReuseExtConfig,
    stats: &mut ResetReuseExtStats,
) -> (IRBody, bool, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::Ctor { info, args } = value {
                let live = cfg.track_field_liveness && args_use_projected(args, proj);
                let exact =
                    info.num_objects == src.num_objects && info.scalar_size() == src.scalar_size();
                let part = cfg.enable_partial_reuse
                    && src.num_objects >= info.num_objects
                    && src.scalar_size() >= info.scalar_size();
                if exact || part {
                    if distance > cfg.max_reuse_distance {
                        stats.candidates_rejected += 1;
                    } else if !live {
                        let rest_t = xform(rest, cfg, stats);
                        return (
                            IRBody::VDecl {
                                var: *var,
                                ty: ty.clone(),
                                value: IRExpr::Reuse {
                                    var: rv,
                                    ctor: info.clone(),
                                    args: args.clone(),
                                },
                                rest: Box::new(rest_t),
                            },
                            true,
                            !exact,
                        );
                    }
                }
            }
            let (rt, did, p) = try_reuse(rest, src, rv, proj, distance + 1, cfg, stats);
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(rt),
                },
                did,
                p,
            )
        }
        IRBody::Inc { var, n, rest } => {
            let (rt, d, p) = try_reuse(rest, src, rv, proj, distance + 1, cfg, stats);
            (
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(rt),
                },
                d,
                p,
            )
        }
        IRBody::Dec { var, rest } => {
            let (rt, d, p) = try_reuse(rest, src, rv, proj, distance + 1, cfg, stats);
            (
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(rt),
                },
                d,
                p,
            )
        }
        _ => (body.clone(), false, false),
    }
}

/// Recursively transform a body, visiting Case nodes for reset/reuse.
fn xform(body: &IRBody, cfg: &ResetReuseExtConfig, stats: &mut ResetReuseExtStats) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(xform(rest, cfg, stats)),
        },
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(xform(jp_body, cfg, stats)),
            rest: Box::new(xform(rest, cfg, stats)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(xform(rest, cfg, stats)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(xform(rest, cfg, stats)),
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
            rest: Box::new(xform(rest, cfg, stats)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(xform(rest, cfg, stats)),
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
            rest: Box::new(xform(rest, cfg, stats)),
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
            rest: Box::new(xform(rest, cfg, stats)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => xform_case(*scrutinee, alts, default.as_deref(), cfg, stats),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
    }
}

/// Transform a Case node: try to insert reset/reuse in each alternative.
fn xform_case(
    scrutinee: VarId,
    alts: &[IRAlt],
    default: Option<&IRBody>,
    cfg: &ResetReuseExtConfig,
    stats: &mut ResetReuseExtStats,
) -> IRBody {
    let resets_before = stats.resets_inserted;
    let mut nv = scrutinee.0;
    for alt in alts {
        nv = nv.max(max_var(&alt.body));
    }
    if let Some(d) = default {
        nv = nv.max(max_var(d));
    }
    nv += 1;

    let transformed_alts: Vec<IRAlt> = alts
        .iter()
        .map(|alt| {
            let rv = VarId(nv);
            nv += 1;
            let proj = if cfg.track_field_liveness {
                collect_proj_vars(&alt.body, scrutinee)
            } else {
                HashSet::new()
            };
            let (rewritten, did, is_partial) =
                try_reuse(&alt.body, &alt.ctor, rv, &proj, 0, cfg, stats);
            if did {
                stats.resets_inserted += 1;
                stats.reuses_inserted += 1;
                if is_partial {
                    stats.partial_reuses += 1;
                }
                IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(IRBody::VDecl {
                        var: rv,
                        ty: IRType::Object,
                        value: IRExpr::Reset(scrutinee),
                        rest: Box::new(rewritten),
                    }),
                }
            } else {
                IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(xform(&alt.body, cfg, stats)),
                }
            }
        })
        .collect();

    if cfg.enable_multi_reset && stats.resets_inserted - resets_before > 1 {
        stats.multi_resets += 1;
    }
    let xdefault = default.map(|d| Box::new(xform(d, cfg, stats)));
    IRBody::Case {
        scrutinee,
        alts: transformed_alts,
        default: xdefault,
    }
}

/// Run extended reset/reuse on declarations (in-place).
#[must_use]
pub(crate) fn optimize_reset_reuse_ext(
    decls: &mut [IRDecl],
    config: &ResetReuseExtConfig,
) -> ResetReuseExtStats {
    let mut stats = ResetReuseExtStats::default();
    for decl in decls.iter_mut() {
        let candidates = find_reuse_candidates(&decl.body);
        let allocations = find_allocation_sites(&decl.body);
        let (_, rejected) = match_reuse_pairs_with_rejections(&candidates, &allocations, config);
        stats.candidates_rejected += rejected;
        decl.body = xform(&decl.body, config, &mut stats);
    }
    stats
}

/// Run extended reset/reuse with default configuration.
#[must_use]
pub(crate) fn optimize_reset_reuse_ext_default(decls: &mut [IRDecl]) -> ResetReuseExtStats {
    optimize_reset_reuse_ext(decls, &ResetReuseExtConfig::default())
}
