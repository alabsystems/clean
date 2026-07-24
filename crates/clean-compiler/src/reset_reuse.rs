// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reset/Reuse Memory Optimization Pass for L5IR
//!
//! When a constructor value has refcount 1 and is destructed by a Case, its
//! memory can be reused for a new constructor of the same layout, avoiding a
//! heap allocation. Runs BEFORE borrow inference.
//!
//! Algorithm (Ullrich & de Moura, "Counting Immutable Beans", IFL 2020, S4.4):
//! 1. In each Case alt, the scrutinee is destructed after field projections.
//! 2. Scan for Ctor allocations with compatible layout (same num_objects + scalar_size).
//! 3. Insert `let r := reset(scrutinee)` and replace Ctor with `Reuse { var: r, ... }`.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{CtorInfo, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use std::collections::HashSet;

/// Configuration for the reset/reuse optimization pass.
#[derive(Clone, Debug)]
pub(crate) struct ResetReuseConfig {
    /// Enable the optimization. When false, returns declarations unchanged.
    pub(crate) enabled: bool,
    /// Maximum number of object fields for a constructor to be eligible.
    /// Very large constructors are unlikely to benefit (allocation cost is
    /// amortized over many fields).
    pub(crate) max_object_fields: u32,
    /// Maximum scalar storage bytes for eligibility.
    pub(crate) max_scalar_bytes: u32,
}

impl Default for ResetReuseConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            max_object_fields: 64,
            max_scalar_bytes: 512,
        }
    }
}

/// Statistics from a reset/reuse pass run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ResetReuseStats {
    /// Number of reset/reuse pairs inserted.
    pub(crate) pairs_inserted: usize,
    /// Number of candidates rejected due to size mismatch.
    pub(crate) size_mismatches: usize,
    /// Number of candidates rejected because fields exceeded threshold.
    pub(crate) threshold_rejected: usize,
    /// Total Case alternatives scanned.
    pub(crate) alts_scanned: usize,
    /// Total Ctor expressions examined as reuse targets.
    pub(crate) ctors_examined: usize,
}

/// Layout signature for size-compatibility checking.
///
/// Two constructors can share memory iff they have the same CtorLayout.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CtorLayout {
    num_objects: u32,
    scalar_size: u32,
}

impl CtorLayout {
    fn from_ctor_info(info: &CtorInfo) -> Self {
        Self {
            num_objects: info.num_objects,
            scalar_size: info.scalar_size(),
        }
    }
}

/// Check if two constructors are size-compatible for memory reuse.
///
/// Returns true if the destructed constructor's memory can hold the new one.
/// Tags can differ (handled by setTag at runtime).
fn layouts_compatible(source: &CtorInfo, target: &CtorInfo) -> bool {
    let src = CtorLayout::from_ctor_info(source);
    let tgt = CtorLayout::from_ctor_info(target);
    src == tgt
}

/// Check if a constructor meets the size thresholds for reuse.
fn within_threshold(info: &CtorInfo, config: &ResetReuseConfig) -> bool {
    info.num_objects <= config.max_object_fields && info.scalar_size() <= config.max_scalar_bytes
}

/// Run the reset/reuse optimization on a list of IR declarations.
///
/// Returns transformed declarations and statistics.
pub(crate) fn insert_reset_reuse(
    decls: &[IRDecl],
    config: &ResetReuseConfig,
) -> (Vec<IRDecl>, ResetReuseStats) {
    let mut stats = ResetReuseStats::default();

    if !config.enabled {
        return (decls.to_vec(), stats);
    }

    let transformed: Vec<IRDecl> = decls
        .iter()
        .map(|decl| transform_decl(decl, config, &mut stats))
        .collect();

    (transformed, stats)
}

/// Run reset/reuse on a single declaration.
pub(crate) fn insert_reset_reuse_single(
    decl: &IRDecl,
    config: &ResetReuseConfig,
) -> (IRDecl, ResetReuseStats) {
    let mut stats = ResetReuseStats::default();
    if !config.enabled {
        return (decl.clone(), stats);
    }
    let transformed = transform_decl(decl, config, &mut stats);
    (transformed, stats)
}

/// Transform a single declaration.
fn transform_decl(decl: &IRDecl, config: &ResetReuseConfig, stats: &mut ResetReuseStats) -> IRDecl {
    let mut next_var = find_max_var_id(&decl.body) + 1;
    let body = transform_body(&decl.body, config, stats, &mut next_var);
    IRDecl {
        name: decl.name.clone(),
        params: decl.params.clone(),
        return_type: decl.return_type.clone(),
        body,
    }
}

/// Find the maximum VarId used in a body, for generating fresh variables.
fn find_max_var_id(body: &IRBody) -> u32 {
    match body {
        IRBody::VDecl { var, rest, .. } => var.0.max(find_max_var_id(rest)),
        IRBody::JDecl {
            params, body, rest, ..
        } => {
            let p_max = params.iter().map(|(v, _)| v.0).max().unwrap_or(0);
            p_max.max(find_max_var_id(body)).max(find_max_var_id(rest))
        }
        IRBody::Inc { var, rest, .. } => var.0.max(find_max_var_id(rest)),
        IRBody::Dec { var, rest, .. } => var.0.max(find_max_var_id(rest)),
        IRBody::Set {
            var, value, rest, ..
        } => var.0.max(value.0).max(find_max_var_id(rest)),
        IRBody::SetTag { var, rest, .. } => var.0.max(find_max_var_id(rest)),
        IRBody::USet {
            var, value, rest, ..
        } => var.0.max(value.0).max(find_max_var_id(rest)),
        IRBody::SSet {
            var, value, rest, ..
        } => var.0.max(value.0).max(find_max_var_id(rest)),
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let alt_max = alts
                .iter()
                .map(|a| find_max_var_id(&a.body))
                .max()
                .unwrap_or(0);
            let def_max = default.as_ref().map(|d| find_max_var_id(d)).unwrap_or(0);
            scrutinee.0.max(alt_max).max(def_max)
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 0,
    }
}

/// Transform a body, looking for Case nodes to insert reset/reuse.
fn transform_body(
    body: &IRBody,
    config: &ResetReuseConfig,
    stats: &mut ResetReuseStats,
    next_var: &mut u32,
) -> IRBody {
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
            rest: Box::new(transform_body(rest, config, stats, next_var)),
        },
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(transform_body(jp_body, config, stats, next_var)),
            rest: Box::new(transform_body(rest, config, stats, next_var)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(transform_body(rest, config, stats, next_var)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(transform_body(rest, config, stats, next_var)),
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
            rest: Box::new(transform_body(rest, config, stats, next_var)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(transform_body(rest, config, stats, next_var)),
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
            rest: Box::new(transform_body(rest, config, stats, next_var)),
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
            rest: Box::new(transform_body(rest, config, stats, next_var)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let transformed_alts: Vec<IRAlt> = alts
                .iter()
                .map(|alt| {
                    stats.alts_scanned += 1;
                    transform_case_alt(*scrutinee, &alt.ctor, &alt.body, config, stats, next_var)
                })
                .collect();
            let transformed_default = default
                .as_ref()
                .map(|d| Box::new(transform_body(d, config, stats, next_var)));
            IRBody::Case {
                scrutinee: *scrutinee,
                alts: transformed_alts,
                default: transformed_default,
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
    }
}

/// Transform a Case alternative: try to insert reset/reuse for the scrutinee.
///
/// The scrutinee of a Case is destructed in each alternative. If a Ctor
/// allocation in the body has a compatible layout, we insert a Reset of the
/// scrutinee and replace the Ctor with a Reuse.
fn transform_case_alt(
    scrutinee: VarId,
    source_ctor: &CtorInfo,
    alt_body: &IRBody,
    config: &ResetReuseConfig,
    stats: &mut ResetReuseStats,
    next_var: &mut u32,
) -> IRAlt {
    // Check if the source constructor is within thresholds
    if !within_threshold(source_ctor, config) {
        stats.threshold_rejected += 1;
        return IRAlt {
            ctor: source_ctor.clone(),
            body: Box::new(transform_body(alt_body, config, stats, next_var)),
        };
    }

    // Collect variables used by projections from the scrutinee.
    // These are live fields — the scrutinee cannot be reset until after
    // all projections are complete.
    let projected_vars = collect_projection_vars(alt_body, scrutinee);

    // Try to find a Ctor allocation that is compatible and insert reset/reuse.
    let reset_var = VarId(*next_var);
    *next_var += 1;

    let (transformed, did_reuse) = try_insert_reuse(
        alt_body,
        scrutinee,
        source_ctor,
        reset_var,
        &projected_vars,
        config,
        stats,
    );

    if did_reuse {
        stats.pairs_inserted += 1;
        // Wrap the transformed body with a Reset of the scrutinee.
        let body_with_reset = IRBody::VDecl {
            var: reset_var,
            ty: IRType::Object,
            value: IRExpr::Reset(scrutinee),
            rest: Box::new(transformed),
        };
        IRAlt {
            ctor: source_ctor.clone(),
            body: Box::new(body_with_reset),
        }
    } else {
        // No reuse opportunity found; still recurse into sub-bodies.
        IRAlt {
            ctor: source_ctor.clone(),
            body: Box::new(transform_body(alt_body, config, stats, next_var)),
        }
    }
}

/// Collect VarIds that are the result of projecting from the scrutinee.
///
/// These variables hold data extracted from the scrutinee, so the scrutinee
/// must remain alive until after all projections are done.
fn collect_projection_vars(body: &IRBody, scrutinee: VarId) -> HashSet<VarId> {
    let mut vars = HashSet::new();
    collect_projection_vars_inner(body, scrutinee, &mut vars);
    vars
}

fn collect_projection_vars_inner(body: &IRBody, scrutinee: VarId, vars: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            match value {
                IRExpr::Proj {
                    arg: IRArg::Var(src),
                    ..
                } if *src == scrutinee => {
                    vars.insert(*var);
                }
                IRExpr::UProj { var: src, .. } if *src == scrutinee => {
                    vars.insert(*var);
                }
                IRExpr::SProj { var: src, .. } if *src == scrutinee => {
                    vars.insert(*var);
                }
                _ => {}
            }
            collect_projection_vars_inner(rest, scrutinee, vars);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            collect_projection_vars_inner(jp_body, scrutinee, vars);
            collect_projection_vars_inner(rest, scrutinee, vars);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_projection_vars_inner(rest, scrutinee, vars);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_projection_vars_inner(&alt.body, scrutinee, vars);
            }
            if let Some(d) = default {
                collect_projection_vars_inner(d, scrutinee, vars);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Try to replace the first compatible Ctor with a Reuse.
///
/// Walks the body looking for `let x := Ctor { info, args }` where `info`
/// is layout-compatible with the source constructor. Replaces it with
/// `let x := Reuse { var: reset_var, ctor: info, args }`.
///
/// Returns (transformed_body, did_reuse).
fn try_insert_reuse(
    body: &IRBody,
    _scrutinee: VarId,
    source_ctor: &CtorInfo,
    reset_var: VarId,
    projected_vars: &HashSet<VarId>,
    config: &ResetReuseConfig,
    stats: &mut ResetReuseStats,
) -> (IRBody, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::Ctor { info, args } = value {
                stats.ctors_examined += 1;
                // Check that the Ctor args do not include any projected vars
                // that are still live (they came from the scrutinee we are resetting).
                // This is safe because the projections happened before the reset.
                let args_use_projected = args.iter().any(|a| {
                    if let IRArg::Var(v) = a {
                        projected_vars.contains(v)
                    } else {
                        false
                    }
                });

                if !args_use_projected
                    && within_threshold(info, config)
                    && layouts_compatible(source_ctor, info)
                {
                    // Replace Ctor with Reuse.
                    let reuse_expr = IRExpr::Reuse {
                        var: reset_var,
                        ctor: info.clone(),
                        args: args.clone(),
                    };
                    let rest_transformed =
                        transform_body(rest, config, stats, &mut (reset_var.0 + 1));
                    return (
                        IRBody::VDecl {
                            var: *var,
                            ty: ty.clone(),
                            value: reuse_expr,
                            rest: Box::new(rest_transformed),
                        },
                        true,
                    );
                } else if !layouts_compatible(source_ctor, info) && within_threshold(info, config) {
                    stats.size_mismatches += 1;
                }
            }

            // Not a compatible Ctor — recurse into rest.
            let (rest_transformed, did_reuse) = try_insert_reuse(
                rest,
                _scrutinee,
                source_ctor,
                reset_var,
                projected_vars,
                config,
                stats,
            );
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(rest_transformed),
                },
                did_reuse,
            )
        }
        IRBody::Inc { var, n, rest } => {
            let (rest_transformed, did_reuse) = try_insert_reuse(
                rest,
                _scrutinee,
                source_ctor,
                reset_var,
                projected_vars,
                config,
                stats,
            );
            (
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(rest_transformed),
                },
                did_reuse,
            )
        }
        IRBody::Dec { var, rest } => {
            let (rest_transformed, did_reuse) = try_insert_reuse(
                rest,
                _scrutinee,
                source_ctor,
                reset_var,
                projected_vars,
                config,
                stats,
            );
            (
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(rest_transformed),
                },
                did_reuse,
            )
        }
        // For control flow nodes (Case, Jmp, Ret, etc.), do not search further.
        // Reset/reuse should be within straight-line code in a single alternative.
        _ => (body.clone(), false),
    }
}

#[cfg(test)]
#[path = "reset_reuse_tests.rs"]
mod tests;
