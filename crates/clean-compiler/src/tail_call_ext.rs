// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tail call optimizations: self-TCO loops, accumulators, mutual trampolines,
//! return continuations, conservative side-effect analysis. Part of #3084.
use crate::ir::{
    eqv_types, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};
use thiserror::Error;
#[derive(Clone, Debug)]
pub(crate) struct TailCallExtConfig {
    pub(crate) max_accumulator_params: usize,
    pub(crate) enable_mutual_tco: bool,
    pub(crate) enable_accumulator_passing: bool,
    pub(crate) enable_continuation_passing: bool,
}
impl Default for TailCallExtConfig {
    fn default() -> Self {
        Self {
            max_accumulator_params: 4,
            enable_mutual_tco: true,
            enable_accumulator_passing: true,
            enable_continuation_passing: true,
        }
    }
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TailCallExtStats {
    pub(crate) direct_tco: usize,
    pub(crate) accumulator_tco: usize,
    pub(crate) mutual_tco: usize,
    pub(crate) continuation_tco: usize,
    pub(crate) failed: usize,
    pub(crate) tail_positions_found: usize,
    pub(crate) join_point_propagations: usize,
    pub(crate) conservative_skips: usize,
}
impl TailCallExtStats {
    #[must_use]
    pub(crate) fn total_optimized(&self) -> usize {
        self.direct_tco + self.accumulator_tco + self.mutual_tco + self.continuation_tco
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TailPosition {
    pub(crate) fn_id: FnId,
    pub(crate) args: Vec<VarId>,
    pub(crate) is_self_recursive: bool,
    pub(crate) is_mutual: bool,
}
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub(crate) enum TailCallExtError {
    #[error("mutual trampoline requires equivalent return types")]
    IncompatibleMutualReturn,
    #[error("continuation passing does not support erased returns")]
    UnsupportedErasedReturn,
}
/// Conservative: returns `true` when Set/USet/SSet mutates a var that is later passed to a tail call.
#[must_use]
pub(crate) fn has_observable_side_effects(body: &IRBody, fn_id: &FnId) -> bool {
    has_side_effects_inner(body, fn_id, &mut HashSet::new())
}
fn has_side_effects_inner(body: &IRBody, fn_id: &FnId, mutated: &mut HashSet<VarId>) -> bool {
    match body {
        IRBody::Set { var, rest, .. }
        | IRBody::USet { var, rest, .. }
        | IRBody::SSet { var, rest, .. } => {
            mutated.insert(*var);
            has_side_effects_inner(rest, fn_id, mutated)
        }
        IRBody::VDecl {
            value: IRExpr::Apply { fn_id: f, args },
            rest,
            var,
            ..
        } if f == fn_id && rest_returns_var(*var, rest) => args
            .iter()
            .any(|a| matches!(a, IRArg::Var(v) if mutated.contains(v))),
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::SetTag { rest, .. } => has_side_effects_inner(rest, fn_id, mutated),
        IRBody::JDecl { body, rest, .. } => {
            has_side_effects_inner(body, fn_id, mutated)
                || has_side_effects_inner(rest, fn_id, mutated)
        }
        IRBody::Case { alts, default, .. } => {
            alts.iter()
                .any(|a| has_side_effects_inner(&a.body, fn_id, &mut mutated.clone()))
                || default
                    .as_ref()
                    .is_some_and(|d| has_side_effects_inner(d, fn_id, &mut mutated.clone()))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => false,
    }
}
#[must_use]
pub(crate) fn optimize_tail_calls_ext(
    decls: &mut [IRDecl],
    config: &TailCallExtConfig,
) -> TailCallExtStats {
    let mut stats = TailCallExtStats::default();
    for d in decls.iter() {
        stats.tail_positions_found += detect_tail_positions(&d.body).len();
        stats.join_point_propagations += collect_tail_join_points(&d.body).len();
    }
    let accum_candidates: Vec<Vec<VarId>> = if config.enable_accumulator_passing {
        decls
            .iter()
            .map(|d| detect_self_tail_result_vars(d, config.max_accumulator_params))
            .collect()
    } else {
        vec![Vec::new(); decls.len()]
    };

    for decl in decls.iter_mut() {
        let self_id = FnId(decl.name.clone());
        if has_observable_side_effects(&decl.body, &self_id) {
            stats.conservative_skips += 1;
            continue;
        }
        if lower_direct_self_tco(decl) {
            stats.direct_tco += 1;
        }
    }
    if config.enable_accumulator_passing {
        for (decl, vars) in decls.iter_mut().zip(accum_candidates) {
            if !vars.is_empty() {
                if transform_accumulator_passing(decl, &vars) {
                    stats.accumulator_tco += 1;
                } else {
                    stats.failed += 1;
                }
            }
        }
    }
    if config.enable_mutual_tco {
        let pairs = detect_mutual_tail_calls(decls);
        let idx: HashMap<_, _> = decls
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.clone(), i))
            .collect();
        for (a, b) in pairs {
            let (Some(&i), Some(&j)) = (idx.get(&a.0), idx.get(&b.0)) else {
                stats.failed += 1;
                continue;
            };
            let ok = if i < j {
                let (left, right) = decls.split_at_mut(j);
                transform_mutual_to_trampoline(&mut left[i], &mut right[0])
            } else {
                let (left, right) = decls.split_at_mut(i);
                transform_mutual_to_trampoline(&mut right[0], &mut left[j])
            };
            if ok {
                stats.mutual_tco += 1;
            } else {
                stats.failed += 1;
            }
        }
    }
    if config.enable_continuation_passing {
        for decl in decls.iter_mut() {
            match lower_return_continuation(decl) {
                Ok(true) => stats.continuation_tco += 1,
                Ok(false) => {}
                Err(_) => stats.failed += 1,
            }
        }
    }
    stats
}
#[must_use]
pub(crate) fn optimize_tail_calls_ext_default(decls: &mut [IRDecl]) -> TailCallExtStats {
    optimize_tail_calls_ext(decls, &TailCallExtConfig::default())
}
#[must_use]
pub(crate) fn detect_tail_positions(body: &IRBody) -> Vec<TailPosition> {
    let mut out = Vec::new();
    let tail_jps = collect_tail_join_points(body);
    detect_tail_positions_inner(body, &tail_jps, None, &HashSet::new(), &mut out);
    out
}
pub(crate) fn transform_accumulator_passing(decl: &mut IRDecl, accum_params: &[VarId]) -> bool {
    if accum_params.is_empty() {
        return false;
    }
    let mut next_var = max_var_in_decl(decl) + 1;
    let mut accum_pairs = Vec::new();
    for src in accum_params {
        let acc = fresh_var(&mut next_var);
        let ty = find_var_type(decl, *src).unwrap_or_else(|| decl.return_type.clone());
        decl.params.push((acc, ty));
        accum_pairs.push((*src, acc));
    }
    decl.body = rewrite_accumulator_body(&decl.body, &FnId(decl.name.clone()), &accum_pairs);
    true
}
#[must_use]
pub(crate) fn detect_mutual_tail_calls(decls: &[IRDecl]) -> Vec<(FnId, FnId)> {
    let ids: Vec<_> = decls.iter().map(|d| FnId(d.name.clone())).collect();
    let mut out = Vec::new();
    for i in 0..decls.len() {
        for j in (i + 1)..decls.len() {
            if is_tail_recursive(&decls[i].body, &ids[j])
                && is_tail_recursive(&decls[j].body, &ids[i])
            {
                out.push((ids[i].clone(), ids[j].clone()));
            }
        }
    }
    out
}
pub(crate) fn transform_mutual_to_trampoline(decl_a: &mut IRDecl, decl_b: &mut IRDecl) -> bool {
    let a0 = decl_a.clone();
    let b0 = decl_b.clone();
    if !eqv_types(&a0.return_type, &b0.return_type)
        || !is_tail_recursive(&a0.body, &FnId(b0.name.clone()))
        || !is_tail_recursive(&b0.body, &FnId(a0.name.clone()))
    {
        return false;
    }
    let Ok(body_a) = build_mutual_body(&a0, &b0, true) else {
        return false;
    };
    let Ok(body_b) = build_mutual_body(&a0, &b0, false) else {
        return false;
    };
    decl_a.body = body_a;
    decl_b.body = body_b;
    true
}
#[must_use]
pub(crate) fn is_tail_recursive(body: &IRBody, fn_id: &FnId) -> bool {
    let tail_jps = collect_tail_join_points(body);
    has_tail_call_to(body, fn_id, &tail_jps)
}
fn detect_tail_positions_inner(
    body: &IRBody,
    tail_jps: &HashSet<JoinPointId>,
    current: Option<&FnId>,
    mutuals: &HashSet<Name>,
    out: &mut Vec<TailPosition>,
) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if let IRExpr::Apply { fn_id, args } = value {
                if rest_returns_var(*var, rest) {
                    out.push(TailPosition {
                        fn_id: fn_id.clone(),
                        args: args
                            .iter()
                            .filter_map(|a| match a {
                                IRArg::Var(v) => Some(*v),
                                IRArg::Erased => None,
                            })
                            .collect(),
                        is_self_recursive: current.is_some_and(|f| f == fn_id),
                        is_mutual: current.is_some_and(|f| f != fn_id)
                            && mutuals.contains(&fn_id.0),
                    });
                }
            }
            detect_tail_positions_inner(rest, tail_jps, current, mutuals, out);
        }
        IRBody::JDecl { jp, body, rest, .. } => {
            if tail_jps.contains(jp) {
                detect_tail_positions_inner(body, tail_jps, current, mutuals, out);
            }
            detect_tail_positions_inner(rest, tail_jps, current, mutuals, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                detect_tail_positions_inner(&alt.body, tail_jps, current, mutuals, out);
            }
            if let Some(d) = default {
                detect_tail_positions_inner(d, tail_jps, current, mutuals, out);
            }
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            detect_tail_positions_inner(rest, tail_jps, current, mutuals, out)
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}
fn detect_self_tail_result_vars(decl: &IRDecl, limit: usize) -> Vec<VarId> {
    let mut out = Vec::new();
    let tail_jps = collect_tail_join_points(&decl.body);
    collect_self_tail_result_vars(&decl.body, &FnId(decl.name.clone()), &tail_jps, &mut out);
    out.truncate(limit);
    out
}
fn collect_self_tail_result_vars(
    body: &IRBody,
    fn_id: &FnId,
    tail_jps: &HashSet<JoinPointId>,
    out: &mut Vec<VarId>,
) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if matches!(value, IRExpr::Apply { fn_id: f, .. } if f == fn_id && rest_returns_var(*var, rest))
                && !out.contains(var)
            {
                out.push(*var);
            }
            collect_self_tail_result_vars(rest, fn_id, tail_jps, out);
        }
        IRBody::JDecl { jp, body, rest, .. } => {
            if tail_jps.contains(jp) {
                collect_self_tail_result_vars(body, fn_id, tail_jps, out);
            }
            collect_self_tail_result_vars(rest, fn_id, tail_jps, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_self_tail_result_vars(&alt.body, fn_id, tail_jps, out);
            }
            if let Some(d) = default {
                collect_self_tail_result_vars(d, fn_id, tail_jps, out);
            }
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_self_tail_result_vars(rest, fn_id, tail_jps, out),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}
fn lower_direct_self_tco(decl: &mut IRDecl) -> bool {
    let self_id = FnId(decl.name.clone());
    if !is_tail_recursive(&decl.body, &self_id) {
        return false;
    }
    let mut next_var = max_var_in_decl(decl) + 1;
    let mut next_jp = max_jp_id(&decl.body) + 1;
    let loop_jp = fresh_jp(&mut next_jp);
    let loop_params: Vec<_> = decl
        .params
        .iter()
        .map(|(_, ty)| (fresh_var(&mut next_var), ty.clone()))
        .collect();
    let mut vars = decl
        .params
        .iter()
        .zip(loop_params.iter())
        .map(|((old, _), (new, _))| (*old, *new))
        .collect();
    let body = freshen_body(
        &decl.body,
        &mut vars,
        &mut HashMap::new(),
        &mut next_var,
        &mut next_jp,
    );
    let jumps = HashMap::from([(decl.name.clone(), loop_jp)]);
    decl.body = IRBody::JDecl {
        jp: loop_jp,
        params: loop_params,
        body: Box::new(rewrite_tail_applies(&body, &jumps)),
        rest: Box::new(IRBody::Jmp {
            jp: loop_jp,
            args: decl.params.iter().map(|(v, _)| IRArg::Var(*v)).collect(),
        }),
    };
    true
}
fn build_mutual_body(a: &IRDecl, b: &IRDecl, entry_a: bool) -> Result<IRBody, TailCallExtError> {
    if !eqv_types(&a.return_type, &b.return_type) {
        return Err(TailCallExtError::IncompatibleMutualReturn);
    }
    let mut next_var = max_var_in_decl(a).max(max_var_in_decl(b)) + 1;
    let mut next_jp = max_jp_id(&a.body).max(max_jp_id(&b.body)) + 1;
    let jp_a = fresh_jp(&mut next_jp);
    let jp_b = fresh_jp(&mut next_jp);
    let a_params: Vec<_> = a
        .params
        .iter()
        .map(|(_, ty)| (fresh_var(&mut next_var), ty.clone()))
        .collect();
    let b_params: Vec<_> = b
        .params
        .iter()
        .map(|(_, ty)| (fresh_var(&mut next_var), ty.clone()))
        .collect();
    let mut a_vars = a
        .params
        .iter()
        .zip(a_params.iter())
        .map(|((old, _), (new, _))| (*old, *new))
        .collect();
    let mut b_vars = b
        .params
        .iter()
        .zip(b_params.iter())
        .map(|((old, _), (new, _))| (*old, *new))
        .collect();
    let a_body = freshen_body(
        &a.body,
        &mut a_vars,
        &mut HashMap::new(),
        &mut next_var,
        &mut next_jp,
    );
    let b_body = freshen_body(
        &b.body,
        &mut b_vars,
        &mut HashMap::new(),
        &mut next_var,
        &mut next_jp,
    );
    let jumps = HashMap::from([(a.name.clone(), jp_a), (b.name.clone(), jp_b)]);
    Ok(IRBody::JDecl {
        jp: jp_a,
        params: a_params,
        body: Box::new(rewrite_tail_applies(&a_body, &jumps)),
        rest: Box::new(IRBody::JDecl {
            jp: jp_b,
            params: b_params,
            body: Box::new(rewrite_tail_applies(&b_body, &jumps)),
            rest: Box::new(IRBody::Jmp {
                jp: if entry_a { jp_a } else { jp_b },
                args: if entry_a {
                    a.params.iter().map(|(v, _)| IRArg::Var(*v)).collect()
                } else {
                    b.params.iter().map(|(v, _)| IRArg::Var(*v)).collect()
                },
            }),
        }),
    })
}
fn lower_return_continuation(decl: &mut IRDecl) -> Result<bool, TailCallExtError> {
    let tail_jps = collect_tail_join_points(&decl.body);
    if !has_any_tail_apply(&decl.body, &tail_jps) {
        return Ok(false);
    }
    if contains_erased_return(&decl.body) {
        return Err(TailCallExtError::UnsupportedErasedReturn);
    }
    let mut next_var = max_var_in_decl(decl) + 1;
    let mut next_jp = max_jp_id(&decl.body) + 1;
    let ret_var = fresh_var(&mut next_var);
    let ret_jp = fresh_jp(&mut next_jp);
    decl.body = IRBody::JDecl {
        jp: ret_jp,
        params: vec![(ret_var, decl.return_type.clone())],
        body: Box::new(IRBody::Ret(IRArg::Var(ret_var))),
        rest: Box::new(rewrite_returns(&decl.body, ret_jp)),
    };
    Ok(true)
}
fn rewrite_tail_applies(body: &IRBody, jumps: &HashMap<Name, JoinPointId>) -> IRBody {
    let tail_jps = collect_tail_join_points(body);
    rewrite_tail_applies_inner(body, &tail_jps, jumps)
}
fn rewrite_tail_applies_inner(
    body: &IRBody,
    tail_jps: &HashSet<JoinPointId>,
    jumps: &HashMap<Name, JoinPointId>,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::Apply { fn_id, args } = value {
                if let Some(&jp) = jumps.get(&fn_id.0) {
                    if let Some(body) = rebuild_tail_terminal(
                        *var,
                        rest,
                        IRBody::Jmp {
                            jp,
                            args: args.clone(),
                        },
                    ) {
                        return body;
                    }
                }
            }
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: value.clone(),
                rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(if tail_jps.contains(jp) {
                rewrite_tail_applies_inner(body, tail_jps, jumps)
            } else {
                (**body).clone()
            }),
            rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
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
            rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
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
            rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
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
            rest: Box::new(rewrite_tail_applies_inner(rest, tail_jps, jumps)),
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
                    body: Box::new(rewrite_tail_applies_inner(&alt.body, tail_jps, jumps)),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|d| Box::new(rewrite_tail_applies_inner(d, tail_jps, jumps))),
        },
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
    }
}
fn rewrite_accumulator_body(
    body: &IRBody,
    self_id: &FnId,
    accum_pairs: &[(VarId, VarId)],
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let value = match value {
                IRExpr::Apply { fn_id, args }
                    if fn_id == self_id && rest_returns_var(*var, rest) =>
                {
                    let mut args = args.clone();
                    args.extend(accum_pairs.iter().map(|(_, acc)| IRArg::Var(*acc)));
                    IRExpr::Apply {
                        fn_id: fn_id.clone(),
                        args,
                    }
                }
                _ => value.clone(),
            };
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value,
                rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(rewrite_accumulator_body(body, self_id, accum_pairs)),
            rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
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
                    body: Box::new(rewrite_accumulator_body(&alt.body, self_id, accum_pairs)),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|d| Box::new(rewrite_accumulator_body(d, self_id, accum_pairs))),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
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
            rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
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
            rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
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
            rest: Box::new(rewrite_accumulator_body(rest, self_id, accum_pairs)),
        },
        IRBody::Ret(IRArg::Var(v)) => IRBody::Ret(IRArg::Var(
            accum_pairs
                .iter()
                .find_map(|(src, acc)| (*src == *v).then_some(*acc))
                .unwrap_or(*v),
        )),
        IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => body.clone(),
    }
}
fn rewrite_returns(body: &IRBody, ret_jp: JoinPointId) -> IRBody {
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
            rest: Box::new(rewrite_returns(rest, ret_jp)),
        },
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(rewrite_returns(body, ret_jp)),
            rest: Box::new(rewrite_returns(rest, ret_jp)),
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
                    body: Box::new(rewrite_returns(&alt.body, ret_jp)),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|d| Box::new(rewrite_returns(d, ret_jp))),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(rewrite_returns(rest, ret_jp)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(rewrite_returns(rest, ret_jp)),
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
            rest: Box::new(rewrite_returns(rest, ret_jp)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(rewrite_returns(rest, ret_jp)),
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
            rest: Box::new(rewrite_returns(rest, ret_jp)),
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
            rest: Box::new(rewrite_returns(rest, ret_jp)),
        },
        IRBody::Ret(arg) => IRBody::Jmp {
            jp: ret_jp,
            args: vec![arg.clone()],
        },
        IRBody::Jmp { .. } | IRBody::Unreachable => body.clone(),
    }
}
fn has_tail_call_to(body: &IRBody, fn_id: &FnId, tail_jps: &HashSet<JoinPointId>) -> bool {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            matches!(value, IRExpr::Apply { fn_id: f, .. } if f == fn_id && rest_returns_var(*var, rest))
                || has_tail_call_to(rest, fn_id, tail_jps)
        }
        IRBody::JDecl { jp, body, rest, .. } => {
            (tail_jps.contains(jp) && has_tail_call_to(body, fn_id, tail_jps))
                || has_tail_call_to(rest, fn_id, tail_jps)
        }
        IRBody::Case { alts, default, .. } => {
            alts.iter()
                .any(|alt| has_tail_call_to(&alt.body, fn_id, tail_jps))
                || default
                    .as_ref()
                    .is_some_and(|d| has_tail_call_to(d, fn_id, tail_jps))
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => has_tail_call_to(rest, fn_id, tail_jps),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => false,
    }
}
fn has_any_tail_apply(body: &IRBody, tail_jps: &HashSet<JoinPointId>) -> bool {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            matches!(value, IRExpr::Apply { .. } if rest_returns_var(*var, rest))
                || has_any_tail_apply(rest, tail_jps)
        }
        IRBody::JDecl { jp, body, rest, .. } => {
            (tail_jps.contains(jp) && has_any_tail_apply(body, tail_jps))
                || has_any_tail_apply(rest, tail_jps)
        }
        IRBody::Case { alts, default, .. } => {
            alts.iter()
                .any(|alt| has_any_tail_apply(&alt.body, tail_jps))
                || default
                    .as_ref()
                    .is_some_and(|d| has_any_tail_apply(d, tail_jps))
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => has_any_tail_apply(rest, tail_jps),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => false,
    }
}
fn freshen_body(
    body: &IRBody,
    vars: &mut HashMap<VarId, VarId>,
    jps: &mut HashMap<JoinPointId, JoinPointId>,
    next_var: &mut u32,
    next_jp: &mut u32,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let new_var = fresh_var(next_var);
            vars.insert(*var, new_var);
            IRBody::VDecl {
                var: new_var,
                ty: ty.clone(),
                value: remap_expr(value, vars),
                rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            let new_jp = fresh_jp(next_jp);
            jps.insert(*jp, new_jp);
            let new_params: Vec<_> = params
                .iter()
                .map(|(v, ty)| {
                    let nv = fresh_var(next_var);
                    vars.insert(*v, nv);
                    (nv, ty.clone())
                })
                .collect();
            IRBody::JDecl {
                jp: new_jp,
                params: new_params,
                body: Box::new(freshen_body(body, vars, jps, next_var, next_jp)),
                rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
            }
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: map_var(vars, *var),
            n: *n,
            rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: map_var(vars, *var),
            rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: map_var(vars, *var),
            idx: *idx,
            value: map_var(vars, *value),
            rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: map_var(vars, *var),
            tag: *tag,
            rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: map_var(vars, *var),
            idx: *idx,
            value: map_var(vars, *value),
            rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: map_var(vars, *var),
            n: *n,
            offset: *offset,
            value: map_var(vars, *value),
            ty: ty.clone(),
            rest: Box::new(freshen_body(rest, vars, jps, next_var, next_jp)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: map_var(vars, *scrutinee),
            alts: alts
                .iter()
                .map(|alt| IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(freshen_body(&alt.body, vars, jps, next_var, next_jp)),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|d| Box::new(freshen_body(d, vars, jps, next_var, next_jp))),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: jps.get(jp).copied().unwrap_or(*jp),
            args: args.iter().map(|a| remap_arg(a, vars)).collect(),
        },
        IRBody::Ret(arg) => IRBody::Ret(remap_arg(arg, vars)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}
fn remap_expr(expr: &IRExpr, vars: &HashMap<VarId, VarId>) -> IRExpr {
    match expr {
        IRExpr::Ctor { info, args } => IRExpr::Ctor {
            info: info.clone(),
            args: args.iter().map(|a| remap_arg(a, vars)).collect(),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: remap_arg(arg, vars),
        },
        IRExpr::Tag(arg) => IRExpr::Tag(remap_arg(arg, vars)),
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: ty.clone(),
            arg: remap_arg(arg, vars),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: remap_arg(arg, vars),
        },
        IRExpr::Apply { fn_id, args } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: args.iter().map(|a| remap_arg(a, vars)).collect(),
        },
        IRExpr::PartialApply { fn_id, arity, args } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: args.iter().map(|a| remap_arg(a, vars)).collect(),
        },
        IRExpr::ClosureApply { closure, args } => IRExpr::ClosureApply {
            closure: remap_arg(closure, vars),
            args: args.iter().map(|a| remap_arg(a, vars)).collect(),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: map_var(vars, *var),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: map_var(vars, *var),
            ty: ty.clone(),
        },
        IRExpr::IsShared(var) => IRExpr::IsShared(map_var(vars, *var)),
        IRExpr::Reset(var) => IRExpr::Reset(map_var(vars, *var)),
        IRExpr::Reuse { var, ctor, args } => IRExpr::Reuse {
            var: map_var(vars, *var),
            ctor: ctor.clone(),
            args: args.iter().map(|a| remap_arg(a, vars)).collect(),
        },
        IRExpr::Lit(lit) => IRExpr::Lit(lit.clone()),
        IRExpr::String(s) => IRExpr::String(s.clone()),
    }
}
fn remap_arg(arg: &IRArg, vars: &HashMap<VarId, VarId>) -> IRArg {
    match arg {
        IRArg::Var(v) => IRArg::Var(map_var(vars, *v)),
        IRArg::Erased => IRArg::Erased,
    }
}
fn find_var_type(decl: &IRDecl, target: VarId) -> Option<IRType> {
    if let Some((_, ty)) = decl.params.iter().find(|(v, _)| *v == target) {
        return Some(ty.clone());
    }
    find_var_type_body(&decl.body, target)
}
fn find_var_type_body(body: &IRBody, target: VarId) -> Option<IRType> {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value: _,
            rest,
        } => {
            if *var == target {
                Some(ty.clone())
            } else {
                find_var_type_body(rest, target)
            }
        }
        IRBody::JDecl {
            params, body, rest, ..
        } => params
            .iter()
            .find(|(v, _)| *v == target)
            .map(|(_, ty)| ty.clone())
            .or_else(|| find_var_type_body(body, target))
            .or_else(|| find_var_type_body(rest, target)),
        IRBody::Case { alts, default, .. } => alts
            .iter()
            .find_map(|alt| find_var_type_body(&alt.body, target))
            .or_else(|| default.as_ref().and_then(|d| find_var_type_body(d, target))),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => find_var_type_body(rest, target),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => None,
    }
}
fn rest_returns_var(var: VarId, rest: &IRBody) -> bool {
    match rest {
        IRBody::Ret(IRArg::Var(v)) => *v == var,
        IRBody::Inc { var: v, rest, .. }
        | IRBody::Dec { var: v, rest }
        | IRBody::SetTag { var: v, rest, .. } => *v != var && rest_returns_var(var, rest),
        _ => false,
    }
}
fn rebuild_tail_terminal(var: VarId, rest: &IRBody, terminal: IRBody) -> Option<IRBody> {
    match rest {
        IRBody::Ret(IRArg::Var(v)) if *v == var => Some(terminal),
        IRBody::Inc { var: v, n, rest } if *v != var => Some(IRBody::Inc {
            var: *v,
            n: *n,
            rest: Box::new(rebuild_tail_terminal(var, rest, terminal)?),
        }),
        IRBody::Dec { var: v, rest } if *v != var => Some(IRBody::Dec {
            var: *v,
            rest: Box::new(rebuild_tail_terminal(var, rest, terminal)?),
        }),
        IRBody::SetTag { var: v, tag, rest } if *v != var => Some(IRBody::SetTag {
            var: *v,
            tag: *tag,
            rest: Box::new(rebuild_tail_terminal(var, rest, terminal)?),
        }),
        _ => None,
    }
}
fn contains_erased_return(body: &IRBody) -> bool {
    match body {
        IRBody::Ret(IRArg::Erased) => true,
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => contains_erased_return(rest),
        IRBody::JDecl { body, rest, .. } => {
            contains_erased_return(body) || contains_erased_return(rest)
        }
        IRBody::Case { alts, default, .. } => {
            alts.iter().any(|alt| contains_erased_return(&alt.body))
                || default.as_ref().is_some_and(|d| contains_erased_return(d))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => false,
    }
}
fn collect_tail_join_points(body: &IRBody) -> HashSet<JoinPointId> {
    let mut all = HashSet::new();
    let mut non_tail = HashSet::new();
    collect_jp_ids(body, &mut all);
    mark_non_tail_jps(body, true, &mut non_tail);
    all.difference(&non_tail).copied().collect()
}
fn collect_jp_ids(body: &IRBody, out: &mut HashSet<JoinPointId>) {
    match body {
        IRBody::JDecl { jp, body, rest, .. } => {
            out.insert(*jp);
            collect_jp_ids(body, out);
            collect_jp_ids(rest, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_jp_ids(&alt.body, out);
            }
            if let Some(d) = default {
                collect_jp_ids(d, out);
            }
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_jp_ids(rest, out),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}
fn mark_non_tail_jps(body: &IRBody, is_tail: bool, out: &mut HashSet<JoinPointId>) {
    match body {
        IRBody::Jmp { jp, .. } if !is_tail => {
            out.insert(*jp);
        }
        IRBody::JDecl { body, rest, .. } => {
            mark_non_tail_jps(body, is_tail, out);
            mark_non_tail_jps(rest, is_tail, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                mark_non_tail_jps(&alt.body, is_tail, out);
            }
            if let Some(d) = default {
                mark_non_tail_jps(d, is_tail, out);
            }
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => mark_non_tail_jps(rest, is_tail, out),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}
fn map_var(vars: &HashMap<VarId, VarId>, v: VarId) -> VarId {
    vars.get(&v).copied().unwrap_or(v)
}
fn fresh_var(next: &mut u32) -> VarId {
    let v = VarId(*next);
    *next += 1;
    v
}
fn fresh_jp(next: &mut u32) -> JoinPointId {
    let jp = JoinPointId(*next);
    *next += 1;
    jp
}
fn max_var_in_decl(decl: &IRDecl) -> u32 {
    decl.params
        .iter()
        .map(|(v, _)| v.0)
        .max()
        .unwrap_or(0)
        .max(max_var_in_body(&decl.body))
}
fn max_var_in_body(body: &IRBody) -> u32 {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => var.0.max(max_var_in_expr(value)).max(max_var_in_body(rest)),
        IRBody::JDecl {
            params, body, rest, ..
        } => params
            .iter()
            .map(|(v, _)| v.0)
            .max()
            .unwrap_or(0)
            .max(max_var_in_body(body))
            .max(max_var_in_body(rest)),
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
            var.0.max(max_var_in_body(rest))
        }
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var_in_body(rest)),
        IRBody::SetTag { var, rest, .. } => var.0.max(max_var_in_body(rest)),
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => scrutinee
            .0
            .max(
                alts.iter()
                    .map(|a| max_var_in_body(&a.body))
                    .max()
                    .unwrap_or(0),
            )
            .max(default.as_ref().map_or(0, |d| max_var_in_body(d))),
        IRBody::Jmp { args, .. } => args
            .iter()
            .filter_map(|a| match a {
                IRArg::Var(v) => Some(v.0),
                IRArg::Erased => None,
            })
            .max()
            .unwrap_or(0),
        IRBody::Ret(IRArg::Var(v)) => v.0,
        IRBody::Ret(IRArg::Erased) | IRBody::Unreachable => 0,
    }
}
fn max_var_in_expr(expr: &IRExpr) -> u32 {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => args
            .iter()
            .filter_map(|a| match a {
                IRArg::Var(v) => Some(v.0),
                IRArg::Erased => None,
            })
            .max()
            .unwrap_or(0),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => match arg {
            IRArg::Var(v) => v.0,
            IRArg::Erased => 0,
        },
        IRExpr::ClosureApply { closure, args } => match closure {
            IRArg::Var(v) => v.0,
            IRArg::Erased => 0,
        }
        .max(
            args.iter()
                .filter_map(|a| match a {
                    IRArg::Var(v) => Some(v.0),
                    IRArg::Erased => None,
                })
                .max()
                .unwrap_or(0),
        ),
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => var.0,
        IRExpr::Reuse { var, args, .. } => var.0.max(
            args.iter()
                .filter_map(|a| match a {
                    IRArg::Var(v) => Some(v.0),
                    IRArg::Erased => None,
                })
                .max()
                .unwrap_or(0),
        ),
        IRExpr::Lit(_) | IRExpr::String(_) => 0,
    }
}
fn max_jp_id(body: &IRBody) -> u32 {
    match body {
        IRBody::JDecl { jp, body, rest, .. } => jp.0.max(max_jp_id(body)).max(max_jp_id(rest)),
        IRBody::Case { alts, default, .. } => alts
            .iter()
            .map(|a| max_jp_id(&a.body))
            .max()
            .unwrap_or(0)
            .max(default.as_ref().map_or(0, |d| max_jp_id(d))),
        IRBody::Jmp { jp, .. } => jp.0,
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => max_jp_id(rest),
        IRBody::Ret(_) | IRBody::Unreachable => 0,
    }
}
