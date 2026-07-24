// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Liveness analysis for L5IR register allocation.
//!
//! Computes live ranges for each `VarId` by walking the IR body linearly,
//! recording definition and last-use program points. Also computes maximum
//! register pressure via an event-based sweep.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, VarId};
use std::collections::{HashMap, HashSet};

/// A linearized program point for liveness analysis.
pub(crate) type ProgramPoint = u32;

/// Live range: the half-open interval `[start, end)` of program points
/// where a variable is live.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LiveRange {
    pub(crate) start: ProgramPoint,
    pub(crate) end: ProgramPoint,
}

/// Linearize the IR body, assigning program points and computing
/// def/use information. Returns (live_ranges, max_program_point, max_pressure).
pub(crate) fn compute_liveness(decl: &IRDecl) -> (HashMap<VarId, LiveRange>, ProgramPoint, usize) {
    let mut defs: HashMap<VarId, ProgramPoint> = HashMap::new();
    let mut last_uses: HashMap<VarId, ProgramPoint> = HashMap::new();
    // Record parameter definitions at point 0.
    for (var, _ty) in &decl.params {
        defs.insert(*var, 0);
    }
    let mut point: ProgramPoint = 1;

    collect_def_use_body(&decl.body, &mut defs, &mut last_uses, &mut point);

    // Build live ranges: [def, last_use + 1) for each variable.
    let mut ranges = HashMap::new();
    let mut all_vars: HashSet<VarId> = HashSet::new();
    all_vars.extend(defs.keys());
    all_vars.extend(last_uses.keys());

    for var in &all_vars {
        let start = defs.get(var).copied().unwrap_or(0);
        let end = last_uses
            .get(var)
            .copied()
            .map(|u| u + 1)
            .unwrap_or(start + 1);
        ranges.insert(*var, LiveRange { start, end });
    }

    let max_point = point;
    let max_pressure = compute_max_pressure(&ranges, max_point);
    (ranges, max_point, max_pressure)
}

/// Compute maximum register pressure: max number of simultaneously live vars.
pub(crate) fn compute_max_pressure(
    ranges: &HashMap<VarId, LiveRange>,
    _max_point: ProgramPoint,
) -> usize {
    let mut max_p = 0usize;
    let mut events: Vec<(ProgramPoint, i32)> = Vec::with_capacity(ranges.len() * 2);
    for range in ranges.values() {
        events.push((range.start, 1));
        events.push((range.end, -1));
    }
    events.sort_by_key(|&(pt, delta)| (pt, delta));
    let mut current = 0i32;
    for (_pt, delta) in &events {
        current += delta;
        if current > max_p as i32 {
            max_p = current as usize;
        }
    }
    max_p
}

/// Walk an IR body linearly, recording def and use points.
fn collect_def_use_body(
    body: &IRBody,
    defs: &mut HashMap<VarId, ProgramPoint>,
    uses: &mut HashMap<VarId, ProgramPoint>,
    point: &mut ProgramPoint,
) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            collect_use_expr(value, uses, *point);
            defs.entry(*var).or_insert(*point);
            *point += 1;
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::JDecl {
            params,
            body: jp_body,
            rest,
            ..
        } => {
            for (var, _ty) in params {
                defs.entry(*var).or_insert(*point);
            }
            *point += 1;
            collect_def_use_body(jp_body, defs, uses, point);
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::Inc { var, rest, .. } => {
            record_use(*var, uses, *point);
            *point += 1;
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::Dec { var, rest } => {
            record_use(*var, uses, *point);
            *point += 1;
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            record_use(*var, uses, *point);
            record_use(*value, uses, *point);
            *point += 1;
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::SetTag { var, rest, .. } => {
            record_use(*var, uses, *point);
            *point += 1;
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::USet {
            var, value, rest, ..
        } => {
            record_use(*var, uses, *point);
            record_use(*value, uses, *point);
            *point += 1;
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::SSet {
            var, value, rest, ..
        } => {
            record_use(*var, uses, *point);
            record_use(*value, uses, *point);
            *point += 1;
            collect_def_use_body(rest, defs, uses, point);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            record_use(*scrutinee, uses, *point);
            *point += 1;
            for alt in alts {
                collect_def_use_body(&alt.body, defs, uses, point);
            }
            if let Some(d) = default {
                collect_def_use_body(d, defs, uses, point);
            }
        }
        IRBody::Jmp { args, .. } => {
            for arg in args {
                collect_use_arg(arg, uses, *point);
            }
            *point += 1;
        }
        IRBody::Ret(arg) => {
            collect_use_arg(arg, uses, *point);
            *point += 1;
        }
        IRBody::Unreachable => {
            *point += 1;
        }
    }
}

fn record_use(var: VarId, uses: &mut HashMap<VarId, ProgramPoint>, pt: ProgramPoint) {
    uses.entry(var)
        .and_modify(|existing| {
            if pt > *existing {
                *existing = pt;
            }
        })
        .or_insert(pt);
}

fn collect_use_arg(arg: &IRArg, uses: &mut HashMap<VarId, ProgramPoint>, pt: ProgramPoint) {
    if let IRArg::Var(v) = arg {
        record_use(*v, uses, pt);
    }
}

fn collect_use_expr(expr: &IRExpr, uses: &mut HashMap<VarId, ProgramPoint>, pt: ProgramPoint) {
    match expr {
        IRExpr::Ctor { args, .. } => {
            for a in args {
                collect_use_arg(a, uses, pt);
            }
        }
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => {
            collect_use_arg(arg, uses, pt);
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
        IRExpr::Apply { args, .. } | IRExpr::PartialApply { args, .. } => {
            for a in args {
                collect_use_arg(a, uses, pt);
            }
        }
        IRExpr::ClosureApply { closure, args } => {
            collect_use_arg(closure, uses, pt);
            for a in args {
                collect_use_arg(a, uses, pt);
            }
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => {
            record_use(*var, uses, pt);
        }
        IRExpr::Reuse { var, args, .. } => {
            record_use(*var, uses, pt);
            for a in args {
                collect_use_arg(a, uses, pt);
            }
        }
    }
}
