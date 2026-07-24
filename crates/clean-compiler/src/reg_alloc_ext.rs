// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended register allocation for L5IR.
//! Part of #3083.

use crate::error::CompilerError;
use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, VarId};
use crate::reg_alloc::{
    allocate_registers, compute_live_intervals, LiveInterval, PhysicalLoc, RegAllocConfig,
    RegAllocStats, RegAllocation,
};
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};
use thiserror::Error;

#[derive(Debug, Error)]
pub(crate) enum RegAllocExtError {
    #[error(transparent)]
    Base(#[from] CompilerError),
    #[error("register allocation missing assignment for variable {var:?}")]
    UnassignedVar { var: VarId },
    #[error("interfering variables {left:?} and {right:?} share register {reg}")]
    InterferenceConflict { left: VarId, right: VarId, reg: u8 },
    #[error("split point {point} is invalid for variable {var:?}")]
    InvalidSplitPoint { var: VarId, point: usize },
}

#[derive(Clone, Debug, Default)]
pub(crate) struct SpillCostAnalysis {
    pub(crate) per_variable: HashMap<VarId, f64>,
    pub(crate) loop_depths: HashMap<VarId, usize>,
    pub(crate) max_loop_depth: usize,
}
impl SpillCostAnalysis {
    #[must_use]
    pub(crate) fn analyze(decl: &IRDecl, intervals: &[LiveInterval]) -> Self {
        let mut analysis = Self::default();
        for (var, _) in &decl.params {
            analysis.bump(*var, 1.0, 0);
        }
        analysis.visit_body(&decl.body, 0);
        for interval in intervals {
            let depth = analysis
                .loop_depths
                .get(&interval.var)
                .copied()
                .unwrap_or(0);
            let span = interval.end.saturating_sub(interval.start).max(1) as f64;
            *analysis.per_variable.entry(interval.var).or_insert(0.0) +=
                span * (1.0 + depth as f64);
        }
        analysis
    }
    #[must_use]
    pub(crate) fn cost(&self, var: VarId) -> f64 {
        self.per_variable.get(&var).copied().unwrap_or(1.0)
    }
    #[must_use]
    pub(crate) fn spill_priority(&self, var: VarId, degree: usize) -> f64 {
        self.cost(var) / degree.max(1) as f64
    }
    pub(crate) fn bump(&mut self, var: VarId, base: f64, depth: usize) {
        *self.per_variable.entry(var).or_insert(0.0) += base * (1usize << depth.min(6)) as f64;
        self.loop_depths
            .entry(var)
            .and_modify(|seen| *seen = (*seen).max(depth))
            .or_insert(depth);
        self.max_loop_depth = self.max_loop_depth.max(depth);
    }
    pub(crate) fn visit_body(&mut self, body: &IRBody, depth: usize) {
        match body {
            IRBody::VDecl {
                var, value, rest, ..
            } => {
                self.visit_expr(value, depth);
                self.bump(*var, 0.5, depth);
                self.visit_body(rest, depth);
            }
            IRBody::JDecl {
                params, body, rest, ..
            } => {
                for (var, _) in params {
                    self.bump(*var, 0.5, depth + 1);
                }
                self.visit_body(body, depth + 1);
                self.visit_body(rest, depth);
            }
            IRBody::Inc { var, rest, .. }
            | IRBody::Dec { var, rest }
            | IRBody::SetTag { var, rest, .. } => {
                self.bump(*var, 1.0, depth);
                self.visit_body(rest, depth);
            }
            IRBody::Set {
                var, value, rest, ..
            }
            | IRBody::USet {
                var, value, rest, ..
            }
            | IRBody::SSet {
                var, value, rest, ..
            } => {
                self.bump(*var, 1.0, depth);
                self.bump(*value, 1.0, depth);
                self.visit_body(rest, depth);
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.bump(*scrutinee, 1.0, depth);
                for alt in alts {
                    self.visit_body(&alt.body, depth);
                }
                if let Some(body) = default {
                    self.visit_body(body, depth);
                }
            }
            IRBody::Jmp { args, .. } => {
                for arg in args {
                    self.visit_arg(arg, depth);
                }
            }
            IRBody::Ret(arg) => self.visit_arg(arg, depth),
            IRBody::Unreachable => {}
        }
    }
    pub(crate) fn visit_expr(&mut self, expr: &IRExpr, depth: usize) {
        match expr {
            IRExpr::Ctor { args, .. }
            | IRExpr::Apply { args, .. }
            | IRExpr::PartialApply { args, .. } => {
                for arg in args {
                    self.visit_arg(arg, depth);
                }
            }
            IRExpr::Proj { arg, .. }
            | IRExpr::Tag(arg)
            | IRExpr::Box { arg, .. }
            | IRExpr::Unbox { arg, .. } => self.visit_arg(arg, depth),
            IRExpr::ClosureApply { closure, args } => {
                self.visit_arg(closure, depth);
                for arg in args {
                    self.visit_arg(arg, depth);
                }
            }
            IRExpr::UProj { var, .. }
            | IRExpr::SProj { var, .. }
            | IRExpr::IsShared(var)
            | IRExpr::Reset(var) => self.bump(*var, 1.0, depth),
            IRExpr::Reuse { var, args, .. } => {
                self.bump(*var, 1.0, depth);
                for arg in args {
                    self.visit_arg(arg, depth);
                }
            }
            IRExpr::Lit(_) | IRExpr::String(_) => {}
        }
    }
    pub(crate) fn visit_arg(&mut self, arg: &IRArg, depth: usize) {
        if let IRArg::Var(var) = arg {
            self.bump(*var, 1.0, depth);
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CoalesceResult {
    pub(crate) allocation: RegAllocation,
    pub(crate) applied_pairs: Vec<(VarId, VarId)>,
    pub(crate) rejected_pairs: Vec<(VarId, VarId)>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct InterferenceGraph {
    pub(crate) adjacency: HashMap<VarId, BTreeSet<u32>>,
}
impl InterferenceGraph {
    #[must_use]
    pub(crate) fn from_intervals(intervals: &[LiveInterval]) -> Self {
        let mut graph = Self::default();
        let mut sorted = intervals.to_vec();
        let mut active: Vec<LiveInterval> = Vec::new();
        sorted.sort_by_key(|iv| (iv.start, iv.end, iv.var.0));
        for interval in &sorted {
            active.retain(|live| live.end > interval.start);
            graph.adjacency.entry(interval.var).or_default();
            for other in &active {
                graph.add_edge(interval.var, other.var);
            }
            active.push(interval.clone());
            active.sort_by_key(|iv| iv.end);
        }
        graph
    }
    pub(crate) fn add_edge(&mut self, left: VarId, right: VarId) {
        if left == right {
            self.adjacency.entry(left).or_default();
            return;
        }
        self.adjacency.entry(left).or_default().insert(right.0);
        self.adjacency.entry(right).or_default().insert(left.0);
    }
    #[must_use]
    pub(crate) fn degree(&self, var: VarId) -> usize {
        self.adjacency.get(&var).map_or(0, BTreeSet::len)
    }
    #[must_use]
    pub(crate) fn neighbors(&self, var: VarId) -> Vec<VarId> {
        self.adjacency
            .get(&var)
            .map(|set| set.iter().copied().map(VarId).collect())
            .unwrap_or_default()
    }
    #[must_use]
    pub(crate) fn interferes(&self, left: VarId, right: VarId) -> bool {
        self.adjacency
            .get(&left)
            .is_some_and(|set| set.contains(&right.0))
    }
    #[must_use]
    pub(crate) fn vars(&self) -> Vec<VarId> {
        let mut vars: Vec<_> = self.adjacency.keys().copied().collect();
        vars.sort_by_key(|var| var.0);
        vars
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SplitPoint {
    pub(crate) var: VarId,
    pub(crate) point: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallingConvention {
    pub(crate) caller_saved: BTreeSet<u8>,
    pub(crate) callee_saved: BTreeSet<u8>,
    pub(crate) argument_registers: Vec<u8>,
    pub(crate) return_register: u8,
}
impl Default for CallingConvention {
    fn default() -> Self {
        Self::for_register_count(16)
    }
}
impl CallingConvention {
    #[must_use]
    pub(crate) fn for_register_count(num_registers: u8) -> Self {
        let caller_cut = num_registers.min(8);
        let mut caller_saved = BTreeSet::new();
        let mut callee_saved = BTreeSet::new();
        for reg in 0..num_registers {
            if reg < caller_cut {
                caller_saved.insert(reg);
            } else {
                callee_saved.insert(reg);
            }
        }
        Self {
            caller_saved,
            callee_saved,
            argument_registers: (0..num_registers.min(6)).collect(),
            return_register: 0,
        }
    }
    #[must_use]
    pub(crate) fn is_caller_saved(&self, reg: u8) -> bool {
        self.caller_saved.contains(&reg)
    }
    #[must_use]
    pub(crate) fn is_callee_saved(&self, reg: u8) -> bool {
        self.callee_saved.contains(&reg)
    }
    #[must_use]
    pub(crate) fn preferred_registers(&self, config: &RegAllocConfig) -> Vec<u8> {
        let (first, second) = if config.prefer_callee_saved {
            (&self.callee_saved, &self.caller_saved)
        } else {
            (&self.caller_saved, &self.callee_saved)
        };
        let mut seen = BTreeSet::new();
        let mut regs = Vec::new();
        for reg in first.iter().chain(second.iter()) {
            if seen.insert(*reg) {
                regs.push(*reg);
            }
        }
        regs
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ExtAllocStats {
    pub(crate) spills: usize,
    pub(crate) coalesces: usize,
    pub(crate) register_pressure_peak: usize,
    pub(crate) split_count: usize,
}

pub(crate) fn allocate_registers_linear_scan_ext(
    decl: &IRDecl,
    config: &RegAllocConfig,
) -> Result<RegAllocation, RegAllocExtError> {
    let _ = compute_live_intervals(decl);
    let mut allocation = allocate_registers(decl, config)?;
    let coalesced = allocation.stats.coalesced;
    refresh_allocation_stats(&mut allocation, coalesced);
    Ok(allocation)
}

pub(crate) fn allocate_registers_ext(
    decl: &IRDecl,
    config: &RegAllocConfig,
    convention: &CallingConvention,
    coalesce_pairs: &[(VarId, VarId)],
) -> Result<(RegAllocation, ExtAllocStats), RegAllocExtError> {
    let intervals = compute_live_intervals(decl);
    if intervals.is_empty() {
        return Ok((
            RegAllocation {
                assignments: HashMap::new(),
                stats: RegAllocStats::default(),
            },
            ExtAllocStats::default(),
        ));
    }
    let pressure_peak = compute_pressure_peak(&intervals);
    let pressure_points = collect_pressure_points(&intervals, config.num_registers as usize + 1);
    let split_count = intervals.iter().try_fold(0usize, |acc, interval| {
        split_lifetime(interval, &pressure_points).map(|(_, splits)| acc + splits.len())
    })?;
    let costs = SpillCostAnalysis::analyze(decl, &intervals);
    let graph = InterferenceGraph::from_intervals(&intervals);
    let linear = allocate_registers_linear_scan_ext(decl, config)?;
    let colored = color_interference_graph(&intervals, &graph, config, &costs, convention);
    let chosen = choose_better_allocation(linear, colored, convention);
    let coalesced = apply_bulk_coalescing(chosen, &graph, coalesce_pairs);
    validate_allocation(decl, &coalesced.allocation)?;
    let spills = count_spills(&coalesced.allocation);
    let coalesces = coalesced.applied_pairs.len();
    Ok((
        coalesced.allocation,
        ExtAllocStats {
            spills,
            coalesces,
            register_pressure_peak: pressure_peak,
            split_count,
        },
    ))
}

pub(crate) fn allocate_registers_ext_default(
    decl: &IRDecl,
) -> Result<(RegAllocation, ExtAllocStats), RegAllocExtError> {
    allocate_registers_ext(
        decl,
        &RegAllocConfig::default(),
        &CallingConvention::default(),
        &[],
    )
}

pub(crate) fn apply_bulk_coalescing(
    allocation: RegAllocation,
    graph: &InterferenceGraph,
    pairs: &[(VarId, VarId)],
) -> CoalesceResult {
    let mut result = CoalesceResult {
        allocation,
        applied_pairs: Vec::new(),
        rejected_pairs: Vec::new(),
    };
    for &(left, right) in pairs {
        if try_coalesce_pair(&mut result.allocation, graph, left, right) {
            result.applied_pairs.push((left, right));
        } else {
            result.rejected_pairs.push((left, right));
        }
    }
    refresh_allocation_stats(&mut result.allocation, result.applied_pairs.len());
    result
}

pub(crate) fn color_interference_graph(
    intervals: &[LiveInterval],
    graph: &InterferenceGraph,
    config: &RegAllocConfig,
    costs: &SpillCostAnalysis,
    convention: &CallingConvention,
) -> RegAllocation {
    let k = config.num_registers as usize;
    let mut work = graph.adjacency.clone();
    let mut spans = HashMap::new();
    let mut stack = Vec::new();
    for interval in intervals {
        spans.insert(interval.var, interval.end.saturating_sub(interval.start));
        work.entry(interval.var).or_default();
    }
    while !work.is_empty() {
        let next = work
            .iter()
            .filter(|(_, neighbors)| neighbors.len() < k)
            .map(|(var, neighbors)| (*var, neighbors.len()))
            .min_by_key(|(var, degree)| (*degree, var.0));
        let spill = next
            .map(|(var, _)| var)
            .unwrap_or_else(|| select_spill_candidate(&work, costs, &spans));
        if let Some(neighbors) = work.remove(&spill) {
            for neighbor in neighbors {
                if let Some(adj) = work.get_mut(&VarId(neighbor)) {
                    adj.remove(&spill.0);
                }
            }
        }
        stack.push(spill);
    }
    let order = register_order(config, convention);
    let mut allocation = RegAllocation {
        assignments: HashMap::new(),
        stats: RegAllocStats::default(),
    };
    let mut next_spill = 0i32;
    while let Some(var) = stack.pop() {
        let mut blocked = BTreeSet::new();
        for neighbor in graph.neighbors(var) {
            if let Some(PhysicalLoc::Register(reg)) = allocation.assignments.get(&neighbor) {
                blocked.insert(*reg);
            }
        }
        if let Some(reg) = order.iter().copied().find(|reg| !blocked.contains(reg)) {
            allocation
                .assignments
                .insert(var, PhysicalLoc::Register(reg));
        } else {
            allocation
                .assignments
                .insert(var, PhysicalLoc::Spilled(next_spill));
            next_spill += 1;
        }
    }
    refresh_allocation_stats(&mut allocation, 0);
    allocation
}

pub(crate) fn split_lifetime(
    interval: &LiveInterval,
    pressure_points: &[usize],
) -> Result<(Vec<LiveInterval>, Vec<SplitPoint>), RegAllocExtError> {
    let span = interval.end.saturating_sub(interval.start);
    if span < 6 {
        return Ok((vec![interval.clone()], Vec::new()));
    }
    let point = pressure_points
        .iter()
        .copied()
        .find(|point| *point > interval.start + 1 && *point + 1 < interval.end)
        .unwrap_or(interval.start + span / 2);
    if point <= interval.start || point >= interval.end {
        return Ok((vec![interval.clone()], Vec::new()));
    }
    if pressure_points
        .iter()
        .any(|candidate| *candidate <= interval.start || *candidate >= interval.end)
        && point <= interval.start + 1
    {
        return Err(RegAllocExtError::InvalidSplitPoint {
            var: interval.var,
            point,
        });
    }
    let left_span = point.saturating_sub(interval.start).max(1);
    let right_span = interval.end.saturating_sub(point).max(1);
    let total = (left_span + right_span) as f64;
    Ok((
        vec![
            LiveInterval {
                var: interval.var,
                start: interval.start,
                end: point,
                weight: interval.weight * left_span as f64 / total,
                is_fixed: interval.is_fixed,
            },
            LiveInterval {
                var: interval.var,
                start: point,
                end: interval.end,
                weight: interval.weight * right_span as f64 / total,
                is_fixed: interval.is_fixed,
            },
        ],
        vec![SplitPoint {
            var: interval.var,
            point,
        }],
    ))
}

pub(crate) fn validate_allocation(
    decl: &IRDecl,
    allocation: &RegAllocation,
) -> Result<(), RegAllocExtError> {
    let intervals = compute_live_intervals(decl);
    let graph = InterferenceGraph::from_intervals(&intervals);
    for interval in &intervals {
        if !allocation.assignments.contains_key(&interval.var) {
            return Err(RegAllocExtError::UnassignedVar { var: interval.var });
        }
    }
    for left in graph.vars() {
        let Some(PhysicalLoc::Register(reg)) = allocation.assignments.get(&left) else {
            continue;
        };
        for right in graph.neighbors(left) {
            if left.0 >= right.0 {
                continue;
            }
            if let Some(PhysicalLoc::Register(other)) = allocation.assignments.get(&right) {
                if reg == other {
                    return Err(RegAllocExtError::InterferenceConflict {
                        left,
                        right,
                        reg: *reg,
                    });
                }
            }
        }
    }
    Ok(())
}

pub(crate) fn collect_pressure_points(intervals: &[LiveInterval], threshold: usize) -> Vec<usize> {
    let mut events = Vec::with_capacity(intervals.len() * 2);
    for interval in intervals {
        events.push((interval.start, 1i32));
        events.push((interval.end, -1i32));
    }
    events.sort_by_key(|(point, delta)| (*point, *delta));
    let mut current = 0i32;
    let mut points = Vec::new();
    for (point, delta) in events {
        current += delta;
        if current as usize >= threshold {
            points.push(point);
        }
    }
    points.sort_unstable();
    points.dedup();
    points
}

pub(crate) fn compute_pressure_peak(intervals: &[LiveInterval]) -> usize {
    let mut events = Vec::with_capacity(intervals.len() * 2);
    for interval in intervals {
        events.push((interval.start, 1i32));
        events.push((interval.end, -1i32));
    }
    events.sort_by_key(|(point, delta)| (*point, *delta));
    let mut peak = 0usize;
    let mut current = 0i32;
    for (_, delta) in events {
        current += delta;
        peak = peak.max(current.max(0) as usize);
    }
    peak
}

pub(crate) fn choose_better_allocation(
    linear: RegAllocation,
    colored: RegAllocation,
    convention: &CallingConvention,
) -> RegAllocation {
    let linear_spills = count_spills(&linear);
    let colored_spills = count_spills(&colored);
    if colored_spills < linear_spills {
        return colored;
    }
    if colored_spills > linear_spills {
        return linear;
    }
    if count_caller_saved_uses(&colored, convention) < count_caller_saved_uses(&linear, convention)
    {
        colored
    } else {
        linear
    }
}

pub(crate) fn refresh_allocation_stats(allocation: &mut RegAllocation, coalesced: usize) {
    let mut regs = BTreeSet::new();
    let mut spills = 0usize;
    for loc in allocation.assignments.values() {
        match loc {
            PhysicalLoc::Register(reg) => {
                regs.insert(*reg);
            }
            PhysicalLoc::Stack(_) | PhysicalLoc::Spilled(_) => spills += 1,
        }
    }
    allocation.stats.registers_used = regs.len();
    allocation.stats.spills = spills;
    allocation.stats.coalesced = coalesced;
}

pub(crate) fn count_spills(allocation: &RegAllocation) -> usize {
    allocation
        .assignments
        .values()
        .filter(|loc| matches!(loc, PhysicalLoc::Stack(_) | PhysicalLoc::Spilled(_)))
        .count()
}

pub(crate) fn count_caller_saved_uses(
    allocation: &RegAllocation,
    convention: &CallingConvention,
) -> usize {
    allocation
        .assignments
        .values()
        .filter(|loc| match loc {
            PhysicalLoc::Register(reg) => convention.is_caller_saved(*reg),
            PhysicalLoc::Stack(_) | PhysicalLoc::Spilled(_) => false,
        })
        .count()
}

pub(crate) fn try_coalesce_pair(
    allocation: &mut RegAllocation,
    graph: &InterferenceGraph,
    left: VarId,
    right: VarId,
) -> bool {
    if graph.interferes(left, right) {
        return false;
    }
    let mut candidates = BTreeSet::new();
    if let Some(PhysicalLoc::Register(reg)) = allocation.assignments.get(&left) {
        candidates.insert(*reg);
    }
    if let Some(PhysicalLoc::Register(reg)) = allocation.assignments.get(&right) {
        candidates.insert(*reg);
    }
    for reg in candidates {
        if can_assign_register(allocation, graph, left, reg, &[right])
            && can_assign_register(allocation, graph, right, reg, &[left])
        {
            allocation
                .assignments
                .insert(left, PhysicalLoc::Register(reg));
            allocation
                .assignments
                .insert(right, PhysicalLoc::Register(reg));
            return true;
        }
    }
    false
}

pub(crate) fn can_assign_register(
    allocation: &RegAllocation,
    graph: &InterferenceGraph,
    var: VarId,
    reg: u8,
    ignored: &[VarId],
) -> bool {
    graph.neighbors(var).into_iter().all(|neighbor| {
        if ignored.contains(&neighbor) { return true; }
        !matches!(allocation.assignments.get(&neighbor), Some(PhysicalLoc::Register(existing)) if *existing == reg)
    })
}

pub(crate) fn select_spill_candidate(
    work: &HashMap<VarId, BTreeSet<u32>>,
    costs: &SpillCostAnalysis,
    spans: &HashMap<VarId, usize>,
) -> VarId {
    work.iter()
        .map(|(var, neighbors)| {
            (
                *var,
                costs.spill_priority(*var, neighbors.len()),
                spans.get(var).copied().unwrap_or(1),
            )
        })
        .min_by(|left, right| {
            left.1
                .partial_cmp(&right.1)
                .unwrap_or(Ordering::Equal)
                .then_with(|| right.2.cmp(&left.2))
                .then_with(|| left.0 .0.cmp(&right.0 .0))
        })
        .map(|(var, _, _)| var)
        .expect("invariant: spill candidate requested for non-empty graph")
}

pub(crate) fn register_order(config: &RegAllocConfig, convention: &CallingConvention) -> Vec<u8> {
    let mut regs = convention.preferred_registers(config);
    let mut seen = BTreeSet::new();
    for reg in &regs {
        seen.insert(*reg);
    }
    for reg in 0..config.num_registers {
        if seen.insert(reg) {
            regs.push(reg);
        }
    }
    regs
}
