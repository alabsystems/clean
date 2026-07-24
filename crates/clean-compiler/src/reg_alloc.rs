// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Register Allocation for L5IR.
//!
//! Assigns virtual `VarId` variables to physical registers or stack slots
//! using linear scan allocation with interference graph construction and
//! copy coalescing.
//!
//! 1. **Liveness analysis** — compute live intervals for each VarId
//! 2. **Interference graph** — variables live at the same point interfere
//! 3. **Linear scan** — assign registers by sweeping sorted intervals
//! 4. **Coalescing** — merge copy-related variables into the same register
//!
//! This pass operates on L5IR after RC insertion. It produces a
//! `RegAllocation` mapping `VarId -> PhysicalLoc` that downstream emitters
//! use for code generation.
//!
//! Part of #3084 - IO/FFI/Native epic.

#[path = "reg_alloc_liveness.rs"]
mod liveness;

use crate::error::CompilerError;
use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, VarId};
pub(crate) use liveness::compute_liveness;
use std::collections::{BTreeSet, HashMap, HashSet};

// -----------------------------------------------------------------------
// Physical location
// -----------------------------------------------------------------------

/// Physical location assignment for a variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PhysicalLoc {
    /// Assigned to physical register `n` (0-indexed).
    Register(u8),
    /// Assigned to stack slot at offset `n`.
    Stack(i32),
    /// Spilled to memory at offset `n` (evicted from register).
    Spilled(i32),
}

// -----------------------------------------------------------------------
// Configuration
// -----------------------------------------------------------------------

/// Configuration for register allocation.
#[derive(Debug, Clone)]
pub(crate) struct RegAllocConfig {
    /// Number of available physical registers.
    pub(crate) num_registers: u8,
    /// Whether to prefer callee-saved registers (reduces save/restore).
    pub(crate) prefer_callee_saved: bool,
    /// Spill weight threshold: intervals with weight below this are
    /// candidates for spilling when register pressure exceeds capacity.
    pub(crate) spill_weight_threshold: f64,
}

impl Default for RegAllocConfig {
    fn default() -> Self {
        Self {
            num_registers: 16,
            prefer_callee_saved: false,
            spill_weight_threshold: 1.0,
        }
    }
}

// -----------------------------------------------------------------------
// Live interval
// -----------------------------------------------------------------------

/// Live interval for a variable: the range of program points where it is live,
/// plus metadata for allocation heuristics.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct LiveInterval {
    /// The variable this interval belongs to.
    pub(crate) var: VarId,
    /// Start program point (inclusive).
    pub(crate) start: usize,
    /// End program point (exclusive).
    pub(crate) end: usize,
    /// Spill weight: higher means more expensive to spill.
    /// Computed as `(end - start) * use_count`.
    pub(crate) weight: f64,
    /// Whether this variable has a fixed register assignment (e.g. ABI constraint).
    pub(crate) is_fixed: bool,
}

// -----------------------------------------------------------------------
// Statistics
// -----------------------------------------------------------------------

/// Statistics from a register allocation pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct RegAllocStats {
    /// Number of physical registers used.
    pub(crate) registers_used: usize,
    /// Number of variables spilled to stack/memory.
    pub(crate) spills: usize,
    /// Number of move instructions that would be needed.
    pub(crate) moves: usize,
    /// Number of variables successfully coalesced.
    pub(crate) coalesced: usize,
}

// -----------------------------------------------------------------------
// Allocation result
// -----------------------------------------------------------------------

/// Result of register allocation for a single declaration.
#[derive(Debug, Clone)]
pub(crate) struct RegAllocation {
    /// Mapping from VarId to physical location.
    pub(crate) assignments: HashMap<VarId, PhysicalLoc>,
    /// Allocation statistics.
    pub(crate) stats: RegAllocStats,
}

// -----------------------------------------------------------------------
// Compute live intervals
// -----------------------------------------------------------------------

/// Compute live intervals for all variables in an IR declaration.
///
/// Walks the IR body to determine def/use ranges and computes a spill
/// weight for each variable based on range length and use frequency.
#[must_use]
pub(crate) fn compute_live_intervals(decl: &IRDecl) -> Vec<LiveInterval> {
    let (ranges, _max_pt, _pressure) = compute_liveness(decl);
    let mut use_counts: HashMap<VarId, usize> = HashMap::new();
    count_uses_body(&decl.body, &mut use_counts);
    for (var, _) in &decl.params {
        *use_counts.entry(*var).or_default() += 1;
    }

    let mut intervals: Vec<LiveInterval> = ranges
        .into_iter()
        .map(|(var, range)| {
            let span = (range.end as usize)
                .saturating_sub(range.start as usize)
                .max(1);
            let uses = use_counts.get(&var).copied().unwrap_or(1) as f64;
            LiveInterval {
                var,
                start: range.start as usize,
                end: range.end as usize,
                weight: span as f64 * uses,
                is_fixed: false,
            }
        })
        .collect();
    intervals.sort_by_key(|iv| iv.start);
    intervals
}

/// Count variable uses across an IR body (for spill weight computation).
fn count_uses_body(body: &IRBody, counts: &mut HashMap<VarId, usize>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            count_uses_expr(value, counts);
            count_uses_body(rest, counts);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            count_uses_body(jp_body, counts);
            count_uses_body(rest, counts);
        }
        IRBody::Inc { var, rest, .. } => {
            *counts.entry(*var).or_default() += 1;
            count_uses_body(rest, counts);
        }
        IRBody::Dec { var, rest } => {
            *counts.entry(*var).or_default() += 1;
            count_uses_body(rest, counts);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            *counts.entry(*var).or_default() += 1;
            *counts.entry(*value).or_default() += 1;
            count_uses_body(rest, counts);
        }
        IRBody::SetTag { var, rest, .. } => {
            *counts.entry(*var).or_default() += 1;
            count_uses_body(rest, counts);
        }
        IRBody::USet {
            var, value, rest, ..
        } => {
            *counts.entry(*var).or_default() += 1;
            *counts.entry(*value).or_default() += 1;
            count_uses_body(rest, counts);
        }
        IRBody::SSet {
            var, value, rest, ..
        } => {
            *counts.entry(*var).or_default() += 1;
            *counts.entry(*value).or_default() += 1;
            count_uses_body(rest, counts);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            *counts.entry(*scrutinee).or_default() += 1;
            for alt in alts {
                count_uses_body(&alt.body, counts);
            }
            if let Some(d) = default {
                count_uses_body(d, counts);
            }
        }
        IRBody::Jmp { args, .. } => {
            for arg in args {
                count_uses_arg(arg, counts);
            }
        }
        IRBody::Ret(arg) => {
            count_uses_arg(arg, counts);
        }
        IRBody::Unreachable => {}
    }
}

fn count_uses_arg(arg: &IRArg, counts: &mut HashMap<VarId, usize>) {
    if let IRArg::Var(v) = arg {
        *counts.entry(*v).or_default() += 1;
    }
}

fn count_uses_expr(expr: &IRExpr, counts: &mut HashMap<VarId, usize>) {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => {
            for a in args {
                count_uses_arg(a, counts);
            }
        }
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => {
            count_uses_arg(arg, counts);
        }
        IRExpr::ClosureApply { closure, args } => {
            count_uses_arg(closure, counts);
            for a in args {
                count_uses_arg(a, counts);
            }
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => {
            *counts.entry(*var).or_default() += 1;
        }
        IRExpr::Reuse { var, args, .. } => {
            *counts.entry(*var).or_default() += 1;
            for a in args {
                count_uses_arg(a, counts);
            }
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
}

// -----------------------------------------------------------------------
// Interference graph
// -----------------------------------------------------------------------

/// Build an interference graph from live intervals.
///
/// Two variables interfere if their live intervals overlap. Returns a
/// list of `(VarId, VarId)` pairs representing interference edges
/// (each edge appears once, with the smaller VarId first).
#[must_use]
pub(crate) fn build_interference_graph(intervals: &[LiveInterval]) -> Vec<(VarId, VarId)> {
    let mut seen: HashSet<(u32, u32)> = HashSet::new();
    let mut edges: Vec<(VarId, VarId)> = Vec::new();
    let n = intervals.len();
    for i in 0..n {
        for j in (i + 1)..n {
            if intervals[j].start >= intervals[i].end {
                break;
            }
            let (a, b) = if intervals[i].var.0 <= intervals[j].var.0 {
                (intervals[i].var, intervals[j].var)
            } else {
                (intervals[j].var, intervals[i].var)
            };
            if seen.insert((a.0, b.0)) {
                edges.push((a, b));
            }
        }
    }
    edges
}

// -----------------------------------------------------------------------
// Linear scan register allocation
// -----------------------------------------------------------------------

/// Perform linear scan register allocation on an IR declaration.
///
/// Sorts intervals by start point, maintains an active set, and assigns
/// registers greedily. When all registers are occupied, the interval with
/// the lowest weight is spilled.
pub(crate) fn allocate_registers(
    decl: &IRDecl,
    config: &RegAllocConfig,
) -> Result<RegAllocation, CompilerError> {
    let intervals = compute_live_intervals(decl);
    if intervals.is_empty() {
        return Ok(RegAllocation {
            assignments: HashMap::new(),
            stats: RegAllocStats::default(),
        });
    }

    let mut assignments: HashMap<VarId, PhysicalLoc> = HashMap::new();
    // Active list: (end point, var, register index)
    let mut active: Vec<(usize, VarId, u8)> = Vec::new();
    let mut free_regs: BTreeSet<u8> = (0..config.num_registers).collect();
    let mut next_spill_slot: i32 = 0;
    let mut spill_count = 0usize;
    let mut regs_used: HashSet<u8> = HashSet::new();

    // Weight map for spill decisions.
    let weight_map: HashMap<VarId, f64> = intervals.iter().map(|iv| (iv.var, iv.weight)).collect();

    for interval in &intervals {
        // Expire old intervals whose end <= current start.
        let cur_start = interval.start;
        active.retain(|&(end, var, reg)| {
            if end <= cur_start {
                free_regs.insert(reg);
                let _ = var; // suppress unused warning
                false
            } else {
                true
            }
        });

        if interval.is_fixed {
            // Fixed intervals get register 0 if available, else spill.
            if let Some(&reg) = free_regs.iter().next() {
                free_regs.remove(&reg);
                regs_used.insert(reg);
                assignments.insert(interval.var, PhysicalLoc::Register(reg));
                active.push((interval.end, interval.var, reg));
                active.sort_by_key(|&(end, _, _)| end);
            } else {
                assignments.insert(interval.var, PhysicalLoc::Spilled(next_spill_slot));
                next_spill_slot += 1;
                spill_count += 1;
            }
            continue;
        }

        if !free_regs.is_empty() {
            // Allocate the lowest (or highest for callee-saved preference) free register.
            let reg = if config.prefer_callee_saved {
                // Prefer higher-numbered registers (typically callee-saved).
                *free_regs
                    .iter()
                    .next_back()
                    .expect("invariant: free_regs non-empty")
            } else {
                *free_regs
                    .iter()
                    .next()
                    .expect("invariant: free_regs non-empty")
            };
            free_regs.remove(&reg);
            regs_used.insert(reg);
            assignments.insert(interval.var, PhysicalLoc::Register(reg));
            active.push((interval.end, interval.var, reg));
            active.sort_by_key(|&(end, _, _)| end);
        } else {
            // All registers occupied: spill the active interval with lowest weight,
            // or spill the current interval if it has the lowest weight.
            let spill_candidate = active.iter().enumerate().min_by(|(_, a), (_, b)| {
                let wa = weight_map.get(&a.1).copied().unwrap_or(0.0);
                let wb = weight_map.get(&b.1).copied().unwrap_or(0.0);
                wa.partial_cmp(&wb).unwrap_or(std::cmp::Ordering::Equal)
            });

            let cur_weight = interval.weight;
            if let Some((idx, &(_, spill_var, spill_reg))) = spill_candidate {
                let candidate_weight = weight_map.get(&spill_var).copied().unwrap_or(0.0);
                if candidate_weight < cur_weight
                    && candidate_weight < config.spill_weight_threshold * cur_weight
                {
                    // Spill the existing active interval, give its register to current.
                    assignments.insert(spill_var, PhysicalLoc::Spilled(next_spill_slot));
                    next_spill_slot += 1;
                    spill_count += 1;
                    active.remove(idx);
                    assignments.insert(interval.var, PhysicalLoc::Register(spill_reg));
                    active.push((interval.end, interval.var, spill_reg));
                    active.sort_by_key(|&(end, _, _)| end);
                } else {
                    // Spill the current interval.
                    assignments.insert(interval.var, PhysicalLoc::Spilled(next_spill_slot));
                    next_spill_slot += 1;
                    spill_count += 1;
                }
            } else {
                // No active intervals (shouldn't happen if k > 0).
                assignments.insert(interval.var, PhysicalLoc::Spilled(next_spill_slot));
                next_spill_slot += 1;
                spill_count += 1;
            }
        }
    }

    Ok(RegAllocation {
        stats: RegAllocStats {
            registers_used: regs_used.len(),
            spills: spill_count,
            moves: 0,
            coalesced: 0,
        },
        assignments,
    })
}

/// Allocate registers with default configuration (16 registers).
pub(crate) fn allocate_registers_default(decl: &IRDecl) -> Result<RegAllocation, CompilerError> {
    allocate_registers(decl, &RegAllocConfig::default())
}

// -----------------------------------------------------------------------
// Coalescing
// -----------------------------------------------------------------------

/// Attempt to coalesce two variables by assigning them the same register.
///
/// Succeeds if `src` and `dst` do not interfere (are never simultaneously
/// live) and `src` currently has a register assignment. On success, `dst`
/// is assigned the same register as `src` and the stats are updated.
///
/// Returns `true` if coalescing succeeded.
pub(crate) fn try_coalesce(allocation: &mut RegAllocation, src: VarId, dst: VarId) -> bool {
    let src_loc = match allocation.assignments.get(&src) {
        Some(loc) => *loc,
        None => return false,
    };

    // Only coalesce if source is in a register.
    let reg = match src_loc {
        PhysicalLoc::Register(r) => r,
        _ => return false,
    };

    // Check that dst doesn't already have a conflicting register.
    if let Some(&PhysicalLoc::Register(existing)) = allocation.assignments.get(&dst) {
        if existing == reg {
            // Already coalesced.
            return true;
        }
        // Different register — cannot coalesce without full interference check.
        return false;
    }

    allocation
        .assignments
        .insert(dst, PhysicalLoc::Register(reg));
    allocation.stats.coalesced += 1;
    true
}

#[cfg(test)]
#[path = "reg_alloc_tests.rs"]
mod tests;
