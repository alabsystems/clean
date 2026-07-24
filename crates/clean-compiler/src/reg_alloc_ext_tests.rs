// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended register allocation (reg_alloc_ext).
//! Part of #3083.

use super::reg_alloc_ext::*;
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use crate::reg_alloc::{
    compute_live_intervals, LiveInterval, PhysicalLoc, RegAllocConfig, RegAllocStats, RegAllocation,
};
use clean_kernel::Name;
use std::collections::{BTreeSet, HashMap};

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

fn var(n: u32) -> VarId {
    VarId(n)
}
fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}
fn lit_u64(v: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(v))
}
fn default_config() -> RegAllocConfig {
    RegAllocConfig::default()
}

fn config_with_regs(n: u8) -> RegAllocConfig {
    RegAllocConfig {
        num_registers: n,
        ..default_config()
    }
}

fn vdecl(id: u32, expr: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(id),
        ty: IRType::UInt64,
        value: expr,
        rest: Box::new(rest),
    }
}

fn ret(id: u32) -> IRBody {
    IRBody::Ret(arg_var(id))
}

fn make_decl(n: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(n),
        params,
        return_type: IRType::UInt64,
        body,
    }
}

fn make_interval(v: u32, start: usize, end: usize) -> LiveInterval {
    LiveInterval {
        var: var(v),
        start,
        end,
        weight: 1.0,
        is_fixed: false,
    }
}

fn make_allocation(pairs: &[(u32, PhysicalLoc)]) -> RegAllocation {
    let mut assignments = HashMap::new();
    for (v, loc) in pairs {
        assignments.insert(var(*v), *loc);
    }
    RegAllocation {
        assignments,
        stats: RegAllocStats::default(),
    }
}

// =======================================================================
// SpillCostAnalysis tests
// =======================================================================

#[test]
fn test_spill_cost_empty_decl() {
    let decl = make_decl("f", vec![], IRBody::Unreachable);
    let intervals: Vec<LiveInterval> = vec![];
    let analysis = SpillCostAnalysis::analyze(&decl, &intervals);
    assert!(analysis.per_variable.is_empty());
    assert_eq!(analysis.max_loop_depth, 0);
}

#[test]
fn test_spill_cost_params_get_cost() {
    let decl = make_decl("f", vec![(var(0), IRType::UInt64)], ret(0));
    let intervals = compute_live_intervals(&decl);
    let analysis = SpillCostAnalysis::analyze(&decl, &intervals);
    assert!(
        analysis.cost(var(0)) > 0.0,
        "parameter should have nonzero cost"
    );
}

#[test]
fn test_spill_cost_higher_for_more_uses() {
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            0,
            lit_u64(1),
            vdecl(
                1,
                lit_u64(2),
                vdecl(
                    2,
                    IRExpr::Apply {
                        fn_id: fn_id("add"),
                        args: vec![arg_var(0), arg_var(1)],
                    },
                    vdecl(
                        3,
                        IRExpr::Apply {
                            fn_id: fn_id("add"),
                            args: vec![arg_var(1), arg_var(2)],
                        },
                        ret(3),
                    ),
                ),
            ),
        ),
    );
    let intervals = compute_live_intervals(&decl);
    let analysis = SpillCostAnalysis::analyze(&decl, &intervals);
    assert!(
        analysis.cost(var(1)) >= analysis.cost(var(0)),
        "var(1) used more often should have >= cost"
    );
}

#[test]
fn test_spill_cost_unknown_var_returns_default() {
    let analysis = SpillCostAnalysis::default();
    assert!(
        (analysis.cost(var(999)) - 1.0).abs() < f64::EPSILON,
        "unknown var should return default cost of 1.0"
    );
}

#[test]
fn test_spill_priority_scales_with_degree() {
    let mut analysis = SpillCostAnalysis::default();
    analysis.bump(var(0), 10.0, 0);
    let p1 = analysis.spill_priority(var(0), 1);
    let p5 = analysis.spill_priority(var(0), 5);
    assert!(p1 > p5, "higher degree should lower spill priority");
}

#[test]
fn test_spill_cost_loop_depth_increases_cost() {
    let mut a = SpillCostAnalysis::default();
    a.bump(var(0), 1.0, 0);
    let cost_depth0 = a.cost(var(0));
    let mut b = SpillCostAnalysis::default();
    b.bump(var(1), 1.0, 3);
    let cost_depth3 = b.cost(var(1));
    assert!(
        cost_depth3 > cost_depth0,
        "deeper loop depth => higher cost"
    );
}

#[test]
fn test_spill_cost_jdecl_increases_depth() {
    let decl = make_decl(
        "f",
        vec![],
        IRBody::JDecl {
            jp: crate::ir::JoinPointId(0),
            params: vec![(var(0), IRType::UInt64)],
            body: Box::new(ret(0)),
            rest: Box::new(vdecl(
                1,
                lit_u64(1),
                IRBody::Jmp {
                    jp: crate::ir::JoinPointId(0),
                    args: vec![arg_var(1)],
                },
            )),
        },
    );
    let intervals = compute_live_intervals(&decl);
    let analysis = SpillCostAnalysis::analyze(&decl, &intervals);
    assert!(
        analysis.loop_depths.get(&var(0)).copied().unwrap_or(0) >= 1,
        "JDecl param should be at depth >= 1"
    );
}

// =======================================================================
// InterferenceGraph tests
// =======================================================================

#[test]
fn test_interference_graph_empty() {
    let graph = InterferenceGraph::from_intervals(&[]);
    assert!(graph.vars().is_empty());
}

#[test]
fn test_interference_graph_no_overlap() {
    let intervals = vec![make_interval(0, 0, 3), make_interval(1, 3, 6)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    assert!(!graph.interferes(var(0), var(1)));
    assert_eq!(graph.degree(var(0)), 0);
    assert_eq!(graph.degree(var(1)), 0);
}

#[test]
fn test_interference_graph_overlap() {
    let intervals = vec![make_interval(0, 0, 5), make_interval(1, 2, 7)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    assert!(graph.interferes(var(0), var(1)));
    assert_eq!(graph.degree(var(0)), 1);
    assert_eq!(graph.degree(var(1)), 1);
}

#[test]
fn test_interference_graph_three_way_clique() {
    let intervals = vec![
        make_interval(0, 0, 10),
        make_interval(1, 0, 10),
        make_interval(2, 0, 10),
    ];
    let graph = InterferenceGraph::from_intervals(&intervals);
    assert!(graph.interferes(var(0), var(1)));
    assert!(graph.interferes(var(1), var(2)));
    assert!(graph.interferes(var(0), var(2)));
    assert_eq!(graph.degree(var(0)), 2);
}

#[test]
fn test_interference_graph_chain() {
    let intervals = vec![
        make_interval(0, 0, 5),
        make_interval(1, 3, 8),
        make_interval(2, 6, 10),
    ];
    let graph = InterferenceGraph::from_intervals(&intervals);
    assert!(graph.interferes(var(0), var(1)));
    assert!(graph.interferes(var(1), var(2)));
    assert!(!graph.interferes(var(0), var(2)));
}

#[test]
fn test_interference_graph_self_edge_noop() {
    let mut graph = InterferenceGraph::default();
    graph.add_edge(var(0), var(0));
    assert_eq!(graph.degree(var(0)), 0);
    assert!(!graph.interferes(var(0), var(0)));
}

#[test]
fn test_interference_graph_neighbors() {
    let intervals = vec![make_interval(0, 0, 10), make_interval(1, 0, 10)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let neighbors = graph.neighbors(var(0));
    assert_eq!(neighbors.len(), 1);
    assert_eq!(neighbors[0], var(1));
}

// =======================================================================
// CallingConvention tests
// =======================================================================

#[test]
fn test_calling_convention_default_16_regs() {
    let cc = CallingConvention::default();
    assert_eq!(cc.caller_saved.len(), 8);
    assert_eq!(cc.callee_saved.len(), 8);
    assert_eq!(cc.argument_registers.len(), 6);
    assert_eq!(cc.return_register, 0);
}

#[test]
fn test_calling_convention_small() {
    let cc = CallingConvention::for_register_count(4);
    assert_eq!(cc.caller_saved.len(), 4);
    assert_eq!(cc.callee_saved.len(), 0);
    assert_eq!(cc.argument_registers.len(), 4);
}

#[test]
fn test_calling_convention_is_caller_saved() {
    let cc = CallingConvention::default();
    assert!(cc.is_caller_saved(0));
    assert!(cc.is_caller_saved(7));
    assert!(!cc.is_caller_saved(8));
    assert!(cc.is_callee_saved(8));
    assert!(cc.is_callee_saved(15));
    assert!(!cc.is_callee_saved(0));
}

#[test]
fn test_calling_convention_preferred_registers_default() {
    let cc = CallingConvention::default();
    let config = default_config();
    let preferred = cc.preferred_registers(&config);
    assert!(preferred.len() >= 16);
    // Without prefer_callee_saved, caller-saved come first.
    assert!(preferred[0] < 8, "first preferred should be caller-saved");
}

#[test]
fn test_calling_convention_preferred_registers_callee_first() {
    let cc = CallingConvention::default();
    let config = RegAllocConfig {
        prefer_callee_saved: true,
        ..default_config()
    };
    let preferred = cc.preferred_registers(&config);
    assert!(
        preferred[0] >= 8,
        "first preferred should be callee-saved with prefer_callee_saved"
    );
}

// =======================================================================
// SplitPoint / split_lifetime tests
// =======================================================================

#[test]
fn test_split_lifetime_short_interval_no_split() {
    let interval = make_interval(0, 0, 3);
    let (parts, splits) = split_lifetime(&interval, &[1]).expect("should not error");
    assert_eq!(parts.len(), 1);
    assert!(splits.is_empty());
}

#[test]
fn test_split_lifetime_long_interval_splits() {
    let interval = make_interval(0, 0, 20);
    let (parts, splits) = split_lifetime(&interval, &[10]).expect("should not error");
    assert_eq!(parts.len(), 2);
    assert_eq!(splits.len(), 1);
    assert_eq!(splits[0].var, var(0));
    assert_eq!(splits[0].point, 10);
    assert_eq!(parts[0].start, 0);
    assert_eq!(parts[0].end, 10);
    assert_eq!(parts[1].start, 10);
    assert_eq!(parts[1].end, 20);
}

#[test]
fn test_split_lifetime_preserves_weight() {
    let interval = LiveInterval {
        var: var(0),
        start: 0,
        end: 20,
        weight: 10.0,
        is_fixed: false,
    };
    let (parts, _) = split_lifetime(&interval, &[10]).expect("should not error");
    let total_weight: f64 = parts.iter().map(|p| p.weight).sum();
    assert!(
        (total_weight - 10.0).abs() < 0.01,
        "split should preserve total weight"
    );
}

#[test]
fn test_split_lifetime_no_pressure_points_splits_at_midpoint() {
    let interval = make_interval(0, 0, 20);
    let (parts, splits) = split_lifetime(&interval, &[]).expect("should not error");
    assert_eq!(parts.len(), 2);
    assert_eq!(splits[0].point, 10);
}

#[test]
fn test_split_lifetime_preserves_is_fixed() {
    let interval = LiveInterval {
        var: var(0),
        start: 0,
        end: 20,
        weight: 1.0,
        is_fixed: true,
    };
    let (parts, _) = split_lifetime(&interval, &[10]).expect("should not error");
    assert!(parts[0].is_fixed);
    assert!(parts[1].is_fixed);
}

// =======================================================================
// Pressure analysis tests
// =======================================================================

#[test]
fn test_compute_pressure_peak_single() {
    let intervals = vec![make_interval(0, 0, 5)];
    assert_eq!(compute_pressure_peak(&intervals), 1);
}

#[test]
fn test_compute_pressure_peak_overlapping() {
    let intervals = vec![
        make_interval(0, 0, 10),
        make_interval(1, 0, 10),
        make_interval(2, 0, 10),
    ];
    assert_eq!(compute_pressure_peak(&intervals), 3);
}

#[test]
fn test_compute_pressure_peak_non_overlapping() {
    let intervals = vec![
        make_interval(0, 0, 3),
        make_interval(1, 3, 6),
        make_interval(2, 6, 9),
    ];
    assert_eq!(compute_pressure_peak(&intervals), 1);
}

#[test]
fn test_collect_pressure_points_above_threshold() {
    let intervals = vec![
        make_interval(0, 0, 10),
        make_interval(1, 0, 10),
        make_interval(2, 0, 10),
    ];
    let points = collect_pressure_points(&intervals, 3);
    assert!(
        !points.is_empty(),
        "should have pressure points at threshold 3"
    );
}

#[test]
fn test_collect_pressure_points_below_threshold() {
    let intervals = vec![make_interval(0, 0, 5)];
    let points = collect_pressure_points(&intervals, 5);
    assert!(
        points.is_empty(),
        "single interval below threshold should yield no pressure points"
    );
}

// =======================================================================
// Coalescing tests
// =======================================================================

#[test]
fn test_coalesce_non_interfering_succeeds() {
    let intervals = vec![make_interval(0, 0, 3), make_interval(1, 5, 8)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let mut alloc =
        make_allocation(&[(0, PhysicalLoc::Register(2)), (1, PhysicalLoc::Register(5))]);
    assert!(try_coalesce_pair(&mut alloc, &graph, var(0), var(1)));
}

#[test]
fn test_coalesce_interfering_fails() {
    let intervals = vec![make_interval(0, 0, 10), make_interval(1, 5, 15)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let mut alloc =
        make_allocation(&[(0, PhysicalLoc::Register(2)), (1, PhysicalLoc::Register(5))]);
    assert!(!try_coalesce_pair(&mut alloc, &graph, var(0), var(1)));
}

#[test]
fn test_bulk_coalesce_mixed() {
    let intervals = vec![
        make_interval(0, 0, 3),
        make_interval(1, 5, 8),
        make_interval(2, 0, 10),
        make_interval(3, 5, 15),
    ];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let alloc = make_allocation(&[
        (0, PhysicalLoc::Register(0)),
        (1, PhysicalLoc::Register(1)),
        (2, PhysicalLoc::Register(2)),
        (3, PhysicalLoc::Register(3)),
    ]);
    let pairs = vec![(var(0), var(1)), (var(2), var(3))];
    let result = apply_bulk_coalescing(alloc, &graph, &pairs);
    assert_eq!(
        result.applied_pairs.len(),
        1,
        "non-interfering pair should coalesce"
    );
    assert_eq!(
        result.rejected_pairs.len(),
        1,
        "interfering pair should be rejected"
    );
}

#[test]
fn test_bulk_coalesce_empty_pairs() {
    let alloc = make_allocation(&[(0, PhysicalLoc::Register(0))]);
    let graph = InterferenceGraph::default();
    let result = apply_bulk_coalescing(alloc, &graph, &[]);
    assert!(result.applied_pairs.is_empty());
    assert!(result.rejected_pairs.is_empty());
}

// =======================================================================
// Graph coloring tests
// =======================================================================

#[test]
fn test_color_interference_graph_no_spill() {
    let intervals = vec![make_interval(0, 0, 5), make_interval(1, 3, 8)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let costs = SpillCostAnalysis::default();
    let cc = CallingConvention::default();
    let config = config_with_regs(16);
    let alloc = color_interference_graph(&intervals, &graph, &config, &costs, &cc);
    assert!(matches!(
        alloc.assignments.get(&var(0)),
        Some(PhysicalLoc::Register(_))
    ));
    assert!(matches!(
        alloc.assignments.get(&var(1)),
        Some(PhysicalLoc::Register(_))
    ));
    let r0 = match alloc.assignments[&var(0)] {
        PhysicalLoc::Register(r) => r,
        _ => panic!(),
    };
    let r1 = match alloc.assignments[&var(1)] {
        PhysicalLoc::Register(r) => r,
        _ => panic!(),
    };
    assert_ne!(r0, r1, "interfering vars must get different registers");
}

#[test]
fn test_color_interference_graph_forces_spill() {
    let intervals = vec![
        make_interval(0, 0, 10),
        make_interval(1, 0, 10),
        make_interval(2, 0, 10),
    ];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let costs = SpillCostAnalysis::default();
    let cc = CallingConvention::for_register_count(2);
    let config = config_with_regs(2);
    let alloc = color_interference_graph(&intervals, &graph, &config, &costs, &cc);
    let spills = count_spills(&alloc);
    assert!(spills >= 1, "3 overlapping vars with 2 regs must spill");
}

#[test]
fn test_color_interference_graph_respects_convention_order() {
    let intervals = vec![make_interval(0, 0, 5)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let costs = SpillCostAnalysis::default();
    let cc = CallingConvention::default();
    let config = default_config();
    let alloc = color_interference_graph(&intervals, &graph, &config, &costs, &cc);
    let reg = match alloc.assignments[&var(0)] {
        PhysicalLoc::Register(r) => r,
        _ => panic!(),
    };
    assert!(
        cc.is_caller_saved(reg),
        "default convention should prefer caller-saved first"
    );
}

// =======================================================================
// choose_better_allocation tests
// =======================================================================

#[test]
fn test_choose_better_fewer_spills_wins() {
    let linear = make_allocation(&[(0, PhysicalLoc::Spilled(0)), (1, PhysicalLoc::Register(0))]);
    let colored = make_allocation(&[(0, PhysicalLoc::Register(0)), (1, PhysicalLoc::Register(1))]);
    let cc = CallingConvention::default();
    let chosen = choose_better_allocation(linear, colored, &cc);
    assert_eq!(
        count_spills(&chosen),
        0,
        "colored with fewer spills should win"
    );
}

#[test]
fn test_choose_better_equal_spills_prefers_fewer_caller_saved() {
    let cc = CallingConvention::default();
    // linear uses reg 0 (caller-saved), colored uses reg 8 (callee-saved)
    let linear = make_allocation(&[(0, PhysicalLoc::Register(0))]);
    let colored = make_allocation(&[(0, PhysicalLoc::Register(8))]);
    let chosen = choose_better_allocation(linear, colored, &cc);
    let reg = match chosen.assignments[&var(0)] {
        PhysicalLoc::Register(r) => r,
        _ => panic!(),
    };
    assert_eq!(
        reg, 8,
        "with equal spills, fewer caller-saved uses should win"
    );
}

// =======================================================================
// Validation tests
// =======================================================================

#[test]
fn test_validate_allocation_valid() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(1), ret(0)));
    let alloc = make_allocation(&[(0, PhysicalLoc::Register(0))]);
    validate_allocation(&decl, &alloc).expect("valid allocation should pass");
}

#[test]
fn test_validate_allocation_missing_var() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(1), ret(0)));
    let alloc = make_allocation(&[]);
    let err = validate_allocation(&decl, &alloc).unwrap_err();
    assert!(matches!(err, RegAllocExtError::UnassignedVar { .. }));
}

#[test]
fn test_validate_allocation_interference_conflict() {
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            0,
            lit_u64(1),
            vdecl(
                1,
                IRExpr::Apply {
                    fn_id: fn_id("id"),
                    args: vec![arg_var(0)],
                },
                ret(1),
            ),
        ),
    );
    let intervals = compute_live_intervals(&decl);
    let graph = InterferenceGraph::from_intervals(&intervals);
    // If v0 and v1 interfere, giving them the same register should fail
    if graph.interferes(var(0), var(1)) {
        let alloc =
            make_allocation(&[(0, PhysicalLoc::Register(0)), (1, PhysicalLoc::Register(0))]);
        let err = validate_allocation(&decl, &alloc).unwrap_err();
        assert!(matches!(err, RegAllocExtError::InterferenceConflict { .. }));
    }
}

// =======================================================================
// ExtAllocStats tests
// =======================================================================

#[test]
fn test_ext_alloc_stats_default() {
    let stats = ExtAllocStats::default();
    assert_eq!(stats.spills, 0);
    assert_eq!(stats.coalesces, 0);
    assert_eq!(stats.register_pressure_peak, 0);
    assert_eq!(stats.split_count, 0);
}

// =======================================================================
// count_spills / count_caller_saved_uses tests
// =======================================================================

#[test]
fn test_count_spills_mixed() {
    let alloc = make_allocation(&[
        (0, PhysicalLoc::Register(0)),
        (1, PhysicalLoc::Spilled(0)),
        (2, PhysicalLoc::Stack(0)),
        (3, PhysicalLoc::Register(1)),
    ]);
    assert_eq!(
        count_spills(&alloc),
        2,
        "Spilled and Stack both count as spills"
    );
}

#[test]
fn test_count_caller_saved_uses() {
    let cc = CallingConvention::default();
    let alloc = make_allocation(&[
        (0, PhysicalLoc::Register(0)), // caller-saved
        (1, PhysicalLoc::Register(8)), // callee-saved
        (2, PhysicalLoc::Register(1)), // caller-saved
        (3, PhysicalLoc::Spilled(0)),  // not a register
    ]);
    assert_eq!(count_caller_saved_uses(&alloc, &cc), 2);
}

// =======================================================================
// refresh_allocation_stats tests
// =======================================================================

#[test]
fn test_refresh_allocation_stats() {
    let mut alloc = make_allocation(&[
        (0, PhysicalLoc::Register(0)),
        (1, PhysicalLoc::Register(1)),
        (2, PhysicalLoc::Spilled(0)),
    ]);
    refresh_allocation_stats(&mut alloc, 5);
    assert_eq!(alloc.stats.registers_used, 2);
    assert_eq!(alloc.stats.spills, 1);
    assert_eq!(alloc.stats.coalesced, 5);
}

// =======================================================================
// register_order tests
// =======================================================================

#[test]
fn test_register_order_includes_all_registers() {
    let cc = CallingConvention::default();
    let config = default_config();
    let order = register_order(&config, &cc);
    for reg in 0..16u8 {
        assert!(order.contains(&reg), "register {} should be in order", reg);
    }
}

#[test]
fn test_register_order_no_duplicates() {
    let cc = CallingConvention::default();
    let config = default_config();
    let order = register_order(&config, &cc);
    let unique: BTreeSet<u8> = order.iter().copied().collect();
    assert_eq!(order.len(), unique.len(), "no duplicates in register order");
}

// =======================================================================
// can_assign_register tests
// =======================================================================

#[test]
fn test_can_assign_register_no_conflict() {
    let intervals = vec![make_interval(0, 0, 10), make_interval(1, 0, 10)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let alloc = make_allocation(&[(0, PhysicalLoc::Register(0)), (1, PhysicalLoc::Register(1))]);
    assert!(can_assign_register(&alloc, &graph, var(0), 0, &[]));
}

#[test]
fn test_can_assign_register_conflict() {
    let intervals = vec![make_interval(0, 0, 10), make_interval(1, 0, 10)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let alloc = make_allocation(&[(0, PhysicalLoc::Register(0)), (1, PhysicalLoc::Register(0))]);
    // var(0) wants reg 0 but neighbor var(1) already has reg 0
    assert!(!can_assign_register(&alloc, &graph, var(0), 0, &[]));
}

#[test]
fn test_can_assign_register_conflict_ignored() {
    let intervals = vec![make_interval(0, 0, 10), make_interval(1, 0, 10)];
    let graph = InterferenceGraph::from_intervals(&intervals);
    let alloc = make_allocation(&[(0, PhysicalLoc::Register(0)), (1, PhysicalLoc::Register(0))]);
    assert!(
        can_assign_register(&alloc, &graph, var(0), 0, &[var(1)]),
        "conflict with ignored var should be allowed"
    );
}

// =======================================================================
// select_spill_candidate tests
// =======================================================================

#[test]
fn test_select_spill_candidate_picks_lowest_priority() {
    let mut work: HashMap<VarId, BTreeSet<u32>> = HashMap::new();
    work.insert(var(0), BTreeSet::new());
    work.insert(var(1), BTreeSet::new());
    let mut costs = SpillCostAnalysis::default();
    costs.bump(var(0), 100.0, 0);
    costs.bump(var(1), 1.0, 0);
    let spans = HashMap::from([(var(0), 10usize), (var(1), 10)]);
    let candidate = select_spill_candidate(&work, &costs, &spans);
    assert_eq!(
        candidate,
        var(1),
        "lower cost variable should be spill candidate"
    );
}

// =======================================================================
// Full pipeline tests (allocate_registers_ext)
// =======================================================================

#[test]
fn test_allocate_registers_ext_trivial() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(42), ret(0)));
    let (alloc, stats) = allocate_registers_ext_default(&decl).expect("should succeed");
    assert!(alloc.assignments.contains_key(&var(0)));
    assert_eq!(stats.spills, 0);
}

#[test]
fn test_allocate_registers_ext_empty_body() {
    let decl = make_decl("f", vec![], IRBody::Unreachable);
    let (alloc, stats) = allocate_registers_ext_default(&decl).expect("should succeed");
    assert!(alloc.assignments.is_empty());
    assert_eq!(stats, ExtAllocStats::default());
}

#[test]
fn test_allocate_registers_ext_multiple_vars() {
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            0,
            lit_u64(1),
            vdecl(
                1,
                lit_u64(2),
                vdecl(
                    2,
                    IRExpr::Apply {
                        fn_id: fn_id("add"),
                        args: vec![arg_var(0), arg_var(1)],
                    },
                    ret(2),
                ),
            ),
        ),
    );
    let (alloc, stats) = allocate_registers_ext_default(&decl).expect("should succeed");
    assert!(alloc.assignments.len() >= 3);
    assert!(stats.register_pressure_peak >= 2);
}

#[test]
fn test_allocate_registers_ext_with_coalesce_pairs() {
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            0,
            lit_u64(1),
            vdecl(
                1,
                IRExpr::Apply {
                    fn_id: fn_id("id"),
                    args: vec![arg_var(0)],
                },
                vdecl(
                    2,
                    IRExpr::Apply {
                        fn_id: fn_id("id"),
                        args: vec![arg_var(1)],
                    },
                    ret(2),
                ),
            ),
        ),
    );
    let config = default_config();
    let cc = CallingConvention::default();
    let pairs = vec![(var(0), var(2))];
    let result = allocate_registers_ext(&decl, &config, &cc, &pairs);
    assert!(
        result.is_ok(),
        "ext allocation with coalesce pairs should succeed"
    );
}

#[test]
fn test_allocate_registers_linear_scan_ext_trivial() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(42), ret(0)));
    let alloc =
        allocate_registers_linear_scan_ext(&decl, &default_config()).expect("should succeed");
    assert!(alloc.assignments.contains_key(&var(0)));
    assert_eq!(alloc.stats.spills, 0);
}

// =======================================================================
// Error variant tests
// =======================================================================

#[test]
fn test_error_display_unassigned_var() {
    let err = RegAllocExtError::UnassignedVar { var: var(42) };
    let msg = format!("{}", err);
    assert!(msg.contains("42"), "error message should contain var id");
}

#[test]
fn test_error_display_interference_conflict() {
    let err = RegAllocExtError::InterferenceConflict {
        left: var(1),
        right: var(2),
        reg: 5,
    };
    let msg = format!("{}", err);
    assert!(
        msg.contains("5"),
        "error message should contain register number"
    );
}

#[test]
fn test_error_display_invalid_split_point() {
    let err = RegAllocExtError::InvalidSplitPoint {
        var: var(3),
        point: 99,
    };
    let msg = format!("{}", err);
    assert!(
        msg.contains("99"),
        "error message should contain split point"
    );
}
