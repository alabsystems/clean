// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR register allocation.
//!
//! Part of #3084 - IO/FFI/Native epic.

use super::liveness::{compute_max_pressure, LiveRange};
use super::*;
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;

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

fn simple_ctor() -> CtorInfo {
    CtorInfo {
        name: name("Unit.unit"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
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

/// Build: `let v<id> := <expr>; <rest>`
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

// =======================================================================
// Live interval computation tests
// =======================================================================

#[test]
fn test_live_intervals_single_var_ret() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(42), ret(0)));
    let intervals = compute_live_intervals(&decl);
    assert_eq!(intervals.len(), 1);
    assert_eq!(intervals[0].var, var(0));
    assert!(intervals[0].weight > 0.0);
}

#[test]
fn test_live_intervals_two_vars() {
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
    assert_eq!(intervals.len(), 2);
    // Intervals should be sorted by start point.
    assert!(intervals[0].start <= intervals[1].start);
}

#[test]
fn test_live_intervals_params_start_at_zero() {
    let decl = make_decl("f", vec![(var(0), IRType::UInt64)], ret(0));
    let intervals = compute_live_intervals(&decl);
    assert_eq!(intervals.len(), 1);
    assert_eq!(intervals[0].start, 0);
}

#[test]
fn test_live_intervals_empty_body() {
    let decl = make_decl("f", vec![], IRBody::Unreachable);
    let intervals = compute_live_intervals(&decl);
    assert!(intervals.is_empty());
}

#[test]
fn test_live_intervals_weight_increases_with_uses() {
    // v0 used once vs v1 used multiple times, same range.
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
    let iv0 = intervals.iter().find(|iv| iv.var == var(0)).unwrap();
    let iv1 = intervals.iter().find(|iv| iv.var == var(1)).unwrap();
    // v1 is used more times than v0, so its weight should be higher
    // (assuming similar range lengths).
    assert!(iv1.weight >= iv0.weight, "more uses => higher weight");
}

#[test]
fn test_live_intervals_sorted_by_start() {
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            0,
            lit_u64(1),
            vdecl(1, lit_u64(2), vdecl(2, lit_u64(3), ret(2))),
        ),
    );
    let intervals = compute_live_intervals(&decl);
    for w in intervals.windows(2) {
        assert!(
            w[0].start <= w[1].start,
            "intervals must be sorted by start"
        );
    }
}

#[test]
fn test_live_intervals_is_fixed_defaults_false() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(1), ret(0)));
    let intervals = compute_live_intervals(&decl);
    for iv in &intervals {
        assert!(!iv.is_fixed, "is_fixed should default to false");
    }
}

// =======================================================================
// Interference graph tests
// =======================================================================

#[test]
fn test_interference_graph_overlapping() {
    let intervals = vec![
        LiveInterval {
            var: var(0),
            start: 0,
            end: 5,
            weight: 1.0,
            is_fixed: false,
        },
        LiveInterval {
            var: var(1),
            start: 2,
            end: 7,
            weight: 1.0,
            is_fixed: false,
        },
    ];
    let edges = build_interference_graph(&intervals);
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0], (var(0), var(1)));
}

#[test]
fn test_interference_graph_non_overlapping() {
    let intervals = vec![
        LiveInterval {
            var: var(0),
            start: 0,
            end: 3,
            weight: 1.0,
            is_fixed: false,
        },
        LiveInterval {
            var: var(1),
            start: 3,
            end: 6,
            weight: 1.0,
            is_fixed: false,
        },
    ];
    let edges = build_interference_graph(&intervals);
    assert!(edges.is_empty(), "non-overlapping intervals have no edges");
}

#[test]
fn test_interference_graph_three_way_clique() {
    let intervals = vec![
        LiveInterval {
            var: var(0),
            start: 0,
            end: 10,
            weight: 1.0,
            is_fixed: false,
        },
        LiveInterval {
            var: var(1),
            start: 0,
            end: 10,
            weight: 1.0,
            is_fixed: false,
        },
        LiveInterval {
            var: var(2),
            start: 0,
            end: 10,
            weight: 1.0,
            is_fixed: false,
        },
    ];
    let edges = build_interference_graph(&intervals);
    assert_eq!(edges.len(), 3, "3-clique has 3 edges");
}

#[test]
fn test_interference_graph_chain() {
    // v0: [0,5), v1: [3,8), v2: [6,10)
    // v0-v1 interfere, v1-v2 interfere, v0-v2 do not.
    let intervals = vec![
        LiveInterval {
            var: var(0),
            start: 0,
            end: 5,
            weight: 1.0,
            is_fixed: false,
        },
        LiveInterval {
            var: var(1),
            start: 3,
            end: 8,
            weight: 1.0,
            is_fixed: false,
        },
        LiveInterval {
            var: var(2),
            start: 6,
            end: 10,
            weight: 1.0,
            is_fixed: false,
        },
    ];
    let edges = build_interference_graph(&intervals);
    assert_eq!(edges.len(), 2);
    assert!(edges.contains(&(var(0), var(1))));
    assert!(edges.contains(&(var(1), var(2))));
}

#[test]
fn test_interference_graph_single_var_no_edges() {
    let intervals = vec![LiveInterval {
        var: var(0),
        start: 0,
        end: 5,
        weight: 1.0,
        is_fixed: false,
    }];
    let edges = build_interference_graph(&intervals);
    assert!(edges.is_empty());
}

#[test]
fn test_interference_graph_empty() {
    let intervals: Vec<LiveInterval> = vec![];
    let edges = build_interference_graph(&intervals);
    assert!(edges.is_empty());
}

// =======================================================================
// Register allocation tests — enough registers
// =======================================================================

#[test]
fn test_allocate_trivial() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(42), ret(0)));
    let result = allocate_registers(&decl, &default_config()).unwrap();
    assert_eq!(result.stats.spills, 0);
    assert!(result.assignments.contains_key(&var(0)));
    assert!(matches!(
        result.assignments[&var(0)],
        PhysicalLoc::Register(_)
    ));
}

#[test]
fn test_allocate_with_params() {
    let decl = make_decl(
        "f",
        vec![(var(0), IRType::UInt64), (var(1), IRType::UInt64)],
        vdecl(
            2,
            IRExpr::Apply {
                fn_id: fn_id("add"),
                args: vec![arg_var(0), arg_var(1)],
            },
            ret(2),
        ),
    );
    let result = allocate_registers(&decl, &default_config()).unwrap();
    assert_eq!(result.stats.spills, 0);
    assert!(result.assignments.len() >= 3);
}

#[test]
fn test_allocate_empty_function() {
    let decl = make_decl("f", vec![], IRBody::Unreachable);
    let result = allocate_registers(&decl, &default_config()).unwrap();
    assert_eq!(result.stats.spills, 0);
    assert_eq!(result.stats.registers_used, 0);
    assert!(result.assignments.is_empty());
}

#[test]
fn test_allocate_default_api() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(42), ret(0)));
    let result = allocate_registers_default(&decl).unwrap();
    assert_eq!(result.stats.spills, 0);
    assert!(result.assignments.contains_key(&var(0)));
}

// =======================================================================
// Spilling behavior
// =======================================================================

#[test]
fn test_allocate_spills_with_insufficient_registers() {
    // 5 overlapping variables, only 2 registers.
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
                    lit_u64(3),
                    vdecl(
                        3,
                        lit_u64(4),
                        vdecl(
                            4,
                            IRExpr::Apply {
                                fn_id: fn_id("add"),
                                args: vec![arg_var(0), arg_var(1), arg_var(2), arg_var(3)],
                            },
                            ret(4),
                        ),
                    ),
                ),
            ),
        ),
    );
    let config = config_with_regs(2);
    let result = allocate_registers(&decl, &config).unwrap();
    assert!(
        result.stats.spills > 0,
        "should spill with only 2 registers"
    );
    // Verify spilled vars get Spilled assignment.
    let spilled = result
        .assignments
        .values()
        .filter(|a| matches!(a, PhysicalLoc::Spilled(_)))
        .count();
    assert_eq!(spilled, result.stats.spills);
}

#[test]
fn test_allocate_no_spill_when_enough() {
    // 3 overlapping variables, 3 registers.
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
    let config = config_with_regs(16);
    let result = allocate_registers(&decl, &config).unwrap();
    assert_eq!(result.stats.spills, 0);
}

#[test]
fn test_spill_slots_are_distinct() {
    // Force multiple spills, verify each gets a unique slot.
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
                    lit_u64(3),
                    vdecl(
                        3,
                        IRExpr::Apply {
                            fn_id: fn_id("use"),
                            args: vec![arg_var(0), arg_var(1), arg_var(2)],
                        },
                        ret(3),
                    ),
                ),
            ),
        ),
    );
    let config = config_with_regs(1);
    let result = allocate_registers(&decl, &config).unwrap();
    let spill_slots: Vec<i32> = result
        .assignments
        .values()
        .filter_map(|a| match a {
            PhysicalLoc::Spilled(s) => Some(*s),
            _ => None,
        })
        .collect();
    let unique: HashSet<i32> = spill_slots.iter().copied().collect();
    assert_eq!(
        spill_slots.len(),
        unique.len(),
        "spill slots must be unique"
    );
}

// =======================================================================
// Config variation tests
// =======================================================================

#[test]
fn test_config_default_values() {
    let config = RegAllocConfig::default();
    assert_eq!(config.num_registers, 16);
    assert!(!config.prefer_callee_saved);
    assert!((config.spill_weight_threshold - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_prefer_callee_saved_uses_higher_registers() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(42), ret(0)));
    let config_no_pref = RegAllocConfig {
        num_registers: 16,
        prefer_callee_saved: false,
        spill_weight_threshold: 1.0,
    };
    let config_pref = RegAllocConfig {
        num_registers: 16,
        prefer_callee_saved: true,
        spill_weight_threshold: 1.0,
    };
    let result_no = allocate_registers(&decl, &config_no_pref).unwrap();
    let result_yes = allocate_registers(&decl, &config_pref).unwrap();
    let reg_no = match result_no.assignments[&var(0)] {
        PhysicalLoc::Register(r) => r,
        _ => panic!("expected register"),
    };
    let reg_yes = match result_yes.assignments[&var(0)] {
        PhysicalLoc::Register(r) => r,
        _ => panic!("expected register"),
    };
    // Without preference, should use register 0; with preference, higher.
    assert_eq!(reg_no, 0);
    assert!(
        reg_yes > reg_no,
        "callee-saved preference should use higher registers"
    );
}

#[test]
fn test_different_register_counts() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(42), ret(0)));
    for n in [1, 2, 4, 8, 16, 32] {
        let config = config_with_regs(n);
        let result = allocate_registers(&decl, &config).unwrap();
        assert_eq!(result.stats.spills, 0, "single var, {} regs", n);
    }
}

// =======================================================================
// Coalescing tests
// =======================================================================

#[test]
fn test_coalesce_success() {
    let mut alloc = RegAllocation {
        assignments: HashMap::new(),
        stats: RegAllocStats::default(),
    };
    alloc.assignments.insert(var(0), PhysicalLoc::Register(3));
    let success = try_coalesce(&mut alloc, var(0), var(1));
    assert!(success);
    assert_eq!(alloc.assignments[&var(1)], PhysicalLoc::Register(3));
    assert_eq!(alloc.stats.coalesced, 1);
}

#[test]
fn test_coalesce_already_same_register() {
    let mut alloc = RegAllocation {
        assignments: HashMap::new(),
        stats: RegAllocStats::default(),
    };
    alloc.assignments.insert(var(0), PhysicalLoc::Register(5));
    alloc.assignments.insert(var(1), PhysicalLoc::Register(5));
    let success = try_coalesce(&mut alloc, var(0), var(1));
    assert!(success, "already same register is a no-op success");
    assert_eq!(alloc.stats.coalesced, 0, "no new coalesce counted");
}

#[test]
fn test_coalesce_fails_different_registers() {
    let mut alloc = RegAllocation {
        assignments: HashMap::new(),
        stats: RegAllocStats::default(),
    };
    alloc.assignments.insert(var(0), PhysicalLoc::Register(1));
    alloc.assignments.insert(var(1), PhysicalLoc::Register(2));
    let success = try_coalesce(&mut alloc, var(0), var(1));
    assert!(
        !success,
        "cannot coalesce vars with different existing registers"
    );
}

#[test]
fn test_coalesce_fails_src_not_assigned() {
    let mut alloc = RegAllocation {
        assignments: HashMap::new(),
        stats: RegAllocStats::default(),
    };
    let success = try_coalesce(&mut alloc, var(0), var(1));
    assert!(!success, "src must have an assignment");
}

#[test]
fn test_coalesce_fails_src_spilled() {
    let mut alloc = RegAllocation {
        assignments: HashMap::new(),
        stats: RegAllocStats::default(),
    };
    alloc.assignments.insert(var(0), PhysicalLoc::Spilled(0));
    let success = try_coalesce(&mut alloc, var(0), var(1));
    assert!(!success, "cannot coalesce from spilled source");
}

#[test]
fn test_coalesce_multiple_vars() {
    let mut alloc = RegAllocation {
        assignments: HashMap::new(),
        stats: RegAllocStats::default(),
    };
    alloc.assignments.insert(var(0), PhysicalLoc::Register(7));
    assert!(try_coalesce(&mut alloc, var(0), var(1)));
    assert!(try_coalesce(&mut alloc, var(0), var(2)));
    assert_eq!(alloc.stats.coalesced, 2);
    assert_eq!(alloc.assignments[&var(1)], PhysicalLoc::Register(7));
    assert_eq!(alloc.assignments[&var(2)], PhysicalLoc::Register(7));
}

// =======================================================================
// Stats tracking accuracy
// =======================================================================

#[test]
fn test_stats_registers_used_count() {
    let decl = make_decl(
        "f",
        vec![],
        vdecl(0, lit_u64(1), vdecl(1, lit_u64(2), ret(1))),
    );
    let result = allocate_registers(&decl, &default_config()).unwrap();
    assert!(result.stats.registers_used >= 1);
    assert!(result.stats.registers_used <= 16);
}

#[test]
fn test_stats_spills_match_assignment_count() {
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
                    lit_u64(3),
                    vdecl(
                        3,
                        IRExpr::Apply {
                            fn_id: fn_id("add"),
                            args: vec![arg_var(0), arg_var(1), arg_var(2)],
                        },
                        ret(3),
                    ),
                ),
            ),
        ),
    );
    let config = config_with_regs(2);
    let result = allocate_registers(&decl, &config).unwrap();
    let actual_spills = result
        .assignments
        .values()
        .filter(|a| matches!(a, PhysicalLoc::Spilled(_)))
        .count();
    assert_eq!(result.stats.spills, actual_spills);
}

#[test]
fn test_stats_empty_function() {
    let decl = make_decl("f", vec![], IRBody::Unreachable);
    let result = allocate_registers_default(&decl).unwrap();
    assert_eq!(result.stats.registers_used, 0);
    assert_eq!(result.stats.spills, 0);
    assert_eq!(result.stats.moves, 0);
    assert_eq!(result.stats.coalesced, 0);
}

// =======================================================================
// Edge cases
// =======================================================================

#[test]
fn test_allocate_single_var_single_register() {
    let decl = make_decl("f", vec![], vdecl(0, lit_u64(1), ret(0)));
    let config = config_with_regs(1);
    let result = allocate_registers(&decl, &config).unwrap();
    assert_eq!(result.stats.spills, 0);
    assert_eq!(result.assignments[&var(0)], PhysicalLoc::Register(0));
}

#[test]
fn test_allocate_inc_dec_extends_liveness() {
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            0,
            IRExpr::Ctor {
                info: simple_ctor(),
                args: vec![],
            },
            IRBody::Inc {
                var: var(0),
                n: 2,
                rest: Box::new(vdecl(
                    1,
                    IRExpr::Proj {
                        idx: 0,
                        ty: IRType::Object,
                        arg: arg_var(0),
                    },
                    IRBody::Dec {
                        var: var(0),
                        rest: Box::new(ret(1)),
                    },
                )),
            },
        ),
    );
    let result = allocate_registers_default(&decl).unwrap();
    assert!(result.assignments.contains_key(&var(0)));
    assert!(result.assignments.contains_key(&var(1)));
    assert_eq!(result.stats.spills, 0);
}

#[test]
fn test_allocate_case_analysis() {
    let decl = make_decl(
        "f",
        vec![(var(0), IRType::Object)],
        IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: simple_ctor(),
                body: Box::new(vdecl(1, lit_u64(42), ret(1))),
            }],
            default: Some(Box::new(IRBody::Ret(arg_var(0)))),
        },
    );
    let result = allocate_registers_default(&decl).unwrap();
    assert!(result.assignments.contains_key(&var(0)));
    assert_eq!(result.stats.spills, 0);
}

#[test]
fn test_allocate_join_point() {
    let decl = make_decl(
        "f",
        vec![],
        IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(var(0), IRType::UInt64)],
            body: Box::new(ret(0)),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![IRArg::Var(var(0))],
            }),
        },
    );
    let result = allocate_registers_default(&decl).unwrap();
    assert!(result.assignments.contains_key(&var(0)));
}

#[test]
fn test_allocate_many_sequential_non_overlapping() {
    // Chain of variables where each is dead before the next is defined.
    // Should need at most 2 registers.
    // Build chain: let v0 = 1; let v1 = id(v0); ... let v9 = id(v8); ret v9
    let body = vdecl(
        8,
        IRExpr::Apply {
            fn_id: fn_id("id"),
            args: vec![arg_var(7)],
        },
        vdecl(
            9,
            IRExpr::Apply {
                fn_id: fn_id("id"),
                args: vec![arg_var(8)],
            },
            ret(9),
        ),
    );
    let body = vdecl(
        6,
        IRExpr::Apply {
            fn_id: fn_id("id"),
            args: vec![arg_var(5)],
        },
        vdecl(
            7,
            IRExpr::Apply {
                fn_id: fn_id("id"),
                args: vec![arg_var(6)],
            },
            body,
        ),
    );
    let body = vdecl(
        4,
        IRExpr::Apply {
            fn_id: fn_id("id"),
            args: vec![arg_var(3)],
        },
        vdecl(
            5,
            IRExpr::Apply {
                fn_id: fn_id("id"),
                args: vec![arg_var(4)],
            },
            body,
        ),
    );
    let body = vdecl(
        2,
        IRExpr::Apply {
            fn_id: fn_id("id"),
            args: vec![arg_var(1)],
        },
        vdecl(
            3,
            IRExpr::Apply {
                fn_id: fn_id("id"),
                args: vec![arg_var(2)],
            },
            body,
        ),
    );
    let body = vdecl(
        0,
        lit_u64(1),
        vdecl(
            1,
            IRExpr::Apply {
                fn_id: fn_id("id"),
                args: vec![arg_var(0)],
            },
            body,
        ),
    );

    let decl = make_decl("f", vec![], body);
    let config = config_with_regs(2);
    let result = allocate_registers(&decl, &config).unwrap();
    // Sequential chain should need at most 2 registers.
    assert!(result.stats.registers_used <= 2);
}

#[test]
fn test_allocate_all_vars_get_assignment() {
    let decl = make_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        vdecl(1, lit_u64(42), vdecl(2, lit_u64(99), ret(2))),
    );
    let intervals = compute_live_intervals(&decl);
    let result = allocate_registers_default(&decl).unwrap();
    for iv in &intervals {
        assert!(
            result.assignments.contains_key(&iv.var),
            "variable {:?} should have an assignment",
            iv.var
        );
    }
}

// =======================================================================
// Correctness invariant: interfering vars don't share registers
// =======================================================================

#[test]
fn test_no_interfering_vars_share_register() {
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
    let intervals = compute_live_intervals(&decl);
    let edges = build_interference_graph(&intervals);
    let result = allocate_registers(&decl, &default_config()).unwrap();

    for (a, b) in &edges {
        if let (Some(PhysicalLoc::Register(r1)), Some(PhysicalLoc::Register(r2))) =
            (result.assignments.get(a), result.assignments.get(b))
        {
            assert_ne!(
                r1, r2,
                "interfering vars {:?} and {:?} share register {}",
                a, b, r1
            );
        }
    }
}

#[test]
fn test_correctness_large_clique() {
    // 6 vars all overlapping, 4 registers => 2 spills, no conflicts.
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
                    lit_u64(3),
                    vdecl(
                        3,
                        lit_u64(4),
                        vdecl(
                            4,
                            lit_u64(5),
                            vdecl(
                                5,
                                IRExpr::Apply {
                                    fn_id: fn_id("use6"),
                                    args: vec![
                                        arg_var(0),
                                        arg_var(1),
                                        arg_var(2),
                                        arg_var(3),
                                        arg_var(4),
                                    ],
                                },
                                ret(5),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let config = config_with_regs(4);
    let intervals = compute_live_intervals(&decl);
    let edges = build_interference_graph(&intervals);
    let result = allocate_registers(&decl, &config).unwrap();

    // Check no register conflicts among interfering vars.
    for (a, b) in &edges {
        if let (Some(PhysicalLoc::Register(r1)), Some(PhysicalLoc::Register(r2))) =
            (result.assignments.get(a), result.assignments.get(b))
        {
            assert_ne!(r1, r2, "conflict between {:?} and {:?}", a, b);
        }
    }
}

// =======================================================================
// Liveness analysis (from liveness module) tests
// =======================================================================

#[test]
fn test_liveness_pressure_two_overlapping() {
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
    let (_, _, pressure) = compute_liveness(&decl);
    assert!(pressure >= 2, "v0 and v1 overlap => pressure >= 2");
}

// -----------------------------------------------------------------------
// compute_liveness: exact LiveRange maps per IRBody / IRExpr variant.
//
// Convention (from collect_def_use_body): params are defined at point 0,
// `point` starts at 1, each body node consumes exactly one program point at
// its own `*point` before advancing. A range is `[def, last_use + 1)`.
// -----------------------------------------------------------------------

#[test]
fn test_liveness_jdecl_param_and_uses() {
    // jdecl j0 [(v1)] { ret v1 }; ret v1
    // point=1: JDecl defs v1 at 1, point->2
    // jp body Ret(v1): use v1 at 2, point->3
    // rest Ret(v1): use v1 at 3, point->4
    let decl = make_decl(
        "f",
        vec![],
        IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(var(1), IRType::UInt64)],
            body: Box::new(ret(1)),
            rest: Box::new(ret(1)),
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 4);
    assert_eq!(ranges.len(), 1);
    assert_eq!(ranges[&var(1)], LiveRange { start: 1, end: 4 });
}

#[test]
fn test_liveness_case_scrutinee_and_alts() {
    // params (v0). case v0 { Ctor0 => ret v1 } default => ret v2
    // point=1: Case uses scrutinee v0 at 1, point->2
    // alt body Ret(v1): use v1 at 2, point->3
    // default Ret(v2): use v2 at 3, point->4
    let decl = make_decl(
        "f",
        vec![(var(0), IRType::Object)],
        IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: simple_ctor(),
                body: Box::new(ret(1)),
            }],
            default: Some(Box::new(ret(2))),
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 4);
    // v0 param: def 0, last use 1 => [0, 2)
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    // v1 used at 2, never defined => def defaults to 0 => [0, 3)
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 3 });
    // v2 used at 3, never defined => [0, 4)
    assert_eq!(ranges[&var(2)], LiveRange { start: 0, end: 4 });
    assert_eq!(ranges.len(), 3);
}

#[test]
fn test_liveness_inc_dec_uses() {
    // inc v0 1; dec v1; ret v2
    // point=1: Inc uses v0 at 1, point->2
    // point=2: Dec uses v1 at 2, point->3
    // point=3: Ret uses v2 at 3, point->4
    let decl = make_decl(
        "f",
        vec![],
        IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: var(1),
                rest: Box::new(ret(2)),
            }),
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 4);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 3 });
    assert_eq!(ranges[&var(2)], LiveRange { start: 0, end: 4 });
}

#[test]
fn test_liveness_set_uses_var_and_value() {
    // set v0[0] := v1; ret v2
    // point=1: Set uses v0 and v1 at 1, point->2
    // point=2: Ret uses v2 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(ret(2)),
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(2)], LiveRange { start: 0, end: 3 });
}

#[test]
fn test_liveness_uset_uses_var_and_value() {
    // uset v0[0] := v1; ret v0
    // point=1: USet uses v0 and v1 at 1, point->2
    // point=2: Ret uses v0 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        IRBody::USet {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(ret(0)),
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    // v0 last used at 2 (the Ret) => [0, 3)
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 3 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 2 });
}

#[test]
fn test_liveness_sset_uses_var_and_value() {
    // sset v0 n=0 off=0 := v1 : UInt64; ret v2
    // point=1: SSet uses v0 and v1 at 1, point->2
    // point=2: Ret uses v2 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        IRBody::SSet {
            var: var(0),
            n: 0,
            offset: 0,
            value: var(1),
            ty: IRType::UInt64,
            rest: Box::new(ret(2)),
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(2)], LiveRange { start: 0, end: 3 });
}

#[test]
fn test_liveness_settag_uses_only_var() {
    // setTag v0 := 1; ret v1
    // point=1: SetTag uses only v0 at 1, point->2
    // point=2: Ret uses v1 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        IRBody::SetTag {
            var: var(0),
            tag: 1,
            rest: Box::new(ret(1)),
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 3 });
}

#[test]
fn test_liveness_jmp_uses_args() {
    // jmp j0 [v0, v1]
    // point=1: Jmp uses v0 and v1 at 1, point->2
    let decl = make_decl(
        "f",
        vec![],
        IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![arg_var(0), arg_var(1)],
        },
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 2);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges.len(), 2);
}

#[test]
fn test_liveness_unreachable_no_vars() {
    // unreachable: consumes one point, defines/uses nothing.
    let decl = make_decl("f", vec![], IRBody::Unreachable);
    let (ranges, max_point, pressure) = compute_liveness(&decl);
    assert_eq!(max_point, 2);
    assert!(ranges.is_empty());
    assert_eq!(pressure, 0);
}

#[test]
fn test_liveness_expr_proj_use() {
    // let v1 := proj 0 v0; ret v1
    // point=1: VDecl value Proj uses v0 at 1, defs v1 at 1, point->2
    // point=2: Ret uses v1 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            1,
            IRExpr::Proj {
                idx: 0,
                ty: IRType::UInt64,
                arg: arg_var(0),
            },
            ret(1),
        ),
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 1, end: 3 });
}

#[test]
fn test_liveness_expr_ctor_uses_all_args() {
    // let v2 := Ctor(v0, v1); ret v2
    // point=1: VDecl value Ctor uses v0,v1 at 1, defs v2 at 1, point->2
    // point=2: Ret uses v2 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            2,
            IRExpr::Ctor {
                info: simple_ctor(),
                args: vec![arg_var(0), arg_var(1)],
            },
            ret(2),
        ),
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(2)], LiveRange { start: 1, end: 3 });
}

#[test]
fn test_liveness_expr_closure_apply_uses_closure_and_args() {
    // let v3 := closureApply v0 [v1, v2]; ret v3
    // point=1: VDecl value uses v0 (closure), v1, v2 at 1, defs v3 at 1, point->2
    // point=2: Ret uses v3 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            3,
            IRExpr::ClosureApply {
                closure: arg_var(0),
                args: vec![arg_var(1), arg_var(2)],
            },
            ret(3),
        ),
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(2)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(3)], LiveRange { start: 1, end: 3 });
}

#[test]
fn test_liveness_expr_reset_use() {
    // let v1 := reset v0; ret v1
    // point=1: VDecl value Reset uses v0 at 1, defs v1 at 1, point->2
    // point=2: Ret uses v1 at 2, point->3
    let decl = make_decl("f", vec![], vdecl(1, IRExpr::Reset(var(0)), ret(1)));
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 1, end: 3 });
}

#[test]
fn test_liveness_expr_reuse_uses_var_and_args() {
    // let v3 := reuse v0 Ctor(v1, v2); ret v3
    // point=1: VDecl value Reuse uses v0 (slot var), v1, v2 at 1, defs v3 at 1
    // point=2: Ret uses v3 at 2, point->3
    let decl = make_decl(
        "f",
        vec![],
        vdecl(
            3,
            IRExpr::Reuse {
                var: var(0),
                ctor: simple_ctor(),
                args: vec![arg_var(1), arg_var(2)],
            },
            ret(3),
        ),
    );
    let (ranges, max_point, _) = compute_liveness(&decl);
    assert_eq!(max_point, 3);
    assert_eq!(ranges[&var(0)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(1)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(2)], LiveRange { start: 0, end: 2 });
    assert_eq!(ranges[&var(3)], LiveRange { start: 1, end: 3 });
}

#[test]
fn test_max_pressure_no_overlap() {
    let mut ranges = HashMap::new();
    ranges.insert(var(0), LiveRange { start: 0, end: 3 });
    ranges.insert(var(1), LiveRange { start: 3, end: 6 });
    ranges.insert(var(2), LiveRange { start: 6, end: 9 });
    let pressure = compute_max_pressure(&ranges, 10);
    assert_eq!(pressure, 1);
}

#[test]
fn test_max_pressure_full_overlap() {
    let mut ranges = HashMap::new();
    ranges.insert(var(0), LiveRange { start: 0, end: 10 });
    ranges.insert(var(1), LiveRange { start: 0, end: 10 });
    ranges.insert(var(2), LiveRange { start: 0, end: 10 });
    let pressure = compute_max_pressure(&ranges, 10);
    assert_eq!(pressure, 3);
}

// =======================================================================
// PhysicalLoc enum tests
// =======================================================================

#[test]
fn test_physical_loc_equality() {
    assert_eq!(PhysicalLoc::Register(0), PhysicalLoc::Register(0));
    assert_ne!(PhysicalLoc::Register(0), PhysicalLoc::Register(1));
    assert_ne!(PhysicalLoc::Register(0), PhysicalLoc::Stack(0));
    assert_ne!(PhysicalLoc::Stack(0), PhysicalLoc::Spilled(0));
    assert_eq!(PhysicalLoc::Spilled(5), PhysicalLoc::Spilled(5));
}
