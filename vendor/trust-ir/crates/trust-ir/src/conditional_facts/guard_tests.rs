// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Guard-region regressions use exact test-only scalar rule assumptions.
//! They check immutable SSA premises, not a source or machine-code theorem.

use super::*;
use crate::{Block, Constant, FuncId, FuncTyId, ICmpOp, Ty};
use std::cell::Cell;

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn b(id: u32) -> BlockId {
    BlockId::new(id)
}
fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}
fn ret() -> InstrNode {
    node(Inst::Return { values: vec![] })
}
fn zero() -> InstrNode {
    node(Inst::Const {
        ty: Ty::U64,
        value: Constant::Int(0),
    })
    .with_result(v(3))
}
fn copy(id: u32, from: u32, ty: Ty) -> InstrNode {
    node(Inst::Copy {
        ty,
        operand: v(from),
    })
    .with_result(v(id))
}
fn test(id: u32, subject: u32, op: ICmpOp) -> InstrNode {
    node(Inst::ICmp {
        op,
        ty: Ty::U64,
        lhs: v(subject),
        rhs: v(3),
    })
    .with_result(v(id))
}
fn br(target: u32, args: &[u32]) -> InstrNode {
    node(Inst::Br {
        target: b(target),
        args: args.iter().copied().map(v).collect(),
    })
}
fn cond(value: u32, yes: u32, yes_args: &[u32], no: u32, no_args: &[u32]) -> InstrNode {
    node(Inst::CondBr {
        cond: v(value),
        then_target: b(yes),
        then_args: yes_args.iter().copied().map(v).collect(),
        else_target: b(no),
        else_args: no_args.iter().copied().map(v).collect(),
    })
}
fn block(id: u32, params: &[(u32, Ty)], body: Vec<InstrNode>) -> Block {
    let mut block = Block::new(b(id));
    block.params = params.iter().map(|(id, ty)| (v(*id), ty.clone())).collect();
    block.body = body;
    block
}
fn function(blocks: Vec<Block>) -> Function {
    let mut function = Function::new(FuncId::new(0), "guard_regions", FuncTyId::new(0), b(0));
    function.blocks = blocks;
    function
}
fn fact(value: u32) -> ConditionalFact {
    ConditionalFact {
        value: v(value),
        property: 0,
    }
}
fn req(block: u32, instruction: usize, value: u32) -> FactRequirement {
    FactRequirement {
        block: b(block),
        instruction,
        fact: fact(value),
    }
}

struct Rules {
    branches: Cell<usize>,
    guards: bool,
    invoke_zero: bool,
}
impl Rules {
    fn new() -> Self {
        Self {
            branches: Cell::new(0),
            guards: true,
            invoke_zero: false,
        }
    }
}
impl ConditionalFactRules for Rules {
    fn establishes(&self, node: &InstrNode, fact: ConditionalFact) -> bool {
        fact.property == 0
            && node.results.contains(&fact.value)
            && (matches!(
                node.inst,
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(0)
                }
            ) || self.invoke_zero
                && matches!(node.inst, Inst::Invoke { callee, .. } if callee == FuncId::new(77)))
    }
    fn branch_fact(
        &self,
        node: &InstrNode,
        condition: ValueId,
        taken: bool,
    ) -> Option<ConditionalFact> {
        self.branches.set(self.branches.get() + 1);
        if !self.guards || node.results.as_slice() != [condition] {
            return None;
        }
        match node.inst {
            Inst::ICmp {
                op,
                ty: Ty::U64,
                lhs,
                rhs,
            } if rhs == v(3) && ((op == ICmpOp::Eq && taken) || (op == ICmpOp::Ne && !taken)) => {
                Some(ConditionalFact {
                    value: lhs,
                    property: 0,
                })
            }
            _ => None,
        }
    }
}

fn simple() -> Function {
    function(vec![
        block(
            0,
            &[(0, Ty::U64), (2, Ty::U64)],
            vec![zero(), test(4, 0, ICmpOp::Eq), cond(4, 1, &[], 2, &[])],
        ),
        block(1, &[], vec![copy(10, 0, Ty::U64), ret()]),
        block(2, &[], vec![ret()]),
        block(99, &[], vec![ret()]),
    ])
}

#[test]
fn guard_regions_long_copy_cfg_chain_needs_no_propagated_entries() {
    const BLOCKS: u32 = 257;
    const COPIES: u32 = 2048;
    let mut blocks = vec![block(
        0,
        &[(0, Ty::U64)],
        vec![zero(), test(4, 0, ICmpOp::Eq), cond(4, 1, &[], BLOCKS, &[])],
    )];
    for id in 1..BLOCKS {
        blocks.push(block(
            id,
            &[],
            if id + 1 == BLOCKS {
                vec![]
            } else {
                vec![br(id + 1, &[])]
            },
        ));
    }
    let last = blocks.last_mut().unwrap();
    for index in 0..COPIES {
        last.body.push(copy(
            10_000 + index,
            if index == 0 { 0 } else { 9_999 + index },
            Ty::U64,
        ));
    }
    last.body.push(copy(u32::MAX, 10_000 + COPIES - 1, Ty::U64));
    last.body.push(ret());
    blocks.push(block(BLOCKS, &[], vec![ret()]));
    let mut function = function(blocks);
    function.blocks.reverse();
    let requirements = vec![req(BLOCKS - 1, COPIES as usize + 1, u32::MAX); 1024];
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let propose = Rules::new();
    let certificate = analysis.analyze(&propose, &requirements).unwrap();
    assert!(
        certificate.entries.is_empty(),
        "one dominating guard, not one fact per intervening block"
    );
    assert!(propose.branches.get() > 0 && propose.branches.get() <= 2);
    let replay = Rules::new();
    analysis
        .check(&replay, &requirements, &certificate)
        .unwrap();
    assert!(
        replay.branches.get() > 0 && replay.branches.get() <= 2,
        "replay derives its own bounded guard evidence"
    );
}

#[test]
fn guard_regions_fast_requirements_do_not_skip_extra_certificate_rows() {
    let function = simple();
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let requirements = [req(1, 1, 10)];
    let empty = analysis.analyze(&Rules::new(), &requirements).unwrap();
    assert!(empty.entries.is_empty());
    let valid = BlockEntryFact {
        block: b(1),
        fact: fact(0),
    };
    analysis
        .check(
            &Rules::new(),
            &requirements,
            &ConditionalFactCertificate {
                entries: vec![valid],
            },
        )
        .unwrap();
    for extra in [
        valid,
        BlockEntryFact {
            block: b(0),
            fact: fact(0),
        },
        BlockEntryFact {
            block: b(99),
            fact: fact(0),
        },
        BlockEntryFact {
            block: b(1234),
            fact: fact(0),
        },
        BlockEntryFact {
            block: b(1),
            fact: fact(1234),
        },
        BlockEntryFact {
            block: b(1),
            fact: fact(10),
        },
        BlockEntryFact {
            block: b(1),
            fact: ConditionalFact {
                value: v(0),
                property: 99,
            },
        },
    ] {
        let forged = ConditionalFactCertificate {
            entries: vec![valid, extra],
        };
        assert!(
            analysis
                .check(&Rules::new(), &requirements, &forged)
                .is_err(),
            "forged unused row: {extra:?}"
        );
    }
}

#[test]
fn guard_regions_replay_does_not_reuse_another_rule_sets_authority() {
    let function = simple();
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let requirements = [req(1, 1, 10)];
    let certificate = analysis.analyze(&Rules::new(), &requirements).unwrap();
    assert!(certificate.entries.is_empty());
    let mut stricter = Rules::new();
    stricter.guards = false;
    assert!(
        analysis
            .check(&stricter, &requirements, &certificate)
            .is_err()
    );
    assert!(analysis.analyze(&stricter, &requirements).is_err());
    analysis
        .check(&Rules::new(), &requirements, &certificate)
        .unwrap();
}

#[test]
fn guard_regions_copy_origin_does_not_make_a_future_copy_available() {
    let function = simple();
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    // x is guarded on entry, but the Copy instruction producing v10 has not
    // executed at instruction zero. Canonicalization cannot erase that check.
    let requirement = [req(1, 0, 10)];
    assert!(analysis.analyze(&Rules::new(), &requirement).is_err());
    assert!(
        analysis
            .check(
                &Rules::new(),
                &requirement,
                &ConditionalFactCertificate::default()
            )
            .is_err()
    );
}

#[test]
fn guard_regions_copy_polarity_and_parallel_edges_remain_exact() {
    for op in [ICmpOp::Eq, ICmpOp::Ne] {
        let (yes, no) = if op == ICmpOp::Eq { (1, 2) } else { (2, 1) };
        let mut function = function(vec![
            block(
                0,
                &[(0, Ty::U64)],
                vec![
                    zero(),
                    copy(6, 0, Ty::U64),
                    test(4, 6, op),
                    copy(7, 4, Ty::Bool),
                    cond(7, yes, &[], no, &[]),
                ],
            ),
            block(1, &[], vec![ret()]),
            block(2, &[], vec![ret()]),
        ]);
        let requirements = [req(1, 0, 0)];
        let analysis = ConditionalFactAnalysis::new(&function).unwrap();
        let certificate = analysis.analyze(&Rules::new(), &requirements).unwrap();
        assert!(certificate.entries.is_empty());
        analysis
            .check(&Rules::new(), &requirements, &certificate)
            .unwrap();
        function.blocks[0].body[4] = cond(7, 1, &[], 1, &[]);
        let analysis = ConditionalFactAnalysis::new(&function).unwrap();
        assert!(analysis.analyze(&Rules::new(), &requirements).is_err());
        assert!(
            analysis
                .check(&Rules::new(), &requirements, &certificate)
                .is_err()
        );
    }
}

#[test]
fn guard_regions_phi_subjects_still_need_every_actual_incoming_value() {
    let mut function = function(vec![
        block(
            0,
            &[(0, Ty::U64), (1, Ty::Bool), (2, Ty::U64)],
            vec![zero(), cond(1, 1, &[], 2, &[])],
        ),
        block(
            1,
            &[],
            vec![test(4, 0, ICmpOp::Eq), cond(4, 3, &[0], 4, &[])],
        ),
        block(
            2,
            &[],
            vec![test(5, 2, ICmpOp::Eq), cond(5, 3, &[2], 4, &[])],
        ),
        block(3, &[(10, Ty::U64)], vec![copy(11, 10, Ty::U64), ret()]),
        block(4, &[], vec![ret()]),
    ]);
    let requirements = [req(3, 1, 11)];
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let certificate = analysis.analyze(&Rules::new(), &requirements).unwrap();
    analysis
        .check(&Rules::new(), &requirements, &certificate)
        .unwrap();
    function.blocks[2].body[1] = cond(5, 3, &[0], 4, &[]);
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    assert!(analysis.analyze(&Rules::new(), &requirements).is_err());
    assert!(
        analysis
            .check(&Rules::new(), &requirements, &certificate)
            .is_err()
    );
}

#[test]
fn guard_regions_loop_phi_does_not_borrow_only_its_first_iteration_guard() {
    let mut function = function(vec![
        block(
            0,
            &[(0, Ty::U64), (1, Ty::Bool), (2, Ty::U64)],
            vec![zero(), test(4, 0, ICmpOp::Eq), cond(4, 1, &[0], 4, &[])],
        ),
        block(1, &[(10, Ty::U64)], vec![cond(1, 2, &[], 3, &[])]),
        block(2, &[], vec![copy(11, 10, Ty::U64), br(1, &[11])]),
        block(3, &[], vec![ret()]),
        block(4, &[], vec![ret()]),
    ]);
    let requirements = [req(3, 0, 10)];
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let certificate = analysis.analyze(&Rules::new(), &requirements).unwrap();
    analysis
        .check(&Rules::new(), &requirements, &certificate)
        .unwrap();
    function.blocks[2].body[1] = br(1, &[2]);
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    assert!(analysis.analyze(&Rules::new(), &requirements).is_err());
    assert!(
        analysis
            .check(&Rules::new(), &requirements, &certificate)
            .is_err()
    );
}

#[test]
fn guard_regions_invoke_availability_precedes_any_guard_shortcut() {
    let function = function(vec![
        block(
            0,
            &[(0, Ty::U64)],
            vec![zero(), test(4, 0, ICmpOp::Eq), cond(4, 1, &[], 4, &[])],
        ),
        block(
            1,
            &[],
            vec![
                node(Inst::Invoke {
                    callee: FuncId::new(77),
                    args: vec![],
                    normal_dest: b(2),
                    normal_args: vec![v(77)],
                    unwind_dest: b(3),
                })
                .with_result(v(77)),
            ],
        ),
        block(
            2,
            &[(78, Ty::U64)],
            vec![test(80, 78, ICmpOp::Eq), cond(80, 5, &[], 4, &[])],
        ),
        block(3, &[], vec![ret()]),
        block(4, &[], vec![ret()]),
        block(5, &[], vec![ret()]),
    ]);
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let requirements = [req(2, 0, 0), req(3, 0, 0), req(5, 0, 78)];
    let certificate = analysis.analyze(&Rules::new(), &requirements).unwrap();
    assert!(certificate.entries.is_empty());
    analysis
        .check(&Rules::new(), &requirements, &certificate)
        .unwrap();
    let mut invocation = Rules::new();
    invocation.invoke_zero = true;
    let normal = [req(2, 0, 78)];
    let normal_certificate = analysis.analyze(&invocation, &normal).unwrap();
    analysis
        .check(&invocation, &normal, &normal_certificate)
        .unwrap();
    for unavailable in [req(1, 0, 77), req(3, 0, 77), req(4, 0, 77)] {
        assert!(analysis.analyze(&invocation, &[unavailable]).is_err());
        assert!(
            analysis
                .check(&invocation, &[unavailable], &certificate)
                .is_err()
        );
    }
}

#[test]
fn guard_regions_irreducible_cycles_require_a_guard_on_every_external_entry() {
    let mut function = function(vec![
        block(
            0,
            &[(0, Ty::U64), (1, Ty::Bool)],
            vec![zero(), test(4, 0, ICmpOp::Eq), cond(4, 1, &[], 5, &[])],
        ),
        block(1, &[], vec![cond(1, 2, &[], 3, &[])]),
        block(2, &[], vec![cond(1, 3, &[], 4, &[])]),
        block(3, &[], vec![cond(1, 2, &[], 4, &[])]),
        block(4, &[], vec![ret()]),
        block(5, &[], vec![ret()]),
    ]);
    let requirements = [req(4, 0, 0)];
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let certificate = analysis.analyze(&Rules::new(), &requirements).unwrap();
    assert!(certificate.entries.is_empty());
    analysis
        .check(&Rules::new(), &requirements, &certificate)
        .unwrap();
    function.blocks[0].body[2] = cond(4, 1, &[], 3, &[]);
    function.blocks.reverse();
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    assert!(analysis.analyze(&Rules::new(), &requirements).is_err());
    assert!(
        analysis
            .check(&Rules::new(), &requirements, &certificate)
            .is_err()
    );
}

#[test]
fn guard_regions_sibling_guards_are_indexed_once_not_once_per_requirement() {
    const GUARDS: u32 = 128;
    const REPEATS: usize = 32;
    const FAILURE_BLOCK: u32 = 99_999;
    let mut blocks = vec![block(
        0,
        &[(0, Ty::U64), (2, Ty::U64)],
        vec![
            zero(),
            node(Inst::Switch {
                value: v(2),
                default: b(1),
                default_args: vec![],
                exhaustive_enum_unreachable: false,
                cases: (1..GUARDS)
                    .map(|index| crate::inst::SwitchCase {
                        value: Constant::Int(i128::from(index)),
                        target: b(index + 1),
                        args: vec![],
                    })
                    .collect(),
            }),
        ],
    )];
    let mut requirements = Vec::new();
    for index in 0..GUARDS {
        blocks.push(block(
            index + 1,
            &[],
            vec![
                test(1000 + index, 0, ICmpOp::Eq),
                cond(1000 + index, 10_000 + index, &[], FAILURE_BLOCK, &[]),
            ],
        ));
        blocks.push(block(10_000 + index, &[], vec![ret()]));
        requirements.extend(std::iter::repeat_n(req(10_000 + index, 0, 0), REPEATS));
    }
    blocks.push(block(FAILURE_BLOCK, &[], vec![ret()]));
    let mut function = function(blocks);
    function.blocks.reverse();
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let index = analysis.guard_index(&Rules::new()).unwrap();
    assert_eq!(
        index.regions[&fact(0)].len(),
        GUARDS as usize,
        "disjoint guarded regions cannot be widened across their siblings"
    );
    let failure_position = analysis
        .dominators
        .dominance_interval(b(FAILURE_BLOCK))
        .unwrap()
        .0;
    assert!(!index.establishes(fact(0), failure_position));
    let rules = Rules::new();
    let certificate = analysis.analyze(&rules, &requirements).unwrap();
    assert!(certificate.entries.is_empty());
    assert!(rules.branches.get() <= 2 * GUARDS as usize);
    let replay = Rules::new();
    analysis
        .check(&replay, &requirements, &certificate)
        .unwrap();
    assert!(replay.branches.get() > 0 && replay.branches.get() <= 2 * GUARDS as usize);
    // Callback counts bound rule evaluation, not elapsed wall time.
}

#[test]
fn guard_regions_nested_guards_coalesce_without_widening_to_failure() {
    const GUARDS: u32 = 128;
    const FAILURE_BLOCK: u32 = 99_999;
    let mut blocks = Vec::new();
    for index in 0..GUARDS {
        let mut nodes = if index == 0 { vec![zero()] } else { vec![] };
        nodes.push(test(1000 + index, 0, ICmpOp::Eq));
        nodes.push(cond(1000 + index, index + 1, &[], FAILURE_BLOCK, &[]));
        blocks.push(block(
            index,
            if index == 0 { &[(0, Ty::U64)] } else { &[] },
            nodes,
        ));
    }
    blocks.push(block(GUARDS, &[], vec![ret()]));
    blocks.push(block(FAILURE_BLOCK, &[], vec![ret()]));
    let function = function(blocks);
    let analysis = ConditionalFactAnalysis::new(&function).unwrap();
    let rules = Rules::new();
    let index = analysis.guard_index(&rules).unwrap();
    assert_eq!(
        index.edges.len(),
        GUARDS as usize,
        "fallback keeps exact actual edge facts"
    );
    assert_eq!(
        index.regions[&fact(0)].len(),
        1,
        "one outer dominance region subsumes all nested guards"
    );
    assert!(rules.branches.get() <= 2 * GUARDS as usize);
    for block in &function.blocks {
        let position = analysis.dominators.dominance_interval(block.id).unwrap().0;
        assert_eq!(
            index.establishes(fact(0), position),
            analysis.dominators.edge_dominates(b(0), 0, block.id)
        );
    }
    let requirements = [req(GUARDS, 0, 0)];
    let certificate = analysis.analyze(&Rules::new(), &requirements).unwrap();
    assert!(certificate.entries.is_empty());
    analysis
        .check(&Rules::new(), &requirements, &certificate)
        .unwrap();
}

#[test]
fn guard_regions_distinct_long_lived_subjects_avoid_triangular_fact_storage() {
    const FAILURE_BLOCK: u32 = 99_999;
    for count in [4u32, 64, 256] {
        let parameters: Vec<_> = (0..count).map(|index| (100 + index, Ty::U64)).collect();
        let mut blocks = Vec::new();
        for index in 0..count {
            let mut nodes = if index == 0 { vec![zero()] } else { vec![] };
            nodes.push(test(10_000 + index, 100 + index, ICmpOp::Eq));
            nodes.push(cond(10_000 + index, index + 1, &[], FAILURE_BLOCK, &[]));
            blocks.push(block(
                index,
                if index == 0 { &parameters } else { &[] },
                nodes,
            ));
        }
        blocks.push(block(count, &[], vec![ret()]));
        blocks.push(block(FAILURE_BLOCK, &[], vec![ret()]));
        let mut function = function(blocks);
        function.blocks.reverse();
        let requirements: Vec<_> = (0..count).map(|index| req(count, 0, 100 + index)).collect();
        let analysis = ConditionalFactAnalysis::new(&function).unwrap();
        let index_rules = Rules::new();
        let index = analysis.guard_index(&index_rules).unwrap();
        assert_eq!(index.regions.len(), count as usize);
        assert_eq!(
            index.regions.values().map(Vec::len).sum::<usize>(),
            count as usize
        );
        assert!(index_rules.branches.get() <= 2 * count as usize);

        let propose = Rules::new();
        let certificate = analysis.analyze(&propose, &requirements).unwrap();
        assert!(
            certificate.entries.is_empty(),
            "{count} long-lived subjects must not produce triangular block-by-fact rows"
        );
        assert!(propose.branches.get() <= 2 * count as usize);
        let replay = Rules::new();
        analysis
            .check(&replay, &requirements, &certificate)
            .unwrap();
        assert!(replay.branches.get() > 0 && replay.branches.get() <= 2 * count as usize);

        // Older producers may still supply valid entry facts. These rows are
        // checked, not forbidden merely because direct guard proof suffices.
        let legacy = ConditionalFactCertificate {
            entries: requirements
                .iter()
                .map(|requirement| BlockEntryFact {
                    block: requirement.block,
                    fact: requirement.fact,
                })
                .collect(),
        };
        let replay = Rules::new();
        analysis.check(&replay, &requirements, &legacy).unwrap();
        assert!(replay.branches.get() > 0 && replay.branches.get() <= 2 * count as usize);
    }
}
