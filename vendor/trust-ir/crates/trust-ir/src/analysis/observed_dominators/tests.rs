// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored controls; all Rust execution remains UNRUN in this task.

use super::*;
use crate::InstrNode;
use crate::inst::{AssertKind, PanicLocation, PanicSite, SwitchCase};
use crate::interpret::InterpretOptions;

mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("original stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(93))
}
fn graph(edges: &[Vec<usize>]) -> Function {
    let ids = [u32::MAX, 17, 4_000_000_000, 99];
    let mut function = Function::new(
        FuncId::new(93),
        "observed_dom",
        FuncTyId::new(0),
        BlockId::new(ids[0]),
    );
    for (index, targets) in edges.iter().enumerate() {
        let instruction = if let Some((&last, rest)) = targets.split_last() {
            Inst::Switch {
                value: ValueId::new(0),
                default: BlockId::new(ids[last]),
                default_args: vec![],
                exhaustive_enum_unreachable: false,
                cases: rest
                    .iter()
                    .enumerate()
                    .map(|(case, &target)| SwitchCase {
                        value: Constant::Int(case as i128),
                        target: BlockId::new(ids[target]),
                        args: vec![],
                    })
                    .collect(),
            }
        } else {
            Inst::Return { values: vec![] }
        };
        let mut block = Block::new(BlockId::new(ids[index]));
        block.body.push(InstrNode::new(instruction));
        function.blocks.push(block);
    }
    function
}
fn diamond() -> Function {
    graph(&[vec![1, 2], vec![3], vec![3], vec![]])
}
fn construct(function: &Function, observer: &mut Observer) -> R<DominatorTree> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    let tree = DominatorTree::new_observed(function, &mut session, site())?;
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    Ok(tree)
}
fn parity(function: &Function) {
    let ordinary = DominatorTree::new(function);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = DominatorTree::new_observed(function, &mut session, site()).unwrap();
    assert_eq!(actual.well_formed, ordinary.well_formed);
    assert_eq!(actual.reachable, ordinary.reachable);
    assert_eq!(actual.immediate_dominator, ordinary.immediate_dominator);
    assert_eq!(actual.preorder, ordinary.preorder);
    assert_eq!(actual.postorder, ordinary.postorder);
    assert_eq!(actual.instruction_counts, ordinary.instruction_counts);
    assert_eq!(actual.invoke_instructions, ordinary.invoke_instructions);
    assert_eq!(actual.dominating_edges, ordinary.dominating_edges);
    let ids: Vec<_> = function
        .blocks
        .iter()
        .map(|block| block.id)
        .chain([BlockId::new(123)])
        .collect();
    for &block in &ids {
        assert_eq!(
            actual
                .is_reachable_observed(block, &mut session, site())
                .unwrap(),
            ordinary.is_reachable(block)
        );
        for &source in &ids {
            assert_eq!(
                actual
                    .strictly_dominates_observed(source, block, &mut session, site())
                    .unwrap(),
                ordinary.strictly_dominates(source, block)
            );
            for successor in 0..5 {
                assert_eq!(
                    actual
                        .edge_dominates_observed(source, successor, block, &mut session, site())
                        .unwrap(),
                    ordinary.edge_dominates(source, successor, block)
                );
            }
            for instruction in [None, Some(0), Some(1), Some(usize::MAX)] {
                let definition = SsaDefinitionSite {
                    block: source,
                    instruction,
                };
                for use_site in [
                    SsaUseSite::BeforeInstruction {
                        block,
                        instruction: 0,
                    },
                    SsaUseSite::BeforeInstruction {
                        block,
                        instruction: usize::MAX,
                    },
                    SsaUseSite::InvokeNormalEdge { block },
                ] {
                    assert_eq!(
                        actual
                            .definition_available_at_observed(
                                definition,
                                use_site,
                                &mut session,
                                site()
                            )
                            .unwrap(),
                        ordinary.definition_available_at(definition, use_site)
                    );
                }
            }
        }
    }
    actual.retire_observed(&mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert!(observer.events.iter().all(|event| event.site == site()));
}

#[test]
fn complete_maps_and_queries_match_sparse_diamonds_loops_and_irreducible_cycles() {
    for edges in [
        vec![vec![1, 2], vec![3], vec![3], vec![]],
        vec![vec![1], vec![2], vec![1]],
        vec![vec![1, 2], vec![2], vec![1]],
        vec![vec![1], vec![0, 2], vec![]],
    ] {
        parity(&graph(&edges));
    }
    let mut function = diamond();
    let mut unreachable = Block::new(BlockId::new(555));
    unreachable.body.push(InstrNode::new(Inst::Br {
        target: function.blocks[3].id,
        args: vec![],
    }));
    function.blocks.insert(0, unreachable);
    parity(&function);
}

#[test]
fn malformed_stored_cfgs_return_exact_empty_fail_closed_trees() {
    let mut cases = vec![graph(&[])];
    let mut f = diamond();
    f.entry = BlockId::new(123);
    cases.push(f);
    let mut f = diamond();
    f.blocks.push(f.blocks[0].clone());
    cases.push(f);
    let mut f = diamond();
    f.blocks[0].body[0] = InstrNode::new(Inst::Br {
        target: BlockId::new(123),
        args: vec![],
    });
    cases.push(f);
    let mut f = diamond();
    f.blocks[0].body.clear();
    cases.push(f);
    let mut f = diamond();
    f.blocks[0].body.push(InstrNode::new(Inst::NullPtr));
    cases.push(f);
    let mut f = diamond();
    f.blocks[0]
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    cases.push(f);
    let mut f = graph(&[vec![], vec![]]);
    f.blocks[1].body.clear();
    cases.push(f);
    for f in cases {
        parity(&f);
        assert!(
            !construct(&f, &mut Observer::default())
                .unwrap()
                .is_well_formed()
        );
    }
}

#[test]
fn canonical_parallel_switch_edges_do_not_collapse_or_become_default_first() {
    for edges in [
        vec![vec![1, 1], vec![]],
        vec![vec![1, 2, 1], vec![], vec![]],
        vec![vec![1], vec![1, 2], vec![]],
    ] {
        parity(&graph(&edges));
    }
    let f = graph(&[vec![1, 2], vec![], vec![]]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let tree = DominatorTree::new_observed(&f, &mut session, site()).unwrap();
    assert!(
        tree.edge_dominates_observed(f.entry, 0, f.blocks[1].id, &mut session, site())
            .unwrap()
    );
    assert!(
        !tree
            .edge_dominates_observed(f.entry, 1, f.blocks[1].id, &mut session, site())
            .unwrap()
    );
    tree.retire_observed(&mut session, site()).unwrap();
}

#[test]
fn invoke_result_availability_preserves_normal_edge_coordinates_for_all_families() {
    for family in 0..4 {
        let mut f = graph(&[vec![1, 2], vec![1], vec![]]);
        let normal_dest = f.blocks[1].id;
        let unwind_dest = f.blocks[2].id;
        let instruction = match family {
            0 => Inst::Invoke {
                callee: FuncId::new(1),
                args: vec![],
                normal_dest,
                normal_args: vec![],
                unwind_dest,
            },
            1 => Inst::InvokeIndirect {
                callee: ValueId::new(0),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: crate::CallingConv::C,
                normal_dest,
                normal_args: vec![],
                unwind_dest,
            },
            2 => Inst::AssertInvoke {
                cond: ValueId::new(0),
                kind: AssertKind::DivByZero,
                site: PanicSite {
                    entry: FuncId::new(1),
                    location: PanicLocation::Value(ValueId::new(0)),
                },
                normal_dest,
                normal_args: vec![],
                unwind_dest,
            },
            _ => Inst::DropInvoke {
                ty: Ty::Bool,
                ptr: ValueId::new(0),
                normal_dest,
                normal_args: vec![],
                unwind_dest,
            },
        };
        f.blocks[0].body[0] = InstrNode::new(instruction).with_result(ValueId::new(0));
        parity(&f);
        f.blocks[2].body[0] = InstrNode::new(Inst::Br {
            target: normal_dest,
            args: vec![],
        });
        parity(&f);
        match &mut f.blocks[0].body[0].inst {
            Inst::Invoke { unwind_dest, .. }
            | Inst::InvokeIndirect { unwind_dest, .. }
            | Inst::AssertInvoke { unwind_dest, .. }
            | Inst::DropInvoke { unwind_dest, .. } => *unwind_dest = normal_dest,
            _ => unreachable!(),
        }
        parity(&f);
    }
}

#[test]
fn wide_child_sort_and_deep_heap_frames_match_original_tour() {
    let mut f = Function::new(FuncId::new(93), "wide", FuncTyId::new(0), BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(InstrNode::new(Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(1),
        default_args: vec![],
        exhaustive_enum_unreachable: false,
        cases: (2..65)
            .map(|id| SwitchCase {
                value: Constant::Int(i128::from(id)),
                target: BlockId::new(id),
                args: vec![],
            })
            .collect(),
    }));
    f.blocks.push(entry);
    for id in 1..65 {
        let mut block = Block::new(BlockId::new(id));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(block);
    }
    let expected = DominatorTree::new(&f);
    let actual = construct(&f, &mut Observer::default()).unwrap();
    assert_eq!(actual.preorder, expected.preorder);
    assert_eq!(actual.postorder, expected.postorder);
    let mut chain = Function::new(FuncId::new(93), "chain", FuncTyId::new(0), BlockId::new(0));
    for id in 0..512 {
        let mut block = Block::new(BlockId::new(id));
        block.body.push(InstrNode::new(if id == 511 {
            Inst::Return { values: vec![] }
        } else {
            Inst::Br {
                target: BlockId::new(id + 1),
                args: vec![],
            }
        }));
        chain.blocks.push(block);
    }
    let expected = DominatorTree::new(&chain);
    let actual = construct(&chain, &mut Observer::default()).unwrap();
    assert_eq!(actual.preorder, expected.preorder);
    assert_eq!(actual.postorder, expected.postorder);
    assert_eq!(actual.immediate_dominator, expected.immediate_dominator);
}

#[test]
fn all_three_node_edge_dominance_answers_match_independent_removed_edge_reachability() {
    fn reachable(edges: &[Vec<usize>], removed: Option<(usize, usize)>) -> [bool; 3] {
        let mut reached = [true, false, false];
        let mut pending = vec![0];
        while let Some(source) = pending.pop() {
            for (index, &target) in edges[source].iter().enumerate() {
                if removed != Some((source, index)) && !reached[target] {
                    reached[target] = true;
                    pending.push(target);
                }
            }
        }
        reached
    }
    for mask in 0..512u32 {
        let edges: Vec<Vec<usize>> = (0..3)
            .map(|source| {
                (0..3)
                    .filter(|target| mask & (1 << (source * 3 + target)) != 0)
                    .collect()
            })
            .collect();
        let f = graph(&edges);
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let tree = DominatorTree::new_observed(&f, &mut session, site()).unwrap();
        let all = reachable(&edges, None);
        for (source, targets) in edges.iter().enumerate() {
            for index in 0..targets.len() {
                let without = reachable(&edges, Some((source, index)));
                for target in 0..3 {
                    assert_eq!(
                        tree.edge_dominates_observed(
                            f.blocks[source].id,
                            index,
                            f.blocks[target].id,
                            &mut session,
                            site()
                        )
                        .unwrap(),
                        all[target] && !without[target]
                    );
                }
            }
        }
        tree.retire_observed(&mut session, site()).unwrap();
    }
}
