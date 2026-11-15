// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::{BorrowRoots, borrow_result_ty, borrow_result_types};
use crate::node::InstrNode;
use crate::value::BlockId;
use crate::{Block, Constant, FatPtrKind, FuncId, FuncTyId, Function, Inst, Ty, ValueId};
use std::cell::RefCell;
use std::collections::BTreeMap;

fn original_walk(function: &Function, known: &dyn Fn(ValueId) -> Option<Ty>) -> Vec<(ValueId, Ty)> {
    let mut definitions = BTreeMap::new();
    for block in &function.blocks {
        for node in &block.body {
            if let Inst::Borrow { ptr } | Inst::BorrowMut { ptr } = node.inst
                && let Some(result) = node.results.first()
            {
                definitions.insert(*result, ptr);
            }
        }
    }
    definitions
        .keys()
        .map(|result| {
            let mut cursor = *result;
            let mut hops = 0;
            let root = loop {
                match definitions.get(&cursor) {
                    Some(operand) => {
                        hops += 1;
                        if hops > definitions.len() {
                            break None;
                        }
                        cursor = *operand;
                    }
                    None => break Some(cursor),
                }
            };
            (*result, borrow_result_ty(root.and_then(known).as_ref()))
        })
        .collect()
}

fn changing_lookup(trace: &RefCell<Vec<ValueId>>, root: ValueId) -> Option<Ty> {
    let ordinal = trace.borrow().len();
    trace.borrow_mut().push(root);
    match (ordinal % 4 + (root.index() % 4) as usize) % 4 {
        0 => Some(Ty::FatPtr(FatPtrKind::Str)),
        1 => None,
        2 => Some(Ty::FatPtr(FatPtrKind::ContainerLen)),
        _ => Some(Ty::U8),
    }
}

fn compare(function: &Function) {
    let before = RefCell::new(Vec::new());
    let after = RefCell::new(Vec::new());
    let expected = original_walk(function, &|root| changing_lookup(&before, root));
    let actual = borrow_result_types(function, &|root| changing_lookup(&after, root));
    assert_eq!(actual, expected);
    assert_eq!(
        *after.borrow(),
        *before.borrow(),
        "callback roots/count/order"
    );
}

fn empty() -> Function {
    Function::new(
        FuncId::new(0),
        "borrow-roots",
        FuncTyId::new(0),
        BlockId::new(0),
    )
}

#[test]
fn cached_roots_preserve_malformed_definition_selection_and_callback_trace() {
    let ids = [0, 1, 2, 7, 42, 1_000_000_000, u32::MAX];
    for seed in 0..4096u64 {
        let mut random = seed + 1;
        let mut next = || {
            random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
            (random >> 32) as usize
        };
        let mut function = empty();
        for block_id in 0..2 {
            let mut block = Block::new(BlockId::new(block_id));
            block.params.push((
                ValueId::new(ids[next() % ids.len()]),
                Ty::FatPtr(FatPtrKind::Str),
            ));
            for _ in 0..12 {
                let result = ValueId::new(ids[next() % ids.len()]);
                let operand = ValueId::new(ids[next() % ids.len()]);
                let kind = next() % 5;
                let inst = match kind {
                    0 => Inst::Const {
                        ty: Ty::U8,
                        value: Constant::Int(0),
                    },
                    1 => Inst::BorrowMut { ptr: operand },
                    _ => Inst::Borrow { ptr: operand },
                };
                let mut node = InstrNode::new(inst);
                if kind != 3 {
                    node.results.push(result);
                }
                if kind == 4 {
                    node.results.push(ValueId::new(99));
                }
                block.body.push(node);
            }
            function.blocks.push(block);
        }
        if seed % 2 == 0 {
            function.blocks.reverse();
        }
        compare(&function);
    }
}

#[test]
fn shared_unknown_roots_are_queried_again_and_cycles_never_query_known() {
    let mut function = empty();
    let mut block = Block::new(BlockId::new(0));
    for (result, operand) in [(1, 99), (2, 1), (3, 2), (4, 5), (5, 4), (6, 5), (7, 7)] {
        block.body.push(
            InstrNode::new(Inst::Borrow {
                ptr: ValueId::new(operand),
            })
            .with_result(ValueId::new(result)),
        );
    }
    // An intermediate provisional fat type must never stop the root walk.
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(1)),
    );
    function.blocks.push(block);
    let trace = RefCell::new(Vec::new());
    let result = borrow_result_types(&function, &|root| changing_lookup(&trace, root));
    assert_eq!(*trace.borrow(), vec![ValueId::new(99); 3]);
    assert!(result[3..].iter().all(|(_, ty)| *ty == Ty::Ptr));
    compare(&function);
}

#[test]
fn sparse_32769_edge_chains_expand_each_edge_once_with_or_without_a_root() {
    for cyclic in [false, true] {
        let count = 32769u32;
        let id = |index| ValueId::new(1 + 7919 * index);
        let terminal = ValueId::new(u32::MAX);
        let edges: BTreeMap<_, _> = (0..count)
            .map(|index| {
                let next = if index + 1 == count {
                    if cyclic { id(0) } else { terminal }
                } else {
                    id(index + 1)
                };
                (id(index), next)
            })
            .collect();
        let mut roots = BorrowRoots::default();
        for value in edges.keys() {
            assert_eq!(
                roots.resolve(*value, &edges),
                if cyclic { None } else { Some(terminal) }
            );
        }
        assert_eq!(roots.expanded, count as usize);
        assert_eq!(roots.memo.len(), count as usize);
    }
}
