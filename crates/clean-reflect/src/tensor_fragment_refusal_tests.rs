// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tensor opcodes have no current reflection vocabulary. These boundary
//! fixtures deliberately omit tensor operand denotations: every walker must
//! refuse the opcode before consulting operands or silently ignoring dead work.
//! They establish neither tensor execution nor well-formed module semantics.
use super::*;
use trust_ir::{Block, BlockId, FuncId, FuncTy, FuncTyId, Function, InstrNode, ValueId};

fn cases() -> Vec<(&'static str, Inst)> {
    let ty = Ty::Tensor(Box::new(Ty::U32), 1);
    let v = ValueId::new(0);
    vec![
        (
            "contract",
            Inst::TensorContract {
                ty: ty.clone(),
                lhs: v,
                rhs: v,
                batch: vec![],
                contract: vec![(0, 0)],
            },
        ),
        (
            "map",
            Inst::TensorMap {
                ty: ty.clone(),
                args: vec![v],
                body: vec![],
            },
        ),
        (
            "reduce",
            Inst::TensorReduce {
                ty: ty.clone(),
                src: v,
                op: trust_ir::TensorReduceOp::Add,
                axes: vec![0],
                order: trust_ir::TensorReduceOrder::RowMajor,
            },
        ),
        (
            "view",
            Inst::TensorView {
                ty: ty.clone(),
                src: v,
                params: vec![],
                exprs: vec![],
                shape: vec![1],
                index: vec![],
                fill: None,
            },
        ),
        (
            "gather",
            Inst::TensorGather {
                ty: ty.clone(),
                data: v,
                coords: vec![v],
            },
        ),
        (
            "scatter",
            Inst::TensorScatter {
                ty,
                init: v,
                src: v,
                coords: vec![v],
            },
        ),
    ]
}

fn fixture(inst: Inst, boxed: bool) -> Module {
    let mut module = Module::new("tensor_refusal_boundary");
    module.func_types.push(FuncTy {
        params: if boxed { vec![] } else { vec![Ty::U32] },
        returns: vec![if boxed { Ty::Ptr } else { Ty::U32 }],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(
        FuncId::new(0),
        "boundary",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    if !boxed {
        block.params.push((ValueId::new(0), Ty::U32));
    }
    block
        .body
        .push(InstrNode::new(inst).with_result(ValueId::new(9)));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(if boxed { 9 } else { 0 })],
    }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    module
}

fn unsupported<T>(result: Result<T, ReflectError>, route: &str, name: &str) {
    assert!(
        matches!(result, Err(ReflectError::Unsupported { .. })),
        "{name}: {route} must return Unsupported, without constructing a model"
    );
}

#[test]
fn every_tensor_opcode_refuses_all_current_walkers_even_when_unused() {
    for (name, inst) in cases() {
        unsupported(crate::reflect_inst(&inst), "obligation", name);
        let mut module = fixture(inst.clone(), false);
        let mut identity = module.clone();
        identity.functions[0].blocks[0].body.remove(0);
        assert!(denote_function(&identity, &identity.functions[0]).is_ok());
        assert!(denote_scalar_function(&identity, &identity.functions[0]).is_ok());
        let function = &module.functions[0];
        unsupported(denote_function(&module, function), "value", name);
        unsupported(
            denote_scalar_function(&module, function),
            "typed scalar",
            name,
        );
        let node = &function.blocks[0].body[0];
        let mut values = BTreeMap::new();
        let mut heap = HeapWalk::new(&module, 0);
        unsupported(
            eval_heap_node(node, 32, &mut values, &mut heap),
            "heap",
            name,
        );
        unsupported(
            eval_value_node(
                node,
                32,
                &modulus(32),
                &mut values,
                false,
                None,
                Some(&mut heap),
            ),
            "SSA",
            name,
        );
        // The same out-of-fragment instruction must not become a terminator.
        module.functions[0].blocks[0].body.pop();
        unsupported(
            denote_function(&module, &module.functions[0]),
            "terminator",
            name,
        );
        let boxed = fixture(inst, true);
        unsupported(
            denote_closed_zeroary(&boxed, &boxed.functions[0], MAX_INLINE_DEPTH),
            "closed helper",
            name,
        );
        unsupported(
            f5_ownership_balance(&boxed, &boxed.functions[0], MAX_INLINE_DEPTH),
            "ownership",
            name,
        );
    }
}

#[test]
fn tensor_types_never_become_scalar_widths_or_initialized_heap_cells() {
    let module = Module::new("tensor_type_boundary");
    for rank in [0, 1, u32::MAX] {
        let tensor = Ty::Tensor(Box::new(Ty::U32), rank);
        assert_eq!(width_of_ty(&tensor), None);
        unsupported(
            alloc_cells(&module, &tensor, 32, 0),
            "allocation",
            "tensor type",
        );
    }
}
