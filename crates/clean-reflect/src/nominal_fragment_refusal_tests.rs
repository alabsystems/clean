// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Boundary probes, not new Box semantics or source/proof licenses. As with
//! the tensor probes, unresolved pointees deliberately test refusal before an
//! unsupported construct can be erased or its fact treated as authority.
use super::*;
use std::fmt::Debug;
use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
};
use trust_ir::{Block, BlockId, FuncId, FuncTy, FuncTyId, Function, InstrNode, ValueId};

fn identity() -> Module {
    let mut module = Module::new("nominal_reflection_boundary");
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(
        FuncId::new(0),
        "identity",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U32));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.try_add_function(function).expect("identity fixture");
    module
}

fn unsupported_named<T: Debug>(result: Result<T, ReflectError>, name: &str) {
    assert!(
        matches!(&result, Err(ReflectError::Unsupported { construct }) if construct.contains(name)),
        "expected named {name} refusal without a denotation or obligation: {result:?}"
    );
}

#[test]
fn box_validity_never_becomes_a_scalar_or_heap_reflection_license() {
    let control = identity();
    let scalar = denote_function(&control, &control.functions[0]).expect("scalar control");
    assert_eq!(scalar.body, Expr::bvar(0));
    assert!(denote_scalar_function(&control, &control.functions[0]).is_ok());
    for root in PremiseRoot::ALL {
        let inst = Inst::BoxDeref {
            ptr_ty: Ty::Ptr,
            pointee: BoxPointee::Sized { ty: Ty::U32 },
            operand: ValueId::new(7),
            fact: Box::new(BoxValidityFact::premise(
                BoxDerefSite {
                    item: [11; 16],
                    ordinal: 3,
                },
                BoxFactSession::PROOF_SNAPSHOT,
                root,
            )),
        };
        unsupported_named(crate::reflect_inst(&inst), "BoxDeref");
        let mut module = identity();
        module.functions[0].blocks[0]
            .body
            .insert(0, InstrNode::new(inst).with_result(ValueId::new(9)));
        let before = module.clone();
        let function = &module.functions[0];
        let node = &function.blocks[0].body[0];
        unsupported_named(denote_function(&module, function), "BoxDeref");
        unsupported_named(denote_scalar_function(&module, function), "BoxDeref");
        let mut values = BTreeMap::new();
        let mut heap = HeapWalk::new(&module, 0);
        unsupported_named(eval_heap_node(node, 32, &mut values, &mut heap), "BoxDeref");
        unsupported_named(
            eval_value_node(
                node,
                32,
                &modulus(32),
                &mut values,
                false,
                None,
                Some(&mut heap),
            ),
            "BoxDeref",
        );
        // The closed/ownership routes require their own actual zero-arity
        // signature and entry, so an arity refusal cannot hide this opcode.
        let mut closed = module.clone();
        closed.func_types[0].params.clear();
        closed.func_types[0].returns = vec![Ty::Ptr];
        closed.functions[0].blocks[0].params.clear();
        closed.functions[0].blocks[0].body[1] = InstrNode::new(Inst::Return {
            values: vec![ValueId::new(9)],
        });
        unsupported_named(
            denote_closed_zeroary(&closed, &closed.functions[0], MAX_INLINE_DEPTH),
            "BoxDeref",
        );
        unsupported_named(
            f5_ownership_balance(&closed, &closed.functions[0], MAX_INLINE_DEPTH),
            "BoxDeref",
        );
        assert_eq!(
            module, before,
            "every source validity field must remain intact"
        );
        module.functions[0].blocks[0].body.pop();
        unsupported_named(denote_function(&module, &module.functions[0]), "BoxDeref");
    }
}

fn with_function_item_target() -> Module {
    let mut module = identity();
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut target = Function::new(
        FuncId::new(1),
        "item_target",
        FuncTyId::new(1),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    target.blocks.push(block);
    module
        .try_add_function(target)
        .expect("real module-owned function-item target");
    module
}

#[test]
fn function_item_singletons_are_not_scalar_widths_or_heap_cells() {
    let mut module = with_function_item_target();
    let nominal = Ty::FnItem(FuncId::new(1));
    assert_eq!(width_of_ty(&nominal), None);
    unsupported_named(alloc_cells(&module, &nominal, 32, 0), "fnitem.1");
    // A well-typed singleton identity retains its actual target in both
    // signature positions. Zero storage size grants no Nat/pointer model.
    module.func_types[0].params = vec![nominal.clone()];
    module.func_types[0].returns = vec![nominal.clone()];
    module.functions[0].blocks[0].params[0].1 = nominal;
    unsupported_named(denote_function(&module, &module.functions[0]), "fnitem.1");
    unsupported_named(
        denote_scalar_function(&module, &module.functions[0]),
        "FnItem",
    );
}

#[test]
fn an_unused_function_item_constant_cannot_disappear_from_a_scalar_body() {
    let mut module = with_function_item_target();
    assert!(denote_function(&module, &module.functions[0]).is_ok());
    assert!(denote_scalar_function(&module, &module.functions[0]).is_ok());
    module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::FnItem(FuncId::new(1)),
            value: Constant::FnItem(FuncId::new(1)),
        })
        .with_result(ValueId::new(9)),
    );
    assert!(matches!(
        denote_function(&module, &module.functions[0]),
        Err(ReflectError::Unsupported { .. })
    ));
    assert!(matches!(
        denote_scalar_function(&module, &module.functions[0]),
        Err(ReflectError::Unsupported { .. })
    ));
}
