// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Runtime closure construction cannot disappear from a scalar denotation,
//! including when its result is unused and the ordinary scalar return is valid.

use super::*;
use std::fmt::Debug;
use trust_ir::{
    Block, BlockId, ClosureTy, ClosureTyId, FuncId, FuncTy, FuncTyId, Function, InstrNode,
    Interpreter, ValueId,
};

fn fixture(with_closure: bool) -> Module {
    let mut module = Module::new("runtime_closure_refusal");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    module.func_types.push(FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::U32],
    });
    let mut main = Function::new(FuncId::new(0), "main", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );
    if with_closure {
        block.body.push(
            InstrNode::new(Inst::MakeClosure {
                ty: ClosureTyId::new(0),
                func: FuncId::new(1),
                captures: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
    }
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    main.blocks.push(block);
    module.try_add_function(main).expect("main fixture");
    let mut target = Function::new(FuncId::new(1), "target", FuncTyId::new(1), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U32));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    target.blocks.push(block);
    module.try_add_function(target).expect("target fixture");
    module
}

fn refuses<T: Debug>(result: Result<T, ReflectError>) {
    let error = result.expect_err("runtime closure construction has no fragment denotation");
    assert!(
        matches!(error, ReflectError::Unsupported { .. }),
        "expected typed fragment refusal: {error:?}"
    );
    assert!(
        error.to_string().contains("MakeClosure"),
        "name the unsupported instruction: {error}"
    );
}

#[test]
fn runtime_closure_unused_result_is_not_erased_from_an_otherwise_valid_scalar_body() {
    let scalar = fixture(false);
    let closure = fixture(true);
    for module in [&scalar, &closure] {
        let outcome = Interpreter::with_module(module)
            .execute_func(FuncId::new(0), [])
            .expect("valid fixture must execute");
        assert_eq!(outcome.returns[0].as_int().expect("U32").as_signed(), 7);
    }
    let scalar_denotation =
        denote_function(&scalar, &scalar.functions[0]).expect("scalar twin is supported");
    assert_eq!(scalar_denotation.arity, 0);
    assert_eq!(scalar_denotation.width, 32);
    refuses(denote_function(&closure, &closure.functions[0]));
}

#[test]
fn runtime_closure_refuses_at_every_reflection_and_denotation_dispatch() {
    let module = fixture(true);
    let function = &module.functions[0];
    let node = &function.blocks[0].body[1];
    refuses(crate::reflect::reflect_inst(&node.inst));
    assert!(fragment2_inst_label(&node.inst).contains("MakeClosure"));
    refuses(eval_heap_node(
        node,
        32,
        &mut BTreeMap::new(),
        &mut HeapWalk::new(&module, 1),
    ));
    refuses(eval_value_node(
        node,
        32,
        &modulus(32),
        &mut BTreeMap::new(),
        false,
        None,
        None,
    ));
    refuses(denote_closed_zeroary(&module, function, MAX_INLINE_DEPTH));
    refuses(f5_ownership_balance(&module, function, MAX_INLINE_DEPTH));
    // Exercise the terminator dispatch separately. A constructor is no valid
    // terminator; it must get the same named refusal rather than any theorem.
    let mut bad_terminator = module.clone();
    bad_terminator.functions[0].blocks[0].body.pop();
    refuses(denote_function(
        &bad_terminator,
        &bad_terminator.functions[0],
    ));
}
