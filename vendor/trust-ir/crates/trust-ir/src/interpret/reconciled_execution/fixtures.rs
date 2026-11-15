// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Historical instruction sequences, using current fallible/unrecorded signatures.

use super::*;

pub(super) fn bulk_module(copy: bool, initialized_bytes: i128) -> Module {
    let mut source = Module::new("bulk");
    let ty = source
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "bulk", ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    let v = ValueId::new;
    block.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::U16,
            count: None,
            align: None,
        })
        .with_result(v(0)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(5),
        })
        .with_result(v(1)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(initialized_bytes),
        })
        .with_result(v(2)),
    );
    block.body.push(InstrNode::new(Inst::MemSet {
        dst: v(0),
        byte: v(1),
        bytes: v(2),
    }));
    let ptr = if copy {
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::U16,
                count: None,
                align: None,
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(2),
            })
            .with_result(v(4)),
        );
        block.body.push(InstrNode::new(Inst::MemCopy {
            dst: v(3),
            src: v(0),
            bytes: v(4),
            overlap: false,
        }));
        v(3)
    } else {
        v(0)
    };
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U16,
            ptr,
            volatile: false,
            align: None,
        })
        .with_result(v(5)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U16,
            value: Constant::Int(0x0505),
        })
        .with_result(v(6)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::U16,
            lhs: v(5),
            rhs: v(6),
        })
        .with_result(v(7)),
    );
    block.body.push(InstrNode::new(Inst::Assert {
        cond: v(7),
        kind: AssertKind::Unspecified,
        site: None,
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    source.functions.push(function);
    source
}

pub(super) fn branch_module(false_write: Option<i128>) -> Module {
    let mut source = Module::new("branch_write");
    let v = ValueId::new;
    let b = BlockId::new;
    let ty = source
        .add_func_type(FuncTy::unrecorded(vec![Ty::Bool], vec![], false))
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "branch", ty, b(0));
    let mut entry = Block::new(b(0)).with_param(v(0), Ty::Bool);
    entry.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::U16,
            count: None,
            align: None,
        })
        .with_result(v(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U16,
            value: Constant::Int(5),
        })
        .with_result(v(2)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: v(0),
        then_target: b(1),
        else_target: b(2),
        then_args: vec![],
        else_args: vec![],
    }));
    let mut yes = Block::new(b(1));
    yes.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U16,
        ptr: v(1),
        value: v(2),
        volatile: false,
        align: None,
    }));
    yes.body.push(InstrNode::new(Inst::Br {
        target: b(3),
        args: vec![],
    }));
    let mut no = Block::new(b(2));
    if let Some(value) = false_write {
        no.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U16,
                value: Constant::Int(value),
            })
            .with_result(v(3)),
        );
        no.body.push(InstrNode::new(Inst::Store {
            ty: Ty::U16,
            ptr: v(1),
            value: v(3),
            volatile: false,
            align: None,
        }));
    }
    no.body.push(InstrNode::new(Inst::Br {
        target: b(3),
        args: vec![],
    }));
    let mut join = Block::new(b(3));
    join.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U16,
            ptr: v(1),
            volatile: false,
            align: None,
        })
        .with_result(v(4)),
    );
    join.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U16,
            lhs: v(4),
            rhs: v(2),
        })
        .with_result(v(5)),
    );
    join.body.push(InstrNode::new(Inst::Assert {
        cond: v(5),
        kind: AssertKind::Unspecified,
        site: None,
    }));
    join.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks = vec![entry, yes, no, join];
    source.functions.push(function);
    source
}

pub(super) fn scalar_module(initialized: bool, overwritten: bool) -> Module {
    let mut module = Module::new("execution_control");
    let ft = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "check", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    let v = ValueId::new;
    block.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::U16,
            count: None,
            align: None,
        })
        .with_result(v(0)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U16,
            value: Constant::Int(5),
        })
        .with_result(v(1)),
    );
    if initialized {
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::U16,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
    }
    if overwritten {
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U16,
                value: Constant::Int(9),
            })
            .with_result(v(2)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::U16,
            ptr: v(0),
            value: v(2),
            volatile: false,
            align: None,
        }));
    }
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U16,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(3)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U16,
            lhs: v(3),
            rhs: v(1),
        })
        .with_result(v(4)),
    );
    block.body.push(InstrNode::new(Inst::Assert {
        cond: v(4),
        kind: AssertKind::Unspecified,
        site: None,
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}
