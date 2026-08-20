// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(all(feature = "parser", feature = "binary"))]

use trust_ir::dialect::vector;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::interpret::Interpreter;
use trust_ir::node::InstrNode;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Constant, FuncTy, Function, Global, Linkage, Module, Ty};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn v16_i8_ty() -> Ty {
    Ty::Vector(Box::new(Ty::I8), 16)
}

fn v8_i16_ty() -> Ty {
    Ty::Vector(Box::new(Ty::I16), 8)
}

fn vector_i8(values: [i8; 16]) -> Constant {
    Constant::vector(values.into_iter().map(|value| Constant::i32(value.into())))
}

fn vector_i16(values: [i16; 8]) -> Constant {
    Constant::vector(values.into_iter().map(|value| Constant::i32(value.into())))
}

fn chc_x86_v4_i32_module() -> Module {
    let v4i32 = Ty::v4_i32();
    let v4bool = Ty::v4_bool();
    let mut module = Module::new("chc_x86_v4_i32_contract");

    module.globals.push(Global {
        name: "V4_VALUES".to_string(),
        ty: v4i32.clone(),
        mutable: false,
        initializer: Some(Constant::v4_i32([1, -2, 0, i32::MAX])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V4_ZERO_MASK".to_string(),
        ty: v4i32.clone(),
        mutable: false,
        initializer: Some(Constant::v4_i32_zero_mask()),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V4_ALL_ONES_MASK".to_string(),
        ty: v4i32.clone(),
        mutable: false,
        initializer: Some(Constant::v4_i32_all_ones_mask()),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V4_BOOL_MASK".to_string(),
        ty: v4bool.clone(),
        mutable: false,
        initializer: Some(Constant::v4_bool_mask([true, false, true, false])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ft = module.add_func_type(FuncTy {
        params: vec![v4i32.clone(), v4i32.clone()],
        returns: vec![
            v4i32.clone(),
            v4i32.clone(),
            v4bool.clone(),
            Ty::I32,
            v4i32.clone(),
            v4bool.clone(),
            v4bool.clone(),
            v4bool.clone(),
            v4bool.clone(),
        ],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "lane_packed_v4_i32", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), v4i32.clone()));
    block.params.push((v(1), v4i32.clone()));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: v4i32.clone(),
            value: Constant::v4_i32_all_ones_mask(),
        })
        .with_result(v(2)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: v4i32.clone(),
            value: Constant::v4_i32_zero_mask(),
        })
        .with_result(v(3)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: v4i32.clone(),
            lhs: v(2),
            rhs: v(3),
        })
        .with_result(v(4)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: v4i32.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(5)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Sub,
            ty: v4i32.clone(),
            lhs: v(5),
            rhs: v(1),
        })
        .with_result(v(6)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Mul,
            ty: v4i32.clone(),
            lhs: v(6),
            rhs: v(1),
        })
        .with_result(v(7)),
    );
    block.body.push(
        InstrNode::new(Inst::Select {
            ty: v4i32.clone(),
            cond: v(4),
            then_val: v(5),
            else_val: v(6),
        })
        .with_result(v(8)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: v4i32.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(9)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::i32(0),
        })
        .with_result(v(10)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::i32(3),
        })
        .with_result(v(11)),
    );
    block.body.push(
        InstrNode::new(Inst::ExtractElement {
            ty: Ty::I32,
            array: v(8),
            index: v(10),
        })
        .with_result(v(12)),
    );
    block.body.push(
        InstrNode::new(Inst::InsertElement {
            ty: v4i32.clone(),
            array: v(8),
            index: v(11),
            value: v(12),
        })
        .with_result(v(13)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: v4i32.clone(),
            lhs: v(6),
            rhs: v(5),
        })
        .with_result(v(14)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sle,
            ty: v4i32.clone(),
            lhs: v(6),
            rhs: v(5),
        })
        .with_result(v(15)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sgt,
            ty: v4i32.clone(),
            lhs: v(5),
            rhs: v(6),
        })
        .with_result(v(16)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sge,
            ty: v4i32,
            lhs: v(5),
            rhs: v(6),
        })
        .with_result(v(17)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![v(7), v(8), v(9), v(12), v(13), v(14), v(15), v(16), v(17)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

fn chc_x86_v2_i64_module() -> Module {
    let v2i64 = Ty::v2_i64();
    let v2bool = Ty::v2_bool();
    let mut module = Module::new("chc_x86_v2_i64_contract");

    module.globals.push(Global {
        name: "V2_VALUES".to_string(),
        ty: v2i64.clone(),
        mutable: false,
        initializer: Some(Constant::v2_i64([i64::MIN, i64::MAX])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V2_ZERO_MASK".to_string(),
        ty: v2i64.clone(),
        mutable: false,
        initializer: Some(Constant::v2_i64_zero_mask()),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V2_ALL_ONES_MASK".to_string(),
        ty: v2i64.clone(),
        mutable: false,
        initializer: Some(Constant::v2_i64_all_ones_mask()),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V2_BOOL_MASK".to_string(),
        ty: v2bool.clone(),
        mutable: false,
        initializer: Some(Constant::v2_bool_mask([true, false])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ft = module.add_func_type(FuncTy {
        params: vec![v2i64.clone(), v2i64.clone()],
        returns: vec![
            v2i64.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
            v2bool.clone(),
        ],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "lane_packed_v2_i64", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), v2i64.clone()));
    block.params.push((v(1), v2i64.clone()));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: v2i64.clone(),
            value: Constant::v2_i64_all_ones_mask(),
        })
        .with_result(v(2)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: v2i64.clone(),
            value: Constant::v2_i64_zero_mask(),
        })
        .with_result(v(3)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: v2i64.clone(),
            lhs: v(2),
            rhs: v(3),
        })
        .with_result(v(4)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: v2i64.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(5)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Sub,
            ty: v2i64.clone(),
            lhs: v(5),
            rhs: v(1),
        })
        .with_result(v(6)),
    );
    block.body.push(
        InstrNode::new(Inst::Select {
            ty: v2i64.clone(),
            cond: v(4),
            then_val: v(5),
            else_val: v(6),
        })
        .with_result(v(7)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: v2i64.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(8)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: v2i64.clone(),
            lhs: v(6),
            rhs: v(5),
        })
        .with_result(v(9)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sle,
            ty: v2i64.clone(),
            lhs: v(6),
            rhs: v(5),
        })
        .with_result(v(10)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sgt,
            ty: v2i64.clone(),
            lhs: v(5),
            rhs: v(6),
        })
        .with_result(v(11)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sge,
            ty: v2i64,
            lhs: v(5),
            rhs: v(6),
        })
        .with_result(v(12)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![v(7), v(8), v(4), v(9), v(10), v(11), v(12)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

fn chc_x86_v16_i8_module() -> Module {
    let v16i8 = v16_i8_ty();
    let v16bool = Ty::v16_bool();
    let mut module = Module::new("chc_x86_v16_i8_contract");

    module.globals.push(Global {
        name: "V16_I8_VALUES".to_string(),
        ty: v16i8.clone(),
        mutable: false,
        initializer: Some(vector_i8([
            i8::MIN,
            -3,
            -1,
            0,
            1,
            7,
            42,
            64,
            95,
            100,
            113,
            120,
            123,
            124,
            125,
            i8::MAX,
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V16_BOOL_MASK".to_string(),
        ty: v16bool.clone(),
        mutable: false,
        initializer: Some(Constant::v16_bool_mask([
            true, false, true, false, true, false, true, false, true, false, true, false, true,
            false, true, false,
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ft = module.add_func_type(FuncTy {
        params: vec![v16i8.clone(), v16i8.clone()],
        returns: vec![
            v16bool.clone(),
            v16bool.clone(),
            v16bool.clone(),
            v16bool.clone(),
            v16bool.clone(),
            v16bool.clone(),
            Ty::I32,
        ],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "narrow_compare_mask_v16_i8", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), v16i8.clone()));
    block.params.push((v(1), v16i8.clone()));
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: v16i8.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: v16i8.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(3)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: v16i8.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(4)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sle,
            ty: v16i8.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(5)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sgt,
            ty: v16i8.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(6)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sge,
            ty: v16i8,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(7)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::mask_to_bits(
            Ty::v16_bool(),
            v(2),
            Ty::I32,
        ))))
        .with_result(v(8)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![v(2), v(3), v(4), v(5), v(6), v(7), v(8)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

fn chc_x86_v8_i16_module() -> Module {
    let v8i16 = v8_i16_ty();
    let v8bool = Ty::v8_bool();
    let mut module = Module::new("chc_x86_v8_i16_contract");

    module.globals.push(Global {
        name: "V8_I16_VALUES".to_string(),
        ty: v8i16.clone(),
        mutable: false,
        initializer: Some(vector_i16([
            i16::MIN,
            -1024,
            -1,
            0,
            1,
            1024,
            16384,
            i16::MAX,
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    module.globals.push(Global {
        name: "V8_BOOL_MASK".to_string(),
        ty: v8bool.clone(),
        mutable: false,
        initializer: Some(Constant::v8_bool_mask([
            true, false, true, false, true, false, true, false,
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ft = module.add_func_type(FuncTy {
        params: vec![v8i16.clone(), v8i16.clone()],
        returns: vec![
            v8bool.clone(),
            v8bool.clone(),
            v8bool.clone(),
            v8bool.clone(),
            v8bool.clone(),
            v8bool.clone(),
            Ty::I32,
        ],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "narrow_compare_mask_v8_i16", ft, b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), v8i16.clone()));
    block.params.push((v(1), v8i16.clone()));
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: v8i16.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: v8i16.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(3)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: v8i16.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(4)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sle,
            ty: v8i16.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(5)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sgt,
            ty: v8i16.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(6)),
    );
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sge,
            ty: v8i16,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(7)),
    );
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector::mask_to_bits(
            Ty::v8_bool(),
            v(2),
            Ty::I32,
        ))))
        .with_result(v(8)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![v(2), v(3), v(4), v(5), v(6), v(7), v(8)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

#[test]
fn chc_x86_v4_i32_contract_roundtrips_text_and_binary() {
    let module = chc_x86_v4_i32_module();
    module
        .validate_vector_select_contracts()
        .expect("select consumes <4 x bool>, not a physical i32 mask");

    let text = format!("{module}");
    assert!(text.contains("global internal @V4_VALUES <4 x i32> = vec[ 1, -2, 0, 2147483647 ]"));
    assert!(text.contains("global internal @V4_ZERO_MASK <4 x i32> = vec[ 0, 0, 0, 0 ]"));
    assert!(text.contains("global internal @V4_ALL_ONES_MASK <4 x i32> = vec[ -1, -1, -1, -1 ]"));
    assert!(
        text.contains("global internal @V4_BOOL_MASK <4 x bool> = vec[ true, false, true, false ]")
    );
    assert!(text.contains("%4 = icmp ne <4 x i32> %2, %3"));
    assert!(text.contains("%5 = add <4 x i32> %0, %1"));
    assert!(text.contains("%6 = sub <4 x i32> %5, %1"));
    assert!(text.contains("%7 = mul <4 x i32> %6, %1"));
    assert!(text.contains("%8 = select <4 x i32> %4, %5, %6"));
    assert!(text.contains("%9 = icmp eq <4 x i32> %0, %1"));
    assert!(text.contains("%12 = extractelement i32 %8, %10"));
    assert!(text.contains("%13 = insertelement <4 x i32> %8, %11, %12"));
    assert!(text.contains("%14 = icmp slt <4 x i32> %6, %5"));
    assert!(text.contains("%15 = icmp sle <4 x i32> %6, %5"));
    assert!(text.contains("%16 = icmp sgt <4 x i32> %5, %6"));
    assert!(text.contains("%17 = icmp sge <4 x i32> %5, %6"));

    let parsed = trust_ir::parser::parse_module(&text).expect("text roundtrip");
    assert_eq!(parsed, module);
    parsed
        .validate_vector_select_contracts()
        .expect("parsed module preserves bool-mask select contract");

    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("binary roundtrip");
    assert_eq!(decoded, module);
    decoded
        .validate_vector_select_contracts()
        .expect("binary module preserves bool-mask select contract");
}

#[test]
fn chc_x86_v16_i8_narrow_compare_mask_contract_roundtrips_text_and_binary() {
    let module = chc_x86_v16_i8_module();

    let text = format!("{module}");
    assert!(text.contains(
        "global internal @V16_I8_VALUES <16 x i8> = vec[ -128, -3, -1, 0, 1, 7, 42, 64, 95, 100, 113, 120, 123, 124, 125, 127 ]"
    ));
    assert!(text.contains(
        "global internal @V16_BOOL_MASK <16 x bool> = vec[ true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false ]"
    ));
    assert!(text.contains("%2 = icmp eq <16 x i8> %0, %1"));
    assert!(text.contains("%3 = icmp ne <16 x i8> %0, %1"));
    assert!(text.contains("%4 = icmp slt <16 x i8> %0, %1"));
    assert!(text.contains("%5 = icmp sle <16 x i8> %0, %1"));
    assert!(text.contains("%6 = icmp sgt <16 x i8> %0, %1"));
    assert!(text.contains("%7 = icmp sge <16 x i8> %0, %1"));
    assert!(text.contains(
        "%8 = dialect_op vector.mask_to_bits(%2) -> i32 [mask_ty=ty:<16 x bool>] [bit_order=str:\"lsb_lane0\"]"
    ));
    assert!(
        !text.contains("icmp ult")
            && !text.contains("icmp ule")
            && !text.contains("icmp ugt")
            && !text.contains("icmp uge"),
        "narrow signed CHC x86 fixture must not publish unsigned compares"
    );

    let parsed = trust_ir::parser::parse_module(&text).expect("text roundtrip");
    assert_eq!(parsed, module);

    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("binary roundtrip");
    assert_eq!(decoded, module);
}

#[test]
fn chc_x86_v8_i16_narrow_compare_mask_contract_roundtrips_text_and_binary() {
    let module = chc_x86_v8_i16_module();

    let text = format!("{module}");
    assert!(text.contains(
        "global internal @V8_I16_VALUES <8 x i16> = vec[ -32768, -1024, -1, 0, 1, 1024, 16384, 32767 ]"
    ));
    assert!(text.contains(
        "global internal @V8_BOOL_MASK <8 x bool> = vec[ true, false, true, false, true, false, true, false ]"
    ));
    assert!(text.contains("%2 = icmp eq <8 x i16> %0, %1"));
    assert!(text.contains("%3 = icmp ne <8 x i16> %0, %1"));
    assert!(text.contains("%4 = icmp slt <8 x i16> %0, %1"));
    assert!(text.contains("%5 = icmp sle <8 x i16> %0, %1"));
    assert!(text.contains("%6 = icmp sgt <8 x i16> %0, %1"));
    assert!(text.contains("%7 = icmp sge <8 x i16> %0, %1"));
    assert!(text.contains(
        "%8 = dialect_op vector.mask_to_bits(%2) -> i32 [mask_ty=ty:<8 x bool>] [bit_order=str:\"lsb_lane0\"]"
    ));
    assert!(
        !text.contains("icmp ult")
            && !text.contains("icmp ule")
            && !text.contains("icmp ugt")
            && !text.contains("icmp uge"),
        "narrow signed CHC x86 fixture must not publish unsigned compares"
    );

    let parsed = trust_ir::parser::parse_module(&text).expect("text roundtrip");
    assert_eq!(parsed, module);

    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("binary roundtrip");
    assert_eq!(decoded, module);
}

#[test]
fn chc_x86_v2_i64_contract_roundtrips_text_and_binary() {
    let module = chc_x86_v2_i64_module();
    module
        .validate_vector_select_contracts()
        .expect("select consumes <2 x bool>, not a physical i64 mask");

    let text = format!("{module}");
    assert!(text.contains(
        "global internal @V2_VALUES <2 x i64> = vec[ -9223372036854775808, 9223372036854775807 ]"
    ));
    assert!(text.contains("global internal @V2_ZERO_MASK <2 x i64> = vec[ 0, 0 ]"));
    assert!(text.contains("global internal @V2_ALL_ONES_MASK <2 x i64> = vec[ -1, -1 ]"));
    assert!(text.contains("global internal @V2_BOOL_MASK <2 x bool> = vec[ true, false ]"));
    assert!(text.contains("%2 = const <2 x i64> vec[ -1, -1 ]"));
    assert!(text.contains("%3 = const <2 x i64> vec[ 0, 0 ]"));
    assert!(text.contains("%4 = icmp ne <2 x i64> %2, %3"));
    assert!(text.contains("%5 = add <2 x i64> %0, %1"));
    assert!(text.contains("%6 = sub <2 x i64> %5, %1"));
    assert!(text.contains("%7 = select <2 x i64> %4, %5, %6"));
    assert!(text.contains("%8 = icmp eq <2 x i64> %0, %1"));
    assert!(text.contains("%9 = icmp slt <2 x i64> %6, %5"));
    assert!(text.contains("%10 = icmp sle <2 x i64> %6, %5"));
    assert!(text.contains("%11 = icmp sgt <2 x i64> %5, %6"));
    assert!(text.contains("%12 = icmp sge <2 x i64> %5, %6"));

    let parsed = trust_ir::parser::parse_module(&text).expect("text roundtrip");
    assert_eq!(parsed, module);
    parsed
        .validate_vector_select_contracts()
        .expect("parsed module preserves bool-mask select contract");

    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("binary roundtrip");
    assert_eq!(decoded, module);
    decoded
        .validate_vector_select_contracts()
        .expect("binary module preserves bool-mask select contract");
}

// Executable pinning of the published `pmulld` semantics (#124): the CHC
// manifest declares a lanewise i32 WRAPPING multiply. This runs the reference
// interpreter on a `<4 x i32>` Mul and asserts the wrapped lane values, tying
// the manifest's semantics string to executable behavior (not just round-trip).
#[test]
fn chc_pmulld_lanewise_wrapping_multiply_executes() {
    let v4i32 = Ty::v4_i32();
    let mut module = Module::new("chc_pmulld_exec");
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![v4i32.clone()],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "pmulld", ft, b(0));
    let mut block = Block::new(b(0));
    // lanes: [i32::MAX, 1, -1, 100]  *  [2, 2, 2, 2]
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: v4i32.clone(),
            value: Constant::v4_i32([i32::MAX, 1, -1, 100]),
        })
        .with_result(v(0)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: v4i32.clone(),
            value: Constant::v4_i32([2, 2, 2, 2]),
        })
        .with_result(v(1)),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Mul,
            ty: v4i32.clone(),
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2)),
    );
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    func.blocks.push(block);
    module.add_function(func);

    let out = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("pmulld executes");
    let lanes = out.returns[0].as_vector().expect("vector result");
    let got: Vec<i32> = lanes
        .iter()
        .map(|l| l.as_int().expect("int lane").as_unsigned() as u32 as i32)
        .collect();
    // i32::MAX*2 wraps to -2; 1*2=2; -1*2=-2; 100*2=200.
    assert_eq!(
        got,
        vec![-2, 2, -2, 200],
        "pmulld lanewise wrapping multiply"
    );
}
