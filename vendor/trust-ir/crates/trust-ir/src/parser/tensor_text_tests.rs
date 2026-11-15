// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The tensor region's text spellings (PKG-U13a): `tensor<ELEM, RANK>` and
//! `tensor_contract TY %l, %r batch [a:b, ..] contract [a:b, ..]`. The printer
//! (`Ty`'s `Display`, `display::write_inst`) and this parser must agree byte
//! for byte, and a malformed spelling is a `ParseError`, never a defaulted
//! field. The grammar is syntax only: the integer-element rule and the
//! contraction's axis rules are the validator's (`InvalidTensorType`,
//! `InvalidTensorContract`), so nothing here validates.

use super::parse_module;
use crate::inst::Inst;
use crate::node::InstrNode;
use crate::ty::{FuncTy, Ty};
use crate::value::{BlockId, FuncId, ValueId};
use crate::{Block, Function, Module};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

/// Print `module`, parse the text back, and require the parsed module to be
/// STRUCTURALLY equal (so a dropped pair list or a defaulted rank fails) and
/// to print the same bytes.
fn round_trip_eq(module: &Module) -> String {
    let text = format!("{module}");
    let parsed = parse_module(&text).unwrap_or_else(|e| {
        panic!("parse failed on:\n{text}\nerror: {e}");
    });
    assert_eq!(
        &parsed, module,
        "structural round-trip lost data.\nText:\n{text}"
    );
    assert_eq!(
        format!("{parsed}"),
        text,
        "text round-trip is not a fixed point"
    );
    text
}

/// The matrix-multiply module of the spec's text example, with the tail of
/// its one `tensor_contract` line (everything after `%1`) supplied.
fn matmul_text(tail: &str) -> String {
    format!(
        r#"; TrustIr text format v1
module "tensor_matmul"

functy.0 = (tensor<i32, 2>, tensor<i32, 2>) -> (tensor<i32, 2>)

fn @matmul(functy.0) {{
bb0(%0: tensor<i32, 2>, %1: tensor<i32, 2>):
    %2 = tensor_contract tensor<i32, 2> %0, %1{tail}
    ret %2
}}
"#
    )
}

/// The spec's example parses to exactly the contraction it spells, and the
/// printer writes the same type and instruction text back.
#[test]
fn tensor_matmul_text_parses_to_the_contraction_and_prints_back() {
    let text = matmul_text(" batch [] contract [1:0]");
    let parsed = parse_module(&text).expect("the matrix-multiply text parses");
    let matrix = tensor(Ty::I32, 2);
    assert_eq!(
        parsed.func_types[0].params,
        vec![matrix.clone(), matrix.clone()]
    );
    assert_eq!(parsed.func_types[0].returns, vec![matrix.clone()]);
    let block = &parsed.functions[0].blocks[0];
    assert_eq!(
        block.params,
        vec![(v(0), matrix.clone()), (v(1), matrix.clone())]
    );
    assert_eq!(block.body[0].results, vec![v(2)]);
    assert_eq!(
        block.body[0].inst,
        Inst::TensorContract {
            ty: matrix,
            lhs: v(0),
            rhs: v(1),
            batch: vec![],
            contract: vec![(1, 0)],
        }
    );

    let printed = format!("{parsed}");
    assert!(
        printed.contains("functy.0 = (tensor<i32, 2>, tensor<i32, 2>) -> (tensor<i32, 2>)"),
        "{printed}"
    );
    assert!(
        printed.contains("bb0(%0: tensor<i32, 2>, %1: tensor<i32, 2>):"),
        "{printed}"
    );
    assert!(
        printed
            .contains("    %2 = tensor_contract tensor<i32, 2> %0, %1 batch [] contract [1:0]\n"),
        "{printed}"
    );
}

/// A batched contraction (`batch [0:0] contract [2:1]`, the batched matrix
/// multiply `[b, m, k] x [b, k, n] -> [b, m, n]`), a two-pair contraction
/// (the `", "` separator), and a rank-0 result (`tensor<u8, 0>`, the dot
/// product of two vectors) all round-trip structurally, each printed with the
/// exact spelling of SPEC §2.2.
#[test]
fn batched_multi_pair_and_rank_zero_contractions_round_trip() {
    let cube = tensor(Ty::I64, 3);
    let plane = tensor(Ty::I64, 2);
    let bytes = tensor(Ty::U8, 1);
    let scalar = tensor(Ty::U8, 0);
    let mut module = Module::new("tensor_contractions");
    let ft_id = module
        .add_func_type(FuncTy {
            params: vec![cube.clone(), cube.clone(), bytes.clone(), bytes.clone()],
            returns: vec![cube.clone(), plane.clone(), scalar.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "contractions", ft_id, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((v(0), cube.clone()));
    block.params.push((v(1), cube.clone()));
    block.params.push((v(2), bytes.clone()));
    block.params.push((v(3), bytes));
    block.body.push(
        InstrNode::new(Inst::TensorContract {
            ty: cube,
            lhs: v(0),
            rhs: v(1),
            batch: vec![(0, 0)],
            contract: vec![(2, 1)],
        })
        .with_result(v(4)),
    );
    block.body.push(
        InstrNode::new(Inst::TensorContract {
            ty: plane,
            lhs: v(0),
            rhs: v(1),
            batch: vec![],
            contract: vec![(1, 0), (2, 1)],
        })
        .with_result(v(5)),
    );
    block.body.push(
        InstrNode::new(Inst::TensorContract {
            ty: scalar,
            lhs: v(2),
            rhs: v(3),
            batch: vec![],
            contract: vec![(0, 0)],
        })
        .with_result(v(6)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![v(4), v(5), v(6)],
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let text = round_trip_eq(&module);
    for line in [
        "functy.0 = (tensor<i64, 3>, tensor<i64, 3>, tensor<u8, 1>, tensor<u8, 1>) -> \
         (tensor<i64, 3>, tensor<i64, 2>, tensor<u8, 0>)",
        "    %4 = tensor_contract tensor<i64, 3> %0, %1 batch [0:0] contract [2:1]\n",
        "    %5 = tensor_contract tensor<i64, 2> %0, %1 batch [] contract [1:0, 2:1]\n",
        "    %6 = tensor_contract tensor<u8, 0> %2, %3 batch [] contract [0:0]\n",
    ] {
        assert!(text.contains(line), "missing `{line}` in:\n{text}");
    }
}

/// The element is an INLINE type read by `parse_ty` itself, so any element
/// the printer writes reads back, a nested tensor and a vector included, and
/// the rank takes the whole u32 range. Refusing a non-integer element is the
/// validator's job; the text form must still carry it unchanged.
#[test]
fn tensor_type_takes_any_inline_element_and_any_u32_rank() {
    for (spelling, ty) in [
        ("tensor<u8, 0>", tensor(Ty::U8, 0)),
        ("tensor<usize, 1>", tensor(Ty::Usize, 1)),
        ("tensor<i128, 7>", tensor(Ty::I128, 7)),
        ("tensor<tensor<i8, 1>, 2>", tensor(tensor(Ty::I8, 1), 2)),
        (
            "tensor<<4 x i32>, 1>",
            tensor(Ty::Vector(Box::new(Ty::I32), 4), 1),
        ),
        ("tensor<f32, 2>", tensor(Ty::F32, 2)),
        ("tensor<i32, 4294967295>", tensor(Ty::I32, u32::MAX)),
    ] {
        assert_eq!(ty.to_string(), spelling, "the printer's spelling of {ty:?}");
        let mut module = Module::new("tensor_types");
        module
            .add_func_type(FuncTy {
                params: vec![ty.clone()],
                returns: vec![ty],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let text = round_trip_eq(&module);
        assert!(
            text.contains(&format!("({spelling}) -> ({spelling})")),
            "{text}"
        );
    }
}

/// A malformed tensor type is refused, never read as a defaulted rank or
/// element. Each case differs from a valid spelling in one place, and the
/// control row proves the surrounding text parses.
#[test]
fn malformed_tensor_types_are_refused() {
    let parse_param = |ty: &str| {
        parse_module(&format!(
            r#"; TrustIr text format v1
module "tensor_types"

functy.0 = ({ty}) -> ()
"#
        ))
    };
    let control = parse_param("tensor<i32, 2>").expect("the control spelling parses");
    assert_eq!(control.func_types[0].params, vec![tensor(Ty::I32, 2)]);

    let missing_rank = parse_param("tensor<i32>").expect_err("a rank is required");
    assert!(
        missing_rank.message.contains("expected ','"),
        "{missing_rank:?}"
    );
    for (ty, label) in [
        ("tensor<i32 2>", "missing comma"),
        ("tensor<i32, >", "missing rank value"),
        ("tensor<i32, -1>", "negative rank"),
        ("tensor<i32, 4294967296>", "rank beyond u32"),
        ("tensor<i32, 2.0>", "non-integer rank"),
        ("tensor<, 2>", "missing element type"),
        ("tensor<i32, 2", "missing closing bracket"),
        ("tensor<2 x i32>", "vector-style rank before the element"),
        ("tensor <i32, 2>", "space before `<`"),
        ("tensor", "bare keyword"),
    ] {
        assert!(parse_param(ty).is_err(), "{label}: `{ty}` must be refused");
    }
}

/// A malformed `tensor_contract` is refused: both clauses are mandatory and
/// ordered, and each pair is exactly `u32:u32`. The control row is the
/// accepted spelling in the same text, so no refusal is vacuous.
#[test]
fn malformed_tensor_contract_spellings_are_refused() {
    parse_module(&matmul_text(" batch [] contract [1:0]")).expect("the control spelling parses");

    let bad_pair =
        parse_module(&matmul_text(" batch [] contract [1]")).expect_err("a pair needs both axes");
    assert!(bad_pair.message.contains("expected ':'"), "{bad_pair:?}");

    for (tail, label) in [
        (" batch [] contract [1:]", "pair missing its rhs axis"),
        (" batch [] contract [:0]", "pair missing its lhs axis"),
        (" batch [] contract [1-0]", "pair with the wrong separator"),
        (" batch [] contract [1:0,]", "trailing comma"),
        (" batch [] contract [1:0 0:1]", "pairs without a comma"),
        (" batch [] contract [-1:0]", "negative axis"),
        (" batch [] contract [4294967296:0]", "axis beyond u32"),
        (" batch [] contract [1:0", "unclosed list"),
        (" batch [] contract (1:0)", "parenthesised list"),
        (" batch [0:0", "unclosed batch list"),
        (" batch []", "missing contract clause"),
        (" contract [1:0]", "missing batch clause"),
        (" contract [1:0] batch []", "clauses swapped"),
        ("", "no clauses"),
    ] {
        assert!(
            parse_module(&matmul_text(tail)).is_err(),
            "{label}: `tensor_contract tensor<i32, 2> %0, %1{tail}` must be refused"
        );
    }

    let missing_comma = matmul_text(" batch [] contract [1:0]").replace("%0, %1", "%0 %1");
    assert!(
        parse_module(&missing_comma).is_err(),
        "operands without a comma must be refused"
    );
}
