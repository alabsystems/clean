// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The text spellings of the tensor region's gather and scatter (PKG-U13d,
//! SPEC_RATIFICATIONS §26):
//!
//! * `tensor_gather TY %data coords [%c, ..]`;
//! * `tensor_scatter TY %init, %src coords [%c, ..]`.
//!
//! The printer and this parser agree byte for byte, and a malformed spelling
//! is a `ParseError`, never a defaulted field. The grammar is syntax only:
//! every rank, element and arity rule (G1-G3, S1-S3) is the validator's, so
//! an ill-typed but well-spelled instruction parses.

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
/// STRUCTURALLY equal and to print the same bytes.
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

/// `fn @t(tensor<i32, 2>, tensor<i32, 1>, tensor<i64, 1>, tensor<u8, 1>) ->
/// (result)` whose one instruction line is `line` (its result `%4`), then
/// `ret %4`.
fn text_with(result: &str, line: &str) -> String {
    format!(
        r#"; TrustIr text format v1
module "tensor_gather_scatter_text"

functy.0 = (tensor<i32, 2>, tensor<i32, 1>, tensor<i64, 1>, tensor<u8, 1>) -> ({result})

fn @t(functy.0) {{
bb0(%0: tensor<i32, 2>, %1: tensor<i32, 1>, %2: tensor<i64, 1>, %3: tensor<u8, 1>):
    %4 = {line}
    ret %4
}}
"#
    )
}

fn the_instruction(module: &Module) -> &Inst {
    &module.functions[0].blocks[0].body[0].inst
}

const GATHER_LINE: &str = "tensor_gather tensor<i32, 1> %0 coords [%2, %3]";

const SCATTER_LINE: &str = "tensor_scatter tensor<i32, 2> %0, %1 coords [%2, %3]";

/// Each spelling parses to exactly the instruction it spells and prints
/// back the same bytes.
#[test]
fn gather_and_scatter_text_parses_to_the_instruction_and_prints_back() {
    let gather =
        parse_module(&text_with("tensor<i32, 1>", GATHER_LINE)).expect("the gather parses");
    assert_eq!(
        the_instruction(&gather),
        &Inst::TensorGather {
            ty: tensor(Ty::I32, 1),
            data: v(0),
            coords: vec![v(2), v(3)],
        }
    );
    let scatter =
        parse_module(&text_with("tensor<i32, 2>", SCATTER_LINE)).expect("the scatter parses");
    assert_eq!(
        the_instruction(&scatter),
        &Inst::TensorScatter {
            ty: tensor(Ty::I32, 2),
            init: v(0),
            src: v(1),
            coords: vec![v(2), v(3)],
        }
    );
    for (module, line) in [(gather, GATHER_LINE), (scatter, SCATTER_LINE)] {
        let printed = round_trip_eq(&module);
        assert!(printed.contains(&format!("    %4 = {line}\n")), "{printed}");
    }
}

/// `f(params..) -> result` whose one instruction is `inst`.
fn one_instruction_module(params: Vec<Ty>, result: Ty, inst: Inst) -> Module {
    let mut module = Module::new("tensor_gather_scatter_text");
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: params.clone(),
            returns: vec![result],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "t", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    let out = v(params.len() as u32);
    for (i, ty) in params.into_iter().enumerate() {
        entry.params.push((v(i as u32), ty));
    }
    entry
        .body
        .push(InstrNode::new(inst).with_results(vec![out]));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![out] }));
    f.blocks.push(entry);
    module.functions.push(f);
    module
}

/// An empty coordinate list (rule G2's and S2's refusal is the validator's),
/// a repeated coordinate operand, a coordinate operand that is also the data,
/// and a coordinate tensor of every integer element round-trip structurally.
#[test]
fn empty_repeated_and_every_element_coordinate_lists_round_trip() {
    let text = round_trip_eq(&one_instruction_module(
        vec![tensor(Ty::I32, 0)],
        tensor(Ty::I32, 0),
        Inst::TensorGather {
            ty: tensor(Ty::I32, 0),
            data: v(0),
            coords: vec![],
        },
    ));
    assert!(
        text.contains("tensor_gather tensor<i32, 0> %0 coords []\n"),
        "{text}"
    );
    let text = round_trip_eq(&one_instruction_module(
        vec![tensor(Ty::I32, 0), tensor(Ty::I32, 0)],
        tensor(Ty::I32, 0),
        Inst::TensorScatter {
            ty: tensor(Ty::I32, 0),
            init: v(0),
            src: v(1),
            coords: vec![],
        },
    ));
    assert!(
        text.contains("tensor_scatter tensor<i32, 0> %0, %1 coords []\n"),
        "{text}"
    );
    // The same operand at every axis, and the data as its own coordinate.
    let text = round_trip_eq(&one_instruction_module(
        vec![tensor(Ty::U32, 3), tensor(Ty::U32, 2)],
        tensor(Ty::U32, 2),
        Inst::TensorGather {
            ty: tensor(Ty::U32, 2),
            data: v(0),
            coords: vec![v(1), v(1), v(0)],
        },
    ));
    assert!(
        text.contains("tensor_gather tensor<u32, 2> %0 coords [%1, %1, %0]\n"),
        "{text}"
    );
    let elements = [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::Isize,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
    ];
    for coord in elements {
        let mut params = vec![tensor(Ty::I16, 1), tensor(Ty::I16, 1)];
        params.push(tensor(coord.clone(), 1));
        round_trip_eq(&one_instruction_module(
            params.clone(),
            tensor(Ty::I16, 1),
            Inst::TensorScatter {
                ty: tensor(Ty::I16, 1),
                init: v(0),
                src: v(1),
                coords: vec![v(2)],
            },
        ));
        round_trip_eq(&one_instruction_module(
            params,
            tensor(Ty::I16, 1),
            Inst::TensorGather {
                ty: tensor(Ty::I16, 1),
                data: v(0),
                coords: vec![v(2)],
            },
        ));
    }
}

/// A malformed spelling is a parse error, never a defaulted field.
#[test]
fn malformed_spellings_are_parse_errors() {
    let gather = |tail: &str| {
        text_with(
            "tensor<i32, 1>",
            &format!("tensor_gather tensor<i32, 1> {tail}"),
        )
    };
    let scatter = |tail: &str| {
        text_with(
            "tensor<i32, 2>",
            &format!("tensor_scatter tensor<i32, 2> {tail}"),
        )
    };
    for (what, text) in [
        (
            "gather: no type",
            text_with("tensor<i32, 1>", "tensor_gather %0 coords [%2]"),
        ),
        ("gather: no data", gather("coords [%2]")),
        ("gather: no coords clause", gather("%0 [%2]")),
        ("gather: no coordinate list", gather("%0 coords")),
        ("gather: an unclosed list", gather("%0 coords [%2, %3")),
        ("gather: an unopened list", gather("%0 coords %2]")),
        ("gather: a trailing separator", gather("%0 coords [%2,]")),
        ("gather: a missing separator", gather("%0 coords [%2 %3]")),
        ("gather: a lane for a value", gather("%0 coords [$2]")),
        ("gather: a bare number for a value", gather("%0 coords [2]")),
        ("gather: a lane for the data", gather("$0 coords [%2]")),
        ("gather: a misspelt clause", gather("%0 coord [%2]")),
        (
            "gather: a separator before the clause",
            gather("%0, coords [%2]"),
        ),
        ("gather: a parenthesized list", gather("%0 coords (%2, %3)")),
        (
            "scatter: no type",
            text_with("tensor<i32, 2>", "tensor_scatter %0, %1 coords [%2]"),
        ),
        ("scatter: no source", scatter("%0 coords [%2]")),
        ("scatter: no separator", scatter("%0 %1 coords [%2]")),
        ("scatter: no init", scatter(", %1 coords [%2]")),
        ("scatter: no coords clause", scatter("%0, %1 [%2]")),
        ("scatter: no coordinate list", scatter("%0, %1 coords")),
        ("scatter: an unclosed list", scatter("%0, %1 coords [%2")),
        (
            "scatter: a trailing separator",
            scatter("%0, %1 coords [%2,]"),
        ),
        ("scatter: a lane for a value", scatter("%0, %1 coords [$2]")),
        (
            "scatter: a lane for the source",
            scatter("%0, $1 coords [%2]"),
        ),
        ("scatter: a misspelt clause", scatter("%0, %1 coord [%2]")),
    ] {
        assert!(parse_module(&text).is_err(), "{what} parsed:\n{text}");
    }
}
