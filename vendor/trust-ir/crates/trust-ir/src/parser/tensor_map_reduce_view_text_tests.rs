// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The text spellings of the tensor region's map, reduce and view
//! (PKG-U13c):
//!
//! * `tensor_map TY (%a, ..) { NODE; .. }`, a NODE the scalar instruction's
//!   own spelling with `$lane` for `%value` (`add i32 $0, $1`, `neg i32 $0`,
//!   `icmp slt i32 $0, $1`, `select i32 $2, $0, $1`, `sext i8 $0 to i32`);
//! * `tensor_reduce OP TY %x axes [a, ..] order row_major`;
//! * `tensor_view TY %src params [%p, ..] exprs [NODE, ..] shape [$i, ..]
//!   index [$j, ..]`, then an optional `fill %f`.
//!
//! The printer and this parser agree byte for byte, and a malformed spelling
//! is a `ParseError`, never a defaulted field. The grammar is syntax only:
//! every lane, axis and node rule is the validator's, so an ill-typed but
//! well-spelled instruction parses.

use super::parse_module;
use crate::inst::{BinOp, CastOp, ICmpOp, Inst, UnOp};
use crate::node::InstrNode;
use crate::ty::{FuncTy, Ty};
use crate::value::{BlockId, FuncId, ValueId};
use crate::{
    Block, Function, Module, TensorIndexExpr as E, TensorMapNode, TensorReduceOp, TensorReduceOrder,
};

type Node = TensorMapNode<crate::NoExt>;

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

/// `fn @t(tensor<i32, 2>, tensor<i32, 2>, i32, usize) -> (result)` whose one
/// instruction line is `line` (its result `%4`), then `ret %4`.
fn text_with(result: &str, line: &str) -> String {
    format!(
        r#"; TrustIr text format v1
module "tensor_map_reduce_view_text"

functy.0 = (tensor<i32, 2>, tensor<i32, 2>, i32, usize) -> ({result})

fn @t(functy.0) {{
bb0(%0: tensor<i32, 2>, %1: tensor<i32, 2>, %2: i32, %3: usize):
    %4 = {line}
    ret %4
}}
"#
    )
}

fn the_instruction(module: &Module) -> &Inst {
    &module.functions[0].blocks[0].body[0].inst
}

const MAP_LINE: &str = "tensor_map tensor<i32, 2> (%0, %1, %2) { add i32 $0, $1; neg i32 $3; \
                        icmp sgt i32 $4, $2; select i32 $5, $4, $2; trunc i32 $6 to i8; sext i8 \
                        $7 to i32 }";

const REDUCE_LINE: &str = "tensor_reduce smax tensor<i32, 1> %0 axes [0] order row_major";

const VIEW_LINE: &str = "tensor_view tensor<i32, 2> %0 params [%3] exprs [src_extent(1), \
                         src_extent(0), coord(1), param(0), add($2, $3), coord(0)] shape [$0, \
                         $1] index [$4, $5] fill %2";

/// Each spelling parses to exactly the instruction it spells and prints
/// back the same bytes.
#[test]
fn map_reduce_and_view_text_parses_to_the_instruction_and_prints_back() {
    let map = parse_module(&text_with("tensor<i32, 2>", MAP_LINE)).expect("the map parses");
    assert_eq!(
        the_instruction(&map),
        &Inst::TensorMap {
            ty: tensor(Ty::I32, 2),
            args: vec![v(0), v(1), v(2)],
            body: vec![
                Node::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: 0,
                    rhs: 1,
                },
                Node::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: 3,
                },
                Node::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I32,
                    lhs: 4,
                    rhs: 2,
                },
                Node::Select {
                    ty: Ty::I32,
                    cond: 5,
                    then_lane: 4,
                    else_lane: 2,
                },
                Node::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I32,
                    dst_ty: Ty::I8,
                    operand: 6,
                },
                Node::Cast {
                    op: CastOp::SExt,
                    src_ty: Ty::I8,
                    dst_ty: Ty::I32,
                    operand: 7,
                },
            ],
        }
    );
    let reduce =
        parse_module(&text_with("tensor<i32, 1>", REDUCE_LINE)).expect("the reduction parses");
    assert_eq!(
        the_instruction(&reduce),
        &Inst::TensorReduce {
            ty: tensor(Ty::I32, 1),
            src: v(0),
            op: TensorReduceOp::SMax,
            axes: vec![0],
            order: TensorReduceOrder::RowMajor,
        }
    );
    let view = parse_module(&text_with("tensor<i32, 2>", VIEW_LINE)).expect("the view parses");
    assert_eq!(
        the_instruction(&view),
        &Inst::TensorView {
            ty: tensor(Ty::I32, 2),
            src: v(0),
            params: vec![v(3)],
            exprs: vec![
                E::SrcExtent(1),
                E::SrcExtent(0),
                E::Coord(1),
                E::Param(0),
                E::Add(2, 3),
                E::Coord(0),
            ],
            shape: vec![0, 1],
            index: vec![4, 5],
            fill: Some(v(2)),
        }
    );
    for (module, line) in [(map, MAP_LINE), (reduce, REDUCE_LINE), (view, VIEW_LINE)] {
        let printed = round_trip_eq(&module);
        assert!(printed.contains(&format!("    %4 = {line}\n")), "{printed}");
    }
}

/// `f(params..) -> result` whose one instruction is `inst`.
fn one_instruction_module(params: Vec<Ty>, result: Ty, inst: Inst) -> Module {
    let mut module = Module::new("tensor_map_reduce_view_text");
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

/// Every reduction operator, every index node (a literal at the top of
/// `u64` included), an empty axis list, a view with no parameters and no
/// fill, and an empty map body round-trip structurally.
#[test]
fn every_operator_node_and_empty_list_round_trips() {
    for op in TensorReduceOp::ALL {
        round_trip_eq(&one_instruction_module(
            vec![tensor(Ty::U16, 2)],
            tensor(Ty::U16, 0),
            Inst::TensorReduce {
                ty: tensor(Ty::U16, 0),
                src: v(0),
                op,
                axes: vec![0, 1],
                order: TensorReduceOrder::RowMajor,
            },
        ));
    }
    round_trip_eq(&one_instruction_module(
        vec![tensor(Ty::I8, 1)],
        tensor(Ty::I8, 1),
        Inst::TensorReduce {
            ty: tensor(Ty::I8, 1),
            src: v(0),
            op: TensorReduceOp::Xor,
            axes: vec![],
            order: TensorReduceOrder::RowMajor,
        },
    ));
    let text = round_trip_eq(&one_instruction_module(
        vec![tensor(Ty::U8, 2), Ty::Usize],
        tensor(Ty::U8, 1),
        Inst::TensorView {
            ty: tensor(Ty::U8, 1),
            src: v(0),
            params: vec![v(1)],
            exprs: vec![
                E::Lit(u64::MAX),
                E::Param(0),
                E::SrcExtent(1),
                E::Coord(0),
                E::Add(0, 1),
                E::Sub(4, 2),
                E::Mul(5, 3),
                E::Div(6, 1),
                E::Rem(7, 2),
                E::Min(8, 1),
                E::Max(9, 2),
            ],
            shape: vec![2],
            index: vec![9, 10],
            fill: None,
        },
    ));
    assert!(
        text.contains(&format!(
            "exprs [lit({}), param(0), src_extent(1), coord(0), add($0, $1), sub($4, $2), \
             mul($5, $3), div($6, $1), rem($7, $2), min($8, $1), max($9, $2)] shape [$2] \
             index [$9, $10]\n",
            u64::MAX
        )),
        "{text}"
    );
    let text = round_trip_eq(&one_instruction_module(
        vec![tensor(Ty::I32, 0)],
        tensor(Ty::I32, 0),
        Inst::TensorView {
            ty: tensor(Ty::I32, 0),
            src: v(0),
            params: vec![],
            exprs: vec![],
            shape: vec![],
            index: vec![],
            fill: None,
        },
    ));
    assert!(
        text.contains("tensor_view tensor<i32, 0> %0 params [] exprs [] shape [] index []\n"),
        "{text}"
    );
    // An empty body (rule M3's refusal is the validator's) and an empty
    // operand list (rule M2's) are well spelled.
    let text = round_trip_eq(&one_instruction_module(
        vec![],
        tensor(Ty::I32, 1),
        Inst::TensorMap {
            ty: tensor(Ty::I32, 1),
            args: vec![],
            body: vec![],
        },
    ));
    assert!(
        text.contains("tensor_map tensor<i32, 1> () { }\n"),
        "{text}"
    );
}

/// A view without its optional `fill` ends at its own line: a `fill` on the
/// next line is not the view's (that line is no instruction, so the text is
/// refused), and the terminator after a fill-less view is still read.
#[test]
fn a_view_without_a_fill_ends_at_its_line() {
    let line = "tensor_view tensor<i32, 2> %0 params [] exprs [src_extent(0), src_extent(1), \
                coord(0), coord(1)] shape [$0, $1] index [$2, $3]";
    let text = text_with("tensor<i32, 2>", line);
    let module = parse_module(&text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    assert!(
        matches!(
            the_instruction(&module),
            Inst::TensorView { fill: None, .. }
        ),
        "{text}"
    );
    let body = &module.functions[0].blocks[0].body;
    assert_eq!(body.len(), 2, "the view, then the terminator:\n{text}");
    assert!(matches!(body[1].inst, Inst::Return { .. }), "{text}");
    let split = text.replace("    ret %4", "    fill %2\n    ret %4");
    assert!(
        parse_module(&split).is_err(),
        "a `fill` on the next line was read as the view's:\n{split}"
    );
}

/// A malformed spelling is a parse error, never a defaulted field.
#[test]
fn malformed_spellings_are_parse_errors() {
    let map = |body: &str| {
        text_with(
            "tensor<i32, 2>",
            &format!("tensor_map tensor<i32, 2> {body}"),
        )
    };
    let reduce = |tail: &str| text_with("tensor<i32, 1>", &format!("tensor_reduce {tail}"));
    let view = |tail: &str| {
        text_with(
            "tensor<i32, 2>",
            &format!("tensor_view tensor<i32, 2> {tail}"),
        )
    };
    for (what, text) in [
        ("map: no operand list", map("{ neg i32 $0 }")),
        ("map: no body", map("(%0)")),
        ("map: an unclosed body", map("(%0) { neg i32 $0")),
        ("map: a %value for a lane", map("(%0) { neg i32 %0 }")),
        ("map: a bare lane number", map("(%0) { neg i32 0 }")),
        ("map: an unknown operation", map("(%0) { frob i32 $0 }")),
        ("map: a node with no lane", map("(%0) { neg i32 }")),
        ("map: a cast with no target", map("(%0) { sext i8 $0 }")),
        (
            "map: a missing separator",
            map("(%0) { neg i32 $0 neg i32 $1 }"),
        ),
        ("map: a trailing separator", map("(%0) { neg i32 $0; }")),
        (
            "reduce: an unknown operator",
            reduce("sum tensor<i32, 1> %0 axes [1] order row_major"),
        ),
        (
            "reduce: no axes",
            reduce("add tensor<i32, 1> %0 order row_major"),
        ),
        ("reduce: no order", reduce("add tensor<i32, 1> %0 axes [1]")),
        (
            "reduce: an unknown order",
            reduce("add tensor<i32, 1> %0 axes [1] order col_major"),
        ),
        (
            "reduce: a negative axis",
            reduce("add tensor<i32, 1> %0 axes [-1] order row_major"),
        ),
        (
            "view: no params",
            view("%0 exprs [coord(0)] shape [] index [$0]"),
        ),
        ("view: no exprs", view("%0 params [] shape [] index []")),
        ("view: no shape", view("%0 params [] exprs [] index []")),
        ("view: no index", view("%0 params [] exprs [] shape []")),
        (
            "view: an unknown node",
            view("%0 params [] exprs [frob(0)] shape [] index []"),
        ),
        (
            "view: a node with one operand",
            view("%0 params [] exprs [add($0)] shape [] index []"),
        ),
        (
            "view: a lit with a lane",
            view("%0 params [] exprs [lit($0)] shape [] index []"),
        ),
        (
            "view: a negative lit",
            view("%0 params [] exprs [lit(-1)] shape [] index []"),
        ),
        (
            "view: a lit past u64",
            view("%0 params [] exprs [lit(18446744073709551616)] shape [] index []"),
        ),
        (
            "view: a bare shape id",
            view("%0 params [] exprs [lit(1)] shape [0] index []"),
        ),
        (
            "view: a fill with no value",
            view("%0 params [] exprs [] shape [] index [] fill"),
        ),
        (
            "view: a parameter that is a node",
            view("%0 params [$0] exprs [] shape [] index []"),
        ),
    ] {
        assert!(parse_module(&text).is_err(), "{what} parsed:\n{text}");
    }
}
