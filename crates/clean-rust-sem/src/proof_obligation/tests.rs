// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{Mutability, RustType, UintType};
use crate::vir::{BasicBlock, LocalDecl, UnwindAction};

fn scalar_uint(value: u128) -> Operand {
    Operand::Constant(Constant::Scalar(ScalarValue::Uint(value)))
}

fn test_body() -> Body {
    let mut body = Body::new();
    body.add_local(LocalDecl::new(RustType::Unit, Mutability::Mutable));
    body.add_local(LocalDecl::new(
        RustType::Uint(UintType::U32),
        Mutability::Mutable,
    ));
    body
}

fn assert_term(msg: AssertMessage) -> Term {
    Term::Assert {
        cond: Operand::Copy(Place::Local(1)),
        expected: true,
        msg,
        target: 1,
        target_args: Vec::new(),
        unwind: UnwindAction::Continue,
    }
}

fn extract_single_assertion(msg: AssertMessage) -> ProofObligation {
    let mut body = test_body();
    body.add_block(BasicBlock::new(assert_term(msg)));
    body.add_block(BasicBlock::new(Term::Return));
    let mut obligations = extract_obligations("demo", &body);
    assert_eq!(obligations.len(), 1);
    obligations.pop().unwrap()
}

#[test]
fn extract_obligations_classifies_assertion_sources() {
    for (msg, source) in [
        (
            AssertMessage::Custom("x > 0".to_string()),
            ObligationSource::AssertionCheck,
        ),
        (
            AssertMessage::BoundsCheck {
                len: scalar_uint(8),
                index: scalar_uint(3),
            },
            ObligationSource::Precondition,
        ),
        (
            AssertMessage::Overflow(BinOp::Add, scalar_uint(1), scalar_uint(2)),
            ObligationSource::Overflow,
        ),
    ] {
        let obligation = extract_single_assertion(msg);
        assert_eq!(obligation.location, "demo:bb0:term");
        assert_eq!(obligation.source, source);
    }
}

#[test]
fn extract_obligations_maps_safety_asserts_to_preconditions() {
    let division = extract_single_assertion(AssertMessage::DivisionByZero(scalar_uint(3)));
    let aligned = extract_single_assertion(AssertMessage::MisalignedPointerDereference {
        required: scalar_uint(8),
        found: scalar_uint(4),
    });

    assert_eq!(division.source, ObligationSource::Precondition);
    assert_eq!(
        division.invariants,
        vec![Expr::app(
            Expr::const_str("RustVIR.nonZero"),
            Expr::nat_lit(3)
        )]
    );
    assert_eq!(aligned.source, ObligationSource::Precondition);
    assert_eq!(
        aligned.invariants,
        vec![Expr::apps(
            Expr::const_str("RustVIR.aligned"),
            [Expr::nat_lit(4), Expr::nat_lit(8)],
        )]
    );
}

#[test]
fn extract_obligations_finds_unsafe_address_of_and_raw_retag_sites() {
    let mut block = BasicBlock::new(Term::Return);
    block.add_statement(Stmt::Assign {
        place: Place::Local(0),
        rvalue: Rvalue::AddressOf {
            mutability: Mutability::Mutable,
            place: Place::Local(1),
        },
    });
    block.add_statement(Stmt::Retag {
        kind: RetagKind::Raw(Mutability::Mutable),
        place: Place::Local(1),
    });

    let mut body = test_body();
    body.add_block(block);
    let obligations = extract_obligations("unsafe_demo", &body);

    assert_eq!(obligations.len(), 2);
    assert_eq!(obligations[0].source, ObligationSource::UnsafeBlock);
    assert_eq!(obligations[0].location, "unsafe_demo:bb0:stmt0");
    assert_eq!(obligations[1].source, ObligationSource::UnsafeBlock);
    assert_eq!(obligations[1].location, "unsafe_demo:bb0:stmt1");
    assert_eq!(
        obligations[0].postconditions,
        vec![Expr::app(
            Expr::const_str("RustVIR.unsafeSite"),
            translate_place(&Place::Local(1)),
        )]
    );
}

#[test]
fn vir_to_lean_translates_assert_terms() {
    let translator = VirToLean::new();
    let term = Term::Assert {
        cond: scalar_uint(7),
        expected: true,
        msg: AssertMessage::DivisionByZero(scalar_uint(3)),
        target: 0,
        target_args: Vec::new(),
        unwind: UnwindAction::Continue,
    };

    assert_eq!(
        translator.translate_term(&term),
        Some(Expr::apps(
            Expr::const_str("RustVIR.assertion"),
            [
                Expr::app(Expr::const_str("RustVIR.divisionByZero"), Expr::nat_lit(3)),
                Expr::nat_lit(7),
                Expr::const_str("Bool.true"),
            ],
        ))
    );
}

#[test]
fn obligation_batch_submits_goal_terms() {
    let batch = ObligationBatch {
        obligations: vec![ProofObligation {
            function: "main".to_string(),
            location: "main:bb0:term".to_string(),
            source: ObligationSource::AssertionCheck,
            preconditions: vec![Expr::const_str("P")],
            postconditions: vec![Expr::const_str("Q")],
            invariants: vec![Expr::const_str("I")],
        }],
    };

    let submitted = batch.submit(|obligation, goal| (obligation.location.clone(), goal));
    assert_eq!(submitted.len(), 1);
    assert_eq!(submitted[0].0, "main:bb0:term");
    assert_eq!(
        submitted[0].1,
        Expr::arrow(
            Expr::const_str("P"),
            Expr::apps(
                Expr::const_str("And"),
                [Expr::const_str("I"), Expr::const_str("Q")],
            ),
        )
    );
}

#[test]
fn translate_constant_tuple_aggregate_encodes_constructor_with_elements() {
    // (1, 2) const tuple -> `Tuple 1 2`
    let constant = Constant::Aggregate(Box::new(AggregateConst::tuple(vec![
        Constant::Scalar(ScalarValue::Uint(1)),
        Constant::Scalar(ScalarValue::Uint(2)),
    ])));
    let expr = translate_constant(&constant);
    let expected = Expr::apps(
        Expr::const_str("Tuple"),
        [Expr::nat_lit(1), Expr::nat_lit(2)],
    );
    assert_eq!(expr, expected);
}

#[test]
fn translate_constant_array_aggregate_encodes_array_head() {
    // [1, 2, 3] const array of non-byte ints -> `Array 1 2 3`
    let constant = Constant::Aggregate(Box::new(AggregateConst::array(
        RustType::Uint(UintType::U32),
        vec![
            Constant::Scalar(ScalarValue::Uint(1)),
            Constant::Scalar(ScalarValue::Uint(2)),
            Constant::Scalar(ScalarValue::Uint(3)),
        ],
    )));
    let expr = translate_constant(&constant);
    let expected = Expr::apps(
        Expr::const_str("Array"),
        [Expr::nat_lit(1), Expr::nat_lit(2), Expr::nat_lit(3)],
    );
    assert_eq!(expr, expected);
}

#[test]
fn translate_constant_struct_aggregate_encodes_named_head() {
    // Point { x: 1, y: 2 } -> `Point 1 2`
    let constant = Constant::Aggregate(Box::new(AggregateConst {
        kind: ConstAggregateKind::Struct {
            name: "Point".to_string(),
            field_names: vec!["x".to_string(), "y".to_string()],
        },
        elements: vec![
            Constant::Scalar(ScalarValue::Uint(1)),
            Constant::Scalar(ScalarValue::Uint(2)),
        ],
    }));
    let expr = translate_constant(&constant);
    let expected = Expr::apps(
        Expr::const_str("Point"),
        [Expr::nat_lit(1), Expr::nat_lit(2)],
    );
    assert_eq!(expr, expected);
}

#[test]
fn translate_constant_enum_aggregate_encodes_qualified_variant_head() {
    // Option::Some(3) -> `Option.Some 3`
    let constant = Constant::Aggregate(Box::new(AggregateConst {
        kind: ConstAggregateKind::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            field_names: Vec::new(),
        },
        elements: vec![Constant::Scalar(ScalarValue::Uint(3))],
    }));
    let expr = translate_constant(&constant);
    let expected = Expr::app(Expr::const_str("Option.Some"), Expr::nat_lit(3));
    assert_eq!(expr, expected);
}

#[test]
fn translate_constant_enum_unit_variant_encodes_bare_head() {
    // Option::None -> `Option.None`
    let constant = Constant::Aggregate(Box::new(AggregateConst {
        kind: ConstAggregateKind::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            field_names: Vec::new(),
        },
        elements: Vec::new(),
    }));
    let expr = translate_constant(&constant);
    assert_eq!(expr, Expr::const_str("Option.None"));
}

#[test]
fn aggregate_constant_serde_round_trips() {
    // The aggregate constant must survive a JSON round-trip unchanged so it can
    // be persisted/transported alongside the rest of the VIR.
    let constant = Constant::Aggregate(Box::new(AggregateConst {
        kind: ConstAggregateKind::Struct {
            name: "Point".to_string(),
            field_names: vec!["x".to_string(), "y".to_string()],
        },
        elements: vec![
            Constant::Scalar(ScalarValue::Int(-1)),
            Constant::Aggregate(Box::new(AggregateConst::tuple(vec![
                Constant::Scalar(ScalarValue::Bool(true)),
                Constant::Str("s".to_string()),
            ]))),
        ],
    }));
    let json = serde_json::to_string(&constant).expect("aggregate constant serializes");
    let back: Constant = serde_json::from_str(&json).expect("aggregate constant deserializes");
    // Compare via the deterministic Lean encoding (Constant has no PartialEq).
    assert_eq!(translate_constant(&constant), translate_constant(&back));
}
