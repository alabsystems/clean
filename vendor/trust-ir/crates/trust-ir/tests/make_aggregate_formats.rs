// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.5 (F-049): the FORMAT half of `Inst::MakeAggregate`. The validator's
// lane rules live in trust-ir-build (tests/make_aggregate.rs); this file pins
// what each transport does with the instruction:
//
//   * text (`%r = make_aggregate <ty> [variant N] (%a, %b)`), JSON and
//     MessagePack round-trip it losslessly, the canonical text is idempotent,
//     and the semantic diff sees the variant clause as identity;
//   * binary: Inst tag 60, read-gated on the v51 INST wire batch
//     (docs/wire-allocation.md). Until that batch the writer FAILED CLOSED on
//     it (a panic, as for `Ty::Error`); now every spelling round-trips at the
//     batch version, an older header carrying the tag is refused, and the
//     conformance corpus's `inst_wire_batch` golden carries it.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::ty::{EnumDef, EnumVariant};
use trust_ir::{
    Block, BlockId, EnumId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

/// `enum E { A(i32, bool), B }` plus one function per spelling:
/// `variant 0 (%x, %b)`, `variant 1 ()`, and a two-lane tuple.
fn module(variant_of_first: u32) -> Module {
    let mut m = Module::new("make_aggregate_formats");
    let e = Ty::Enum(EnumId::new(0));
    m.add_enum(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::I32, Ty::Bool],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    ));
    let tuple = Ty::Tuple(vec![Ty::I32, Ty::Bool]);
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::Bool],
            returns: vec![e.clone(), e.clone(), tuple.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "build", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((v(0), Ty::I32));
    b.params.push((v(1), Ty::Bool));
    b.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: e.clone(),
            variant: Some(variant_of_first),
            fields: vec![v(0), v(1)],
        })
        .with_results(vec![v(2)]),
    );
    b.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: e,
            variant: Some(1),
            fields: vec![],
        })
        .with_results(vec![v(3)]),
    );
    b.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: tuple,
            variant: None,
            fields: vec![v(0), v(1)],
        })
        .with_results(vec![v(4)]),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![v(2), v(3), v(4)],
    }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}

#[test]
fn text_round_trips_every_spelling_and_is_idempotent() {
    let m = module(0);
    let text = trust_ir::format::canonical_checked(&m).expect("text carries the instruction");
    assert!(
        text.contains("make_aggregate enum.0 variant 0 (%0, %1)"),
        "enum spelling: {text}"
    );
    assert!(
        text.contains("make_aggregate enum.0 variant 1 ()"),
        "fieldless variant keeps its empty parenthesis: {text}"
    );
    assert!(
        text.contains("make_aggregate tuple(i32, bool) (%0, %1)")
            || text.contains("make_aggregate ("),
        "tuple spelling has no variant clause: {text}"
    );
    let parsed = trust_ir::parser::parse_module(&text).expect("the parser reads it back");
    assert_eq!(
        parsed.functions[0].blocks[0].body,
        m.functions[0].blocks[0].body
    );
    let again = trust_ir::format::canonical(&parsed);
    assert_eq!(again, text, "canonical text is idempotent");
    assert!(
        trust_ir::diff::diff(&m, &parsed).is_empty(),
        "no semantic change across the text round trip"
    );
}

#[test]
fn json_and_msgpack_round_trip() {
    let m = module(0);
    let json = serde_json::to_string(&m).expect("json");
    let back: Module = serde_json::from_str(&json).expect("json decode");
    assert_eq!(
        back.functions[0].blocks[0].body,
        m.functions[0].blocks[0].body
    );
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(
        back.functions[0].blocks[0].body,
        m.functions[0].blocks[0].body
    );
}

/// Two constructions of the SAME enum type differing only in `variant` are
/// different instructions to the semantic diff, and the absent clause is a
/// third, distinct spelling — never a defaulted 0.
#[test]
fn diff_treats_the_variant_clause_as_identity() {
    let a = module(0);
    let b = module(1);
    assert!(
        !trust_ir::diff::diff(&a, &b).is_empty(),
        "variant 0 vs variant 1"
    );
    let mut c = module(0);
    if let Inst::MakeAggregate { variant, .. } = &mut c.functions[0].blocks[0].body[0].inst {
        *variant = None;
    }
    assert!(
        !trust_ir::diff::diff(&a, &c).is_empty(),
        "variant 0 vs absent"
    );
    assert!(
        trust_ir::diff::diff(&a, &module(0)).is_empty(),
        "same spelling"
    );
}

#[test]
fn the_parser_refuses_a_malformed_lane_list() {
    let text = trust_ir::format::canonical(&module(0));
    // Drop the closing parenthesis of the first lane list.
    let broken = text.replacen("(%0, %1)", "(%0, %1", 1);
    assert!(
        trust_ir::parser::parse_module(&broken).is_err(),
        "an unterminated lane list must not parse"
    );
}

#[test]
fn binary_round_trips_every_spelling_at_the_inst_wire_batch_version() {
    for variant_of_first in [0, 1] {
        let m = module(variant_of_first);
        let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
        let (back, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
            .expect("a MakeAggregate module decodes");
        assert_eq!(
            version.get(),
            trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION,
            "MakeAggregate selects the INST wire batch version"
        );
        assert_eq!(back, m, "lossless: type, variant clause and lanes");
        assert_eq!(
            trust_ir::binary::serialize_module(&back).expect("serialize_module: test fixture"),
            bytes
        );
        assert_eq!(back.stable_digest(), m.stable_digest());
    }
    // The variant clause is identity on the wire too: variant 0 vs 1 differ.
    assert_ne!(
        trust_ir::binary::serialize_module(&module(0)).expect("serialize_module: test fixture"),
        trust_ir::binary::serialize_module(&module(1)).expect("serialize_module: test fixture")
    );
}

/// `has_observable_effects` is `false` (total, pure, freely removable), and
/// the instruction is not a terminator; every lane is a value operand.
#[test]
fn effect_and_operand_classification() {
    let inst = Inst::MakeAggregate {
        ty: Ty::Tuple(vec![Ty::I32, Ty::Bool]),
        variant: None,
        fields: vec![v(7), v(9)],
    };
    assert!(!inst.has_observable_effects());
    assert!(!inst.is_terminator());
    let mut seen = Vec::new();
    inst.visit_value_operands(|id| seen.push(id));
    assert_eq!(seen, vec![v(7), v(9)]);
}
