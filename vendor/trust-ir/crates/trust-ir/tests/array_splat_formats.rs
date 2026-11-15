// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// v50: the FORMAT half of the constant-size uniform array — `Constant::Splat
// { elem, len }` (Constant tag 16) and `Inst::ArraySplat { ty, value }` (Inst
// tag 59). The validator's rules and the interpreter's execution live in
// trust-ir-build (tests/array_splat.rs). This file pins, at u64-scale lengths,
// that every codec carries the pair in space independent of the length:
//
//   * binary: header v50 exactly when the pair occurs, a lossless round trip,
//     a few hundred bytes for 2^40 copies, the `version >= 50` read gate
//     load-bearing, the v38 projections refusing by name, and a
//     non-canonical splat (`len < 2`) refused at decode;
//   * text: `splat[ c; n ]` / `array_splat <ty> %v`, idempotent, and the
//     parser refusing a non-canonical splat;
//   * JSON / MessagePack round trips;
//   * the stable digest (every module stays digestible through the
//     infallible writer) and the semantic diff see the length.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::binary::{
    self, ARRAY_SPLAT_FORMAT_VERSION, BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions,
    ProjectedModuleBinaryPlan,
};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage, Module,
    Ty, ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

const HUGE: u64 = 1 << 40;

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

/// `ZEROS: [u8 x 2^32] = splat[ 0; 2^32 ]`, a nested `GRID`, and
/// `fill(x: i64) -> ([i64 x n], [i64 x n])` returning `array_splat %x` and a
/// `Const` splat — every length `len`.
fn module(len: u64) -> Module {
    let mut m = Module::new("array_splat_formats");
    let u8_id = m.add_type(Ty::U8).expect("Module::add_type: test fixture");
    let i64_id = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let row_id = m
        .add_type(Ty::Array(u8_id, len))
        .expect("Module::add_type: test fixture");
    let global = |name: &str, ty: Ty, c: Constant| Global {
        name: name.to_string(),
        ty,
        mutable: false,
        initializer: Some(c),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    };
    m.globals.push(global(
        "ZEROS",
        Ty::Array(u8_id, len),
        Constant::splat(Constant::Int(0), len),
    ));
    m.globals.push(global(
        "GRID",
        Ty::Array(row_id, len),
        Constant::splat(Constant::splat(Constant::Int(7), len), len),
    ));
    let big = Ty::Array(i64_id, len);
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![big.clone(), big.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "fill", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((v(0), Ty::I64));
    b.body.push(
        InstrNode::new(Inst::ArraySplat {
            ty: big.clone(),
            value: v(0),
        })
        .with_results(vec![v(1)]),
    );
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: big,
            value: Constant::splat(Constant::Int(-3), len),
        })
        .with_results(vec![v(2)]),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![v(1), v(2)],
    }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}

#[test]
fn binary_round_trips_at_v50_in_space_independent_of_the_length() {
    let m = module(HUGE);
    let bytes = binary::serialize_module(&m).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), ARRAY_SPLAT_FORMAT_VERSION);
    let back = binary::deserialize_module(&bytes).expect("decodes");
    assert_eq!(back, m);
    assert_eq!(
        binary::serialize_module(&back).expect("serialize_module: test fixture"),
        bytes,
        "re-encoding is exact"
    );
    // Every length is one word (a fixed u64 in a splat, a varint in the
    // array type), never a list: 2^40 copies of each of the three splats and
    // the instruction fit in a few hundred bytes.
    assert!(
        bytes.len() < 1024,
        "a splat's wire size does not depend on its length: {} bytes",
        bytes.len()
    );
    let max = module(u64::MAX);
    assert_eq!(
        binary::deserialize_module(
            &binary::serialize_module(&max).expect("serialize_module: test fixture")
        )
        .unwrap(),
        max
    );
}

#[test]
fn a_module_without_the_pair_keeps_its_pre_v50_header() {
    let mut m = module(HUGE);
    m.globals.clear();
    m.functions.clear();
    assert!(
        header_version(&binary::serialize_module(&m).expect("serialize_module: test fixture"))
            < ARRAY_SPLAT_FORMAT_VERSION
    );
    // Each member alone selects v50.
    let mut only_inst = module(HUGE);
    only_inst.globals.clear();
    only_inst.functions[0].blocks[0].body.remove(1);
    only_inst.functions[0].blocks[0].body[1] = InstrNode::new(Inst::Return { values: vec![v(1)] });
    assert_eq!(
        header_version(
            &binary::serialize_module(&only_inst).expect("serialize_module: test fixture")
        ),
        ARRAY_SPLAT_FORMAT_VERSION
    );
    let mut only_constant = module(HUGE);
    only_constant.functions.clear();
    assert_eq!(
        header_version(
            &binary::serialize_module(&only_constant).expect("serialize_module: test fixture")
        ),
        ARRAY_SPLAT_FORMAT_VERSION
    );
}

/// The `version >= 50` read gate is load-bearing: the same bytes relabelled
/// with the previous header are refused at the tag, never misread.
#[test]
fn the_v50_read_gate_refuses_an_older_header() {
    let mut only_constant = module(HUGE);
    only_constant.functions.clear();
    let mut only_inst = module(HUGE);
    only_inst.globals.clear();
    only_inst.functions[0].blocks[0].body.remove(1);
    only_inst.functions[0].blocks[0].body[1] = InstrNode::new(Inst::Return { values: vec![v(1)] });
    for (tag, m) in [(16u8, only_constant), (59u8, only_inst)] {
        let mut bytes = binary::serialize_module(&m).expect("serialize_module: test fixture");
        bytes[8..12].copy_from_slice(&(ARRAY_SPLAT_FORMAT_VERSION - 1).to_le_bytes());
        match binary::deserialize_module(&bytes) {
            Err(binary::BinaryError::InvalidTag(t)) => assert_eq!(t, tag),
            other => panic!("tag {tag} under an older header must be refused: {other:?}"),
        }
    }
}

#[test]
fn the_v38_projections_refuse_the_pair_by_name() {
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        let refused = ProjectedModuleBinaryPlan::try_new(
            &module(HUGE),
            ModuleBinaryOptions {
                body,
                ..Default::default()
            },
        )
        .map(|_| ())
        .unwrap_err();
        assert_eq!(refused, BinaryProjectionError::ArraySplatRequiresV50);
    }
}

/// One spelling (SPEC_RATIFICATIONS §3.1): zero or one copy is the list
/// spelling, so the decoder refuses a `Splat` with `len < 2`, as it refuses a
/// non-canonical `U128`.
#[test]
fn the_decoder_refuses_a_non_canonical_splat() {
    for len in [0u64, 1] {
        let mut m = module(HUGE);
        m.functions.clear();
        m.globals.truncate(1);
        m.globals[0].initializer = Some(Constant::Splat {
            elem: Box::new(Constant::Int(0)),
            len,
        });
        let bytes = binary::serialize_module(&m).expect("serialize_module: test fixture");
        match binary::deserialize_module(&bytes) {
            Err(binary::BinaryError::InvalidData(message)) => {
                assert!(
                    message.contains("non-canonical Constant::Splat"),
                    "{message}"
                )
            }
            other => panic!("a splat of {len} must be refused: {other:?}"),
        }
        // The serde formats refuse it on read too.
        let json = serde_json::to_string(&m).expect("json");
        let error = serde_json::from_str::<Module>(&json).expect_err("json refuses it");
        assert!(
            error.to_string().contains("non-canonical Constant::Splat"),
            "{error}"
        );
        let packed = rmp_serde::to_vec(&m).expect("msgpack");
        let error = rmp_serde::from_slice::<Module>(&packed).expect_err("msgpack refuses it");
        assert!(
            error.to_string().contains("non-canonical Constant::Splat"),
            "{error}"
        );
    }
}

#[test]
fn text_round_trips_and_is_idempotent() {
    let m = module(HUGE);
    let text = trust_ir::format::canonical_checked(&m).expect("text carries the pair");
    assert!(
        text.contains(&format!("splat[ -3; {HUGE} ]")),
        "constant spelling: {text}"
    );
    assert!(
        text.contains(&format!("splat[ splat[ 7; {HUGE} ]; {HUGE} ]")),
        "a nested splat is written once per level: {text}"
    );
    assert!(
        text.contains("array_splat "),
        "instruction spelling: {text}"
    );
    let parsed = trust_ir::parser::parse_module(&text).expect("the parser reads it back");
    assert_eq!(parsed.globals, m.globals);
    assert_eq!(
        parsed.functions[0].blocks[0].body,
        m.functions[0].blocks[0].body
    );
    assert_eq!(trust_ir::format::canonical(&parsed), text, "idempotent");
    assert!(trust_ir::diff::diff(&m, &parsed).is_empty());
}

#[test]
fn the_parser_refuses_a_non_canonical_splat() {
    let text = trust_ir::format::canonical(&module(HUGE));
    for len in ["0", "1"] {
        let broken = text.replacen(
            &format!("splat[ -3; {HUGE} ]"),
            &format!("splat[ -3; {len} ]"),
            1,
        );
        assert_ne!(broken, text);
        let error = trust_ir::parser::parse_module(&broken).expect_err("len < 2 is refused");
        assert!(error.to_string().contains("non-canonical splat"), "{error}");
    }
}

#[test]
fn json_and_msgpack_round_trip() {
    let m = module(u64::MAX);
    let json = serde_json::to_string(&m).expect("json");
    let back: Module = serde_json::from_str(&json).expect("json decode");
    assert_eq!(back, m);
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(back, m);
}

/// Every module stays digestible through the INFALLIBLE writer (a consumer
/// digesting every module it sees must not panic), and the digest sees the
/// length and the spelling.
#[test]
fn the_stable_digest_is_total_and_sees_the_length() {
    let a = module(HUGE).stable_digest();
    assert_eq!(a, module(HUGE).stable_digest());
    assert_ne!(a, module(HUGE - 1).stable_digest());
    // A splat and the equal list are different SPELLINGS (the validator keeps
    // a valid module to one of them), so they are different identities.
    let mut spelled = Module::new("spelling");
    let u8_id = spelled
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    spelled.globals.push(Global {
        name: "G".into(),
        ty: Ty::Array(u8_id, 3),
        mutable: false,
        initializer: Some(Constant::splat(Constant::Int(1), 3)),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let mut listed = spelled.clone();
    listed.globals[0].initializer = Some(Constant::Array(vec![Constant::Int(1); 3]));
    assert_ne!(spelled.stable_digest(), listed.stable_digest());
}

#[test]
fn the_semantic_diff_sees_the_length() {
    assert!(trust_ir::diff::diff(&module(HUGE), &module(HUGE)).is_empty());
    assert!(!trust_ir::diff::diff(&module(HUGE), &module(HUGE - 1)).is_empty());
}

/// Pure, not a terminator, one value operand; the constant has one child.
#[test]
fn effect_operand_and_child_classification() {
    let inst = Inst::ArraySplat {
        ty: Ty::Array(trust_ir::TyId::new(0), HUGE),
        value: v(7),
    };
    assert!(!inst.has_observable_effects());
    assert!(!inst.is_terminator());
    let mut seen = Vec::new();
    inst.visit_value_operands(|id| seen.push(id));
    assert_eq!(seen, vec![v(7)]);
    let splat = Constant::splat(Constant::Int(4), HUGE);
    assert_eq!(splat.children().len(), 1, "the element is ONE child");
    let mut count = 0;
    splat.visit_constants(|_| count += 1);
    assert_eq!(
        count, 2,
        "a walk visits the splat and its element, never `len` nodes"
    );
}

/// The sanctioned constructors pick the canonical spelling by LENGTH and by
/// CONTENT, in time proportional to what the caller built.
#[test]
fn the_sanctioned_constructors_pick_the_one_spelling() {
    assert_eq!(
        Constant::splat(Constant::Int(1), 0),
        Constant::Array(vec![])
    );
    assert_eq!(
        Constant::splat(Constant::Int(1), 1),
        Constant::Array(vec![Constant::Int(1)])
    );
    assert!(matches!(
        Constant::splat(Constant::Int(1), HUGE),
        Constant::Splat { len: HUGE, .. }
    ));
    assert_eq!(
        Constant::array(vec![Constant::Int(5); 4]),
        Constant::splat(Constant::Int(5), 4)
    );
    assert_eq!(
        Constant::array(vec![Constant::Int(5), Constant::Int(6)]),
        Constant::Array(vec![Constant::Int(5), Constant::Int(6)])
    );
    assert_eq!(
        Constant::array(vec![Constant::Int(5)]),
        Constant::Array(vec![Constant::Int(5)])
    );
}
