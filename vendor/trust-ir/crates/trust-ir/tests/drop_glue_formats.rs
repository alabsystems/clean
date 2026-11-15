// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment D, Part 1 (wire v55, `docs/SPEC_RATIFICATIONS.md` §20): the
// FORMAT half of executable drops outside the binary codec (whose section and
// tag 68 are pinned in `src/binary/drop_glue_tests.rs`):
//
//   * text: `drop_glue @func.N <ty>` module lines in the table's one order
//     (the parser refuses another), and `drop_invoke <ty>, %p to bbN(..)
//     unwind bbM`;
//   * JSON / MessagePack: `drop_glue` was the module's sole trailing skipped
//     field until wire v58, which made `completeness` before it always
//     emitted; v58 appended `closure_layouts` after it, so `drop_glue` is now
//     always emitted too and `closure_layouts` is the one trailing skip.
//     Documents written before the table existed still decode, with an empty
//     table.

#![cfg(all(
    feature = "binary",
    feature = "diff",
    feature = "fmt",
    feature = "parser",
    feature = "serde"
))]

use trust_ir::ty::{FieldDef, StructDef, StructRepr};
use trust_ir::value::{ClosureTyId, StructId};
use trust_ir::{
    Block, BlockId, ClosureLayoutDescriptor, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// Two structs with glue, a caller that drops one and drop-invokes the
/// other into a cleanup pad that resumes.
fn module() -> Module {
    let mut m = Module::new("drop_glue_formats");
    for id in 0..2 {
        m.add_struct(StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![FieldDef {
                name: "p".into(),
                ty: Ty::Ptr,
                offset: None,
            }],
            size: None,
            align: None,
            repr: StructRepr::default(),
            origin: None,
        });
    }
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (id, name) in [(0, "drop_s0"), (1, "drop_s1")] {
        let mut glue = Function::new(FuncId::new(id), name, sig, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        glue.blocks.push(block);
        m.try_add_function(glue)
            .expect("Module::try_add_function: test fixture");
    }
    let mut f = Function::new(FuncId::new(2), "f", sig, b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::Ptr));
    entry.body.push(InstrNode::new(Inst::Drop {
        ty: s(0),
        ptr: v(0),
    }));
    entry.body.push(InstrNode::new(Inst::DropInvoke {
        ty: s(1),
        ptr: v(0),
        normal_dest: b(1),
        normal_args: vec![v(0)],
        unwind_dest: b(2),
    }));
    f.blocks.push(entry);
    let mut normal = Block::new(b(1));
    normal.params.push((v(1), Ty::Ptr));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(normal);
    let mut pad = Block::new(b(2));
    pad.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(2), v(3)]),
    );
    pad.body.push(InstrNode::new(Inst::Resume { exn: v(2) }));
    f.blocks.push(pad);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    m.set_drop_glue(s(1), FuncId::new(1)).unwrap();
    m
}

#[test]
fn drop_glue_and_drop_invoke_round_trip_through_text_json_and_msgpack() {
    let m = module();

    let text = trust_ir::format::canonical_checked(&m).expect("text carries the table");
    for spelling in [
        "drop_glue @func.0 struct.0\n",
        "drop_glue @func.1 struct.1\n",
        "drop struct.0, %0\n",
        "drop_invoke struct.1, %0 to bb1(%0) unwind bb2",
    ] {
        assert!(text.contains(spelling), "missing `{spelling}`: {text}");
    }
    let parsed = trust_ir::parser::parse_module(&text).expect("the parser reads it back");
    assert_eq!(parsed.drop_glue, m.drop_glue);
    assert_eq!(parsed.functions[2].blocks, m.functions[2].blocks);
    assert_eq!(trust_ir::format::canonical(&parsed), text, "idempotent");
    // The text format loses nothing here.
    assert!(trust_ir::format::text_losses(&m).is_empty());

    let json = serde_json::to_string(&m).expect("json");
    let back: Module = serde_json::from_str(&json).expect("json decode");
    assert_eq!(back, m);
    let value: serde_json::Value = serde_json::from_str(&json).unwrap();
    assert_eq!(
        value["drop_glue"],
        serde_json::json!([
            { "glue": 0, "ty": { "Struct": 0 } },
            { "glue": 1, "ty": { "Struct": 1 } },
        ])
    );
    assert_eq!(
        value["functions"][2]["blocks"][0]["body"][1]["inst"],
        serde_json::json!({ "DropInvoke": {
            "ty": { "Struct": 1 }, "ptr": 0, "normal_dest": 1,
            "normal_args": [0], "unwind_dest": 2 } })
    );

    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(back, m);
}

#[test]
fn the_parser_refuses_a_non_canonical_drop_glue_table() {
    let text = trust_ir::format::canonical(&module());
    let swapped = text
        .replace("drop_glue @func.0 struct.0", "drop_glue @func.X struct.0")
        .replace("drop_glue @func.1 struct.1", "drop_glue @func.0 struct.1")
        .replace("drop_glue @func.X struct.0", "drop_glue @func.1 struct.0");
    assert_ne!(swapped, text);
    let duplicate_glue = text.replace("drop_glue @func.1 struct.1", "drop_glue @func.0 struct.1");
    let duplicate_key = text.replace("drop_glue @func.1 struct.1", "drop_glue @func.1 struct.0");
    for (what, broken) in [
        ("descending glue", swapped),
        ("equal glue", duplicate_glue),
        ("duplicate key", duplicate_key),
    ] {
        let error = trust_ir::parser::parse_module(&broken)
            .expect_err(what)
            .to_string();
        assert!(
            error.contains("canonical order") || error.contains("one row per type"),
            "{what}: {error}"
        );
    }
}

#[test]
fn a_pre_drop_glue_json_and_msgpack_module_decodes_with_an_empty_table() {
    // Pinned copies of the `assert_invoke` golden as it was written before
    // the table existed (`completeness` skipped when absent, no `drop_glue`).
    let compat = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-ir-conformance/tests/fixtures/compat");
    let bytes = std::fs::read(compat.join("pre_drop_glue_assert_invoke.msgpack"))
        .expect("pinned pre-drop-glue msgpack");
    let from_msgpack: Module = rmp_serde::from_slice(&bytes).expect("decodes");
    assert!(from_msgpack.drop_glue.is_empty());
    assert_eq!(from_msgpack.completeness, None);
    let json = std::fs::read_to_string(compat.join("pre_drop_glue_assert_invoke.json"))
        .expect("pinned pre-drop-glue json");
    assert!(!json.contains("completeness") && !json.contains("drop_glue"));
    let from_json: Module = serde_json::from_str(&json).expect("decodes");
    assert!(from_json.drop_glue.is_empty());
    assert_eq!(from_json, from_msgpack);
}

#[test]
fn completeness_and_the_drop_glue_and_closure_tables_are_always_emitted_and_blobs_is_the_trailing_skipped_field()
 {
    // No claim, no drop-glue table, no closure table, no blob table:
    // `completeness` is written (null), `drop_glue` and `closure_layouts` are
    // written (`[]`) — wire v58 appended `closure_layouts` after the
    // drop-glue table, v70 appended `blobs` after the closure table, and
    // positional MessagePack may skip only a TRAILING field — while `blobs`
    // is skipped, so a module without a blob table keeps one exact serde form.
    let plain = Module::new("plain");
    let text = serde_json::to_string(&plain).unwrap();
    assert!(
        text.ends_with(",\"completeness\":null,\"drop_glue\":[],\"closure_layouts\":[]}"),
        "completeness, drop_glue then closure_layouts are the last emitted fields: {text}"
    );
    assert!(!text.contains("blobs"), "{text}");

    // A drop-glue table no longer changes the document's SHAPE, only the
    // always-emitted field's value.
    let mut with_table = plain.clone();
    with_table.set_drop_glue(s(0), FuncId::new(0)).unwrap();
    let text_table = serde_json::to_string(&with_table).unwrap();
    assert!(
        text_table.contains(",\"completeness\":null,\"drop_glue\":[{")
            && text_table.ends_with("}],\"closure_layouts\":[]}"),
        "closure_layouts still follows the drop-glue table: {text_table}"
    );
    assert!(!text_table.contains("blobs"), "{text_table}");

    // Nor does a closure table, since v70.
    let mut with_closure = plain.clone();
    with_closure.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    let text_closure = serde_json::to_string(&with_closure).unwrap();
    assert!(
        text_closure.contains(",\"completeness\":null,\"drop_glue\":[],\"closure_layouts\":[{")
            && text_closure.ends_with("}]}"),
        "closure_layouts is the last emitted field: {text_closure}"
    );
    assert!(!text_closure.contains("blobs"), "{text_closure}");
    let mut with_both = with_table.clone();
    with_both.closure_layouts = with_closure.closure_layouts.clone();

    // A blob table is the one trailing skip: it appends exactly one field
    // after the always-emitted ones.
    let mut with_blob = plain.clone();
    with_blob.intern_blob(vec![1, 2, 3]);
    let text_blob = serde_json::to_string(&with_blob).unwrap();
    assert!(
        text_blob.contains(",\"drop_glue\":[],\"closure_layouts\":[],\"blobs\":[{"),
        "blobs trails the always-emitted fields: {text_blob}"
    );

    // Positional MessagePack: the module array ends with the nil claim, the
    // drop-glue table and the closure table, whether or not the tables are
    // empty; only a blob table appends exactly one trailing element after
    // them.
    let shapes = [&plain, &with_table, &with_closure, &with_both, &with_blob];
    let arrays: Vec<(Vec<u8>, Vec<rmpv_like::Any>)> = shapes
        .into_iter()
        .map(|m| {
            let mp = rmp_serde::to_vec(m).unwrap();
            let array = rmp_serde::from_slice(&mp).unwrap();
            (mp, array)
        })
        .collect();
    let [plain_a, table_a, closure_a, both_a, blob_a] = [0, 1, 2, 3, 4].map(|i| &arrays[i].1);
    assert_eq!(table_a.len(), plain_a.len(), "drop_glue is always emitted");
    assert_eq!(
        closure_a.len(),
        plain_a.len(),
        "closure_layouts is always emitted"
    );
    assert_eq!(both_a.len(), plain_a.len());
    assert_eq!(blob_a.len(), plain_a.len() + 1, "one trailing skip");
    use rmpv_like::Any::{Nil, Seq};
    assert!(
        matches!(plain_a[plain_a.len() - 3..], [Nil, Seq(0), Seq(0)]),
        "{plain_a:?}"
    );
    assert!(
        matches!(table_a[table_a.len() - 3..], [Nil, Seq(1), Seq(0)]),
        "{table_a:?}"
    );
    assert!(
        matches!(closure_a[closure_a.len() - 3..], [Nil, Seq(0), Seq(1)]),
        "{closure_a:?}"
    );
    assert!(
        matches!(both_a[both_a.len() - 3..], [Nil, Seq(1), Seq(1)]),
        "{both_a:?}"
    );
    assert!(
        matches!(blob_a[blob_a.len() - 4..], [Nil, Seq(0), Seq(0), Seq(1)]),
        "{blob_a:?}"
    );
    // Every shape decodes back exactly.
    for ((mp, _), m) in arrays.iter().zip(shapes) {
        assert_eq!(&rmp_serde::from_slice::<Module>(mp).unwrap(), m);
        let json = serde_json::to_string(m).unwrap();
        assert_eq!(&serde_json::from_str::<Module>(&json).unwrap(), m);
    }
    // A pre-v70 array (no closure slot) decodes with both tables empty.
    let (plain_mp, _) = &arrays[0];
    let mut legacy = plain_mp.clone();
    assert_eq!(legacy[0], 0xdc, "array16 header");
    legacy.pop();
    let n = u16::from_be_bytes([legacy[1], legacy[2]]) - 1;
    legacy[1..3].copy_from_slice(&n.to_be_bytes());
    assert_eq!(rmp_serde::from_slice::<Module>(&legacy).unwrap(), plain);
}

/// A minimal "any MessagePack value" decoder (the crate has no `rmpv`
/// dependency): enough to count a positional array's elements, see a nil,
/// and count a nested array's elements.
mod rmpv_like {
    use serde::de::{Deserialize, Deserializer, IgnoredAny, MapAccess, SeqAccess, Visitor};

    #[derive(Debug)]
    pub enum Any {
        Nil,
        Seq(usize),
        Other,
    }

    impl<'de> Deserialize<'de> for Any {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            struct V;
            impl<'de> Visitor<'de> for V {
                type Value = Any;
                fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.write_str("any value")
                }
                fn visit_unit<E>(self) -> Result<Any, E> {
                    Ok(Any::Nil)
                }
                fn visit_none<E>(self) -> Result<Any, E> {
                    Ok(Any::Nil)
                }
                fn visit_bool<E>(self, _: bool) -> Result<Any, E> {
                    Ok(Any::Other)
                }
                fn visit_i64<E>(self, _: i64) -> Result<Any, E> {
                    Ok(Any::Other)
                }
                fn visit_u64<E>(self, _: u64) -> Result<Any, E> {
                    Ok(Any::Other)
                }
                fn visit_f64<E>(self, _: f64) -> Result<Any, E> {
                    Ok(Any::Other)
                }
                fn visit_str<E>(self, _: &str) -> Result<Any, E> {
                    Ok(Any::Other)
                }
                fn visit_bytes<E>(self, _: &[u8]) -> Result<Any, E> {
                    Ok(Any::Other)
                }
                fn visit_seq<A: SeqAccess<'de>>(self, mut a: A) -> Result<Any, A::Error> {
                    let mut n = 0;
                    while a.next_element::<IgnoredAny>()?.is_some() {
                        n += 1;
                    }
                    Ok(Any::Seq(n))
                }
                fn visit_map<A: MapAccess<'de>>(self, mut a: A) -> Result<Any, A::Error> {
                    while a.next_entry::<IgnoredAny, IgnoredAny>()?.is_some() {}
                    Ok(Any::Other)
                }
            }
            d.deserialize_any(V)
        }
    }
}
