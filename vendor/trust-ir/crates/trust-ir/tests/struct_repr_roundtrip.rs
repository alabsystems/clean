// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// StructDef.repr (ABI classification) survives every serialization format.

use trust_ir::ty::{FieldDef, StructDef, StructRepr};
use trust_ir::value::StructId;
use trust_ir::{Module, Ty};

// Used only by the feature-gated round-trip tests below (binary/parser/serde).
// In a no-feature `--all-targets` build none of them compile, so the helper is
// dead — allow it precisely in that configuration (its body still references
// its imports, so `unused_imports` does not fire).
#[cfg_attr(
    not(any(feature = "binary", feature = "parser", feature = "serde")),
    allow(dead_code)
)]
fn module_with_reprs() -> Module {
    let mut m = Module::new("repr");
    for (i, repr) in [
        StructRepr::Rust,
        StructRepr::C,
        StructRepr::Transparent,
        StructRepr::Packed(4),
        StructRepr::Packed(1),
    ]
    .into_iter()
    .enumerate()
    {
        let fields = if repr == StructRepr::Transparent {
            vec![FieldDef {
                name: "inner".into(),
                ty: Ty::I64,
                offset: None,
            }]
        } else {
            vec![FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: None,
            }]
        };
        m.add_struct(StructDef {
            id: StructId::new(i as u32),
            name: format!("S{i}"),
            fields,
            size: None,
            align: None,
            repr,
            origin: None,
        });
    }
    m
}

#[test]
fn struct_repr_display() {
    assert_eq!(format!("{}", StructRepr::Rust), "rust");
    assert_eq!(format!("{}", StructRepr::C), "c");
    assert_eq!(format!("{}", StructRepr::Transparent), "transparent");
    assert_eq!(format!("{}", StructRepr::Packed(4)), "packed(4)");
    assert_eq!(StructRepr::default(), StructRepr::Rust);
}

#[cfg(feature = "binary")]
#[test]
fn struct_repr_binary_round_trip() {
    let m = module_with_reprs();
    let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let back = trust_ir::binary::deserialize_module(&bytes).expect("binary round trip");
    let got: Vec<_> = back.structs.iter().map(|s| s.repr).collect();
    let want: Vec<_> = m.structs.iter().map(|s| s.repr).collect();
    assert_eq!(got, want);
}

#[cfg(feature = "parser")]
#[test]
fn struct_repr_text_round_trip() {
    let m = module_with_reprs();
    let text = format!("{m}");
    assert!(text.contains("repr=c"), "text: {text}");
    assert!(text.contains("repr=transparent"));
    assert!(text.contains("repr=packed(4)"));
    // The default Rust repr is NOT emitted (keeps existing struct text stable).
    assert!(
        !text.contains("repr=rust"),
        "default repr must not be emitted"
    );
    // Roadmap WS4.2: field names/offsets are not carried by text, so the dump
    // is `#lossy`-marked and refused; the repr is checked on the loss-free
    // projection (fields reduced to their types).
    if !trust_ir::text_loss::text_losses(&m).is_empty() {
        assert!(trust_ir::parser::parse_module(&text).is_err());
    }
    let mut carried = m.clone();
    for sd in &mut carried.structs {
        for field in &mut sd.fields {
            field.name.clear();
            field.offset = None;
        }
    }
    let reparsed = trust_ir::parser::parse_module(&format!("{carried}")).expect("text round trip");
    let got: Vec<_> = reparsed.structs.iter().map(|s| s.repr).collect();
    let want: Vec<_> = m.structs.iter().map(|s| s.repr).collect();
    assert_eq!(got, want);
}

#[cfg(feature = "serde")]
#[test]
fn struct_repr_serde_round_trip() {
    let m = module_with_reprs();
    let json = serde_json::to_string(&m).expect("json");
    let back: Module = serde_json::from_str(&json).expect("json back");
    assert_eq!(
        back.structs.iter().map(|s| s.repr).collect::<Vec<_>>(),
        m.structs.iter().map(|s| s.repr).collect::<Vec<_>>()
    );
}
