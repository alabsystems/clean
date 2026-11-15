// Copyright 2026 Andrew Yates. Apache-2.0.
//! Exact original compiler bytes and the current writer's full v63 projection.
use super::*;

const ORIGINAL: &[u8] = include_bytes!("../../../../lean/semr/fixtures/original-u64-addition.bin");

#[test]
fn original_u64_addition_and_canonical_v63_writer_are_same_module() {
    let (module, original_version) = deserialize_module_with_wire_version(ORIGINAL).unwrap();
    assert_eq!(original_version.get(), 38);
    assert_eq!(serialize_module(&module).unwrap(), ORIGINAL);
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].calling_conv, CallingConv::Rust);
    assert_eq!(module.functions[0].name, "addition");
    assert_eq!(module.functions[0].body_gate, None);
    let mut builder = StringPoolBuilder::new();
    builder.raise_to(MAKE_CLOSURE_FORMAT_VERSION);
    let pool = collect_strings_into(&module, None, builder);
    let mut current = Vec::new();
    write_module_with_pool(&module, None, &pool, &mut current);
    let (recovered, current_version) = deserialize_module_with_wire_version(&current).unwrap();
    assert_eq!(current_version.get(), 63);
    assert_eq!(recovered, module);
    assert_ne!(current, ORIGINAL);
    assert_eq!(
        current,
        include_bytes!("../../../../lean/semr/fixtures/canonical-v63-u64-addition.bin")
    );
    // Bind the kernel's literal byte subjects to the complete retained files.
    // This is data correspondence, never a source/NoUB authority constructor.
    let terms = include_str!("../../../../lean/semr/U64Addition.lean");
    for (name, expected) in [
        ("originalBytes", ORIGINAL),
        ("currentBytes", current.as_slice()),
    ] {
        let marker = format!("def {name} : List Nat := ");
        let line = terms
            .split(&marker)
            .nth(1)
            .expect("unique subject declaration")
            .lines()
            .next()
            .unwrap();
        let bytes: Vec<u8> = serde_json::from_str(line).expect("literal byte list");
        assert_eq!(bytes, expected);
    }
    // This uses every version-gated field of the ONE canonical writer, not a
    // patched header pretending the original producer emitted different bytes.
    if let Some(path) = std::env::var_os("TRUST_IR_SEMR_U64_FIXTURE_OUT") {
        let path = std::path::PathBuf::from(path);
        assert!(!path.exists(), "fresh owned output required");
        std::fs::write(path, current).unwrap();
    }
}
