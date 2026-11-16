// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Optional complete DATA handoff for independent owner replay. JSON carries
//! public IR/declaration data; it conveys no acceptance or publication authority.
use super::*;
use std::io::Write;
use std::path::PathBuf;
use trust_ir::Module;

pub(super) fn write(
    label: &str,
    module: &Module,
    environment: &Environment,
    source: &Name,
    checked: &CheckedSourceEquation,
) {
    let Some(root) = std::env::var_os("CLEAN_SCALAR_SOURCE_EQUATION_EXPORT_DIR") else {
        return;
    };
    let root = PathBuf::from(root);
    assert!(root.is_absolute(), "scalar export root must be absolute");
    assert!(label
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'_'));
    assert_eq!(checked.source(), source);
    assert_eq!(
        environment.declaration_verification(source),
        Some(DeclarationVerification::FullKernelCheck)
    );
    let info = environment
        .get_const(source)
        .expect("actual checked source");
    assert_eq!(info.kind, ConstantKind::Definition);
    assert!(info.level_params.is_empty());
    let definition = Declaration::Definition {
        name: source.clone(),
        level_params: info.level_params.clone(),
        type_: info.type_.clone(),
        value: info.value.clone().expect("actual source body"),
        is_reducible: info.is_reducible,
    };
    let data = serde_json::json!({
        "format": "clean-scalar-original-source-data-v1",
        "module": module,
        "source_declaration": definition,
        "theorem": checked.declaration(),
        "source_closure_digest": checked.source_closure_digest(),
        "equation_closure_digest": checked.equation_closure_digest(),
    });
    let bytes = serde_json::to_vec(&data).expect("serialize complete scalar proof data");
    assert!(
        bytes.len() <= 8 * 1024 * 1024,
        "scalar fixture exceeds its byte bound"
    );
    let decoded: serde_json::Value = serde_json::from_slice(&bytes).expect("decode fixture data");
    let decoded_module: Module =
        serde_json::from_value(decoded["module"].clone()).expect("whole IR roundtrip");
    assert_eq!(&decoded_module, module);
    for key in ["source_declaration", "theorem"] {
        let declaration: Declaration =
            serde_json::from_value(decoded[key].clone()).expect("whole declaration roundtrip");
        assert_eq!(
            serde_json::to_value(declaration).expect("serialize declaration"),
            data[key]
        );
    }
    std::fs::create_dir_all(&root).expect("create scalar export root");
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(root.join(format!("{label}.json")))
        .expect("each scalar export must be fresh");
    file.write_all(&bytes).expect("write complete scalar data");
}
