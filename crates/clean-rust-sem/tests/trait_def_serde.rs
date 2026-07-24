// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::types::{FunctionSignature, ReceiverMode};
use clean_rust_sem::{AssociatedTypeDef, IntType, RustType, TraitDef, TypeParamDef};

#[test]
fn test_trait_def_roundtrip_preserves_method_type_params() {
    let trait_def = TraitDef::with_associated_types(
        "Iterator".to_string(),
        vec![FunctionSignature {
            name: "next".to_string(),
            receiver: ReceiverMode::ByMut,
            params: vec![],
            ret: RustType::Option {
                inner: Box::new(RustType::Int(IntType::I32)),
            },
            is_async: false,
            type_params: vec![TypeParamDef {
                id: 0,
                name: "T".to_string(),
                bounds: vec!["Clone".to_string(), "Default".to_string()],
            }],
        }],
        vec![AssociatedTypeDef::with_default(
            "Item".to_string(),
            vec![],
            RustType::Unit,
        )],
    );

    let json = serde_json::to_string(&trait_def).expect("serialization failed");
    let deserialized: TraitDef = serde_json::from_str(&json).expect("deserialization failed");

    assert_eq!(deserialized.name, "Iterator");
    assert_eq!(deserialized.methods.len(), 1);
    assert_eq!(deserialized.methods[0].type_params.len(), 1);
    assert_eq!(deserialized.methods[0].type_params[0].name, "T");
    assert_eq!(
        deserialized.methods[0].type_params[0].bounds,
        vec!["Clone".to_string(), "Default".to_string()]
    );
    assert_eq!(deserialized.associated_types.len(), 1);
    assert_eq!(deserialized.associated_types[0].name, "Item");
}

#[test]
fn test_trait_def_deserialization_defaults_missing_method_type_params() {
    let json = r#"{
        "name":"Iterator",
        "supertraits":[],
        "methods":[
            {
                "name":"next",
                "receiver":"ByMut",
                "params":[],
                "ret":{"Option":{"inner":{"Int":"I32"}}}
            }
        ],
        "associated_types":[
            {
                "name":"Item",
                "bounds":[],
                "default":"Unit"
            }
        ],
        "default_bodies":{},
        "type_params":[]
    }"#;

    let deserialized: TraitDef = serde_json::from_str(json).expect("deserialization failed");

    assert_eq!(deserialized.name, "Iterator");
    assert_eq!(deserialized.methods.len(), 1);
    assert!(deserialized.methods[0].type_params.is_empty());
    assert_eq!(deserialized.associated_types.len(), 1);
    assert_eq!(deserialized.associated_types[0].name, "Item");
}

#[test]
fn test_trait_def_roundtrip_preserves_static_associated_function_receiver() {
    let trait_def = TraitDef::new(
        "Factory".to_string(),
        vec![FunctionSignature {
            name: "make".to_string(),
            receiver: ReceiverMode::Static,
            params: vec![],
            ret: RustType::Unit,
            is_async: false,
            type_params: vec![],
        }],
    );

    let json = serde_json::to_string(&trait_def).expect("serialization failed");
    let deserialized: TraitDef = serde_json::from_str(&json).expect("deserialization failed");

    assert_eq!(deserialized.methods.len(), 1);
    assert_eq!(deserialized.methods[0].receiver, ReceiverMode::Static);
}
