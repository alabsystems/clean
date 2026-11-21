// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

fn declaration(words: &[u64]) -> IRDecl {
    IRDecl {
        name: Name::from_string("wide_literal"),
        params: Vec::new(),
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::Lit(IRLiteral::NatLimbs(words.to_vec())),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    }
}

#[cfg(any(feature = "trust-ir-backend", feature = "runtime-lcnf"))]
#[test]
fn wide_nat_wire_preserves_main_slots_and_refuses_noncanonical_vectors() {
    for words in [vec![], vec![1u64], vec![0, 1], vec![1, 0, 0]] {
        let mut wire = 7u32.to_le_bytes().to_vec();
        wire.extend_from_slice(&(words.len() as u64).to_le_bytes());
        for word in words {
            wire.extend_from_slice(&word.to_le_bytes());
        }
        assert!(bincode::deserialize::<IRLiteral>(&wire).is_err());
    }
    for (value, tag, payload) in [
        (
            IRLiteral::NatBig(u128::MAX),
            6u32,
            u128::MAX.to_le_bytes().to_vec(),
        ),
        (IRLiteral::Float32(1.5), 8, 1.5f32.to_le_bytes().to_vec()),
        (IRLiteral::Float64(1.5), 9, 1.5f64.to_le_bytes().to_vec()),
    ] {
        let mut expected = tag.to_le_bytes().to_vec();
        expected.extend(payload);
        assert_eq!(bincode::serialize(&value).unwrap(), expected);
        assert_eq!(bincode::deserialize::<IRLiteral>(&expected).unwrap(), value);
    }
    let value = IRLiteral::NatLimbs(vec![19, 1, 0, 1]);
    let wire = bincode::serialize(&value).unwrap();
    assert_eq!(&wire[..4], &7u32.to_le_bytes());
    assert_eq!(bincode::deserialize::<IRLiteral>(&wire).unwrap(), value);
    for invalid in ["[]", "[1]", "[0,1]", "[1,0,0]"] {
        let wire = format!(r#"{{"NatLimbs":{invalid}}}"#);
        assert!(serde_json::from_str::<IRLiteral>(&wire).is_err());
    }
    let wire = serde_json::to_string(&value).unwrap();
    assert_eq!(wire, r#"{"NatLimbs":[19,1,0,1]}"#);
    assert_eq!(serde_json::from_str::<IRLiteral>(&wire).unwrap(), value);
}

#[test]
fn wide_nat_direct_ir_refuses_noncanonical_vectors_at_emitter_boundaries() {
    for words in [
        vec![],
        vec![1],
        vec![0, 1],
        vec![1, 0, 0],
        vec![19, 1, 0, 1, 0],
    ] {
        let decls = [declaration(&words)];
        assert!(crate::ir_checker::check_decls(&decls).is_err());
        for check_ir in [true, false] {
            assert!(crate::emit_c::emit_c_with_config(
                &decls,
                crate::emit_c::CEmitConfig {
                    check_ir,
                    ..Default::default()
                }
            )
            .is_err());
            assert!(crate::emit_rust::emit_rust_with_config(
                &decls,
                crate::emit_rust::RustEmitConfig {
                    check_ir,
                    ..Default::default()
                }
            )
            .is_err());
        }
        #[cfg(feature = "trust-ir-backend")]
        assert!(crate::emit_trust_ir::emit_trust_ir_with_config(
            &decls,
            &crate::emit_trust_ir::TrustIrConfig {
                runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
                ..Default::default()
            }
        )
        .is_err());
    }
}

#[test]
fn wide_nat_rust_emits_owned_word_constructor_and_wasm_refuses_objects() {
    let declarations = [declaration(&[0, 0, 1])];
    let rust = crate::emit_rust::emit_rust(&declarations).unwrap();
    assert!(rust.contains("clean_nat_from_limbs(&[0u64, 0u64, 1u64])"));
    assert!(matches!(
        crate::emit_wasm::emit_wasm_binary(&declarations),
        Err(crate::emit_wasm::WasmEmitError::UnsupportedType { .. })
            | Err(crate::emit_wasm::WasmEmitError::UnsupportedLiteral { .. })
    ));
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn wide_nat_valid_c_and_trust_ir_keep_the_existing_limb_fold() {
    use crate::emit_trust_ir::{emit_trust_ir_with_config, RuntimeLowering, TrustIrConfig};
    use std::collections::HashMap;
    use trust_ir::{constant::Constant, inst::Inst};
    for words in [vec![0, 0, 1], vec![19, 1, 0, 1], vec![u64::MAX; 3]] {
        let decls = [declaration(&words)];
        let mut expected = format!(
            "clean_nat_big(UINT64_C({}), UINT64_C({}))",
            words[words.len() - 2],
            words[words.len() - 1]
        );
        for word in words.iter().take(words.len() - 2).rev() {
            expected = format!("clean_nat_limb_step({expected}, UINT64_C({word}))");
        }
        assert!(crate::emit_c::emit_c(&decls).unwrap().contains(&expected));
        let module = emit_trust_ir_with_config(
            &decls,
            &TrustIrConfig {
                runtime_lowering: RuntimeLowering::ExternCalls,
                ..Default::default()
            },
        )
        .unwrap();
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let names = module
            .functions
            .iter()
            .map(|f| (f.id, f.name.as_str()))
            .collect::<HashMap<_, _>>();
        let body = module
            .functions
            .iter()
            .find(|f| f.name == "wide_literal")
            .unwrap();
        let mut scalars = HashMap::new();
        let mut nats = HashMap::new();
        let mut calls = 0;
        let mut returned = None;
        for node in body.instructions() {
            match &node.inst {
                Inst::Const {
                    value: Constant::Int(n),
                    ..
                } => {
                    scalars.insert(node.results[0], *n as u64);
                }
                Inst::Call { callee, args, .. } if names[callee] == "clean_nat_big" => {
                    assert_eq!(args.len(), 2);
                    nats.insert(node.results[0], vec![scalars[&args[0]], scalars[&args[1]]]);
                    calls += 1;
                }
                Inst::Call { callee, args, .. } if names[callee] == "clean_nat_limb_step" => {
                    assert_eq!(args.len(), 2);
                    let mut value = nats[&args[0]].clone();
                    value.insert(0, scalars[&args[1]]);
                    nats.insert(node.results[0], value);
                    calls += 1;
                }
                Inst::Return { values } => {
                    assert_eq!(values.len(), 1);
                    returned = Some(nats[&values[0]].clone());
                }
                _ => {}
            }
        }
        assert_eq!(returned, Some(words.clone()));
        assert_eq!(calls, words.len() - 1);
    }
}
