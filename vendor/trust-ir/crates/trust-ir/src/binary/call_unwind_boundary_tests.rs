// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{Block, Function, InstrNode};

fn module(indirect: bool, cannot: bool) -> Module {
    let mut m = Module::new("call_boundary_codec_control");
    let sig = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId(0), "call_boundary", sig, BlockId(0));
    let mut block = Block::new(BlockId(0));
    let inst = match (indirect, cannot) {
        (false, false) => Inst::Call {
            callee: FuncId(0),
            args: vec![],
        },
        (false, true) => Inst::CallCannotUnwind {
            callee: FuncId(0),
            args: vec![],
        },
        (true, false) => Inst::CallIndirect {
            callee: ValueId(0),
            sig,
            args: vec![],
            calling_conv: CallingConv::C,
        },
        (true, true) => Inst::CallIndirectCannotUnwind {
            callee: ValueId(0),
            sig,
            args: vec![],
            calling_conv: CallingConv::C,
        },
    };
    block.body.push(InstrNode::new(inst));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(block);
    m.functions.push(f);
    m
}

#[test]
fn call_unwind_boundary_tags_and_ordinary_bytes_are_exact() {
    for (indirect, old, new) in [
        (false, vec![18, 0, 0], vec![64, 0, 0]),
        (true, vec![19, 0, 0, 0, 0], vec![65, 0, 0, 0, 0]),
    ] {
        for (cannot, expected) in [(false, old), (true, new)] {
            let m = module(indirect, cannot);
            let encoded = SealedStringPool::by_replay(|pool, bytes| {
                write_inst(bytes, pool, None, &m.functions[0].blocks[0].body[0].inst);
            });
            assert_eq!(encoded, expected);
            let bytes = serialize_module(&m).expect("serialize_module: test fixture");
            assert_eq!(
                &bytes[8..12],
                &(if cannot {
                    CALL_UNWIND_BOUNDARY_FORMAT_VERSION
                } else {
                    BASE_FORMAT_VERSION
                })
                .to_le_bytes()
            );
            assert_eq!(deserialize_module(&bytes).expect("lossless boundary"), m);
        }
    }
}

#[test]
fn call_unwind_boundary_old_header_and_legacy_projection_refuse() {
    for (indirect, tag) in [(false, 64), (true, 65)] {
        let m = module(indirect, true);
        for version in [BASE_FORMAT_VERSION, CALL_UNWIND_BOUNDARY_FORMAT_VERSION - 1] {
            let mut bytes = serialize_module(&m).expect("serialize_module: test fixture");
            bytes[8..12].copy_from_slice(&version.to_le_bytes());
            assert_eq!(
                deserialize_module(&bytes),
                Err(BinaryError::InvalidTag(tag))
            );
        }
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&m, options).err(),
                Some(BinaryProjectionError::CallUnwindBoundaryRequiresV53)
            );
            assert!(ProjectedModuleBinaryPlan::try_new(&module(indirect, false), options).is_ok());
        }
    }
}

#[test]
fn call_unwind_boundary_executable_and_stable_identities_do_not_erase_it() {
    for indirect in [false, true] {
        let ordinary = module(indirect, false);
        let boundary = module(indirect, true);
        assert_ne!(ordinary.stable_digest(), boundary.stable_digest());
        assert_ne!(
            ordinary.executable_content_digest_v1(),
            boundary.executable_content_digest_v1()
        );
        for m in [&ordinary, &boundary] {
            assert_eq!(
                m.stable_digest(),
                deserialize_module(&serialize_module(m).expect("serialize_module: test fixture"))
                    .unwrap()
                    .stable_digest()
            );
            let decoded =
                deserialize_module(&serialize_module(m).expect("serialize_module: test fixture"))
                    .unwrap();
            assert_eq!(
                m.executable_content_digest_v1(),
                decoded.executable_content_digest_v1()
            );
            assert_eq!(
                m.functions[0].blocks[0].body[0].inst,
                decoded.functions[0].blocks[0].body[0].inst
            );
        }
    }
}

// The pre-boundary call schema, retaining the exact old externally tagged
// constructors and fields. Other old opcodes are irrelevant to these payloads:
// serde's unknown-constructor refusal occurs before decoding any fields.
#[cfg(feature = "serde")]
#[derive(Debug, PartialEq, serde::Deserialize)]
enum PreBoundaryCall {
    Call {
        callee: FuncId,
        args: Vec<ValueId>,
    },
    CallIndirect {
        callee: ValueId,
        sig: FuncTyId,
        args: Vec<ValueId>,
        calling_conv: CallingConv,
    },
}

#[cfg(feature = "serde")]
#[test]
fn call_unwind_boundary_pre_boundary_serde_call_readers_refuse_unknown_constructors() {
    for indirect in [false, true] {
        let ordinary = module(indirect, false);
        let boundary = module(indirect, true);
        let old = &ordinary.functions[0].blocks[0].body[0].inst;
        let new = &boundary.functions[0].blocks[0].body[0].inst;
        assert!(
            serde_json::from_slice::<PreBoundaryCall>(&serde_json::to_vec(old).unwrap()).is_ok()
        );
        assert!(rmp_serde::from_slice::<PreBoundaryCall>(&rmp_serde::to_vec(old).unwrap()).is_ok());
        let json = serde_json::from_slice::<PreBoundaryCall>(&serde_json::to_vec(new).unwrap())
            .unwrap_err();
        let msgpack =
            rmp_serde::from_slice::<PreBoundaryCall>(&rmp_serde::to_vec(new).unwrap()).unwrap_err();
        assert!(json.to_string().contains("unknown variant"), "{json}");
        assert!(msgpack.to_string().contains("unknown variant"), "{msgpack}");
    }
}
