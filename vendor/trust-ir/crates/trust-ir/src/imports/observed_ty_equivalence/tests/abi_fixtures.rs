// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn scalar() -> AbiScalar {
    AbiScalar {
        register: AbiRegister {
            class: AbiRegisterClass::Integer,
            bytes: 8,
        },
        source_offset: 0,
        source_bytes: 8,
        value_bits: 64,
        attributes: AbiAttributes::default(),
    }
}
pub(super) fn argument(mode: AbiPassMode) -> AbiArgument {
    AbiArgument {
        size: 8,
        align: 8,
        mode,
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::Parameter(0),
            source_offset: 0,
            source_bytes: 8,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    }
}
pub(super) fn modes() -> Vec<AbiPassMode> {
    vec![
        AbiPassMode::Ignore,
        AbiPassMode::Direct(scalar()),
        AbiPassMode::Pair(scalar(), scalar()),
        AbiPassMode::Cast {
            pad_i32: true,
            prefix: vec![AbiRegister {
                class: AbiRegisterClass::Float,
                bytes: 4,
            }],
            rest_offset: Some(8),
            rest: AbiUniform {
                unit: AbiRegister {
                    class: AbiRegisterClass::Vector,
                    bytes: 16,
                },
                total: 32,
                consecutive: false,
            },
            attributes: AbiAttributes::default(),
        },
        AbiPassMode::Indirect {
            attributes: AbiAttributes::default(),
            metadata_attributes: Some(AbiAttributes::default()),
            on_stack: true,
            caller_copy: false,
        },
    ]
}
pub(super) fn fixture() -> FuncTy {
    let mut sig = FuncTy::unrecorded(
        vec![
            Ty::Bool,
            Ty::Tuple(vec![Ty::U64, Ty::PtrMut(Box::new(Ty::Char))]),
        ],
        vec![Ty::Bool],
        true,
    );
    sig.abi = Some(SignatureAbi {
        target: AbiTarget {
            triple: "raw-target".into(),
            data_layout: "e-p:64:64".into(),
            abi: "raw-abi".into(),
            cpu: "raw-cpu".into(),
            features: vec!["z".into(), "a".into(), "a".into()],
            target_spec: "raw-spec".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "raw-frontend".into(),
            revision: "raw-revision".into(),
        },
        convention: "raw-convention".into(),
        lowered_convention: crate::CallingConv::C,
        source_abi: "raw-source".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 999,
        arguments: modes().into_iter().map(argument).collect(),
        result: argument(AbiPassMode::Ignore),
    });
    sig
}
