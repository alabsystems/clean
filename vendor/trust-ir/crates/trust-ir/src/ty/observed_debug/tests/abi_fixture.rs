// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use crate::signature_abi::*;
pub(super) fn modes() -> Vec<AbiPassMode> {
    let attrs = AbiAttributes {
        extension: AbiExtension::Sign,
        in_reg: true,
        no_alias: true,
        nonnull: false,
        readonly: true,
        no_undef: true,
        writable: false,
        no_free: true,
        capture: AbiCapture::Address,
        pointee_size: u64::MAX,
        pointee_align: Some(3),
    };
    let scalar = AbiScalar {
        register: AbiRegister {
            class: AbiRegisterClass::Float,
            bytes: 0,
        },
        source_offset: u64::MAX,
        source_bytes: 2,
        value_bits: u16::MAX,
        attributes: attrs.clone(),
    };
    vec![
        AbiPassMode::Ignore,
        AbiPassMode::Direct(scalar.clone()),
        AbiPassMode::Pair(scalar.clone(), scalar),
        AbiPassMode::Cast {
            pad_i32: true,
            prefix: vec![
                AbiRegister {
                    class: AbiRegisterClass::Vector,
                    bytes: 3,
                },
                AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: u64::MAX,
                },
            ],
            rest_offset: None,
            rest: AbiUniform {
                unit: AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 2,
                },
                total: 0,
                consecutive: true,
            },
            attributes: attrs.clone(),
        },
        AbiPassMode::Indirect {
            attributes: attrs.clone(),
            metadata_attributes: Some(AbiAttributes {
                extension: AbiExtension::Zero,
                capture: AbiCapture::ReadOnly,
                pointee_align: None,
                ..attrs
            }),
            on_stack: true,
            caller_copy: false,
        },
    ]
}
pub(super) fn abi(mode: AbiPassMode) -> SignatureAbi {
    SignatureAbi {
        target: AbiTarget {
            triple: "bad\n'é".into(),
            data_layout: "data中".into(),
            abi: "abi".into(),
            cpu: "cpu".into(),
            features: vec!["z".into(), "a".into(), "a".into()],
            target_spec: "spec".into(),
            pointer_bytes: 0,
            little_endian: false,
        },
        frontend: AbiFrontend {
            name: "name".into(),
            revision: "rev".into(),
        },
        convention: "bad".into(),
        lowered_convention: crate::CallingConv::RustCold,
        source_abi: "source".into(),
        can_unwind: true,
        variadic: true,
        fixed_count: u32::MAX,
        arguments: vec![AbiArgument {
            size: 0,
            align: 3,
            mode: mode.clone(),
            bindings: vec![
                AbiBinding {
                    place: AbiBindingPlace::Parameter(9),
                    source_offset: u64::MAX,
                    source_bytes: 0,
                    carrier_offset: 3,
                    carrier_bytes: 7,
                },
                AbiBinding {
                    place: AbiBindingPlace::HiddenResult(1),
                    source_offset: 1,
                    source_bytes: 2,
                    carrier_offset: 3,
                    carrier_bytes: 4,
                },
            ],
        }],
        result: AbiArgument {
            size: 7,
            align: 0,
            mode,
            bindings: vec![AbiBinding {
                place: AbiBindingPlace::Result(2),
                source_offset: 1,
                source_bytes: 2,
                carrier_offset: 3,
                carrier_bytes: 4,
            }],
        },
    }
}
