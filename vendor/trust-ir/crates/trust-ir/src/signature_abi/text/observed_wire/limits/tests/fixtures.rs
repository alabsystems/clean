// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn minimal() -> SignatureAbi {
    SignatureAbi {
        target: AbiTarget {
            triple: "x".into(),
            data_layout: "e-p:64:64".into(),
            abi: "c".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "identity-only".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "producer".into(),
            revision: "revision".into(),
        },
        convention: "c".into(),
        lowered_convention: crate::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: argument(AbiPassMode::Ignore, vec![]),
    }
}
fn argument(mode: AbiPassMode, bindings: Vec<AbiBinding>) -> AbiArgument {
    AbiArgument {
        size: 16,
        align: 8,
        mode,
        bindings,
    }
}
fn scalar(class: AbiRegisterClass, extension: AbiExtension, capture: AbiCapture) -> AbiScalar {
    AbiScalar {
        register: AbiRegister { class, bytes: 1 },
        source_offset: 0,
        source_bytes: 1,
        value_bits: 8,
        attributes: AbiAttributes {
            extension,
            capture,
            pointee_align: Some(8),
            ..AbiAttributes::default()
        },
    }
}
fn binding(place: AbiBindingPlace) -> AbiBinding {
    AbiBinding {
        place,
        source_offset: 0,
        source_bytes: 1,
        carrier_offset: 0,
        carrier_bytes: 1,
    }
}
pub(super) fn fixture() -> SignatureAbi {
    let mut a = minimal();
    let integer = scalar(
        AbiRegisterClass::Integer,
        AbiExtension::None,
        AbiCapture::Any,
    );
    let float = scalar(
        AbiRegisterClass::Float,
        AbiExtension::Sign,
        AbiCapture::ReadOnly,
    );
    let vector = scalar(
        AbiRegisterClass::Vector,
        AbiExtension::Zero,
        AbiCapture::Address,
    );
    let attrs = AbiAttributes {
        in_reg: true,
        no_alias: true,
        nonnull: true,
        readonly: true,
        no_undef: true,
        writable: true,
        no_free: true,
        capture: AbiCapture::None,
        pointee_size: 42,
        pointee_align: None,
        ..AbiAttributes::default()
    };
    a.arguments = vec![
        argument(
            AbiPassMode::Direct(integer),
            vec![binding(AbiBindingPlace::Parameter(0))],
        ),
        argument(AbiPassMode::Ignore, vec![]),
        argument(
            AbiPassMode::Pair(float, vector),
            vec![binding(AbiBindingPlace::Result(1))],
        ),
        argument(
            AbiPassMode::Cast {
                pad_i32: true,
                prefix: vec![AbiRegister {
                    class: AbiRegisterClass::Vector,
                    bytes: 16,
                }],
                rest_offset: Some(16),
                rest: AbiUniform {
                    unit: AbiRegister {
                        class: AbiRegisterClass::Float,
                        bytes: 4,
                    },
                    total: 16,
                    consecutive: false,
                },
                attributes: attrs.clone(),
            },
            vec![binding(AbiBindingPlace::HiddenResult(2))],
        ),
        argument(
            AbiPassMode::Indirect {
                attributes: attrs.clone(),
                metadata_attributes: Some(attrs.clone()),
                on_stack: true,
                caller_copy: false,
            },
            vec![],
        ),
        argument(
            AbiPassMode::Indirect {
                attributes: attrs,
                metadata_attributes: None,
                on_stack: false,
                caller_copy: true,
            },
            vec![],
        ),
    ];
    a.fixed_count = 6;
    a.target.features = vec!["feature".into(), "λ".into()];
    a
}
