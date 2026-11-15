// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Descriptor-only fixture shared with consumers that do not build a signature
// or module. The full signature_abi fixture re-exports this same constructor.
use crate::CallingConv;
use crate::signature_abi::*;

fn binding(index: u32, offset: u64, bytes: u64) -> AbiBinding {
    AbiBinding {
        place: AbiBindingPlace::Parameter(index),
        source_offset: offset,
        source_bytes: bytes,
        carrier_offset: 0,
        carrier_bytes: if index == 5 { 8 } else { bytes },
    }
}
/// A scalar of `bytes` bytes. The width is a `u8` so that its bit count,
/// `bytes * 8 <= 2040`, is exact in the `u16` `value_bits` field: the former
/// `(bytes * 8) as u16` over a `u64` could overflow the multiply and truncate.
fn scalar(class: AbiRegisterClass, offset: u64, bytes: u8) -> AbiScalar {
    AbiScalar {
        register: AbiRegister {
            class,
            bytes: u64::from(bytes),
        },
        source_offset: offset,
        source_bytes: u64::from(bytes),
        value_bits: u16::from(bytes) * 8,
        attributes: AbiAttributes::default(),
    }
}
pub fn descriptor() -> SignatureAbi {
    let mut narrow = scalar(AbiRegisterClass::Integer, 0, 1);
    narrow.attributes.extension = AbiExtension::Sign;
    let pointer_attrs = AbiAttributes {
        pointee_size: 24,
        pointee_align: Some(8),
        ..AbiAttributes::default()
    };
    SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-m:o-p:64:64-i64:64-i128:128-n32:64-S128".into(),
            abi: "darwinpcs".into(),
            cpu: "apple-m5".into(),
            features: vec!["+fp-armv8".into(), "+neon".into()],
            target_spec: format!("sha256:{}", "a".repeat(64)),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "trustc".into(),
            revision: "450403669".into(),
        },
        convention: "C".into(),
        lowered_convention: CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 5,
        arguments: vec![
            AbiArgument {
                size: 0,
                align: 1,
                mode: AbiPassMode::Ignore,
                bindings: vec![],
            },
            AbiArgument {
                size: 1,
                align: 1,
                mode: AbiPassMode::Direct(narrow),
                bindings: vec![binding(1, 0, 1)],
            },
            AbiArgument {
                size: 16,
                align: 8,
                mode: AbiPassMode::Pair(
                    scalar(AbiRegisterClass::Integer, 0, 8),
                    scalar(AbiRegisterClass::Float, 8, 8),
                ),
                bindings: vec![binding(2, 0, 8), binding(3, 8, 8)],
            },
            // Over-aligned HFA: only twelve bytes of the sixteen-byte source
            // storage are live in registers. Tail padding is not a fourth lane.
            AbiArgument {
                size: 16,
                align: 16,
                mode: AbiPassMode::Cast {
                    pad_i32: false,
                    prefix: vec![],
                    rest_offset: None,
                    rest: AbiUniform {
                        unit: AbiRegister {
                            class: AbiRegisterClass::Float,
                            bytes: 4,
                        },
                        total: 12,
                        consecutive: true,
                    },
                    attributes: AbiAttributes::default(),
                },
                bindings: vec![binding(4, 0, 12)],
            },
            AbiArgument {
                size: 24,
                align: 8,
                mode: AbiPassMode::Indirect {
                    attributes: pointer_attrs.clone(),
                    metadata_attributes: None,
                    on_stack: false,
                    caller_copy: true,
                },
                bindings: vec![binding(5, 0, 24)],
            },
        ],
        result: AbiArgument {
            size: 24,
            align: 8,
            mode: AbiPassMode::Indirect {
                attributes: pointer_attrs,
                metadata_attributes: None,
                on_stack: false,
                caller_copy: false,
            },
            bindings: vec![AbiBinding {
                place: AbiBindingPlace::HiddenResult(0),
                source_offset: 0,
                source_bytes: 24,
                carrier_offset: 0,
                carrier_bytes: 8,
            }],
        },
    }
}
