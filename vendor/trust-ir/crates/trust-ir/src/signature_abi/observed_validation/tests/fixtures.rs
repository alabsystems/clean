// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn full() -> (SignatureAbi, FuncTy) {
    (
        descriptor::descriptor(),
        FuncTy::unrecorded(
            vec![
                Ty::Ptr,
                Ty::I8,
                Ty::U64,
                Ty::F64,
                Ty::Tuple(vec![Ty::F32, Ty::F32, Ty::F32]),
                Ty::Ptr,
            ],
            vec![],
            false,
        ),
    )
}
pub(super) fn minimal() -> (SignatureAbi, FuncTy) {
    let (mut a, _) = full();
    a.arguments.clear();
    a.fixed_count = 0;
    a.result = AbiArgument {
        size: 0,
        align: 1,
        mode: AbiPassMode::Ignore,
        bindings: vec![],
    };
    (a, FuncTy::unrecorded(vec![], vec![], false))
}
pub(super) fn binding(
    place: AbiBindingPlace,
    source: u64,
    bytes: u64,
    carrier: u64,
    carrier_bytes: u64,
) -> AbiBinding {
    AbiBinding {
        place,
        source_offset: source,
        source_bytes: bytes,
        carrier_offset: carrier,
        carrier_bytes,
    }
}
pub(super) fn scalar(bytes: u64) -> AbiScalar {
    AbiScalar {
        register: AbiRegister {
            class: AbiRegisterClass::Integer,
            bytes,
        },
        source_offset: 0,
        source_bytes: bytes,
        value_bits: u16::try_from(bytes * 8).unwrap(),
        attributes: AbiAttributes::default(),
    }
}
pub(super) fn direct() -> (SignatureAbi, FuncTy) {
    let (mut a, _) = minimal();
    a.arguments.push(AbiArgument {
        size: 8,
        align: 8,
        mode: AbiPassMode::Direct(scalar(8)),
        bindings: vec![binding(AbiBindingPlace::Parameter(0), 0, 8, 0, 8)],
    });
    a.fixed_count = 1;
    (a, FuncTy::unrecorded(vec![Ty::U64], vec![], false))
}
pub(super) fn packed() -> (SignatureAbi, FuncTy) {
    let (mut a, _) = minimal();
    a.fixed_count = 2;
    a.arguments = (0..2)
        .map(|index| {
            let mut s = scalar(1);
            s.attributes.extension = AbiExtension::Sign;
            AbiArgument {
                size: 1,
                align: 1,
                mode: AbiPassMode::Direct(s),
                bindings: vec![binding(AbiBindingPlace::Parameter(0), 0, 1, index, 1)],
            }
        })
        .collect();
    (a, FuncTy::unrecorded(vec![Ty::I16], vec![], false))
}
pub(super) fn target(a: &SignatureAbi) -> TargetInfo {
    TargetInfo {
        triple: a.target.triple.clone(),
        pointer_size: u32::from(a.target.pointer_bytes),
        endianness: if a.target.little_endian {
            Endianness::Little
        } else {
            Endianness::Big
        },
        abi: Some(a.target.abi.clone()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}
pub(super) fn function() -> Function {
    Function::new(
        FuncId::new(6401),
        "caller",
        FuncTyId::new(0),
        BlockId::new(0),
    )
}
pub(super) fn full_function() -> Function {
    let mut f = function();
    f.attrs.params = vec![ParamAttrs::default(); 6];
    f.attrs.params[0].sret = true;
    f.attrs.params[1].ext = ArgExt::SignExt;
    f
}
