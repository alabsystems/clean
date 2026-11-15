// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn unrecorded_parameters_returns_vararg_and_absent_record_remain_exact() {
    let a = FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::U64], false);
    assert!(run(&a, &a).0);
    for b in [
        FuncTy::unrecorded(vec![], vec![Ty::U64], false),
        FuncTy::unrecorded(vec![Ty::U64], vec![Ty::U64], false),
        FuncTy::unrecorded(vec![Ty::Bool], vec![], false),
        FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::Char], false),
        FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::U64], true),
    ] {
        mismatch(&a, &b);
    }
    let a = fixture();
    let mut b = a.clone();
    b.abi = None;
    mismatch(&a, &b);
}

#[test]
fn all_nine_raw_identity_strings_keep_complete_unicode_nul_and_late_bytes() {
    for index in 0..9 {
        let mut a = fixture();
        let mut b = a.clone();
        let raw = "λ\0\n尾".repeat(800);
        for sig in [&mut a, &mut b] {
            let abi = abi_mut(sig);
            let fields = [
                &mut abi.target.triple,
                &mut abi.target.data_layout,
                &mut abi.target.abi,
                &mut abi.target.cpu,
                &mut abi.target.target_spec,
                &mut abi.frontend.name,
                &mut abi.frontend.revision,
                &mut abi.convention,
                &mut abi.source_abi,
            ];
            *fields.into_iter().nth(index).unwrap() = raw.clone();
        }
        assert!(run(&a, &b).0);
        let abi = abi_mut(&mut b);
        let fields = [
            &mut abi.target.triple,
            &mut abi.target.data_layout,
            &mut abi.target.abi,
            &mut abi.target.cpu,
            &mut abi.target.target_spec,
            &mut abi.frontend.name,
            &mut abi.frontend.revision,
            &mut abi.convention,
            &mut abi.source_abi,
        ];
        let text = fields.into_iter().nth(index).unwrap();
        let end = text.len();
        text.replace_range(end - 3.., "外");
        mismatch(&a, &b);
    }
}

#[test]
fn raw_features_preserve_order_duplicates_empty_strings_and_last_payload() {
    let mut a = fixture();
    abi_mut(&mut a).target.features = vec!["".into(), "z".repeat(2500), "a".into(), "a".into()];
    assert!(run(&a, &a).0);
    let mut b = a.clone();
    abi_mut(&mut b).target.features.swap(0, 1);
    mismatch(&a, &b);
    let mut b = a.clone();
    abi_mut(&mut b).target.features.pop();
    mismatch(&a, &b);
    let mut b = a.clone();
    abi_mut(&mut b).target.features[3] = "b".into();
    mismatch(&a, &b);
}

#[test]
fn every_target_and_callable_header_scalar_is_part_of_raw_equality() {
    let a = fixture();
    let changes: [fn(&mut SignatureAbi); 7] = [
        |x| x.target.pointer_bytes = 0,
        |x| x.target.little_endian = false,
        |x| x.lowered_convention = crate::CallingConv::CUnwind,
        |x| x.can_unwind = true,
        |x| x.variadic = true,
        |x| x.fixed_count += 1,
        |x| x.fixed_count = u32::MAX,
    ];
    for change in changes {
        let mut b = a.clone();
        change(abi_mut(&mut b));
        mismatch(&a, &b);
    }
}

#[test]
fn arguments_result_size_alignment_and_order_are_never_erased() {
    let a = fixture();
    let changes: [fn(&mut SignatureAbi); 6] = [
        |x| {
            x.arguments.pop();
        },
        |x| x.arguments.swap(0, 1),
        |x| x.arguments[0].size = u64::MAX,
        |x| x.arguments[0].align = 0,
        |x| x.result.size = 0,
        |x| x.result.align = 1,
    ];
    for change in changes {
        let mut b = a.clone();
        change(abi_mut(&mut b));
        mismatch(&a, &b);
    }
}

#[test]
fn every_binding_place_offset_extent_and_complete_tail_is_compared() {
    let a = fixture();
    let changes: [fn(&mut AbiBinding); 7] = [
        |x| x.place = AbiBindingPlace::Result(0),
        |x| x.place = AbiBindingPlace::HiddenResult(0),
        |x| x.place = AbiBindingPlace::Parameter(1),
        |x| x.source_offset = 1,
        |x| x.source_bytes = 9,
        |x| x.carrier_offset = 2,
        |x| x.carrier_bytes = 4,
    ];
    for change in changes {
        let mut b = a.clone();
        change(&mut abi_mut(&mut b).result.bindings[0]);
        mismatch(&a, &b);
    }
    let mut a = a;
    let binding = abi_mut(&mut a).result.bindings[0].clone();
    abi_mut(&mut a).result.bindings = vec![binding; 200];
    let mut b = a.clone();
    abi_mut(&mut b).result.bindings[199].carrier_bytes = 0;
    mismatch(&a, &b);
    let mut b = a.clone();
    abi_mut(&mut b).result.bindings.pop();
    mismatch(&a, &b);
}

#[test]
fn all_five_pass_modes_match_derived_identity_and_pair_second_scalar_matters() {
    for a_mode in modes() {
        for b_mode in modes() {
            let mut a = fixture();
            let mut b = a.clone();
            abi_mut(&mut a).result.mode = a_mode.clone();
            abi_mut(&mut b).result.mode = b_mode;
            run(&a, &b);
        }
    }
    let a = fixture();
    let mut b = a.clone();
    if let AbiPassMode::Pair(_, second) = &mut abi_mut(&mut b).arguments[2].mode {
        second.value_bits = 1;
    }
    mismatch(&a, &b);
}

#[test]
fn every_direct_scalar_register_source_and_value_field_is_retained() {
    let a = fixture();
    let changes: [fn(&mut AbiScalar); 5] = [
        |x| x.register.class = AbiRegisterClass::Float,
        |x| x.register.bytes = 16,
        |x| x.source_offset = 1,
        |x| x.source_bytes = 0,
        |x| x.value_bits = 0,
    ];
    for change in changes {
        let mut b = a.clone();
        if let AbiPassMode::Direct(value) = &mut abi_mut(&mut b).arguments[1].mode {
            change(value);
        }
        mismatch(&a, &b);
    }
}

#[test]
fn all_attribute_bits_enums_pointee_extent_and_optional_alignment_remain_distinct() {
    let a = fixture();
    let changes: [fn(&mut AbiAttributes); 12] = [
        |x| x.extension = AbiExtension::Sign,
        |x| x.in_reg = true,
        |x| x.no_alias = true,
        |x| x.nonnull = true,
        |x| x.readonly = true,
        |x| x.no_undef = true,
        |x| x.writable = true,
        |x| x.no_free = true,
        |x| x.capture = AbiCapture::None,
        |x| x.pointee_size = 1,
        |x| x.pointee_align = Some(0),
        |x| x.extension = AbiExtension::Zero,
    ];
    for change in changes {
        let mut b = a.clone();
        if let AbiPassMode::Direct(value) = &mut abi_mut(&mut b).arguments[1].mode {
            change(&mut value.attributes);
        }
        mismatch(&a, &b);
    }
}

#[test]
fn cast_complete_prefix_padding_offset_rest_and_attributes_keep_raw_identity() {
    let a = fixture();
    for index in 0..11 {
        let mut b = a.clone();
        if let AbiPassMode::Cast {
            pad_i32,
            prefix,
            rest_offset,
            rest,
            attributes,
        } = &mut abi_mut(&mut b).arguments[3].mode
        {
            match index {
                0 => *pad_i32 = false,
                1 => prefix.push(AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 1,
                }),
                2 => prefix[0].class = AbiRegisterClass::Integer,
                3 => prefix[0].bytes = 8,
                4 => *rest_offset = None,
                5 => rest.unit.class = AbiRegisterClass::Float,
                6 => rest.total = 0,
                7 => rest.consecutive = true,
                8 => attributes.no_free = true,
                9 => rest.unit.bytes = 32,
                _ => *rest_offset = Some(0),
            }
        }
        mismatch(&a, &b);
    }
}

#[test]
fn indirect_metadata_absence_explicit_claims_stack_and_caller_copy_remain_distinct() {
    let a = fixture();
    for index in 0..5 {
        let mut b = a.clone();
        if let AbiPassMode::Indirect {
            attributes,
            metadata_attributes,
            on_stack,
            caller_copy,
        } = &mut abi_mut(&mut b).arguments[4].mode
        {
            match index {
                0 => attributes.no_alias = true,
                1 => *metadata_attributes = None,
                2 => metadata_attributes.as_mut().unwrap().pointee_align = Some(16),
                3 => *on_stack = false,
                _ => *caller_copy = true,
            }
        }
        mismatch(&a, &b);
    }
}

#[test]
fn full_type_payloads_and_invalid_equal_recorded_abi_do_not_require_encoding_validity() {
    let mut a = fixture();
    a.params[1] = Ty::Tuple(vec![Ty::handle("λ\0".repeat(2000), "rt::raw"); 20]);
    assert!(a.abi.as_ref().unwrap().validate(&a).is_err());
    assert!(run(&a, &a).0);
    let mut b = a.clone();
    b.returns.push(Ty::Char);
    mismatch(&a, &b);
    let mut b = a.clone();
    b.params[1] = Ty::Tuple(vec![Ty::Bool; 20]);
    mismatch(&a, &b);
    let mut b = a.clone();
    abi_mut(&mut b).arguments[0].align = u64::MAX;
    assert!(b.abi.as_ref().unwrap().validate(&b).is_err());
    mismatch(&a, &b);
}
