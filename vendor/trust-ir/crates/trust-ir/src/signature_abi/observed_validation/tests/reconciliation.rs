// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn exact_target_absence_triple_width_endian_and_optional_abi_match() {
    let (a, _) = full();
    assert!(run(&a, Request::Target(None)).0.is_err());
    for mode in 0..6 {
        let mut t = target(&a);
        match mode {
            0 => {}
            1 => t.triple.push('x'),
            2 => t.pointer_size = 4,
            3 => t.endianness = Endianness::Big,
            4 => t.abi = Some("other".into()),
            _ => t.abi = None,
        };
        let out = run(&a, Request::Target(Some(&t))).0;
        assert_eq!(out.is_ok(), mode == 0 || mode == 5);
    }
}
#[test]
fn target_long_equal_length_utf8_tail_difference_is_compared_in_actual_chunks() {
    let (mut a, _) = full();
    a.target.triple = "λ🦀".repeat(2000);
    a.target.abi = "abi尾".repeat(2000);
    let mut t = target(&a);
    assert!(run(&a, Request::Target(Some(&t))).0.is_ok());
    t.abi.as_mut().unwrap().pop();
    t.abi.as_mut().unwrap().push('差');
    assert!(run(&a, Request::Target(Some(&t))).0.is_err());
}
#[test]
fn actual_function_empty_legacy_and_full_sret_extension_owners_match() {
    let (a, _) = full();
    assert!(run(&a, Request::Function(&function())).0.is_ok());
    assert!(run(&a, Request::Function(&full_function())).0.is_ok());
}
#[test]
fn convention_or_out_of_range_nonempty_legacy_slot_is_refused_in_original_order() {
    let (a, _) = full();
    let mut f = full_function();
    f.calling_conv = CallingConv::Fast;
    assert!(run(&a, Request::Function(&f)).0.is_err());
    f.calling_conv = a.lowered_convention;
    f.attrs.params.resize(20, ParamAttrs::default());
    f.attrs.params[19].nonnull = true;
    assert_eq!(
        run(&a, Request::Function(&f)).0,
        Err("function attribute 19 has no typed ABI binding".into())
    );
}
#[test]
fn whole_carrier_legacy_attributes_must_agree_with_every_source_owner() {
    let (mut a, s) = packed();
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
    let mut f = function();
    f.attrs.params.push(ParamAttrs {
        ext: ArgExt::SignExt,
        ..ParamAttrs::default()
    });
    assert!(run(&a, Request::Function(&f)).0.is_ok());
    let AbiPassMode::Direct(second) = &mut a.arguments[1].mode else {
        panic!()
    };
    second.attributes.extension = AbiExtension::Zero;
    assert!(run(&a, Request::Function(&f)).0.is_err());
}
#[test]
fn every_legacy_scalar_attribute_and_pass_mode_refinement_keeps_actual_first_error() {
    let (a, _) = direct();
    for mode in 0..11 {
        let mut f = function();
        let mut attr = ParamAttrs::default();
        match mode {
            0 => attr.byval = true,
            1 => attr.sret = true,
            2 => attr.ext = ArgExt::ZeroExt,
            3 => attr.nonnull = true,
            4 => attr.noalias = true,
            5 => attr.readonly = true,
            6 => attr.align = Some(8),
            7 => attr.dereferenceable = Some(1),
            8 => attr.pass = Some(PassMode::Ignore),
            9 => attr.pass = Some(PassMode::Pair),
            _ => {
                attr.pass = Some(PassMode::Cast {
                    pieces: vec![Ty::U64],
                })
            }
        };
        f.attrs.params.push(attr);
        assert!(run(&a, Request::Function(&f)).0.is_err());
    }
    let mut f = function();
    f.attrs.params.push(ParamAttrs {
        pass: Some(PassMode::Direct),
        ..ParamAttrs::default()
    });
    assert!(run(&a, Request::Function(&f)).0.is_ok());
}
#[test]
fn return_legacy_attributes_require_one_actual_return_binding_and_exact_source_owner() {
    let (mut a, _) = minimal();
    let mut f = function();
    f.attrs.ret.nonnull = true;
    assert!(run(&a, Request::Function(&f)).0.is_err());
    a.result = AbiArgument {
        size: 8,
        align: 8,
        mode: AbiPassMode::Direct(scalar(8)),
        bindings: vec![binding(AbiBindingPlace::Result(0), 0, 8, 0, 8)],
    };
    assert!(run(&a, Request::Function(&f)).0.is_err());
    let AbiPassMode::Direct(x) = &mut a.result.mode else {
        panic!()
    };
    x.attributes.nonnull = true;
    assert!(run(&a, Request::Function(&f)).0.is_ok());
    a.result.bindings[0].place = AbiBindingPlace::HiddenResult(0);
    assert!(run(&a, Request::Function(&f)).0.is_err());
}
