// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_pass_mode_attribute_binding_and_calling_convention_keeps_exact_text() {
    let mut a = fixture();
    for cc in crate::CallingConv::ALL {
        a.lowered_convention = cc;
        let text = run(&a, false).0.unwrap();
        assert_eq!(SignatureAbi::from_canonical_text(&text).unwrap(), a);
    }
}
#[test]
fn all_raw_escapes_unicode_and_unsigned_extremes_match_ordinary_result() {
    let mut a = fixture();
    a.frontend.name = "quote\" slash\\ newline\n\r\t NUL\0 DEL\u{7f} NEXT\u{85} λ🚀".into();
    a.target.pointer_bytes = u8::MAX;
    a.fixed_count = u32::MAX;
    a.arguments[0].size = u64::MAX;
    a.arguments[0].align = u64::MAX;
    a.arguments[0].bindings[0].place = AbiBindingPlace::Parameter(u32::MAX);
    if let AbiPassMode::Direct(v) = &mut a.arguments[0].mode {
        v.value_bits = u16::MAX;
        v.register.bytes = u64::MAX;
        v.source_offset = u64::MAX;
        v.source_bytes = u64::MAX;
    } else {
        panic!("fixture");
    }
    run(&a, false).0.unwrap();
}
#[test]
fn identity_limit_precedes_node_limit_with_the_exact_original_error_string() {
    let mut a = too_many_nodes();
    a.frontend.name = "x".repeat(MAX_ABI_TEXT_BYTES + 1);
    assert_eq!(
        run(&a, false).0,
        Err("ABI identity exceeds wire byte limit".into())
    );
}
#[test]
fn feature_binding_and_cast_prefix_node_limits_keep_exact_original_diagnostics() {
    let mut binding = fixture();
    binding.arguments[0].bindings =
        vec![binding.arguments[0].bindings[0].clone(); MAX_NODES / 7 + 1];
    let mut cast = fixture();
    if let AbiPassMode::Cast { prefix, .. } = &mut cast.arguments[3].mode {
        *prefix = vec![
            AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: 1
            };
            MAX_NODES / 3 + 1
        ];
    } else {
        panic!("fixture");
    }
    for a in [too_many_nodes(), binding, cast] {
        assert_eq!(
            run(&a, false).0,
            Err("ABI record count exceeds wire node limit".into())
        );
    }
}
#[test]
fn actual_canonical_escape_expansion_is_a_byte_diagnostic_not_raw_identity_error() {
    let a = escaped_limit();
    assert!(a.frontend.name.len() < MAX_ABI_TEXT_BYTES);
    assert_eq!(run(&a, false).0, Err("ABI text exceeds byte limit".into()));
}
#[test]
fn complete_canonical_text_equal_to_limit_succeeds_and_one_more_byte_refuses() {
    let mut a = minimal();
    a.frontend.name.clear();
    let fixed = a.to_canonical_text().len();
    a.frontend.name = "x".repeat(MAX_ABI_TEXT_BYTES - fixed);
    let text = run(&a, false).0.unwrap();
    assert_eq!(text.len(), MAX_ABI_TEXT_BYTES);
    a.frontend.name.push('x');
    assert_eq!(run(&a, false).0, Err("ABI text exceeds byte limit".into()));
}
#[test]
fn exact_maximum_node_count_is_accepted_but_next_real_feature_is_not() {
    let mut a = minimal();
    a.target.features = vec![String::new(); MAX_NODES - 26];
    assert!(run(&a, false).0.is_ok());
    a.target.features.push(String::new());
    assert_eq!(
        run(&a, false).0,
        Err("ABI record count exceeds wire node limit".into())
    );
}
#[test]
fn semantic_abi_contradictions_and_empty_identity_are_encoding_data_only() {
    let mut a = minimal();
    a.target.triple.clear();
    a.target.cpu.clear();
    a.fixed_count = u32::MAX;
    a.variadic = true;
    a.arguments.clear();
    assert!(run(&a, false).0.is_ok());
    assert!(
        a.validate(&crate::FuncTy::unrecorded(vec![], vec![], false))
            .is_err()
    );
}
#[test]
fn complete_success_and_limit_diagnostic_outlive_the_borrowed_descriptor() {
    for a in [minimal(), too_many_bytes()] {
        let expected = ordinary(&a);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let result = a
            .canonical_text_encoding_result_observed(&mut s, site())
            .unwrap();
        drop(a);
        assert_eq!(result, expected);
        SignatureAbi::retire_encoding_result_observed(result, &mut s, site()).unwrap();
    }
}
#[test]
fn changed_actual_load_bearing_claim_changes_text_without_any_authority_grant() {
    let a = fixture();
    let before = run(&a, false).0.unwrap();
    let mut b = a.clone();
    b.arguments[0].bindings[0].carrier_offset = 1;
    let after = run(&b, false).0.unwrap();
    assert_ne!(before, after);
    b = a;
    b.target.target_spec.push('!');
    assert_ne!(run(&b, false).0.unwrap(), before);
}

#[test]
fn checked_count_overflow_keeps_ordinary_text_but_original_stop_stays_outer() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Writer::new(&mut s, site()).unwrap();
    let mut bytes = usize::MAX;
    assert_eq!(
        budget::identity_add(&mut bytes, 1, &mut out).unwrap(),
        Some("ABI identity byte count overflows")
    );
    assert_eq!(bytes, usize::MAX);
    let mut nodes = usize::MAX;
    assert_eq!(
        budget::add(&mut nodes, 1, &mut out).unwrap(),
        Some("ABI node count overflows")
    );
    assert_eq!(nodes, usize::MAX);
    drop(out);
    drop(s);
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Writer {
        session: &mut s,
        site: site(),
        text: String::new(),
    };
    assert_eq!(
        budget::identity_add(&mut bytes, 1, &mut out),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(bytes, usize::MAX);
}
