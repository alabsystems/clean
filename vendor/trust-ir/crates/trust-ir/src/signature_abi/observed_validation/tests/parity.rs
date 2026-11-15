// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn full_actual_ignore_direct_pair_cast_indirect_hidden_fixture_and_empty_signature_match() {
    let (a, s) = full();
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
    let (a, s) = minimal();
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
}
#[test]
fn every_identity_feature_sort_uniqueness_pointer_and_variadic_census_refusal_is_exact() {
    let (base, s) = minimal();
    for field in 0..8 {
        let mut a = base.clone();
        match field {
            0 => a.target.triple.clear(),
            1 => a.target.data_layout.clear(),
            2 => a.target.cpu.clear(),
            3 => a.target.target_spec.clear(),
            4 => a.frontend.name.clear(),
            5 => a.frontend.revision.clear(),
            6 => a.convention.clear(),
            _ => a.source_abi.clear(),
        };
        assert_eq!(
            run(&a, Request::Validate(&s)).0,
            Err("signature ABI identity is incomplete".into())
        );
    }
    for features in [vec!["a", ""], vec!["b", "a"], vec!["a", "a"]] {
        let mut a = base.clone();
        a.target.features = features.into_iter().map(str::to_owned).collect();
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
    for width in [0, 1, 3, 32, 255] {
        let mut a = base.clone();
        a.target.pointer_bytes = width;
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
    let mut a = base.clone();
    a.variadic = true;
    assert!(run(&a, Request::Validate(&s)).0.is_err());
    let mut a = base;
    a.fixed_count = 1;
    assert!(run(&a, Request::Validate(&s)).0.is_err());
}
#[test]
fn full_unicode_and_long_same_prefix_feature_lexical_order_is_not_hash_or_length_identity() {
    let (mut a, s) = minimal();
    let prefix = "λ🦀".repeat(1025);
    a.target.features = vec![format!("{prefix}a"), format!("{prefix}尾")];
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
    a.target.features.swap(0, 1);
    assert!(run(&a, Request::Validate(&s)).0.is_err());
}
#[test]
fn source_alignment_ignore_binding_storage_overflow_overlap_and_prefix_order_match() {
    let (base, s) = direct();
    for mode in 0..7 {
        let mut a = base.clone();
        match mode {
            0 => a.arguments[0].align = 0,
            1 => a.arguments[0].mode = AbiPassMode::Ignore,
            2 => a.arguments[0].bindings.clear(),
            3 => a.arguments[0].size = 0,
            4 => a.arguments[0].bindings[0].source_offset = u64::MAX,
            5 => a.arguments[0].bindings[0].source_bytes = 0,
            _ => {
                let b = a.arguments[0].bindings[0].clone();
                a.arguments[0].bindings.push(b)
            }
        }
        let out = run(&a, Request::Validate(&s)).0.unwrap_err();
        assert!(out.starts_with("source argument 0: "));
    }
}
#[test]
fn every_scalar_register_bits_live_extent_extension_and_pointee_attribute_guard_matches() {
    let (base, s) = direct();
    for mode in 0..9 {
        let mut a = base.clone();
        let AbiPassMode::Direct(x) = &mut a.arguments[0].mode else {
            panic!()
        };
        match mode {
            0 => x.register.bytes = 0,
            1 => x.register.bytes = 257,
            2 => x.attributes.pointee_align = Some(3),
            3 => x.value_bits = 0,
            4 => x.value_bits = 65,
            5 => x.source_bytes = 0,
            6 => x.source_bytes = 9,
            7 => x.source_offset = u64::MAX,
            _ => {
                x.attributes.extension = AbiExtension::Sign;
                x.register.class = AbiRegisterClass::Float
            }
        }
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
}
#[test]
fn pair_overlap_and_exact_live_lane_coverage_keep_actual_first_error() {
    let (base, s) = full();
    for mode in 0..3 {
        let mut a = base.clone();
        match mode {
            0 => {
                let AbiPassMode::Pair(_, b) = &mut a.arguments[2].mode else {
                    panic!()
                };
                b.source_offset = 0
            }
            1 => a.arguments[2].bindings[1].carrier_bytes = 7,
            _ => a.arguments[2].bindings[0].source_bytes = 7,
        };
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
}
#[test]
fn cast_prefix_rest_partial_integer_and_each_extent_refusal_match_full_ordinary_method() {
    let (base, s) = full();
    for mode in 0..7 {
        let mut a = base.clone();
        let AbiPassMode::Cast {
            prefix,
            rest_offset,
            rest,
            attributes,
            ..
        } = &mut a.arguments[3].mode
        else {
            panic!()
        };
        match mode {
            0 => attributes.pointee_align = Some(3),
            1 => rest.unit.bytes = 0,
            2 => {
                prefix.push(AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 8,
                });
                *rest_offset = Some(4)
            }
            3 => *rest_offset = Some(u64::MAX),
            4 => rest.total = 32,
            5 => rest.total = 11,
            _ => a.arguments[3].bindings[0].carrier_bytes = 8,
        };
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
    let mut a = base;
    let AbiPassMode::Cast { rest, .. } = &mut a.arguments[3].mode else {
        panic!()
    };
    rest.unit.class = AbiRegisterClass::Integer;
    rest.total = 11;
    a.arguments[3].bindings[0].source_bytes = 11;
    a.arguments[3].bindings[0].carrier_bytes = 11;
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
}
#[test]
fn unsized_metadata_and_indirect_storage_or_nonptr_transport_are_never_admitted() {
    let (base, s) = full();
    for mode in 0..4 {
        let mut a = base.clone();
        match mode {
            0 => {
                let AbiPassMode::Indirect {
                    metadata_attributes,
                    ..
                } = &mut a.arguments[4].mode
                else {
                    panic!()
                };
                *metadata_attributes = Some(AbiAttributes::default())
            }
            1 => a.arguments[4].bindings[0].source_bytes = 23,
            2 => a.arguments[4].bindings[0].carrier_offset = 1,
            _ => a.arguments[4].bindings[0].carrier_bytes = 7,
        };
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
    let a = base;
    let mut s = s;
    s.params[5] = Ty::U64;
    assert!(run(&a, Request::Validate(&s)).0.is_err());
}
#[test]
fn wrong_binding_roles_ranges_empty_overlap_and_omitted_census_match() {
    let (base, s) = direct();
    for mode in 0..6 {
        let mut a = base.clone();
        match mode {
            0 => a.arguments[0].bindings[0].place = AbiBindingPlace::Result(0),
            1 => a.arguments[0].bindings[0].place = AbiBindingPlace::Parameter(9),
            2 => a.arguments[0].bindings[0].carrier_offset = u64::MAX,
            3 => a.arguments[0].bindings[0].carrier_bytes = 0,
            4 => {
                a.arguments.push(a.arguments[0].clone());
                a.fixed_count = 2
            }
            _ => a.arguments[0].bindings[0].carrier_bytes = 4,
        }
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
    let a = base;
    let mut s = s;
    s.params.push(Ty::U64);
    assert!(run(&a, Request::Validate(&s)).0.is_err());
}
#[test]
fn actual_hidden_result_shape_type_width_and_result_prefix_guards_are_exact() {
    let (base, s) = full();
    for mode in 0..7 {
        let mut a = base.clone();
        let mut s = s.clone();
        match mode {
            0 => a.result.align = 3,
            1 => {
                let AbiPassMode::Indirect { on_stack, .. } = &mut a.result.mode else {
                    panic!()
                };
                *on_stack = true
            }
            2 => s.returns.push(Ty::U64),
            3 => s.params[0] = Ty::U64,
            4 => a.result.bindings[0].place = AbiBindingPlace::HiddenResult(99),
            5 => a.result.bindings[0].carrier_bytes = 7,
            _ => a.result.bindings[0].place = AbiBindingPlace::Parameter(0),
        }
        assert!(run(&a, Request::Validate(&s)).0.is_err());
    }
}
#[test]
fn direct_result_complete_scalar_census_and_nonignored_missing_result_are_exact() {
    let (mut a, mut s) = minimal();
    a.result = AbiArgument {
        size: 8,
        align: 8,
        mode: AbiPassMode::Direct(scalar(8)),
        bindings: vec![binding(AbiBindingPlace::Result(0), 0, 8, 0, 8)],
    };
    s.returns = vec![Ty::U64];
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
    a.result.bindings[0].carrier_bytes = 4;
    assert!(run(&a, Request::Validate(&s)).0.is_err());
}
#[test]
fn disjoint_multiple_source_owners_and_unsorted_argument_bindings_keep_full_scalar_coverage() {
    let (mut a, s) = packed();
    a.arguments.swap(0, 1);
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
    a.arguments[1].bindings[0].carrier_offset = 1;
    assert!(run(&a, Request::Validate(&s)).0.is_err());
}
#[test]
fn actual_nested_vector_width_queries_preserve_checked_overflow_and_scalar_gaps() {
    let (mut a, mut s) = direct();
    a.arguments[0].size = 1;
    a.arguments[0].align = 1;
    a.arguments[0].mode = AbiPassMode::Direct(scalar(1));
    a.arguments[0].bindings[0].source_bytes = 1;
    a.arguments[0].bindings[0].carrier_bytes = 1;
    let mut ty = Ty::U8;
    for _ in 0..32 {
        ty = Ty::Vector(Box::new(ty), 1)
    }
    s.params[0] = ty;
    assert!(run(&a, Request::Validate(&s)).0.is_ok());
    s.params[0] = Ty::Vector(Box::new(s.params[0].clone()), 2);
    assert_eq!(
        run(&a, Request::Validate(&s)).0,
        Err("scalar carrier census omits bytes".into())
    );
}
#[test]
fn actual_wire_limit_failure_is_typed_operational_refusal_and_never_smaller_semantic_success() {
    let (mut a, s) = minimal();
    a.frontend.name = "x".repeat(MAX_ABI_TEXT_BYTES + 1);
    assert!(a.validate(&s).is_err());
    let mut o = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.validate_observed(&s, &mut session, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert!(session.first_refusal().is_none());
}
