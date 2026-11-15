// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn implicit_zero_increment_explicit_reset_and_ignored_excess_tail_are_exact() {
    for (n, input, want) in [
        (3, vec![], vec![0, 1, 2]),
        (
            5,
            vec![None, Some(17), None, Some(-8)],
            vec![0, 17, 18, -8, -7],
        ),
        (2, vec![Some(2), Some(3), Some(2)], vec![2, 3]),
    ] {
        let e = definition(n, input, None);
        assert_eq!(assignment(&e).0, Some(want));
        canonical(&e);
    }
}
#[test]
fn duplicate_and_required_implicit_overflow_are_none_but_last_max_and_later_explicit_are_valid() {
    for e in [
        definition(2, vec![Some(0), Some(0)], None),
        definition(2, vec![Some(i128::MAX)], None),
        definition(3, vec![Some(i128::MAX), Some(-1), Some(i128::MAX)], None),
    ] {
        assert!(assignment(&e).0.is_none());
        assert!(canonical(&e).0.is_none());
    }
    for e in [
        definition(1, vec![Some(i128::MAX)], Some(EnumTagRepr::I128)),
        definition(2, vec![Some(i128::MAX), Some(7)], Some(EnumTagRepr::I128)),
    ] {
        assert!(assignment(&e).0.is_some());
        assert_eq!(canonical(&e).0, Some(EnumTagRepr::I128));
    }
}
#[test]
fn inferred_signed_unsigned_thresholds_preserve_original_64_bit_cap() {
    for values in [
        vec![0],
        vec![255],
        vec![256],
        vec![65535],
        vec![65536],
        vec![u32::MAX as i128],
        vec![i128::from(u64::MAX)],
        vec![i128::from(u64::MAX) + 1],
        vec![-1],
        vec![-128, 127],
        vec![-129],
        vec![i128::from(i64::MIN), 0],
        vec![i128::MIN],
    ] {
        let e = definition(values.len(), values.into_iter().map(Some).collect(), None);
        canonical(&e);
    }
    assert_eq!(
        canonical(&definition(1, vec![Some(i128::MAX)], None)).0,
        None
    );
}
#[test]
fn all_ten_explicit_hints_and_fixed_scalar_fit_boundaries_match_original() {
    let hints = [
        EnumTagRepr::U8,
        EnumTagRepr::U16,
        EnumTagRepr::U32,
        EnumTagRepr::U64,
        EnumTagRepr::I8,
        EnumTagRepr::I16,
        EnumTagRepr::I32,
        EnumTagRepr::I64,
        EnumTagRepr::U128,
        EnumTagRepr::I128,
    ];
    for hint in hints {
        for value in [
            i128::MIN,
            i128::from(i64::MIN),
            -129,
            -128,
            -1,
            0,
            127,
            128,
            255,
            256,
            i128::from(u64::MAX),
            i128::MAX,
        ] {
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                fits(
                    hint,
                    value,
                    &mut Work {
                        session: &mut s,
                        site: site()
                    }
                )
                .unwrap(),
                hint.fits(value)
            );
            canonical(&definition(1, vec![Some(value)], Some(hint)));
        }
    }
}
#[test]
fn empty_assignment_is_some_empty_but_canonical_empty_is_none_even_with_hint() {
    let e = definition(0, vec![Some(i128::MAX)], Some(EnumTagRepr::I128));
    assert_eq!(assignment(&e).0, Some(vec![]));
    assert_eq!(canonical(&e).0, None);
}
#[test]
fn actual_assignment_copies_all_rows_into_independent_owned_storage() {
    let e = definition(
        100,
        (0..100).map(|i| Some(i128::from(i) * 7)).collect(),
        None,
    );
    let out = assignment(&e).0.unwrap();
    assert_eq!(out.len(), 100);
    assert_ne!(
        out.as_ptr().cast::<u8>(),
        e.discriminants.as_ptr().cast::<u8>()
    );
    assert_eq!(out[99], 693);
}
#[test]
fn variant_names_fields_and_excess_discriminant_tail_remain_original_opaque_payloads() {
    let mut e = definition(4, vec![], None);
    let (_, before) = assignment(&e);
    let (_, repr_before) = canonical(&e);
    for v in &mut e.variants {
        v.name = "λ".repeat(10000);
        v.fields = vec![super::super::super::Ty::Tuple(
            vec![super::super::super::Ty::Error; 1000],
        )];
        v.field_names = vec!["untrusted".repeat(10000)];
    }
    e.discriminants = vec![None; 10000];
    let (_, after) = assignment(&e);
    let (_, repr_after) = canonical(&e);
    assert_eq!(before.events, after.events);
    assert_eq!(repr_before.events, repr_after.events);
}
#[test]
fn inadequate_hints_never_silently_widen_or_reinterpret_signed_values() {
    assert_eq!(
        canonical(&definition(1, vec![Some(-1)], Some(EnumTagRepr::U128))).0,
        None
    );
    assert_eq!(
        canonical(&definition(1, vec![Some(128)], Some(EnumTagRepr::I8))).0,
        None
    );
    assert_eq!(
        canonical(&definition(
            1,
            vec![Some(i128::MAX)],
            Some(EnumTagRepr::U128)
        ))
        .0,
        Some(EnumTagRepr::U128)
    );
}
