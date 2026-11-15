// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn sort_parser_accepts_exact_original_unbounded_range_and_width_grammar() {
    let mut inputs = vec![
        "Bool".into(),
        "Int".into(),
        "BitVec(1)".into(),
        format!("BitVec({})", u32::MAX),
        "BitVec(0)".into(),
        "BitVec(+1)".into(),
        "BitVec(01)".into(),
        "BitVec(4294967296)".into(),
        " Bool".into(),
        "bool".into(),
        "0..0".into(),
        "-1..0".into(),
        "-10..-2".into(),
        "-2..-10".into(),
        "-0..1".into(),
        "01..2".into(),
        "1..+2".into(),
        "1...2".into(),
        "1..2..3".into(),
        "λ..中".into(),
    ];
    inputs.push("1".repeat(4000) + ".." + &"2".repeat(4000));
    for text in inputs {
        let expected = crate::spec_surface::parse_spec_var_sort(&text)
            .ok()
            .map(|s| match s {
                crate::spec_surface::SpecSort::Bool => sorts::Fixed::Bool,
                crate::spec_surface::SpecSort::Int => sorts::Fixed::Int,
                crate::spec_surface::SpecSort::BitVec(w) => sorts::Fixed::BitVec(w),
            });
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(sorts::parse(&text, &mut work).unwrap(), expected);
    }
}
#[test]
fn all_clause_sort_debug_variants_and_nested_tuple_vec_unicode_match_derived_debug() {
    for sort in [
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(u32::MAX),
        ClauseSort::Float {
            eb: 0,
            sb: u32::MAX,
        },
        ClauseSort::RoundingMode,
        ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(ClauseSort::Int)),
        ClauseSort::Datatype {
            name: "empty".into(),
            constructors: vec![],
        },
        deep_sort(),
    ] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        state
            .sort_text(sorts::Sort::Borrowed(&sort), &mut work)
            .unwrap();
        assert_eq!(state.detail, format!("{sort:?}"));
        assert_eq!(state.format.capacity(), 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn recursive_sort_equality_matches_all_current_tags_full_names_and_last_children() {
    let sorts = vec![
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(0),
        ClauseSort::BitVec(u32::MAX),
        ClauseSort::Float { eb: 8, sb: 24 },
        ClauseSort::RoundingMode,
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
        deep_sort(),
    ];
    for left in &sorts {
        for right in &sorts {
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut work = Work {
                session: &mut s,
                site: site(),
            };
            let mut state = State::default();
            assert_eq!(
                state
                    .equal_sort(sorts::Sort::Borrowed(left), right, &mut work)
                    .unwrap(),
                left == right
            );
            assert_eq!(state.equality.capacity(), 0);
            drain(&mut state, &mut work);
        }
    }
    let mut changed = deep_sort();
    if let ClauseSort::Datatype { constructors, .. } = &mut changed {
        constructors[0].1[0].0.push_str("TAIL");
    }
    let left = deep_sort();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert!(
        !state
            .equal_sort(sorts::Sort::Borrowed(&left), &changed, &mut work)
            .unwrap()
    );
    drain(&mut state, &mut work);
}
#[test]
fn all_eleven_place_debug_spellings_include_exact_value_id_and_extreme_indices() {
    for place in [
        ClausePlace::Param { index: u32::MAX },
        ClausePlace::ResultSlot { index: 0 },
        ClausePlace::MutParamExit { index: 3 },
        ClausePlace::World,
        ClausePlace::Unwind,
        ClausePlace::Value(ValueId::new(u32::MAX)),
        ClausePlace::SpecVar { index: 2 },
        ClausePlace::SpecVarNext { index: 3 },
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::ParamPointeeEntry { index: 4 },
    ] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut out = String::new();
        format::place(place, &mut out, &mut work).unwrap();
        assert_eq!(out, format!("{place:?}"));
        work.retire_text(&mut out);
    }
}
#[test]
fn blank_and_chunked_byte_order_match_original_for_unicode_boundaries_and_long_tails() {
    let values = [
        "".to_owned(),
        "\u{2003}\n\u{3000}".into(),
        "x".into(),
        "λ".repeat(1200) + "A",
        "λ".repeat(1200) + "B",
        "中".repeat(1000),
    ];
    for a in &values {
        for b in &values {
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut work = Work {
                session: &mut s,
                site: site(),
            };
            assert_eq!(work.blank(a).unwrap(), a.trim().is_empty());
            assert_eq!(work.compare(a, b).unwrap(), a.cmp(b));
        }
    }
}
#[test]
fn all_twenty_two_variant_keys_sort_and_dedup_exactly_like_original_full_equality() {
    let mut input = witnesses::all();
    input.reverse();
    input.extend(witnesses::all());
    let mut expected = input.clone();
    normalize_violations(&mut expected);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State {
        errors: input,
        ..State::default()
    };
    state.normalize(&mut work).unwrap();
    assert_eq!(state.errors, expected);
    assert_eq!(state.errors.len(), 22);
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn every_variant_retirement_observes_each_owned_string_byte_length_before_consuming() {
    for value in witnesses::all() {
        let lengths = witnesses::lengths(&value);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        value.retire_observed(&mut s, site()).unwrap();
        let mut positive = o
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work > 0)
            .map(|e| e.work)
            .collect::<Vec<_>>();
        for len in lengths {
            let expected = len + size_of::<String>() + 1;
            let at = positive.iter().position(|work| *work == expected).unwrap();
            positive.remove(at);
        }
        assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
        assert_eq!(o.events.last().unwrap().work, 0);
    }
}
#[test]
fn consuming_retirement_refuses_every_callback_and_cumulates_original_work() {
    for value in witnesses::all() {
        let mut base = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        value.clone().retire_observed(&mut s, site()).unwrap();
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                value.clone().retire_observed(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        }
        let mut o = Observer {
            work_cap: Some(base.work),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        value.clone().retire_observed(&mut s, site()).unwrap();
        assert_eq!(
            value.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
