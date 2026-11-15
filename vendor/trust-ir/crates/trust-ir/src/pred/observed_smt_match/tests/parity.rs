// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_predicate_arms_spaces_and_decimal_extremes_match_original() {
    let universes = vec![
        Universe::IntRange { lo: -9, hi: 17 },
        Universe::Members(vec![
            Constant::Int(-1),
            Constant::Int(9),
            Constant::Bool(false),
            Constant::Bool(true),
        ]),
    ];
    let preds = vec![
        Pred::Top,
        Pred::Bottom,
        Pred::NonZero,
        Pred::NonNull,
        Pred::Interval {
            lo: i128::MIN,
            hi: i128::MAX,
        },
        Pred::FiniteSet(vec![
            Constant::Bool(false),
            Constant::Bool(true),
            Constant::U128(u128::MAX),
        ]),
        Pred::InUniverse(UnivId::new(0), Space::Member),
        Pred::InUniverse(UnivId::new(0), Space::Index),
        Pred::InUniverse(UnivId::new(1), Space::Member),
        Pred::InUniverse(UnivId::new(1), Space::Index),
        Pred::Conj(vec![PredId::new(0), PredId::new(2), PredId::new(4)]),
        Pred::Disj(vec![PredId::new(1), PredId::new(3), PredId::new(5)]),
    ];
    let table = PredTable::new(&preds, &universes);
    for at in 0..preds.len() {
        let id = u32::try_from(at).unwrap();
        let text = table.smtlib_of(PredId::new(id)).unwrap();
        assert!(run(&preds, &universes, id, &text).0);
        assert!(!run(&preds, &universes, id, &(text + " ")).0);
    }
}
#[test]
fn every_nonfloat_constant_carrier_uses_exact_original_display() {
    let values = vec![
        Constant::Int(i128::MIN),
        Constant::U128(u128::MAX),
        Constant::Bool(true),
        Constant::Bytes {
            data: vec![0, 15, 16, 255],
            utf8: true,
        },
        Constant::Aggregate(vec![Constant::Int(3)]),
        Constant::Array(vec![]),
        Constant::Vector(vec![Constant::Bool(false)]),
        Constant::Sequence(vec![]),
        Constant::Set(vec![]),
        Constant::Splat {
            elem: Box::new(Constant::Int(-8)),
            len: u64::MAX,
        },
        Constant::Record(vec![("raw λ\0尾".into(), Constant::PhantomData)]),
        Constant::Closure {
            func: FuncId::new(7),
            captures: vec![Constant::Uninit],
        },
        Constant::FnDef(FuncId::new(9)),
        Constant::SymbolAddr {
            symbol: "raw λ\0尾".into(),
            addend: i64::MIN,
        },
        Constant::PhantomData,
        Constant::Uninit,
    ];
    let preds = vec![
        Pred::FiniteSet(values.clone()),
        Pred::InUniverse(UnivId::new(0), Space::Member),
    ];
    let universes = vec![Universe::Members(values)];
    for id in [0, 1] {
        let text = PredTable::new(&preds, &universes)
            .smtlib_of(PredId::new(id))
            .unwrap();
        assert!(run(&preds, &universes, id, &text).0);
    }
}
#[test]
fn every_single_ascii_mutation_and_all_prefix_suffix_lengths_are_unequal() {
    let preds = vec![Pred::Interval {
        lo: -123456789,
        hi: 987654321,
    }];
    let text = PredTable::new(&preds, &[])
        .smtlib_of(PredId::new(0))
        .unwrap();
    for at in 0..text.len() {
        let mut bad = text.clone().into_bytes();
        bad[at] = b'?';
        assert!(!run(&preds, &[], 0, &String::from_utf8(bad).unwrap()).0);
        assert!(!run(&preds, &[], 0, &text[..at]).0);
    }
    for suffix in [" ", "\0", "λ", "尾"] {
        assert!(!run(&preds, &[], 0, &(text.clone() + suffix)).0);
    }
}
#[test]
fn dangling_predicates_universes_cycles_and_depth_boundary_preserve_none() {
    assert!(!run(&[], &[], u32::MAX, "true").0);
    for pred in [
        Pred::Conj(vec![PredId::new(7)]),
        Pred::InUniverse(UnivId::new(7), Space::Member),
        Pred::InUniverse(UnivId::new(7), Space::Index),
        Pred::Conj(vec![PredId::new(0)]),
    ] {
        assert!(!run(&[pred], &[], 0, &"(and ".repeat(100)).0);
    }
    let mut preds = vec![Pred::Top];
    for id in 0..65 {
        preds.push(Pred::Conj(vec![PredId::new(id)]));
    }
    let table = PredTable::new(&preds, &[]);
    let text = table.smtlib_of(PredId::new(64)).unwrap();
    assert!(run(&preds, &[], 64, &text).0);
    assert!(table.smtlib_of(PredId::new(65)).is_none());
    assert!(!run(&preds, &[], 65, &"(and ".repeat(70)).0);
}
#[test]
fn empty_and_noncanonical_member_rendering_does_not_gain_validity_checks() {
    let universes = vec![
        Universe::Members(vec![]),
        Universe::Members(vec![
            Constant::Bool(true),
            Constant::Int(2),
            Constant::Int(2),
        ]),
    ];
    let preds = vec![
        Pred::FiniteSet(vec![]),
        Pred::Conj(vec![]),
        Pred::Disj(vec![]),
        Pred::InUniverse(UnivId::new(0), Space::Member),
        Pred::InUniverse(UnivId::new(1), Space::Member),
    ];
    for (id, expected) in [
        (0, "(or )"),
        (1, "(and )"),
        (2, "(or )"),
        (3, "(or )"),
        (4, "(or (= self true) (= self 2) (= self 2))"),
    ] {
        assert!(run(&preds, &universes, id, expected).0);
    }
}
#[test]
fn index_cardinality_replays_actual_canonical_members_and_overflow_cases() {
    let cases = vec![
        Universe::IntRange { lo: 3, hi: 2 },
        Universe::IntRange {
            lo: i128::MIN,
            hi: i128::MAX,
        },
        Universe::IntRange {
            lo: i128::MIN,
            hi: i128::MAX - 1,
        },
        Universe::Members(vec![]),
        Universe::Members(vec![Constant::Int(2), Constant::Int(2)]),
        Universe::Members(vec![Constant::Bool(false), Constant::Int(0)]),
        Universe::Members(vec![Constant::PhantomData]),
        Universe::Members((0..4096).map(Constant::Int).collect()),
        Universe::Members((0..4097).map(Constant::Int).collect()),
    ];
    for universe in cases {
        let preds = vec![Pred::InUniverse(UnivId::new(0), Space::Index)];
        let universes = [universe];
        let text = PredTable::new(&preds, &universes).smtlib_of(PredId::new(0));
        match text {
            Some(text) => assert!(run(&preds, &universes, 0, &text).0),
            None => assert!(!run(&preds, &universes, 0, "(and (<= 0 self) (< self 1))").0),
        }
    }
}
#[test]
fn exponential_dag_mismatching_prefix_never_expands_its_tail() {
    let mut preds = vec![Pred::Top];
    for id in 0..64 {
        preds.push(Pred::Conj(vec![PredId::new(id), PredId::new(id)]));
    }
    let (answer, o) = run(&preds, &[], 64, "false");
    assert!(!answer);
    assert!(o.events.len() < 100);
    assert!(o.work < 10_000);
}
#[test]
fn wide_connective_traverses_actual_children_but_mismatch_stops_early() {
    let preds = vec![Pred::Top, Pred::Disj(vec![PredId::new(0); 1024])];
    let text = PredTable::new(&preds, &[])
        .smtlib_of(PredId::new(1))
        .unwrap();
    let (_, full) = run(&preds, &[], 1, &text);
    let (_, short) = run(&preds, &[], 1, "(or false)");
    assert!(full.events.len() > 1024);
    assert!(short.events.len() * 100 < full.events.len());
}
