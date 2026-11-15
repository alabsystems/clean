// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn predicates_keep_interval_simple_tags_and_missing_rows_exact() {
    let variants = [
        Pred::Interval { lo: -2, hi: 9 },
        Pred::NonZero,
        Pred::NonNull,
        Pred::Top,
        Pred::Bottom,
    ];
    for a in &variants {
        for b in &variants {
            let (a, ta, b, tb) = pred_pair(vec![a.clone()], 0, vec![b.clone()], 0);
            check(&a, &ta, &b, &tb);
        }
    }
    let (a, ta, b, tb) = pred_pair(vec![], 0, vec![], 0);
    unequal(&a, &ta, &b, &tb);
}
#[test]
fn conj_and_disj_match_sets_in_both_directions_without_sorting() {
    for connective in [Pred::Conj as fn(Vec<PredId>) -> Pred, Pred::Disj] {
        let a = vec![
            Pred::Top,
            Pred::NonZero,
            connective(vec![PredId::new(0), PredId::new(1)]),
        ];
        let b = vec![
            Pred::NonZero,
            Pred::Top,
            connective(vec![PredId::new(0), PredId::new(1)]),
        ];
        let (a, ta, b, tb) = pred_pair(a, 2, b, 2);
        equal(&a, &ta, &b, &tb);
        let mut b = b;
        b.predicates[2] = connective(vec![PredId::new(1), PredId::new(1)]);
        unequal(&a, &ta, &b, &tb);
    }
}
#[test]
fn reverse_set_membership_is_required_even_when_all_forward_rows_match() {
    let a = vec![Pred::Top, Pred::Conj(vec![PredId::new(0), PredId::new(0)])];
    let b = vec![
        Pred::Top,
        Pred::Bottom,
        Pred::Conj(vec![PredId::new(0), PredId::new(1)]),
    ];
    let (a, ta, b, tb) = pred_pair(a, 1, b, 2);
    unequal(&a, &ta, &b, &tb);
}
#[test]
fn cyclic_predicate_active_pairs_and_empty_connectives_match_ordinary() {
    let a = vec![Pred::Conj(vec![PredId::new(0)])];
    let b = vec![Pred::Top, Pred::Conj(vec![PredId::new(1)])];
    let (a, ta, b, tb) = pred_pair(a, 0, b, 1);
    equal(&a, &ta, &b, &tb);
    for p in [Pred::Conj(vec![]), Pred::Disj(vec![])] {
        let (a, ta, b, tb) = pred_pair(vec![p.clone()], 0, vec![p], 0);
        equal(&a, &ta, &b, &tb);
    }
}
#[test]
fn finite_sets_keep_full_nested_constant_spelling_float_bits_and_order() {
    let values = vec![
        Constant::Int(-1),
        Constant::U128(u128::MAX),
        Constant::Bool(true),
        Constant::Float(f64::from_bits(0x7ff8000000000001)),
        Constant::Bytes {
            data: vec![0xff, 0, 3],
            utf8: true,
        },
        Constant::Aggregate(vec![Constant::Int(2)]),
        Constant::Array(vec![Constant::Int(3)]),
        Constant::Vector(vec![Constant::Bool(false)]),
        Constant::Sequence(vec![Constant::Int(4)]),
        Constant::Set(vec![Constant::Int(5)]),
        Constant::Record(vec![("λ".into(), Constant::Uninit)]),
        Constant::Closure {
            func: FuncId::new(3),
            captures: vec![Constant::PhantomData],
        },
        Constant::FnDef(FuncId::new(8)),
        Constant::SymbolAddr {
            symbol: "symbol".into(),
            addend: -8,
        },
        Constant::Splat {
            elem: Box::new(Constant::Int(1)),
            len: u64::MAX,
        },
        Constant::PhantomData,
        Constant::Uninit,
    ];
    let (a, ta, b, tb) = pred_pair(
        vec![Pred::FiniteSet(values.clone())],
        0,
        vec![Pred::FiniteSet(values.clone())],
        0,
    );
    equal(&a, &ta, &b, &tb);
    for i in 0..values.len() {
        let mut changed = values.clone();
        changed[i] = Constant::Int(999);
        let mut b = b.clone();
        b.predicates[0] = Pred::FiniteSet(changed);
        unequal(&a, &ta, &b, &tb);
    }
    let (a, ta, b, tb) = pred_pair(
        vec![Pred::FiniteSet(vec![Constant::Float(-0.0)])],
        0,
        vec![Pred::FiniteSet(vec![Constant::Float(0.0)])],
        0,
    );
    unequal(&a, &ta, &b, &tb);
}
#[test]
fn universes_keep_space_and_complete_ordered_raw_member_identity() {
    let (mut a, ta, mut b, tb) = pred_pair(
        vec![Pred::InUniverse(UnivId::new(0), Space::Member)],
        0,
        vec![Pred::InUniverse(UnivId::new(1), Space::Member)],
        0,
    );
    a.universes.push(Universe::Members(vec![
        Constant::Int(2),
        Constant::Int(1),
        Constant::Int(1),
    ]));
    b.universes
        .extend([Universe::IntRange { lo: 0, hi: 1 }, a.universes[0].clone()]);
    equal(&a, &ta, &b, &tb);
    if let Universe::Members(v) = &mut b.universes[1] {
        v.swap(0, 1);
    }
    unequal(&a, &ta, &b, &tb);
    b.universes[1] = a.universes[0].clone();
    b.predicates[0] = Pred::InUniverse(UnivId::new(1), Space::Index);
    unequal(&a, &ta, &b, &tb);
    b.predicates[0] = a.predicates[0].clone();
    b.universes.clear();
    unequal(&a, &ta, &b, &tb);
    a.universes[0] = Universe::IntRange { lo: 7, hi: -2 };
    b.universes.push(a.universes[0].clone());
    equal(&a, &ta, &b, &tb);
}
#[test]
fn retained_conflict_does_not_override_a_true_final_machine_relation() {
    // Direct state control: ordinary top-level gives ty()==true precedence.
    // No claim that a nominal conflict is reachable through today's Pred-only any.
    let m = Module::new("precedence");
    let root = Ty::Bool;
    let mut s = State::new();
    s.conflict = Some(TypeOriginConflict {
        origin: origin("retained"),
        table: "struct",
        left: "left".into(),
        right: "right".into(),
    });
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(options(), &mut observer);
    let mut w = Work {
        session: &mut session,
        site: site(),
    };
    engine::run(&mut s, &m, &root, &m, &root, &mut w).unwrap();
    assert!(s.last);
    assert!(s.conflict.is_some());
    s.scratch(&mut w);
    if s.last {
        s.owned(&mut w);
    }
    w.publication(size_of::<TyEquivalence>()).unwrap();
    assert_state_empty(&s);
}

#[test]
fn nested_constant_metadata_and_universe_range_endpoints_are_not_lost() {
    let samples = vec![
        (
            Constant::Record(vec![("left".into(), Constant::Int(1))]),
            Constant::Record(vec![("right".into(), Constant::Int(1))]),
        ),
        (
            Constant::SymbolAddr {
                symbol: "s".into(),
                addend: 1,
            },
            Constant::SymbolAddr {
                symbol: "s".into(),
                addend: 2,
            },
        ),
        (
            Constant::Bytes {
                data: vec![1],
                utf8: true,
            },
            Constant::Bytes {
                data: vec![1],
                utf8: false,
            },
        ),
        (
            Constant::Splat {
                elem: Box::new(Constant::Int(1)),
                len: 4,
            },
            Constant::Splat {
                elem: Box::new(Constant::Int(1)),
                len: 5,
            },
        ),
        (
            Constant::Closure {
                func: FuncId::new(1),
                captures: vec![],
            },
            Constant::Closure {
                func: FuncId::new(2),
                captures: vec![],
            },
        ),
        (
            Constant::FnDef(FuncId::new(1)),
            Constant::FnDef(FuncId::new(2)),
        ),
        (
            Constant::Float(f64::from_bits(0x7ff8000000000001)),
            Constant::Float(f64::from_bits(0x7ff8000000000002)),
        ),
    ];
    for (ca, cb) in samples {
        let (a, ta, b, tb) = pred_pair(
            vec![Pred::FiniteSet(vec![ca])],
            0,
            vec![Pred::FiniteSet(vec![cb])],
            0,
        );
        unequal(&a, &ta, &b, &tb);
    }
    for changed in [
        Universe::IntRange { lo: 1, hi: 8 },
        Universe::IntRange { lo: 0, hi: 9 },
    ] {
        let (mut a, ta, mut b, tb) = pred_pair(
            vec![Pred::InUniverse(UnivId::new(0), Space::Index)],
            0,
            vec![Pred::InUniverse(UnivId::new(0), Space::Index)],
            0,
        );
        a.universes.push(Universe::IntRange { lo: 0, hi: 8 });
        b.universes.push(changed);
        unequal(&a, &ta, &b, &tb);
    }
}
