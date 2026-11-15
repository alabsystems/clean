// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_resolver_callback_refuses_instead_of_returning_resolved_or_semantic_error() {
    let m = fixture();
    for place in [
        ClausePlace::Param { index: 0 },
        ClausePlace::MutParamExit { index: 0 },
        ClausePlace::Value(ValueId::new(1)),
    ] {
        let base = run(&m, FuncId::new(7), &place);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert!(matches!(
                resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(o.events.len(), stop);
        }
    }
}
#[test]
fn actual_unique_candidate_scan_can_stop_interior_after_an_early_matching_function() {
    let mut m = fixture();
    for id in 100..1200 {
        let mut f = m.functions[0].clone();
        f.id = FuncId::new(id);
        m.functions.push(f);
    }
    let place = ClausePlace::Param { index: 0 };
    let base = run(&m, FuncId::new(7), &place);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<Option<&Function>>()
        })
        .nth(200)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    assert_eq!(o.events.len(), stop);
}
#[test]
fn original_work_and_copy_limits_cumulate_and_sticky_stop_prevents_reentry() {
    let m = fixture();
    let place = ClausePlace::Param { index: 0 };
    let base = run(&m, FuncId::new(7), &place);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, site())
                .unwrap()
                .is_ok()
        );
        assert!(matches!(
            resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        let first = s.first_refusal().unwrap().progress;
        assert!(matches!(
            resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn first_header_refusal_and_exact_instruction_coordinate_preserve_zero_fuel() {
    let m = fixture();
    let place = ClausePlace::Param { index: 0 };
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(o.events.len(), 1);
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(7),
        block: BlockId::new(8),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, exact)
        .unwrap()
        .unwrap();
    clause_sort_admits_observed(&ClauseSort::Int, &Ty::U8, None, &mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn every_sort_table_callback_refuses_instead_of_true_or_false() {
    for sort in [
        ClauseSort::Int,
        ClauseSort::Bool,
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Int)),
    ] {
        let (_, base) = admit(&sort, &Ty::U8, None);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                clause_sort_admits_observed(&sort, &Ty::U8, None, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(o.events.len(), stop);
        }
    }
}
#[test]
fn refused_borrowed_result_publication_exposes_neither_type_nor_named_semantic_error() {
    let m = fixture();
    for place in [
        ClausePlace::Param { index: 0 },
        ClausePlace::Param { index: u32::MAX },
    ] {
        let base = run(&m, FuncId::new(7), &place);
        let mut o = Observer {
            stop: Some(base.events.len()),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            resolve_clause_place_borrowed_observed(&m, FuncId::new(7), &place, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        assert_eq!(o.events.len(), base.events.len());
    }
}
