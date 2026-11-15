// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_public_callback_refuses_without_publishing_partial_executable_diagnostics() {
    let mut duplicate = compact();
    let anchor = duplicate.spec_modules[0].anchors[0].clone();
    duplicate.spec_modules[0]
        .anchors
        .extend([anchor.clone(), anchor]);
    // The second same-entry fixture exercises deduplication's held duplicate,
    // observed shifts and consuming helper publication, not just target scans.
    for m in [compact(), duplicate] {
        let (_, base) = run(&m);
        for stop in 1..=base.events.len() {
            let mut o = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_spec_executable_links_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original executable stop");
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert!(
                o.events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn first_header_copy_refusal_and_preexisting_stop_prevent_all_actual_input_walks() {
    let m = compact();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_spec_executable_links_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_spec_executable_links_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn original_work_and_copy_caps_cumulate_across_calls_without_fuel_or_owner_reset() {
    let m = compact();
    let (_, base) = run(&m);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_spec_executable_links_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_spec_executable_links_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_spec_executable_links_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn exact_instruction_site_and_zero_fuel_survive_actual_nested_signature_debug() {
    let mut m = fixture();
    m.func_types[0].is_vararg = true;
    m.func_types[0].params = types();
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(15),
        block: BlockId::new(16),
        instruction_index: 700,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        validate_spec_executable_links_observed(&m, &mut s, exact).unwrap(),
        validate_spec_executable_links(&m)
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn actual_full_definition_count_can_stop_interior_even_when_target_is_early() {
    let mut m = fixture();
    for i in 100..1200 {
        let mut f = m.functions[0].clone();
        f.id = FuncId::new(i);
        m.functions.push(f);
    }
    let base = trace(&m);
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
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.errors.is_empty());
    drain(&mut state, &mut w);
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn actual_long_name_comparison_can_stop_before_tail_or_any_owned_diagnostic() {
    let mut m = fixture();
    m.functions[0].name = "λ".repeat(2000) + "A";
    m.spec_modules[0].anchors[0].rust_symbol = "λ".repeat(2000) + "B";
    let base = trace(&m);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.detail.capacity(), 0);
    assert!(state.errors.is_empty());
    assert!(m.functions[0].name.ends_with('A'));
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn actual_wide_signature_debug_stop_retains_prefix_and_drains_all_borrowed_tasks() {
    let mut m = fixture();
    m.func_types[0].params = (0..100)
        .map(|i| Ty::Tuple(vec![Ty::Array(TyId::new(i), i as u64)]))
        .collect();
    m.func_types[0].is_vararg = true;
    let base = trace(&m);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 41
                && e.copy_bytes == 4 * size_of::<super::super::debug::Task<'_>>()
        })
        .nth(100)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.detail.starts_with("projection signature"));
    assert_eq!(state.tasks.capacity(), 0);
    assert!(state.errors.is_empty());
    assert_eq!(m.func_types[0].params.len(), 100);
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
