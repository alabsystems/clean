// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls for actual private scratch ownership and stops.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};

#[derive(Default)]
struct ScratchObserver {
    events: Vec<ExecutionProgress>,
    work: usize,
    cap: Option<usize>,
    retirement_cut: Option<usize>,
    retirements: usize,
    next: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for ScratchObserver {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.next.as_ref().is_some_and(|v| v.replace(false)) {
            return Err("original admission");
        }
        if e.phase == ExecutionPhase::ScratchRetirement {
            self.retirements += 1;
            if self.retirement_cut == Some(self.retirements) {
                return Err("scratch stop");
            }
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("cumulative work");
        }
        Ok(())
    }
}
fn scratch_site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(151))
}
fn retirement_work(o: &ScratchObserver) -> usize {
    o.events
        .iter()
        .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .map(|e| e.work)
        .sum()
}

#[test]
fn copy_vectors_consume_each_scalar_and_zero_sized_slot_under_the_original_site() {
    let mut o = ScratchObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, scratch_site()).unwrap();
    w.retire_copy_vec(vec![u128::MAX; 37]);
    w.retire_copy_vec(vec![(); 41]);
    assert!(w.poll().is_ok());
    drop(w);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.retirements >= 2 * (37 + 41));
    assert!(retirement_work(&o) >= 37 * size_of::<u128>() + 41);
    assert!(o.events.iter().all(|e| e.site == scratch_site()));
}

#[test]
fn nested_rows_continue_through_all_owned_rows_after_an_interior_retirement_stop() {
    let mut o = ScratchObserver {
        retirement_cut: Some(5),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, scratch_site()).unwrap();
    w.retire_rows(vec![
        vec![17u64; 100],
        Vec::with_capacity(100),
        vec![19; 101],
    ]);
    assert!(matches!(
        w.poll(),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "scratch stop");
    drop(s);
    assert!(o.retirements > 400);
    assert!(retirement_work(&o) >= 201 * size_of::<u64>());
    assert!(o.events.iter().all(|e| e.site == scratch_site()));
}

#[test]
fn copy_map_and_set_pops_are_observed_before_each_actual_population_change() {
    let mut o = ScratchObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, scratch_site()).unwrap();
    w.retire_copy_map(BTreeMap::from([(2u32, 4u64), (3, 9), (5, 25)]));
    w.retire_set(BTreeSet::from([2u32, 3, 5]));
    assert!(w.poll().is_ok());
    drop(w);
    drop(s);
    let amounts: Vec<_> = o
        .events
        .iter()
        .filter(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work != 0)
        .map(|e| e.work)
        .collect();
    let map_image = size_of::<Option<(u32, u64)>>();
    assert_eq!(amounts[0], map_image + 4);
    assert_eq!(amounts[2], map_image + 3);
    assert_eq!(amounts[4], map_image + 2);
    assert_eq!(amounts[6], map_image + 1); // final empty probe
    let set_image = size_of::<Option<(u32, ())>>();
    assert!(amounts.windows(7).any(|p| p[0] == set_image + 4
        && p[2] == set_image + 3
        && p[4] == set_image + 2
        && p[6] == set_image + 1));
}

#[test]
fn field_names_and_metadata_are_fully_retired_even_when_the_first_field_stops() {
    let mut o = ScratchObserver {
        retirement_cut: Some(2),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, scratch_site()).unwrap();
    w.retire_fields(vec![
        FieldOffsetShape {
            field: 0,
            name: "λ".repeat(3000),
            ty_shape: TyShape::Unit,
            offset_bits: Some(0),
        },
        FieldOffsetShape {
            field: u32::MAX,
            name: "tail".repeat(2000),
            ty_shape: TyShape::Int {
                signed: false,
                bits: 128,
            },
            offset_bits: None,
        },
    ]);
    assert!(matches!(
        w.poll(),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "scratch stop");
    drop(s);
    assert!(retirement_work(&o) >= 14000);
    assert!(
        o.events
            .iter()
            .any(|e| e.work == 6000 + size_of::<String>() + 1)
    );
    assert!(
        o.events
            .iter()
            .any(|e| e.work == 8000 + size_of::<String>() + 1)
    );
}

#[test]
fn original_admission_cause_survives_complete_scratch_cache_and_metadata_retirement() {
    let next = Rc::new(Cell::new(false));
    let mut o = ScratchObserver {
        next: Some(next.clone()),
        retirement_cut: Some(1),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, scratch_site()).unwrap();
    let value = Arc::new(TyLayoutShape {
        size_bits: 8,
        align_bits: Some(8),
        kind: TyLayoutKind::Scalar(TyShape::Int {
            signed: false,
            bits: 8,
        }),
    });
    let weak = Arc::downgrade(&value);
    w.cache.insert((0, 1), value);
    for i in 0..50 {
        w.inhabitedness.insert(inhabit::Node::Entry(i), false);
        w.open.insert((0, i));
        w.definitions.insert((0, i as u32), i);
        w.spans.insert((i as u64, i as u64 + 1));
    }
    next.set(true);
    assert!(w.poll().is_err());
    w.retire_scratch();
    assert!(weak.upgrade().is_none());
    assert!(w.value.is_none() && w.cache.is_empty() && w.enums.is_empty());
    assert!(
        w.inhabitedness.is_empty()
            && w.open.is_empty()
            && w.definitions.is_empty()
            && w.spans.is_empty()
    );
    assert!(w.poll().is_err());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "original admission");
    drop(s);
    assert!(o.retirements > 400);
}

#[test]
fn scalar_container_retirement_consumes_one_cumulative_original_budget() {
    let baseline = {
        let mut o = ScratchObserver::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work::new(&mut s, scratch_site()).unwrap();
        w.retire_copy_vec(vec![0u64; 200]);
        assert!(w.poll().is_ok());
        drop(w);
        drop(s);
        o.work
    };
    let mut o = ScratchObserver {
        cap: Some(baseline),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, scratch_site()).unwrap();
    w.retire_copy_vec(vec![0u64; 200]);
    assert!(w.poll().is_ok());
    w.retire_copy_vec(vec![0u64; 200]);
    assert!(w.poll().is_err());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "cumulative work");
    drop(s);
    assert!(o.retirements > 800);
}

#[test]
fn failed_chunked_text_construction_retires_the_copied_prefix_under_the_same_cause() {
    // Discover the actual second text-chunk admission; no guessed global
    // callback ordinal and no new owner is introduced on the refused path.
    let text = "λ".repeat(2000);
    let cut = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work::new(&mut s, scratch_site()).unwrap();
        let copied = w.copy_text(&text);
        assert!(copied.is_ok());
        w.retire_text(copied.ok().unwrap());
        drop(w);
        drop(s);
        let chunks: Vec<_> = o
            .events
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                e.phase == ExecutionPhase::Layout && e.work == 1024 && e.copy_bytes == 1024
            })
            .map(|(index, _)| index)
            .collect();
        // The first allocation and first payload copy both cost1024.
        // Refuse the following matching payload event, after the first
        // actual chunk was copied; a reserve is not a copied prefix.
        assert!(chunks.len() >= 3);
        assert_eq!(chunks[1], chunks[0] + 1);
        chunks[2] + 1
    };
    let mut o = Observer {
        stop_at: Some(cut),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, scratch_site()).unwrap();
    assert!(matches!(
        w.copy_text(&text),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "interior");
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work >= 1024 + size_of::<String>())
    );
}

#[test]
fn real_least_fixpoint_scratch_stop_refuses_publication_without_changing_success() {
    let mut m = Module::new("inhabit scratch");
    m.structs
        .push(structure(1, vec![field("never", Ty::Never, Some(0))], 0, 1));
    let root = Ty::Struct(StructId::new(1));
    let expected = m.layout_table().ty_is_uninhabited(&root);
    assert!(expected);
    let mut success = ScratchObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut success);
    let table = LayoutTable::new_observed(&m, &mut s, scratch_site()).unwrap();
    assert_eq!(
        table.ty_is_uninhabited_observed(&root, &mut s, scratch_site()),
        Ok(expected)
    );
    drop(s);
    assert!(retirement_work(&success) > 0);
    let mut stopped = ScratchObserver {
        retirement_cut: Some(5),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut stopped);
    let table = LayoutTable::new_observed(&m, &mut s, scratch_site()).unwrap();
    assert_eq!(
        table.ty_is_uninhabited_observed(&root, &mut s, scratch_site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "scratch stop");
    drop(s);
    assert!(stopped.retirements > 5);
}

#[test]
fn every_real_small_query_retirement_cut_rejects_the_owned_result_without_short_cleanup() {
    let m = Module::new("scalar scratch");
    let count = {
        let mut o = ScratchObserver::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let table = LayoutTable::new_observed(&m, &mut s, scratch_site()).unwrap();
        let shape = table
            .ty_layout_observed(&Ty::U8, &mut s, scratch_site())
            .unwrap()
            .unwrap();
        drop(s);
        // This successful external result is outside private scratch. Its
        // disposal is not counted as a private-query completion receipt.
        drop(shape);
        o.retirements
    };
    assert!(count > 5);
    for cut in 1..=count {
        let mut o = ScratchObserver {
            retirement_cut: Some(cut),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let table = LayoutTable::new_observed(&m, &mut s, scratch_site()).unwrap();
        assert!(matches!(
            table.ty_layout_observed(&Ty::U8, &mut s, scratch_site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().cause, "scratch stop");
        drop(s);
        assert!(o.retirements >= count);
    }
}
