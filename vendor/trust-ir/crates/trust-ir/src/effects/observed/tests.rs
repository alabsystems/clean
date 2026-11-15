// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN actual canonicality/parity and original-budget controls.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::{FuncId, interpret::InterpretOptions};
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    at: Option<usize>,
    work: usize,
    cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.at == Some(self.events.len()) {
            return Err("original interior");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("cumulative");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(154))
}
#[test]
fn observed_canonicality_matches_every_short_place_order_duplicate_and_empty_spelling() {
    let places = [
        EffectPlace::ParamPointee { index: 0 },
        EffectPlace::ParamPointee { index: u32::MAX },
        EffectPlace::Global(GlobalId::new(0)),
        EffectPlace::Global(GlobalId::new(u32::MAX)),
    ];
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for value in [
        EffectSet::Nothing,
        EffectSet::Everything,
        EffectSet::Places(Vec::new()),
    ] {
        assert_eq!(
            value.is_canonical_observed(&mut s, site()),
            Ok(value.is_canonical())
        );
    }
    for a in places {
        for b in places {
            for c in places {
                for row in [vec![a], vec![a, b], vec![a, b, c]] {
                    let value = EffectSet::Places(row);
                    assert_eq!(
                        value.is_canonical_observed(&mut s, site()),
                        Ok(value.is_canonical())
                    );
                }
            }
        }
    }
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn actual_interior_comparison_and_final_publication_refusals_never_return_a_boolean() {
    let value = EffectSet::Places(
        (0..4000)
            .map(|index| EffectPlace::ParamPointee { index })
            .collect(),
    );
    let trace = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(value.is_canonical_observed(&mut s, site()), Ok(true));
        drop(s);
        o.events
    };
    let comparisons: Vec<_> = trace
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.copy_bytes == size_of::<(EffectPlace, EffectPlace)>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(comparisons.len(), 3999);
    for at in [
        comparisons[0],
        comparisons[1999],
        *comparisons.last().unwrap(),
        trace.len(),
    ] {
        let mut o = Observer {
            at: Some(at),
            ..Default::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            value.is_canonical_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original interior");
    }
}
#[test]
fn repeated_canonicality_uses_the_same_original_cumulative_work_without_fuel_reset() {
    let value = EffectSet::Places(
        (0..100)
            .map(|index| EffectPlace::ParamPointee { index })
            .collect(),
    );
    let cap = {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(value.is_canonical_observed(&mut s, site()), Ok(true));
        drop(s);
        o.work
    };
    let mut o = Observer {
        cap: Some(cap),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(value.is_canonical_observed(&mut s, site()), Ok(true));
    assert_eq!(
        value.is_canonical_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "cumulative");
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
}
#[test]
fn descending_first_pair_short_circuits_the_tail_with_the_exact_false_answer() {
    let value = EffectSet::Places(
        (0..100000)
            .rev()
            .map(|index| EffectPlace::ParamPointee { index })
            .collect(),
    );
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(value.is_canonical_observed(&mut s, site()), Ok(false));
    drop(s);
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation
                && e.copy_bytes == size_of::<(EffectPlace, EffectPlace)>())
            .count(),
        1
    );
    assert!(o.events.len() < 10);
}
