// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: exact derived equality is the complete ordinary oracle.
use super::*;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::value::{BlockId, FuncId, ValueId};
use std::{cell::Cell, rc::Rc};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original equality stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(e.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(170))
}
fn sort(left: &ClauseSort, right: &ClauseSort) -> (bool, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = left
        .structurally_eq_observed(right, &mut s, site())
        .unwrap();
    assert_eq!(result, left == right);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (result, o)
}
fn formula(left: &ProofFormula, right: &ProofFormula) -> (bool, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = left
        .structurally_eq_observed(right, &mut s, site())
        .unwrap();
    assert_eq!(result, left == right);
    assert!(s.first_refusal().is_none());
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (result, o)
}
fn sorts() -> Vec<ClauseSort> {
    vec![
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(u32::MAX),
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
        ClauseSort::Float { eb: 8, sb: 24 },
        ClauseSort::RoundingMode,
        ClauseSort::Datatype {
            name: "D".into(),
            constructors: vec![("C".into(), vec![("f".into(), ClauseSort::Bool)])],
        },
    ]
}
fn places() -> Vec<ClausePlace> {
    vec![
        ClausePlace::Param { index: u32::MAX },
        ClausePlace::ResultSlot { index: u32::MAX },
        ClausePlace::MutParamExit { index: u32::MAX },
        ClausePlace::World,
        ClausePlace::Unwind,
        ClausePlace::Value(ValueId::new(u32::MAX)),
        ClausePlace::SpecVar { index: u32::MAX },
        ClausePlace::SpecVarNext { index: u32::MAX },
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::ParamPointeeEntry { index: u32::MAX },
    ]
}
fn sample() -> ProofFormula {
    let mut f = ProofFormula::new("opaque-schema", "opaque-payload");
    f.smtlib = Some("rendering".into());
    f.sort = Some("Bool".into());
    f.bindings = vec![
        (
            "x".into(),
            ClauseBinding {
                sort: sorts().pop().unwrap(),
                place: ClausePlace::Param { index: 0 },
            },
        ),
        (
            "x".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(0),
                place: ClausePlace::World,
            },
        ),
    ];
    f
}
fn raw_trace(left: &ClauseSort, right: &ClauseSort) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(state.sorts(left, right, &mut w).unwrap(), left == right);
    state.retire(&mut w);
    assert_eq!(state.tasks.capacity(), 0);
    o
}
