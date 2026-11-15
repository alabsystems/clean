// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls, all UNRUN.
use super::*;
use crate::interpret::InterpretOptions;
use crate::value::FuncId;
use std::{cell::Cell, rc::Rc};
mod fixtures;
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
    cleanup_stop: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original type-query stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_stop.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original type-query cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
#[derive(Clone, Copy)]
enum Query {
    Handle,
    Dialect,
    Bool,
    Width,
    Target(u32),
}
#[derive(Debug, PartialEq)]
enum Answer {
    Bool(bool),
    Width(Option<u32>),
}
const ALL: [Query; 5] = [
    Query::Handle,
    Query::Dialect,
    Query::Bool,
    Query::Width,
    Query::Target(32),
];
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(111))
}
fn invoke<O: ExecutionObserver>(
    ty: &Ty,
    query: Query,
    session: &mut ObservedSession<'_, O>,
) -> R<Answer> {
    match query {
        Query::Handle => ty
            .contains_handle_observed(session, site())
            .map(Answer::Bool),
        Query::Dialect => ty
            .contains_dialect_observed(session, site())
            .map(Answer::Bool),
        Query::Bool => ty
            .has_bool_lanes_observed(session, site())
            .map(Answer::Bool),
        Query::Width => ty.bit_width_observed(session, site()).map(Answer::Width),
        Query::Target(bits) => ty
            .bit_width_with_observed(bits, session, site())
            .map(Answer::Width),
    }
}
fn expected(ty: &Ty, query: Query) -> Answer {
    match query {
        Query::Handle => Answer::Bool(ty.contains_handle()),
        Query::Dialect => Answer::Bool(ty.contains_dialect()),
        Query::Bool => Answer::Bool(ty.has_bool_lanes()),
        Query::Width => Answer::Width(ty.bit_width()),
        Query::Target(bits) => Answer::Width(ty.bit_width_with(bits)),
    }
}
fn run(ty: &Ty, query: Query) -> (Answer, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let answer = invoke(ty, query, &mut session).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (answer, observer)
}
fn parity(ty: &Ty, query: Query) -> Answer {
    let (answer, observer) = run(ty, query);
    assert_eq!(answer, expected(ty, query));
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    answer
}
fn fixture() -> Ty {
    Ty::Tuple(vec![
        Ty::Handle(Box::new(HandleTy::new("Nat", "runtime"))),
        Ty::Ref(Box::new(Ty::Tuple(vec![
            Ty::Bool,
            Ty::Dialect(Box::new(DialectTy::new("vector", "lanes", 1))),
        ]))),
        Ty::Tuple(vec![Ty::U32; 17]),
    ])
}
fn vectors(mut ty: Ty, depth: usize, lanes: u32) -> Ty {
    for _ in 0..depth {
        ty = Ty::Vector(Box::new(ty), lanes);
    }
    ty
}
