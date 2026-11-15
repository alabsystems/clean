// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN actual parity and original-session controls.
use super::*;
use crate::interpret::InterpretOptions;
use crate::value::{EnumId, FuncId};
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
            return Err("original discriminant stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(132))
}
fn definition(
    count: usize,
    discriminants: Vec<Option<i128>>,
    repr: Option<EnumTagRepr>,
) -> EnumDef {
    let mut e = EnumDef::new(
        EnumId::new(7),
        "E",
        vec![
            super::super::EnumVariant {
                name: "V".into(),
                fields: vec![],
                field_names: vec![]
            };
            count
        ],
    );
    e.discriminants = discriminants;
    e.repr = repr;
    e
}
fn assignment(e: &EnumDef) -> (Option<Vec<i128>>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = e.effective_discriminants_observed(&mut s, site()).unwrap();
    assert_eq!(out, e.effective_discriminants());
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|x| x.site == site()));
    (out, o)
}
fn canonical(e: &EnumDef) -> (Option<EnumTagRepr>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = e.canonical_tag_repr_observed(&mut s, site()).unwrap();
    assert_eq!(out, e.canonical_tag_repr());
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|x| x.site == site()));
    (out, o)
}
