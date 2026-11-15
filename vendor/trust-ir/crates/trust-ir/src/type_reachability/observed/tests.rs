// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual graph, queries, original stops and owned retirement.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::{
    ClosureTy, ClosureTyId, DialectTy, EnumDef, EnumId, EnumVariant, FieldDef, FuncTy, FuncTyId,
    PredId, RecordDef, RecordId, SetRepr, StructDef, StructId, StructRepr, TyId,
};
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod queries;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    total_work: Rc<Cell<usize>>,
    total_copy: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original nominal graph stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        let work = self
            .total_work
            .get()
            .checked_add(e.work)
            .ok_or("work overflow")?;
        let copy = self
            .total_copy
            .get()
            .checked_add(e.copy_bytes)
            .ok_or("copy overflow")?;
        self.total_work.set(work);
        self.total_copy.set(copy);
        if self.work_cap.is_some_and(|n| work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| copy > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(613))
}
fn array(id: u32) -> Ty {
    Ty::Array(TyId::new(id), 0)
}
fn dialect() -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("ns", "name", 1)))
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn field(ty: Ty) -> FieldDef {
    FieldDef {
        name: "raw λ\0field".into(),
        ty,
        offset: None,
    }
}
fn structure(id: u32, ty: Ty) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: "S".into(),
        fields: vec![field(ty)],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn enumeration(id: u32, ty: Ty) -> EnumDef {
    EnumDef::new(
        EnumId::new(id),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![ty],
            field_names: vec![],
        }],
    )
}
fn record(id: u32, ty: Ty) -> RecordDef {
    RecordDef {
        id: RecordId::new(id),
        name: "R".into(),
        fields: vec![field(ty)],
    }
}
fn fixture() -> Module {
    let mut m = Module::new("actual graph");
    m.types = vec![
        Ty::Tuple(vec![array(1), dialect()]),
        array(0),
        handle(),
        Ty::Func(FuncTyId::new(0)),
        array(5),
        array(4),
    ];
    m.func_types = vec![
        FuncTy::unrecorded(vec![array(0)], vec![array(2)], false),
        FuncTy::unrecorded(vec![], vec![], false),
    ];
    m.structs = vec![structure(70, array(0)), structure(70, array(2))];
    m.enums = vec![enumeration(90, Ty::Struct(StructId::new(70)))];
    m.records = vec![record(100, Ty::Enum(EnumId::new(90)))];
    m.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Record(RecordId::new(100))],
    }];
    m
}
fn state(m: &Module) -> State<'_> {
    State {
        summary: ObservedNominalTypeReachability {
            _module: m,
            tables: Tables::default(),
            reachable: [vec![], vec![], vec![]],
        },
        heads: vec![],
        edges: vec![],
        pending: [vec![], vec![], vec![]],
        inline: Inline::default(),
    }
}
fn retired(state: &State<'_>) -> bool {
    state.heads.capacity() == 0
        && state.edges.capacity() == 0
        && state.pending.iter().all(|v| v.capacity() == 0)
        && state.summary.tables.structs.capacity() == 0
        && state.summary.tables.enums.capacity() == 0
        && state.summary.tables.records.capacity() == 0
        && state.summary.reachable.iter().all(|v| v.capacity() == 0)
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_builder(work);
    state.summary.retire(work);
}
fn query<O: ExecutionObserver>(
    summary: &ObservedNominalTypeReachability<'_>,
    axis: NominalAxis,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
) -> R<bool> {
    match axis {
        NominalAxis::Dialect => summary.contains_dialect_observed(ty, session, site()),
        NominalAxis::Handle => summary.contains_handle_observed(ty, session, site()),
        NominalAxis::Callable => summary.contains_callable_observed(ty, session, site()),
    }
}
fn parity(m: &Module, roots: &[Ty]) -> Observer {
    let original = m.nominal_type_reachability();
    let mut o = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let observed = m
        .nominal_type_reachability_observed(&mut session, site())
        .unwrap();
    assert!(core::ptr::eq(observed._module, m));
    assert_eq!(observed.reachable, original.reachable);
    for ty in roots {
        for axis in AXES {
            assert_eq!(
                query(&observed, axis, ty, &mut session).unwrap(),
                original.contains(axis, ty)
            );
        }
    }
    observed.retire_observed(&mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    drop(session);
    assert!(o.events.iter().all(|e| e.site == site()));
    o
}
fn build_events(m: &Module) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let bound = calls.get();
    out.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (o, bound)
}
