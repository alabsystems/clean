// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Authored source controls, all UNRUN.
use super::*;
use crate::Constant;
use crate::dialect::DialectInst;
use crate::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, BinOp, BindingFrameDef, CastOp, FCmpOp, ICmpOp,
    InstShape, Ordering, OverflowOp, PanicLocation, PanicSite, SwitchCase, UnOp,
};
use crate::interpret::InterpretOptions;
use crate::value::{BindingFrameId, BlockId, FuncId, FuncTyId, GlobalId, TyId, ValueId};
mod oracle;
mod parity;
mod stops;
mod witnesses;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("original type stop");
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
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(97))
}
fn v() -> ValueId {
    ValueId::new(0)
}
fn observed(instruction: &Inst) -> (Vec<&Ty>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let types = instruction
        .inline_types_observed(&mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (types, observer)
}
fn parity(instruction: &Inst) -> Vec<&Ty> {
    let expected = oracle::collect(instruction);
    let (actual, observer) = observed(instruction);
    assert_eq!(actual.len(), expected.len());
    for (actual, expected) in actual.iter().zip(expected) {
        // Do not invoke recursive derived Ty equality, even in the oracle.
        assert!(core::ptr::eq(*actual, expected));
    }
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn frame(count: usize) -> Inst {
    Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(71),
            "frame",
            (0..count)
                .map(|index| BindingSlot::new(index.to_string(), Ty::Tuple(vec![Ty::U32])))
                .collect(),
        ),
    }
}
fn dialect(count: usize) -> Inst {
    let mut op = DialectInst::new("observed", "types");
    op.result_tys = (0..count).map(|_| Ty::Tuple(vec![Ty::U8])).collect();
    Inst::DialectOp(Box::new(op))
}
