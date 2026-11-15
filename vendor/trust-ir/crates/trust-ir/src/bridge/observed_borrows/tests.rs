// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Authored controls; all UNRUN.
use super::*;
use crate::bridge::{borrow_result_ty, borrow_result_types};
use crate::interpret::InterpretOptions;
use crate::value::{BlockId, FuncId, FuncTyId, PredId, TyId};
use crate::{Block, FatPtrKind, InstrNode};
mod parity;
mod stops;

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
            return Err("original borrow stop");
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
    ExecutionSite::Entry(FuncId::new(98))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn fat() -> Ty {
    Ty::FatPtr(FatPtrKind::Str)
}
fn borrow(result: u32, operand: u32, mutable: bool) -> InstrNode {
    InstrNode::new(if mutable {
        Inst::BorrowMut { ptr: v(operand) }
    } else {
        Inst::Borrow { ptr: v(operand) }
    })
    .with_result(v(result))
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut f = Function::new(
        FuncId::new(98),
        "borrow chain",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.body = nodes;
    f.blocks.push(block);
    f
}
fn chain(count: u32) -> Function {
    function(
        (1..=count)
            .rev()
            .map(|id| borrow(id, id - 1, id % 2 == 0))
            .collect(),
    )
}
fn observed(function: &Function, known: &[(u32, Ty)]) -> (Vec<(ValueId, Ty)>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let rows = borrow_result_types_observed(function, known, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (rows, observer)
}
fn parity(function: &Function, known: &[(u32, Ty)]) -> Vec<(ValueId, Ty)> {
    // This is the actual ordinary callback-map implementation, not a mirror
    // of the new row index or chain traversal. Fixture setup is unobserved.
    let map: std::collections::BTreeMap<_, _> = known.iter().cloned().collect();
    let expected = borrow_result_types(function, &|id| map.get(&id.index()).cloned());
    let (actual, observer) = observed(function, known);
    assert_eq!(actual, expected);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn known() -> Vec<(u32, Ty)> {
    vec![(0, fat()), (1, Ty::Ptr), (2, Ty::Ptr), (3, Ty::Ptr)]
}
