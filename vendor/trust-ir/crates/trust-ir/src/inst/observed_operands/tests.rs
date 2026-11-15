// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored source controls; UNRUN in this task.
use super::*;
use crate::inst::{
    AllocOrigin, AssertOverflowOp, AtomicRMWOp, BinOp, BindingFrameDef, CastOp, FCmpOp, ICmpOp,
    Ordering, OverflowOp, UnOp,
};
use crate::interpret::InterpretOptions;
use crate::value::{BindingFrameId, GlobalId};
use crate::{BlockId, Constant, FuncId, FuncTyId, Ty, TyId};
use core::ops::ControlFlow;
mod membership;
mod parity;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_phase: Option<ExecutionPhase>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) || self.stop_phase == Some(event.phase) {
            return Err("original stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|limit| self.work > limit) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|limit| self.bytes > limit) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(99))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn ids(values: &[u32]) -> Vec<ValueId> {
    values.iter().copied().map(v).collect()
}
fn ordinary(instruction: &Inst) -> Vec<ValueId> {
    let mut values = Vec::new();
    let _: ControlFlow<()> = instruction.try_visit_value_operands(|value| {
        values.push(value);
        ControlFlow::Continue(())
    });
    values
}
fn observed(instruction: &Inst) -> (Vec<ValueId>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let values = instruction
        .value_operands_observed(&mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (values, observer)
}
fn parity(instruction: &Inst) -> Vec<ValueId> {
    let (values, observer) = observed(instruction);
    assert_eq!(values, ordinary(instruction));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    values
}
fn switch(empty: bool, count: usize) -> Inst {
    Inst::Switch {
        value: v(1),
        default: BlockId::new(91),
        default_args: if empty { vec![] } else { ids(&[2, 1]) },
        cases: (0..count)
            .map(|index| SwitchCase {
                value: Constant::Int(index as i128),
                target: BlockId::new(92),
                args: if empty { vec![] } else { ids(&[3, 3, 4]) },
            })
            .collect(),
        exhaustive_enum_unreachable: true,
    }
}
fn invocations() -> Vec<Inst> {
    vec![
        Inst::Invoke {
            callee: FuncId::new(90),
            args: ids(&[1, 2]),
            normal_dest: BlockId::new(91),
            normal_args: ids(&[3, 1]),
            unwind_dest: BlockId::new(92),
        },
        Inst::InvokeIndirect {
            callee: v(90),
            sig: FuncTyId::new(93),
            args: ids(&[1, 2]),
            calling_conv: crate::CallingConv::C,
            normal_dest: BlockId::new(91),
            normal_args: ids(&[3, 1]),
            unwind_dest: BlockId::new(92),
        },
        Inst::DropInvoke {
            ty: Ty::U32,
            ptr: v(90),
            normal_dest: BlockId::new(91),
            normal_args: ids(&[3, 1]),
            unwind_dest: BlockId::new(92),
        },
        Inst::AssertInvoke {
            cond: v(1),
            kind: AssertKind::BoundsCheck {
                index: v(2),
                len: v(3),
            },
            site: PanicSite {
                entry: FuncId::new(90),
                location: PanicLocation::Value(v(4)),
            },
            normal_dest: BlockId::new(91),
            normal_args: ids(&[5, 1]),
            unwind_dest: BlockId::new(92),
        },
    ]
}
