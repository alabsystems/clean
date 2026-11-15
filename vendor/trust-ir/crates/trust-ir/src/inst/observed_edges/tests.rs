// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored controls; all are deliberately UNRUN in this task.

use super::*;
use crate::inst::{AssertKind, PanicLocation, PanicSite, SwitchCase};
use crate::interpret::InterpretOptions;
use crate::{CallingConv, Constant, FuncId, FuncTyId, Ty};

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
            return Err("original stop");
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
    ExecutionSite::Instruction(crate::interpret::InstructionSite {
        function: FuncId::new(83),
        block: BlockId::new(7),
        instruction_index: 11,
    })
}
fn switch(count: u32) -> Inst {
    Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(99),
        default_args: vec![ValueId::new(3), ValueId::new(4)],
        cases: (0..count)
            .map(|index| SwitchCase {
                value: Constant::Int(i128::from(index)),
                target: BlockId::new(index % 7),
                args: vec![ValueId::new(index), ValueId::new(index + 1)],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    }
}
fn invokes() -> [Inst; 4] {
    [
        Inst::Invoke {
            callee: FuncId::new(4),
            args: vec![ValueId::new(1)],
            normal_dest: BlockId::new(5),
            normal_args: vec![ValueId::new(2)],
            unwind_dest: BlockId::new(6),
        },
        Inst::AssertInvoke {
            cond: ValueId::new(1),
            kind: AssertKind::DivByZero,
            site: PanicSite {
                entry: FuncId::new(4),
                location: PanicLocation::Value(ValueId::new(9)),
            },
            normal_dest: BlockId::new(5),
            normal_args: vec![ValueId::new(2)],
            unwind_dest: BlockId::new(6),
        },
        Inst::DropInvoke {
            ty: Ty::Ref(Box::new(Ty::Bool)),
            ptr: ValueId::new(1),
            normal_dest: BlockId::new(5),
            normal_args: vec![ValueId::new(2)],
            unwind_dest: BlockId::new(6),
        },
        Inst::InvokeIndirect {
            callee: ValueId::new(1),
            sig: FuncTyId::new(0),
            args: vec![ValueId::new(9)],
            calling_conv: CallingConv::C,
            normal_dest: BlockId::new(5),
            normal_args: vec![ValueId::new(2)],
            unwind_dest: BlockId::new(6),
        },
    ]
}
fn observed<'a>(instruction: &'a Inst, observer: &mut Observer) -> R<Vec<Edge<'a>>> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    let edges = instruction.successor_edges_observed(&mut session, site())?;
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    Ok(edges)
}
fn parity(instruction: &Inst) {
    let mut observer = Observer::default();
    let actual = observed(instruction, &mut observer).unwrap();
    let expected = instruction.successor_edges();
    assert_eq!(actual, expected);
    for (actual, expected) in actual.iter().zip(&expected) {
        if actual.kind == EdgeKind::Normal {
            assert_eq!(actual.args.as_ptr(), expected.args.as_ptr());
        }
    }
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.iter().all(|event| event.site == site()));
}

#[test]
fn branch_and_terminal_edges_match_original_order_and_argument_identity() {
    for instruction in [
        Inst::Br {
            target: BlockId::new(5),
            args: vec![ValueId::new(1), ValueId::new(2)],
        },
        Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(5),
            then_args: vec![ValueId::new(1)],
            else_target: BlockId::new(5),
            else_args: vec![ValueId::new(2)],
        },
        Inst::Return {
            values: vec![ValueId::new(1)],
        },
        Inst::Resume {
            exn: ValueId::new(1),
        },
        Inst::CoroSuspend {
            frame: ValueId::new(1),
            state_slot: 2,
            next_state: -7,
            value: ValueId::new(4),
        },
        Inst::Unreachable,
        Inst::NullPtr,
    ] {
        parity(&instruction);
    }
}

#[test]
fn all_four_invoke_families_keep_normal_then_unwind_and_empty_unwind_args() {
    for instruction in invokes() {
        parity(&instruction);
        let edges = observed(&instruction, &mut Observer::default()).unwrap();
        assert_eq!(edges.len(), 2);
        assert_eq!(
            (edges[0].target, edges[0].kind),
            (BlockId::new(5), EdgeKind::Normal)
        );
        assert_eq!(edges[0].args, &[ValueId::new(2)]);
        assert_eq!(
            (edges[1].target, edges[1].kind),
            (BlockId::new(6), EdgeKind::Unwind)
        );
        assert!(edges[1].args.is_empty());
    }
}

#[test]
fn empty_and_wide_switches_keep_every_case_then_default_without_deduplication() {
    for count in [0, 1, 257, 50_000] {
        let mut instruction = switch(count);
        for exhaustive in [false, true] {
            if let Inst::Switch {
                exhaustive_enum_unreachable,
                ..
            } = &mut instruction
            {
                *exhaustive_enum_unreachable = exhaustive;
            }
            parity(&instruction);
            let edges = observed(&instruction, &mut Observer::default()).unwrap();
            assert_eq!(edges.len(), count as usize + 1);
            assert_eq!(edges.last().unwrap().target, BlockId::new(99));
            assert_eq!(
                edges.last().unwrap().args,
                &[ValueId::new(3), ValueId::new(4)]
            );
            for (index, edge) in edges[..count as usize].iter().enumerate() {
                assert_eq!(edge.target, BlockId::new(index as u32 % 7));
                assert_eq!(
                    edge.args,
                    &[ValueId::new(index as u32), ValueId::new(index as u32 + 1)]
                );
            }
        }
    }
}

#[test]
fn large_argument_vectors_are_borrowed_with_constant_edge_header_charges() {
    let small = Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(2)],
    };
    let large = Inst::Br {
        target: BlockId::new(1),
        args: (0..50_000).map(ValueId::new).collect(),
    };
    let mut a = Observer::default();
    let mut b = Observer::default();
    observed(&small, &mut a).unwrap();
    let edges = observed(&large, &mut b).unwrap();
    assert_eq!((a.work, a.bytes), (b.work, b.bytes));
    let Inst::Br { args, .. } = &large else {
        unreachable!()
    };
    assert_eq!(edges[0].args.as_ptr(), args.as_ptr());
    assert_eq!(edges[0].args.len(), 50_000);
}

#[test]
fn borrowed_edges_outlive_session_and_observer_while_retaining_instruction_borrow() {
    let instruction = switch(3);
    let edges = {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        instruction
            .successor_edges_observed(&mut session, site())
            .unwrap()
    };
    assert_eq!(edges, instruction.successor_edges());
}
