// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual whole ordinary oracle and original-owner controls; all Rust UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::{Constant, DropGlueEntry, FuncTy, GateEvidence, InlinedAt};
use std::cell::Cell;
use std::rc::Rc;
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    copy: usize,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
    marker: Rc<Cell<usize>>,
    dynamic_stop: Rc<Cell<Option<usize>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> core::result::Result<(), Self::Refusal> {
        self.events.push(e);
        self.marker.set(self.events.len());
        if self.stop.or(self.dynamic_stop.get()) == Some(self.events.len()) {
            return Err("body stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.copy = self.copy.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.copy_cap.is_some_and(|n| self.copy > n) {
            return Err("copy");
        }
        Ok(())
    }
}
struct Trace {
    observer: Observer,
    split: usize,
}
impl Trace {
    fn events(&self) -> &[ExecutionProgress] {
        &self.observer.events[..self.split]
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(900),
        block: BlockId::new(800),
        instruction_index: 700,
    })
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn f() -> FuncId {
    FuncId::new(17)
}
fn module() -> Module {
    let mut m = Module::new("outside minimal image λ");
    m.func_types
        .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![], false));
    let mut f = Function::new(f(), "body_λ", FuncTyId::new(0), BlockId::new(8));
    let mut late = Block::new(BlockId::new(8));
    late.params.push((v(40), Ty::Ptr));
    late.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: v(40),
        })
        .with_result(v(80)),
    );
    late.body.push(InstrNode::new(Inst::Return {
        values: vec![v(80), v(999)],
    }));
    let mut early = Block::new(BlockId::new(2));
    early.params.push((v(30), Ty::I64));
    early.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(-7),
        })
        .with_result(v(70)),
    );
    early.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(8),
        args: vec![v(30), v(70)],
    }));
    f.blocks = vec![late, early];
    m.functions.push(f);
    m
}
fn drops() -> Module {
    let mut m = module();
    let body = &mut m.functions[0].blocks[0].body;
    body.insert(
        0,
        InstrNode::new(Inst::Drop {
            ty: Ty::I64,
            ptr: v(40),
        }),
    );
    body.insert(
        1,
        InstrNode::new(Inst::Drop {
            ty: Ty::U8,
            ptr: v(40),
        }),
    );
    body.insert(
        2,
        InstrNode::new(Inst::DropInvoke {
            ty: Ty::I64,
            ptr: v(40),
            normal_dest: BlockId::new(2),
            normal_args: vec![v(40)],
            unwind_dest: BlockId::new(8),
        }),
    );
    m.drop_glue = vec![
        DropGlueEntry {
            glue: FuncId::new(90),
            ty: Ty::I64,
        },
        DropGlueEntry {
            glue: FuncId::new(3),
            ty: Ty::U8,
        },
    ];
    m
}
fn ambiguous() -> Module {
    let mut m = drops();
    m.drop_glue.push(DropGlueEntry {
        glue: FuncId::new(2),
        ty: Ty::I64,
    });
    m
}
fn same_glue() -> Module {
    let mut m = drops();
    m.drop_glue[1].glue = m.drop_glue[0].glue;
    m
}
fn inlining() -> ScopeData {
    ScopeData {
        parent: None,
        span: None,
        inlined_at: Some(InlinedAt {
            span: SourceSpan {
                file: 0,
                line: 1,
                col: 2,
            },
            callee: "callee_λ".into(),
        }),
    }
}
fn call<O: ExecutionObserver>(
    m: &Module,
    id: FuncId,
    s: &mut ObservedSession<'_, O>,
) -> R<core::result::Result<ProofDigest, String>> {
    m.function_body_digest_observed(id, s, site())
}
fn run(m: &Module, id: FuncId) -> Trace {
    let expected = m.function_body_digest(id);
    let mut o = Observer::default();
    let marker = Rc::clone(&o.marker);
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = call(m, id, &mut s).unwrap();
    assert_eq!(actual, expected);
    let split = marker.get();
    Module::retire_function_body_digest_result_observed(actual, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    Trace { observer: o, split }
}
fn total(events: &[ExecutionProgress], copy: bool) -> usize {
    events
        .iter()
        .map(|e| if copy { e.copy_bytes } else { e.work })
        .sum()
}

mod cast_preimage;
