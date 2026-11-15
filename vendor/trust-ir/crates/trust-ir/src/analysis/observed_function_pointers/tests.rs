// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored meaningful controls; compilation and execution UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::InstrNode;
use crate::interpret::InterpretOptions;
mod custody;
mod lazy;
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
            return Err("original stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
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
    ExecutionSite::Entry(FuncId::new(901))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn ft(n: u32) -> Ty {
    Ty::Func(FuncTyId::new(n))
}
fn seed(n: u32, target: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: ft(0),
        value: Constant::FnDef(FuncId::new(target)),
    })
    .with_result(v(n))
}
fn copy(n: u32, operand: u32, ty: Ty) -> InstrNode {
    InstrNode::new(Inst::Copy {
        ty,
        operand: v(operand),
    })
    .with_result(v(n))
}
fn reify(n: u32, operand: u32, src_ty: Ty, dst_ty: Ty) -> InstrNode {
    InstrNode::new(Inst::Cast {
        op: CastOp::ReifyFnPointer,
        src_ty,
        dst_ty,
        operand: v(operand),
    })
    .with_result(v(n))
}
fn call(n: u32) -> InstrNode {
    InstrNode::new(Inst::CallIndirect {
        callee: v(n),
        sig: FuncTyId::new(0),
        args: vec![],
        calling_conv: crate::CallingConv::C,
    })
}
fn ret() -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![] })
}
fn function(body: Vec<InstrNode>) -> Function {
    let mut f = Function::new(
        FuncId::new(17),
        "original_pointer",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.body = body;
    f.blocks.push(b);
    f
}
fn chain() -> Function {
    function(vec![
        seed(0, 7),
        copy(1, 0, ft(0)),
        reify(2, 1, ft(0), Ty::Ptr),
        call(2),
        ret(),
    ])
}
fn query(
    f: &Function,
    value: u32,
    block: u32,
    index: usize,
) -> (Option<StaticFunctionPointerResolution>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(f, &mut s, site()).unwrap();
    let actual = a
        .resolve_typed_at_observed(v(value), BlockId::new(block), index, &mut s, site())
        .unwrap();
    let ordinary = StaticFunctionPointerAnalysis::new(f);
    assert_eq!(
        actual,
        ordinary.resolve_typed_at(v(value), BlockId::new(block), index)
    );
    assert_eq!(a.cache_state(), ordinary.cache_state());
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    a.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (actual, o)
}
fn empty(s: &State<'_>) {
    assert!(!s.use_built && !s.definitions_built && !s.provenance_built);
    assert!(s.uses.is_empty() && s.definitions.is_empty() && s.provenances.is_empty());
    assert!(s.dominators.is_none() && s.pending_use.is_none() && s.old_use.is_none());
    assert!(s.active.is_empty() && s.path.is_empty());
    assert_eq!(s.path.capacity(), 0);
}
fn run_query_only(f: &Function, value: u32, index: usize) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = ObservedStaticFunctionPointerAnalysis::new_observed(f, &mut s, site()).unwrap();
    a.resolve_typed_at_observed(v(value), BlockId::new(0), index, &mut s, site())
        .unwrap();
    // The caller deliberately keeps the complete analysis; no implicit disposal
    // is credited as observed work. Tests using this baseline stop before cleanup.
    drop(a);
    drop(s);
    o
}
