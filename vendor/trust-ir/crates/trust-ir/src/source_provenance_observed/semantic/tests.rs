// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls, all UNRUN.
use super::*;
use crate::interpret::InterpretOptions;
use crate::{Block, BlockId, FuncTyId, Function, Global, Inst, InstrNode, Linkage, Ty};
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
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original source semantic stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original source semantic cleanup");
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
    ExecutionSite::Entry(FuncId::new(151))
}
fn carrier(name: &str) -> SourceProvenance {
    SourceProvenance::new(
        ProofDigest::sha256([3; 32]),
        ProofDigest::sha256([7; 32]),
        vec![crate::SourceLoopProvenance {
            source_loop_id: 0,
            hir_local_id: 41,
            header: BlockId::new(0),
            bindings: vec![crate::SourceBindingProvenance {
                name: name.into(),
                hir_local_id: 43,
                place: SourcePlace::FunctionParameter { index: 0 },
            }],
        }],
    )
}
fn function(id: u32, name: &str) -> Function {
    let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    f.source_provenance = Some(carrier(name));
    f
}
fn module() -> Module {
    let mut m = Module::new("semantic_λ");
    m.files = vec!["one.rs".into(), "two.rs".into()];
    m.types.push(Ty::U32);
    m.functions = vec![function(17, "sibling"), function(151, "target_λ")];
    m.globals.push(Global {
        name: "global".into(),
        ty: Ty::U32,
        mutable: false,
        initializer: Some(crate::Constant::Int(3)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: crate::Visibility::Default,
        retained: false,
    });
    m
}
fn run(m: &Module, id: FuncId) -> (Result<ProofDigest, String>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out = m
        .source_provenance_semantic_digest_observed(id, &mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (out, observer)
}
fn parity(m: &Module, id: FuncId) -> Result<ProofDigest, String> {
    let (out, observer) = run(m, id);
    assert_eq!(out, m.source_provenance_semantic_digest(id));
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    out
}
