// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual complete original formula group and label custody.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::proof::{ObligationKind, ProofObligation, ProofStatus};
use crate::value::{FuncTyId, ProofId};
use crate::{BlockId, Function, FunctionSummary, SpecInvariant, SpecModule, SpecTemporal};
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original formula inventory stop");
        }
        if self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(479))
}
fn good() -> ProofFormula {
    ProofFormula::smtlib2("true", "Bool")
}
fn bad() -> ProofFormula {
    let mut f = good();
    f.payload = "false".into();
    f
}
fn obligation(id: u32, formula: Option<ProofFormula>) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind: ObligationKind::Precondition,
        status: ProofStatus::Pending,
        description: "unread".into(),
        formula,
        function: None,
        source: None,
        site: None,
        spec: None,
    }
}
fn function(
    id: u32,
    requires: Vec<ProofFormula>,
    ensures: Vec<ProofFormula>,
    decreases: Vec<ProofFormula>,
) -> Function {
    let mut f = Function::new(FuncId::new(id), "unread", FuncTyId::new(0), BlockId::new(0));
    f.summary = Some(FunctionSummary {
        requires,
        ensures,
        decreases,
        ..FunctionSummary::default()
    });
    f
}
fn fixture() -> Module {
    let mut m = Module::new("formulas");
    m.proof_obligations = vec![
        obligation(1, None),
        obligation(2, Some(good())),
        obligation(3, Some(bad())),
    ];
    m.functions
        .push(function(7, vec![good(), bad()], vec![bad()], vec![bad()]));
    let mut spec = SpecModule::new("M");
    spec.invariants = vec![
        SpecInvariant::new("untyped", "ignored"),
        SpecInvariant::new("I", "ignored").with_typed(bad()),
    ];
    spec.temporal = vec![
        SpecTemporal::new("A", TemporalForm::Always(bad())),
        SpecTemporal::new("E", TemporalForm::Eventually(good())),
        SpecTemporal::new("L", TemporalForm::LeadsTo(bad(), bad())),
        SpecTemporal::new(
            "W",
            TemporalForm::WeakFair {
                action: "ignored".into(),
                relation: Some(bad()),
            },
        ),
        SpecTemporal::new(
            "S",
            TemporalForm::StrongFair {
                action: "ignored".into(),
                relation: None,
            },
        ),
    ];
    m.spec_modules.push(spec);
    m
}
fn ordinary(m: &Module) -> Vec<E> {
    m.formulas_stating_two_texts_iter()
        .map(|site| E::FormulaTextsDisagree {
            site: site.into_owned(),
        })
        .collect()
}
fn run(m: &Module) -> (Vec<E>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = bundle(m.clone())
        .formula_text_errors_observed(&mut s, site())
        .unwrap();
    assert_eq!(out, ordinary(m));
    let saved = out.clone();
    let bound = calls.get();
    retire_native_bundle_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (saved, o, bound)
}
fn empty(s: &State) -> bool {
    s.machine.capacity() == 0
        && s.label.capacity() == 0
        && s.errors.capacity() == 0
        && s.pending.is_none()
}
fn drain<O: ExecutionObserver>(s: &mut State, w: &mut Work<'_, '_, O>) {
    s.retire_scratch(w);
    w.record(1, size_of::<Vec<E>>());
    let _ = retire_native_bundle_errors_observed(take(&mut s.errors), w.session, w.site);
}
fn prior() -> E {
    E::FormulaTextsDisagree {
        site: FormulaSite::SpecInvariant {
            machine: "prior λ\0full".into(),
            invariant: "prior 尾\0full".into(),
        },
    }
}

fn bundle(m: Module) -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.module = m;
    b
}
