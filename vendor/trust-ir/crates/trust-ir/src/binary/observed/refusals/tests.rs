// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN: actual raw writer and CheckSink parity/custody.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::signature_abi::*;
use crate::{Block, Constant, FuncTy, Function, Global, InstrNode, ModuleCompleteness};
use std::{cell::Cell, rc::Rc};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
    retirement_stop: bool,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("interior");
        }
        if self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if self.retirement_stop && p.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(p.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(p.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9751))
}
fn run(m: &Module) -> (Vec<BinaryProjectionError>, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = m.wire_image_refusals_observed(&mut s, site()).unwrap();
    assert_eq!(rows, m.wire_image_refusals());
    let saved = rows.clone();
    let end = c.get();
    retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    assert!(
        !o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::CanonicalDigest)
    );
    (saved, o, end)
}
fn empty(h: &Refusals) {
    assert!(h.first.iter().all(Option::is_none));
    assert!(h.pending.is_none() && h.converted.is_none());
    assert_eq!(h.result.capacity(), 0);
}
#[cfg(target_pointer_width = "64")]
fn feed<O: ExecutionObserver>(out: &mut Output<'_, '_, O>) -> R {
    out.refuse(|| WireRefusal::ProducerInternalType)?;
    out.refuse(|| WireRefusal::CompletenessClaim)?;
    out.refuse(|| WireRefusal::InlinedScopeChain {
        function: 9,
        scope: 7,
    })?;
    out.refuse(|| WireRefusal::NoWireTag {
        construct: "FIRST",
        site: Some(WireNodeSite {
            function: 8,
            block: 3,
            index: 99,
        }),
    })?;
    out.admit(3, 3 + size_of::<WireRefusal>() + size_of::<String>())?;
    let detail = "raw".to_owned();
    out.refuse_owned(WireRefusal::SignatureAbi {
        signature: 17,
        detail,
    })?;
    observed_write_count(out, "FIRST count", u32::MAX as usize + 1)?;
    out.refuse(|| WireRefusal::NoWireTag {
        construct: "SECOND",
        site: None,
    })?;
    out.refuse(|| WireRefusal::InlinedScopeChain {
        function: 3,
        scope: 1,
    })?;
    out.admit(5, 5 + size_of::<WireRefusal>() + size_of::<String>())?;
    let detail = "later".to_owned();
    out.refuse_owned(WireRefusal::SignatureAbi {
        signature: 2,
        detail,
    })?;
    observed_write_count(out, "SECOND count", u32::MAX as usize + 2)
}
#[cfg(target_pointer_width = "64")]
fn ordinary_feed() -> Vec<BinaryProjectionError> {
    let mut sink = CheckSink::default();
    sink.refuse(WireRefusal::ProducerInternalType);
    sink.refuse(WireRefusal::CompletenessClaim);
    sink.refuse(WireRefusal::InlinedScopeChain {
        function: 9,
        scope: 7,
    });
    sink.refuse(WireRefusal::NoWireTag {
        construct: "FIRST",
        site: Some(WireNodeSite {
            function: 8,
            block: 3,
            index: 99,
        }),
    });
    sink.refuse(WireRefusal::SignatureAbi {
        signature: 17,
        detail: "raw".into(),
    });
    write_count(&mut sink, "FIRST count", u32::MAX as usize + 1);
    sink.refuse(WireRefusal::NoWireTag {
        construct: "SECOND",
        site: None,
    });
    sink.refuse(WireRefusal::InlinedScopeChain {
        function: 3,
        scope: 1,
    });
    sink.refuse(WireRefusal::SignatureAbi {
        signature: 2,
        detail: "later".into(),
    });
    write_count(&mut sink, "SECOND count", u32::MAX as usize + 2);
    sink.first.into_iter().flatten().collect()
}
#[cfg(target_pointer_width = "64")]
fn direct(o: &mut Observer) -> R<Vec<BinaryProjectionError>> {
    let mut s = ObservedSession::new(InterpretOptions::default(), o);
    let mut h = Refusals::default();
    let result = {
        let mut out = Output::checker(&mut s, site(), &mut h)?;
        feed(&mut out).and_then(|()| out.take_refusals())
    };
    if result.is_err() {
        h.retire(&mut s, site());
    }
    let rows = result?;
    let saved = rows.clone(); // Independent test oracle copy, never transferred authority.
    retire_wire_image_refusals_observed(rows, &mut s, site())?;
    Ok(saved)
}
