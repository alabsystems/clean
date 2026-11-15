// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: full actual std predicate and original observation controls.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::{FuncId, interpret::InterpretOptions};
mod parity;
mod stops;
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(71))
}
#[derive(Default)]
struct Meter {
    calls: usize,
    work: usize,
    copy: usize,
    last: Option<ExecutionProgress>,
    stop: Option<usize>,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
}
impl ExecutionObserver for Meter {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        assert_eq!(e.site, site());
        self.calls += 1;
        self.work += e.work;
        self.copy += e.copy_bytes;
        self.last = Some(e);
        if self.stop == Some(self.calls)
            || self.work_cap.is_some_and(|cap| self.work > cap)
            || self.copy_cap.is_some_and(|cap| self.copy > cap)
        {
            Err("original utf8 refusal")
        } else {
            Ok(())
        }
    }
}
fn run(bytes: &[u8]) -> (bool, Meter) {
    let mut o = Meter::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = utf8_is_valid_observed(bytes, &mut s, site()).unwrap();
    assert_eq!(result, std::str::from_utf8(bytes).is_ok(), "{bytes:x?}");
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert_eq!(o.last.unwrap().phase, ExecutionPhase::Publication);
    (result, o)
}
