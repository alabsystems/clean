// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. The original effective_sort and Debug are parity oracles.
use super::*;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::value::{BlockId, FuncId};
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    count: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    refuse_cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.count.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original effective-sort stop");
        }
        if self.refuse_cleanup
            && self.stop.is_some_and(|stop| self.events.len() > stop)
            && event.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
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
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(37),
        block: BlockId::new(13),
        instruction_index: 59,
    })
}
fn oracle(variable: &SpecVar, binding: &ClauseSort) -> Option<String> {
    variable.effective_sort().and_then(|sort| {
        if sort == *binding {
            None
        } else {
            Some(format!("{sort:?}"))
        }
    })
}
fn dispose<O: ExecutionObserver>(output: Option<String>, session: &mut ObservedSession<'_, O>) {
    let mut work = Work {
        session,
        site: site(),
    };
    work.step(size_of::<Option<String>>().saturating_add(1));
    if let Some(mut text) = output {
        work.retire_text(&mut text);
    }
    work.poll();
}
fn run(variable: &SpecVar, binding: &ClauseSort) -> (Option<String>, Observer, usize) {
    let mut observer = Observer::default();
    let count = observer.count.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let output = variable
        .effective_sort_mismatch_observed(binding, &mut session, site())
        .unwrap();
    let bound = count.get();
    assert_eq!(output, oracle(variable, binding));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    let saved = output.clone();
    dispose(output, &mut session);
    assert!(session.first_refusal().is_none());
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events[bound - 1].phase,
        ExecutionPhase::Publication
    );
    (saved, observer, bound)
}
fn nested(depth: usize, leaf: ClauseSort) -> ClauseSort {
    (0..depth).fold(leaf, |sort, _| {
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(sort))
    })
}
fn datatype(name: &str) -> ClauseSort {
    ClauseSort::Datatype {
        name: name.into(),
        constructors: vec![
            (
                "some\nλ\"'\\".into(),
                vec![("field\0\t".into(), ClauseSort::BitVec(17))],
            ),
            ("none".into(), Vec::new()),
        ],
    }
}
fn empty(state: &State<'_>) -> bool {
    state.fields.iter().all(|field| field.capacity() == 0)
        && state.detail.capacity() == 0
        && state.format.capacity() == 0
        && state.equality.capacity() == 0
        && state.pending.is_none()
        && state.errors.capacity() == 0
}
