// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: ordinary derived Debug is the diagnostic oracle only.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::{InstructionSite, InterpretOptions};
use crate::value::{BlockId, FuncId};
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod stops;
mod unicode_pricing;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    at: Option<usize>,
    work: usize,
    bytes: usize,
    cap: Option<usize>,
    byte_cap: Option<usize>,
    next: Option<Rc<Cell<bool>>>,
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.at == Some(self.events.len())
            || self.next.as_ref().is_some_and(|flag| flag.replace(false))
        {
            return Err("original interior");
        }
        if self.cleanup && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(78),
        block: BlockId::new(91),
        instruction_index: 17,
    })
}
fn execute(value: &ClauseSort) -> (String, Observer) {
    let mut observer = Observer::default();
    let options = InterpretOptions {
        fuel: 7,
        ..InterpretOptions::default()
    };
    let mut session = ObservedSession::new(options, &mut observer);
    let text = value.debug_observed(&mut session, site()).unwrap();
    assert_eq!(text, format!("{value:?}"));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), 7);
    drop(session);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer
            .events
            .last()
            .map(|event| (event.phase, event.work, event.copy_bytes)),
        Some((ExecutionPhase::Publication, 1, size_of::<String>()))
    );
    (text, observer)
}
fn examples() -> Vec<ClauseSort> {
    vec![
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(64),
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
        ClauseSort::Float { eb: 8, sb: 24 },
        ClauseSort::RoundingMode,
        ClauseSort::Datatype {
            name: "D".into(),
            constructors: Vec::new(),
        },
    ]
}
fn mixed() -> ClauseSort {
    ClauseSort::Datatype {
        name: "D'λ\n".into(),
        constructors: vec![
            ("None".into(), Vec::new()),
            (
                "Some".into(),
                vec![
                    (
                        "value".into(),
                        ClauseSort::Array(
                            Box::new(ClauseSort::BitVec(0)),
                            Box::new(ClauseSort::Float {
                                eb: u32::MAX,
                                sb: 0,
                            }),
                        ),
                    ),
                    ("mode".into(), ClauseSort::RoundingMode),
                ],
            ),
        ],
    }
}
