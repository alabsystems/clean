// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual iterative diagnostic type spelling, never a canonical identity.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
#[cfg(test)]
mod precedence_tests;
mod storage;
#[cfg(test)]
mod tests;
mod types;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Clone, Copy)]
enum Task<'a> {
    Type(&'a Ty),
    Types(&'a [Ty], bool),
    Text(&'a str),
    /// A fixed decimal written after a child type (a tensor's rank).
    Number(u32),
}

#[derive(Default)]
struct State<'a> {
    tasks: Vec<Task<'a>>,
    output: String,
}

impl Ty {
    /// Exact ordinary level-R Display spelling through actual borrowed type
    /// traversal, bounded raw text copies, fixed-width decimal conversion and
    /// observed per-scalar Debug escaping of handle fields. Malformed handle
    /// text is spelled, never silently normalized or accepted as a valid type.
    /// No derived Display/Debug or recursive formatter walks a variable input.
    ///
    /// This is diagnostic data only: not wire/canonical identity, validation,
    /// source/proof authority or a physical allocation/deallocation/time bound.
    /// Successful String/input disposal remains caller-owned. No new session,
    /// grant/deadline/TLS/fuel is introduced.
    pub fn display_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut state = State::default();
        let mut work = Work { session, site };
        let result = state.walk(self, &mut work);
        state.finish(result, &mut work)
    }
}

impl<'a> State<'a> {
    fn finish<O: ExecutionObserver>(mut self, result: R, work: &mut Work<'_, '_, O>) -> R<String> {
        self.retire_tasks(work);
        let result = result.and_then(|()| work.publication());
        match result {
            Ok(()) => Ok(take(&mut self.output)),
            Err(error) => {
                work.retire(take(&mut self.output));
                Err(work.terminal(error))
            }
        }
    }

    fn push<O: ExecutionObserver>(&mut self, task: Task<'a>, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.tasks)?;
        work.admit(1, size_of::<Task<'_>>())?;
        self.tasks.push(task);
        Ok(())
    }

    fn walk<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        self.push(Task::Type(ty), work)?;
        while !self.tasks.is_empty() {
            work.admit(1, size_of::<Task<'_>>())?;
            let Some(task) = self.tasks.pop() else { break };
            match task {
                Task::Type(ty) => {
                    work.admit(41, 0)?;
                    self.ty(ty, work)?;
                }
                Task::Text(text) => work.text(text, &mut self.output)?,
                Task::Number(value) => work.number(u128::from(value), &mut self.output)?,
                Task::Types(types, first) => {
                    work.admit(1, 0)?;
                    if let Some((head, tail)) = types.split_first() {
                        if !first {
                            work.text(", ", &mut self.output)?;
                        }
                        self.push(Task::Types(tail, false), work)?;
                        self.push(Task::Type(head), work)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn wrapped<O: ExecutionObserver>(
        &mut self,
        prefix: &str,
        suffix: &'static str,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(prefix, &mut self.output)?;
        self.push(Task::Text(suffix), work)?;
        self.push(Task::Type(ty), work)
    }

    fn id<O: ExecutionObserver>(&mut self, prefix: &str, id: u32, work: &mut Work<'_, '_, O>) -> R {
        work.text(prefix, &mut self.output)?;
        work.number(u128::from(id), &mut self.output)
    }

    fn retire_tasks<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.tasks.is_empty() {
            work.session.retirement_step(work.site, 1);
            self.tasks.pop();
        }
        // Every task owns only fixed numbers or borrowed headers.
        work.retire(take(&mut self.tasks));
    }
}
