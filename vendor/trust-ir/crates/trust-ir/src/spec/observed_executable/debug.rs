// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact non-alternate derived Ty/Vec Debug for the original signature reason.
use super::*;
mod types;
#[derive(Clone, Copy)]
pub(super) enum Task<'a> {
    Type(&'a Ty),
    Types(&'a [Ty], usize),
    Text(&'static str),
    Number(u128),
}
impl<'a> State<'a> {
    fn task<O: ExecutionObserver>(&mut self, task: Task<'a>, work: &mut Work<'_, '_, O>) -> R {
        // Every caller preadmits the descriptor BEFORE constructing it; this
        // separate push charge covers actual transport and requested Vec growth.
        work.push(&mut self.tasks, task)
    }
    pub(super) fn types_text<O: ExecutionObserver>(
        &mut self,
        types: &'a [Ty],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let result = (|| {
            work.admit(1, 0)?;
            if self.tasks.capacity() != 0 {
                return Err(ObservedValueError::InvalidRange);
            }
            work.admit(1, size_of::<Task<'_>>())?;
            self.task(Task::Types(types, 0), work)?;
            loop {
                work.admit(1, size_of::<Option<Task<'_>>>())?;
                let Some(task) = self.tasks.pop() else { break };
                // Exhaustive fixed dispatch and at most four actual borrowed/
                // scalar descriptors before construction; growth is separate.
                work.admit(41, 4 * size_of::<Task<'_>>())?;
                match task {
                    Task::Text(text) => work.text(text, &mut self.detail)?,
                    Task::Number(n) => work.number(n, &mut self.detail)?,
                    Task::Type(ty) => self.ty_text(ty, work)?,
                    Task::Types(rows, index) => {
                        if index == 0 {
                            work.text("[", &mut self.detail)?;
                        }
                        if let Some(ty) = work.at(rows, index)? {
                            if index > 0 {
                                work.text(", ", &mut self.detail)?;
                            }
                            let mut next = index;
                            work.next(&mut next)?;
                            self.task(Task::Types(rows, next), work)?;
                            self.task(Task::Type(ty), work)?;
                        } else {
                            work.text("]", &mut self.detail)?;
                        }
                    }
                }
            }
            Ok(())
        })();
        work.retire_fixed_vec(&mut self.tasks);
        result.map_err(|e| work.terminal(e))?;
        work.admit(1, 0)
    }
    fn wrapped<O: ExecutionObserver>(
        &mut self,
        name: &str,
        ty: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(name, &mut self.detail)?;
        work.text("(", &mut self.detail)?;
        self.task(Task::Text(")"), work)?;
        self.task(Task::Type(ty), work)
    }
    fn id<O: ExecutionObserver>(&mut self, prefix: &str, id: u32, work: &mut Work<'_, '_, O>) -> R {
        work.text(prefix, &mut self.detail)?;
        work.number(id as u128, &mut self.detail)
    }
}
