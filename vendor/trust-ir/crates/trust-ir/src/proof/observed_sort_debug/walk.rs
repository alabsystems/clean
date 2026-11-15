// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        value: &'a ClauseSort,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.sort(value, work)?;
        loop {
            work.admit(1, size_of::<Option<Task<'_>>>())?;
            let Some(task) = self.tasks.pop() else { break };
            // Fixed four-case task dispatch precedes actual task field reads.
            work.admit(4, size_of::<Task<'_>>())?;
            match task {
                Task::Sort(sort) => self.render_sort(sort, work)?,
                Task::Text(text) => work.text(text, &mut self.output)?,
                Task::Ctors(rows, index) => self.render_ctors(rows, index, work)?,
                Task::Fields(rows, index) => self.render_fields(rows, index, work)?,
            }
        }
        Ok(())
    }
    fn render_sort<O: ExecutionObserver>(
        &mut self,
        value: &'a ClauseSort,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Fixed seven-case dispatch and bounded scalar/borrowed field transport;
        // queued descriptors and real storage growth are admitted separately.
        work.admit(7, 4 * size_of::<Task<'_>>())?;
        match value {
            ClauseSort::Bool => work.text("Bool", &mut self.output),
            ClauseSort::Int => work.text("Int", &mut self.output),
            ClauseSort::RoundingMode => work.text("RoundingMode", &mut self.output),
            ClauseSort::BitVec(width) => {
                work.text("BitVec(", &mut self.output)?;
                work.number(u128::from(*width), &mut self.output)?;
                work.text(")", &mut self.output)
            }
            ClauseSort::Float { eb, sb } => {
                work.text("Float { eb: ", &mut self.output)?;
                work.number(u128::from(*eb), &mut self.output)?;
                work.text(", sb: ", &mut self.output)?;
                work.number(u128::from(*sb), &mut self.output)?;
                work.text(" }", &mut self.output)
            }
            ClauseSort::Array(index, value) => {
                work.text("Array(", &mut self.output)?;
                self.text(")", work)?;
                self.sort(value, work)?;
                self.text(", ", work)?;
                self.sort(index, work)
            }
            ClauseSort::Datatype { name, constructors } => {
                work.text("Datatype { name: ", &mut self.output)?;
                work.quoted(name, &mut self.output)?;
                work.text(", constructors: ", &mut self.output)?;
                self.text(" }", work)?;
                self.ctors(constructors, 0, work)
            }
        }
    }
    fn render_ctors<O: ExecutionObserver>(
        &mut self,
        rows: &'a [(String, Vec<(String, ClauseSort)>)],
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, 2 * size_of::<usize>())?;
        if index == 0 {
            work.text("[", &mut self.output)?;
        }
        if let Some((name, fields)) = work.at(rows, index)? {
            work.admit(1, 0)?;
            if index > 0 {
                work.text(", ", &mut self.output)?;
            }
            work.text("(", &mut self.output)?;
            work.quoted(name, &mut self.output)?;
            work.text(", ", &mut self.output)?;
            work.admit(1, size_of::<usize>())?;
            let mut next = index;
            work.next(&mut next)?;
            self.ctors(rows, next, work)?;
            self.text(")", work)?;
            self.fields(fields, 0, work)
        } else {
            work.text("]", &mut self.output)
        }
    }
    fn render_fields<O: ExecutionObserver>(
        &mut self,
        rows: &'a [(String, ClauseSort)],
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, 2 * size_of::<usize>())?;
        if index == 0 {
            work.text("[", &mut self.output)?;
        }
        if let Some((name, sort)) = work.at(rows, index)? {
            work.admit(1, 0)?;
            if index > 0 {
                work.text(", ", &mut self.output)?;
            }
            work.text("(", &mut self.output)?;
            work.quoted(name, &mut self.output)?;
            work.text(", ", &mut self.output)?;
            work.admit(1, size_of::<usize>())?;
            let mut next = index;
            work.next(&mut next)?;
            self.fields(rows, next, work)?;
            self.text(")", work)?;
            self.sort(sort, work)
        } else {
            work.text("]", &mut self.output)
        }
    }
}
