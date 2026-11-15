// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual iterative ordinary diagnostic spelling, without recursive Display.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod float;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Task<'a> {
    Value(&'a Constant),
    Items(&'a [Constant], bool),
    Fields(&'a [(String, Constant)], bool),
    Text(&'a str),
    Number(u128),
    Bytes(&'a [u8]),
    /// A tensor blob's extents, `, `-separated.
    Dims(&'a [u64], bool),
}
#[derive(Default)]
struct State<'a> {
    tasks: Vec<Task<'a>>,
    output: String,
}
impl Constant {
    /// The exact ordinary Display spelling of every currently covered carrier.
    /// Inline children, text and bytes are actually traversed in bounded steps
    /// with original-session pre-growth/copy admission, not by a recursive
    /// formatter after a prewalk. No value validity, wire/canonical identity,
    /// proof/source authority, owner or deadline is established.
    ///
    /// Float uses observed Dragon shortest conversion and exact Debug layout.
    /// No opaque numeric formatter walks an input after a prewalk.
    /// Physical allocator/panic/time bounds and
    /// disposal of a successful String/original input remain caller duties.
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
        let mut work = Work { session, site };
        let mut state = State::default();
        let result = state.run(self, &mut work);
        state.retire_tasks(&mut work);
        let result = result.and_then(|()| work.publication());
        match result {
            Ok(()) => Ok(take(&mut state.output)),
            Err(error) => {
                work.retire(take(&mut state.output));
                Err(work.terminal(error))
            }
        }
    }
}
impl<'a> State<'a> {
    fn run<O: ExecutionObserver>(&mut self, value: &'a Constant, work: &mut Work<'_, '_, O>) -> R {
        self.push(Task::Value(value), work)?;
        while !self.tasks.is_empty() {
            work.admit(1, 0)?;
            let Some(task) = self.tasks.pop() else { break };
            match task {
                Task::Value(value) => self.value(value, work)?,
                Task::Text(text) => work.text(text, &mut self.output)?,
                Task::Number(value) => work.unsigned(value, &mut self.output)?,
                Task::Items(items, first) => {
                    if let Some((value, rest)) = items.split_first() {
                        if !first {
                            work.text(", ", &mut self.output)?;
                        }
                        self.push(Task::Items(rest, false), work)?;
                        self.push(Task::Value(value), work)?;
                    }
                }
                Task::Fields(fields, first) => {
                    if let Some(((name, value), rest)) = fields.split_first() {
                        if !first {
                            work.text(", ", &mut self.output)?;
                        }
                        work.text(name, &mut self.output)?;
                        work.text(" = ", &mut self.output)?;
                        self.push(Task::Fields(rest, false), work)?;
                        self.push(Task::Value(value), work)?;
                    }
                }
                Task::Bytes(bytes) => self.bytes(bytes, work)?,
                Task::Dims(dims, first) => {
                    if let Some((dim, rest)) = dims.split_first() {
                        if !first {
                            work.text(", ", &mut self.output)?;
                        }
                        work.unsigned(u128::from(*dim), &mut self.output)?;
                        self.push(Task::Dims(rest, false), work)?;
                    }
                }
            }
        }
        Ok(())
    }
    fn push<O: ExecutionObserver>(&mut self, task: Task<'a>, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.tasks)?;
        work.admit(1, size_of::<Task<'_>>())?;
        self.tasks.push(task);
        Ok(())
    }
    fn value<O: ExecutionObserver>(
        &mut self,
        value: &'a Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        match value {
            Constant::Int(value) => work.signed(*value, &mut self.output),
            Constant::U128(value) => work.unsigned(*value, &mut self.output),
            Constant::Float(value) => float::write(*value, &mut self.output, work),
            Constant::Bool(value) => {
                work.text(if *value { "true" } else { "false" }, &mut self.output)
            }
            Constant::Bytes { data, utf8 } => {
                work.text(
                    if *utf8 { "utf8bytes<" } else { "bytes<" },
                    &mut self.output,
                )?;
                self.push(Task::Text(">"), work)?;
                self.push(Task::Bytes(data), work)
            }
            Constant::Aggregate(items) => self.items("{ ", " }", items, work),
            Constant::Array(items) => self.items("array[ ", " ]", items, work),
            Constant::Vector(items) => self.items("vec[ ", " ]", items, work),
            Constant::Sequence(items) => self.items("seq[ ", " ]", items, work),
            Constant::Set(items) => self.items("set{ ", " }", items, work),
            Constant::Splat { elem, len } => {
                work.text("splat[ ", &mut self.output)?;
                self.push(Task::Text(" ]"), work)?;
                self.push(Task::Number(u128::from(*len)), work)?;
                self.push(Task::Text("; "), work)?;
                self.push(Task::Value(elem), work)
            }
            Constant::Record(fields) => {
                work.text("record{ ", &mut self.output)?;
                self.push(Task::Text(" }"), work)?;
                self.push(Task::Fields(fields, true), work)
            }
            Constant::Closure { func, captures } => {
                work.text("closure<func.", &mut self.output)?;
                work.unsigned(u128::from(func.index()), &mut self.output)?;
                if captures.is_empty() {
                    work.text(">{ }", &mut self.output)
                } else {
                    self.items(">{ ", " }", captures, work)
                }
            }
            Constant::FnDef(func) => {
                work.text("fndef<func.", &mut self.output)?;
                work.unsigned(u128::from(func.index()), &mut self.output)?;
                work.text(">", &mut self.output)
            }
            Constant::SymbolAddr { symbol, addend } => {
                work.text("symaddr<", &mut self.output)?;
                work.text(symbol, &mut self.output)?;
                if *addend != 0 {
                    work.text(" + ", &mut self.output)?;
                    work.signed(i128::from(*addend), &mut self.output)?;
                }
                work.text(">", &mut self.output)
            }
            Constant::PhantomData => work.text("phantomdata", &mut self.output),
            Constant::Uninit => work.text("uninit", &mut self.output),
            Constant::Ext(extension) => extension.unreachable(),
            // v70: `tensor_blob<DIGEST>[d0, d1, ..]`, the digest in lower-case hex.
            Constant::TensorBlob { digest, dims } => {
                work.text("tensor_blob<", &mut self.output)?;
                self.push(Task::Text("]"), work)?;
                self.push(Task::Dims(dims, true), work)?;
                self.push(Task::Text(">["), work)?;
                self.push(Task::Bytes(&digest.0), work)
            }
        }
    }
    fn items<O: ExecutionObserver>(
        &mut self,
        start: &'a str,
        end: &'a str,
        items: &'a [Constant],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(start, &mut self.output)?;
        self.push(Task::Text(end), work)?;
        self.push(Task::Items(items, true), work)
    }
    fn bytes<O: ExecutionObserver>(&mut self, bytes: &'a [u8], work: &mut Work<'_, '_, O>) -> R {
        if bytes.is_empty() {
            return Ok(());
        }
        // Fixed <=512 input bytes -> <=1024 lowercase ASCII output bytes.
        let count = bytes.len().min(512);
        work.admit(1024, 1024)?;
        let mut hex = [0u8; 1024];
        for (index, byte) in bytes[..count].iter().enumerate() {
            work.admit(1, 2)?;
            const DIGITS: &[u8; 16] = b"0123456789abcdef";
            hex[index * 2] = DIGITS[(byte >> 4) as usize];
            hex[index * 2 + 1] = DIGITS[(byte & 15) as usize];
        }
        work.admit(count * 2, 0)?;
        let text = core::str::from_utf8(&hex[..count * 2])
            .map_err(|_| ObservedValueError::InvalidRange)?;
        work.text(text, &mut self.output)?;
        self.push(Task::Bytes(&bytes[count..]), work)
    }
    fn retire_tasks<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.tasks.is_empty() {
            work.session.retirement_step(work.site, 1);
            self.tasks.pop();
        }
        work.retire(take(&mut self.tasks));
    }
}
