// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact non-pretty derived Debug of raw level-R types and function ABI claims.
//! Diagnostic text only. No canonicalization, validation or semantic authority.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::signature_abi::*;
use core::mem::{size_of, take};
// Admit each fixed temporary Task array before its expressions are evaluated.
// Stringify counts syntax at compile time; it never reads or formats input.
macro_rules! scheduled {
    ($state:ident, $work:ident; [$($task:expr),* $(,)?]) => {{
        const COUNT: usize = [$(stringify!($task)),*].len();
        $work.admit(COUNT, COUNT.checked_mul(size_of::<Task<'_>>()).ok_or(ObservedValueError::CapacityOverflow)?)?;
        $state.fields(&[$($task),*], $work)
    }};
}
mod abi;
mod storage;
#[cfg(test)]
mod tests;
mod types;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum List<'a> {
    Types(&'a [Ty]),
    Strings(&'a [String]),
    Arguments(&'a [AbiArgument]),
    Bindings(&'a [AbiBinding]),
    Registers(&'a [AbiRegister]),
}
#[derive(Clone, Copy)]
enum Task<'a> {
    Text(&'static str),
    Quoted(&'a str),
    Num(u128),
    Bool(bool),
    OptNum(Option<u64>),
    Ty(&'a Ty),
    Func(&'a FuncTy),
    Signature(&'a SignatureAbi),
    Argument(&'a AbiArgument),
    Pass(&'a AbiPassMode),
    Register(&'a AbiRegister),
    Scalar(&'a AbiScalar),
    Uniform(&'a AbiUniform),
    Attributes(&'a AbiAttributes),
    Binding(&'a AbiBinding),
    List(List<'a>, bool),
}
#[derive(Default)]
struct State<'a> {
    tasks: Vec<Task<'a>>,
    output: String,
}
impl Ty {
    /// Raw Debug, including malformed nominal strings/IDs. No recursive formatter.
    pub fn debug_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        render(Task::Ty(self), session, site)
    }
}
impl FuncTy {
    /// Complete raw Debug, including every unvalidated ABI field and binding.
    pub fn debug_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        render(Task::Func(self), session, site)
    }
}
fn render<O: ExecutionObserver>(
    task: Task<'_>,
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
    let result = state
        .push(task, &mut work)
        .and_then(|()| state.run(&mut work));
    while !state.tasks.is_empty() {
        work.session
            .retirement_step(site, size_of::<Task<'_>>() + 1);
        state.tasks.pop();
    }
    work.retire(take(&mut state.tasks));
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.output)),
        Err(e) => {
            work.retire(take(&mut state.output));
            Err(work.terminal(e))
        }
    }
}
impl<'a> State<'a> {
    fn push<O: ExecutionObserver>(&mut self, task: Task<'a>, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.tasks)?;
        work.admit(1, size_of::<Task<'_>>())?;
        self.tasks.push(task);
        Ok(())
    }
    fn fields<O: ExecutionObserver>(
        &mut self,
        tasks: &[Task<'a>],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = tasks.len();
        while at > 0 {
            work.admit(1, size_of::<usize>())?;
            at -= 1;
            self.push(tasks[at], work)?;
        }
        Ok(())
    }
    fn run<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        while !self.tasks.is_empty() {
            work.admit(1, size_of::<Task<'_>>())?;
            let Some(task) = self.tasks.pop() else { break };
            match task {
                Task::Text(s) => work.text(s, &mut self.output)?,
                Task::Quoted(s) => work.quoted(s, &mut self.output)?,
                Task::Num(n) => work.number(n, &mut self.output)?,
                Task::Bool(v) => work.text(if v { "true" } else { "false" }, &mut self.output)?,
                Task::OptNum(n) => match n {
                    None => work.text("None", &mut self.output)?,
                    Some(n) => scheduled!(self, work; [
                        Task::Text("Some("),
                        Task::Num(u128::from(n)),
                        Task::Text(")"),
                    ])?,
                },
                Task::Ty(t) => self.ty(t, work)?,
                Task::Func(f) => self.function(f, work)?,
                Task::Signature(s) => self.signature(s, work)?,
                Task::Argument(a) => self.argument(a, work)?,
                Task::Pass(a) => self.pass(a, work)?,
                Task::Register(a) => self.register(a, work)?,
                Task::Scalar(a) => self.scalar(a, work)?,
                Task::Uniform(a) => self.uniform(a, work)?,
                Task::Attributes(a) => self.attributes(a, work)?,
                Task::Binding(a) => self.binding(a, work)?,
                Task::List(rows, first) => self.list(rows, first, work)?,
            }
        }
        Ok(())
    }
    fn list<O: ExecutionObserver>(
        &mut self,
        rows: List<'a>,
        first: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<List<'_>>())?;
        macro_rules! item {
            ($r:expr,$kind:ident,$task:ident) => {
                if let Some((head, tail)) = $r.split_first() {
                    if !first {
                        work.text(", ", &mut self.output)?;
                    }
                    self.push(Task::List(List::$kind(tail), false), work)?;
                    self.push(Task::$task(head), work)?;
                }
            };
        }
        match rows {
            List::Types(r) => item!(r, Types, Ty),
            List::Strings(r) => item!(r, Strings, Quoted),
            List::Arguments(r) => item!(r, Arguments, Argument),
            List::Bindings(r) => item!(r, Bindings, Binding),
            List::Registers(r) => item!(r, Registers, Register),
        }
        Ok(())
    }
}
