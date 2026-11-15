// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual iterative level-R cloning, retaining partial ownership on refusal.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
mod build;
mod storage;
#[cfg(test)]
mod tests;
type R<T = ()> = Result<T, ObservedValueError>;
use storage::Work;

#[derive(Default)]
struct State<'a> {
    tasks: Vec<Task<'a>>,
    values: Vec<Ty>,
    tuple: Vec<Ty>,
    first: String,
    second: String,
    output: Option<Ty>,
}
enum Task<'a> {
    Visit(&'a Ty),
    Tail(&'a [Ty]),
    Box(&'a Ty),
    Tuple(usize),
}

impl Ty {
    /// Clone the complete exact type using the caller's original session/site.
    /// Every actual child, allocation request and bounded string copy is
    /// observed; partial owned trees retire without recursive type Drop.
    /// A successful output remains caller-owned. Logical prepayment does not
    /// make allocator allocation/deallocation latency or physical OOM bounded.
    pub fn clone_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut work = Work { session, site };
        let mut state = State::default();
        let result = state.run(self, &mut work);
        state.retire_scratch(&mut work);
        let result = result.and_then(|()| work.publication());
        match result {
            Ok(()) => state.output.take().ok_or(ObservedValueError::InvalidRange),
            Err(error) => {
                if let Some(output) = state.output.take() {
                    observed_retirement::retire_type(output, work.session, site);
                }
                Err(work.terminal(error))
            }
        }
    }
}
impl<'a> State<'a> {
    fn run<O: ExecutionObserver>(&mut self, root: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        self.task(Task::Visit(root), work)?;
        while !self.tasks.is_empty() {
            work.admit(1, 0)?;
            let Some(task) = self.tasks.pop() else { break };
            match task {
                Task::Visit(ty) => self.visit(ty, work)?,
                Task::Tail(children) => {
                    if let Some((head, tail)) = children.split_first() {
                        if !tail.is_empty() {
                            self.task(Task::Tail(tail), work)?;
                        }
                        self.task(Task::Visit(head), work)?;
                    }
                }
                Task::Box(parent) => self.boxed(parent, work)?,
                Task::Tuple(count) => self.tuple(count, work)?,
            }
        }
        work.admit(1, size_of::<Ty>())?;
        if self.values.len() != 1 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.output = self.values.pop();
        Ok(())
    }
    fn task<O: ExecutionObserver>(&mut self, task: Task<'a>, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.tasks, 1)?;
        work.admit(1, size_of::<Task<'_>>())?;
        self.tasks.push(task);
        Ok(())
    }
    fn output_slot<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.values, 1)?;
        work.admit(1, size_of::<Ty>())
    }
    fn visit<O: ExecutionObserver>(&mut self, ty: &'a Ty, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        match ty {
            Ty::Tuple(children) => {
                self.task(Task::Tuple(children.len()), work)?;
                self.task(Task::Tail(children), work)
            }
            Ty::Vector(child, _)
            | Ty::Tensor(child, _)
            | Ty::Ref(child)
            | Ty::RefMut(child)
            | Ty::PtrConst(child)
            | Ty::PtrMut(child)
            | Ty::Rc(child) => {
                self.task(Task::Box(ty), work)?;
                self.task(Task::Visit(child), work)
            }
            Ty::Dialect(value) => self.dialect(value, work),
            Ty::Handle(value) => self.handle(value, work),
            _ => {
                self.output_slot(work)?;
                self.values.push(leaf(ty)?);
                Ok(())
            }
        }
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while let Some(value) = self.values.pop() {
            observed_retirement::retire_type(value, work.session, work.site);
        }
        while let Some(value) = self.tuple.pop() {
            observed_retirement::retire_type(value, work.session, work.site);
        }
        work.retire(core::mem::take(&mut self.tasks));
        work.retire(core::mem::take(&mut self.values));
        work.retire(core::mem::take(&mut self.tuple));
        work.retire(core::mem::take(&mut self.first));
        work.retire(core::mem::take(&mut self.second));
    }
}

// Exhaustive: no derived Clone or recursive equality is used for any leaf.
fn leaf(ty: &Ty) -> R<Ty> {
    Ok(match ty {
        Ty::Storage(layout) => Ty::Storage(*layout),
        Ty::I8 => Ty::I8,
        Ty::I16 => Ty::I16,
        Ty::I32 => Ty::I32,
        Ty::I64 => Ty::I64,
        Ty::I128 => Ty::I128,
        Ty::U8 => Ty::U8,
        Ty::U16 => Ty::U16,
        Ty::U32 => Ty::U32,
        Ty::U64 => Ty::U64,
        Ty::U128 => Ty::U128,
        Ty::Isize => Ty::Isize,
        Ty::Usize => Ty::Usize,
        Ty::Char => Ty::Char,
        Ty::Error => Ty::Error,
        Ty::F16 => Ty::F16,
        Ty::F32 => Ty::F32,
        Ty::F64 => Ty::F64,
        Ty::Bool => Ty::Bool,
        Ty::Ptr => Ty::Ptr,
        Ty::Unit => Ty::Unit,
        Ty::Never => Ty::Never,
        Ty::FatPtr(kind) => Ty::FatPtr(*kind),
        Ty::Struct(id) => Ty::Struct(*id),
        Ty::Array(id, len) => Ty::Array(*id, *len),
        Ty::Enum(id) => Ty::Enum(*id),
        Ty::Func(id) => Ty::Func(*id),
        Ty::Set(id, repr) => Ty::Set(*id, *repr),
        Ty::Sequence(id) => Ty::Sequence(*id),
        Ty::Record(id) => Ty::Record(*id),
        Ty::Closure(id) => Ty::Closure(*id),
        Ty::Refine(id, pred) => Ty::Refine(*id, *pred),
        Ty::Ext(extension) => extension.unreachable(),
        Ty::Tuple(_)
        | Ty::Vector(_, _)
        | Ty::Tensor(_, _)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Dialect(_)
        | Ty::Handle(_) => return Err(ObservedValueError::InvalidRange),
    })
}
