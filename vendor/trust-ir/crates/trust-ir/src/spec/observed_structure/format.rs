// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
pub(super) enum Task<'a> {
    Sort(&'a ClauseSort),
    Text(&'static str),
    Ctors(&'a [(String, Vec<(String, ClauseSort)>)], usize),
    Fields(&'a [(String, ClauseSort)], usize),
}
impl<'a> State<'a> {
    pub(super) fn sort_text<O: ExecutionObserver>(
        &mut self,
        sort: sorts::Sort<'a>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let sorts::Sort::Fixed(sort) = sort {
            return fixed(sort, &mut self.detail, work);
        }
        let sorts::Sort::Borrowed(sort) = sort else {
            return Err(ObservedValueError::InvalidRange);
        };
        let result = (|| {
            work.admit(1, 0)?;
            if self.format.capacity() != 0 {
                return Err(ObservedValueError::InvalidRange);
            }
            work.admit(1, size_of::<Task<'_>>())?;
            work.push(&mut self.format, Task::Sort(sort))?;
            loop {
                work.admit(1, size_of::<Option<Task<'_>>>())?;
                let Some(task) = self.format.pop() else { break };
                // Fixed dispatch/transport before actual shape reads and up to
                // four borrowed task headers; real Vec growth is separate.
                work.admit(8, 4 * size_of::<Task<'_>>())?;
                match task {
                    Task::Text(text) => work.text(text, &mut self.detail)?,
                    Task::Sort(sort) => match sort {
                        ClauseSort::Bool => work.text("Bool", &mut self.detail)?,
                        ClauseSort::Int => work.text("Int", &mut self.detail)?,
                        ClauseSort::RoundingMode => work.text("RoundingMode", &mut self.detail)?,
                        ClauseSort::BitVec(width) => {
                            work.text("BitVec(", &mut self.detail)?;
                            work.number(u128::from(*width), &mut self.detail)?;
                            work.text(")", &mut self.detail)?;
                        }
                        ClauseSort::Float { eb, sb } => {
                            work.text("Float { eb: ", &mut self.detail)?;
                            work.number(u128::from(*eb), &mut self.detail)?;
                            work.text(", sb: ", &mut self.detail)?;
                            work.number(u128::from(*sb), &mut self.detail)?;
                            work.text(" }", &mut self.detail)?;
                        }
                        ClauseSort::Array(index, value) => {
                            work.text("Array(", &mut self.detail)?;
                            work.push(&mut self.format, Task::Text(")"))?;
                            work.push(&mut self.format, Task::Sort(value))?;
                            work.push(&mut self.format, Task::Text(", "))?;
                            work.push(&mut self.format, Task::Sort(index))?;
                        }
                        ClauseSort::Datatype { name, constructors } => {
                            work.text("Datatype { name: ", &mut self.detail)?;
                            work.quoted(name, &mut self.detail)?;
                            work.text(", constructors: ", &mut self.detail)?;
                            work.push(&mut self.format, Task::Text(" }"))?;
                            work.push(&mut self.format, Task::Ctors(constructors, 0))?;
                        }
                    },
                    Task::Ctors(rows, index) => {
                        if index == 0 {
                            work.text("[", &mut self.detail)?;
                        }
                        if let Some((name, fields)) = work.at(rows, index)? {
                            if index > 0 {
                                work.text(", ", &mut self.detail)?;
                            }
                            work.text("(", &mut self.detail)?;
                            work.quoted(name, &mut self.detail)?;
                            work.text(", ", &mut self.detail)?;
                            let mut next = index;
                            work.next(&mut next)?;
                            work.push(&mut self.format, Task::Ctors(rows, next))?;
                            work.push(&mut self.format, Task::Text(")"))?;
                            work.push(&mut self.format, Task::Fields(fields, 0))?;
                        } else {
                            work.text("]", &mut self.detail)?;
                        }
                    }
                    Task::Fields(rows, index) => {
                        if index == 0 {
                            work.text("[", &mut self.detail)?;
                        }
                        if let Some((name, sort)) = work.at(rows, index)? {
                            if index > 0 {
                                work.text(", ", &mut self.detail)?;
                            }
                            work.text("(", &mut self.detail)?;
                            work.quoted(name, &mut self.detail)?;
                            work.text(", ", &mut self.detail)?;
                            let mut next = index;
                            work.next(&mut next)?;
                            work.push(&mut self.format, Task::Fields(rows, next))?;
                            work.push(&mut self.format, Task::Text(")"))?;
                            work.push(&mut self.format, Task::Sort(sort))?;
                        } else {
                            work.text("]", &mut self.detail)?;
                        }
                    }
                }
            }
            Ok(())
        })();
        work.retire_fixed_vec(&mut self.format);
        result.map_err(|error| work.terminal(error))?;
        work.admit(1, 0)
    }
}
fn fixed<O: ExecutionObserver>(
    sort: sorts::Fixed,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(3, size_of::<sorts::Fixed>())?;
    match sort {
        sorts::Fixed::Bool => work.text("Bool", out),
        sorts::Fixed::Int => work.text("Int", out),
        sorts::Fixed::BitVec(width) => {
            work.text("BitVec(", out)?;
            work.number(u128::from(width), out)?;
            work.text(")", out)
        }
    }
}
pub(super) fn place<O: ExecutionObserver>(
    place: ClausePlace,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(11, size_of::<ClausePlace>())?;
    let (name, index) = match place {
        ClausePlace::Param { index } => ("Param", Some(index)),
        ClausePlace::ResultSlot { index } => ("ResultSlot", Some(index)),
        ClausePlace::MutParamExit { index } => ("MutParamExit", Some(index)),
        ClausePlace::SpecVar { index } => ("SpecVar", Some(index)),
        ClausePlace::SpecVarNext { index } => ("SpecVarNext", Some(index)),
        ClausePlace::ParamPointeeEntry { index } => ("ParamPointeeEntry", Some(index)),
        ClausePlace::World => ("World", None),
        ClausePlace::Unwind => ("Unwind", None),
        ClausePlace::WorldPre => ("WorldPre", None),
        ClausePlace::WorldPost => ("WorldPost", None),
        ClausePlace::Value(id) => {
            work.text("Value(ValueId(", out)?;
            work.number(u128::from(id.index()), out)?;
            return work.text("))", out);
        }
    };
    work.text(name, out)?;
    if let Some(index) = index {
        work.text(" { index: ", out)?;
        work.number(u128::from(index), out)?;
        work.text(" }", out)?;
    }
    Ok(())
}
