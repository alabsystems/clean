// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn sorts<O: ExecutionObserver>(
        &mut self,
        left: &'a ClauseSort,
        right: &'a ClauseSort,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        // The descriptor is admitted before construction, separately from its
        // actual Vec transport and any requested old/new allocation images.
        work.admit(1, size_of::<Pair<'_>>())?;
        work.push(&mut self.tasks, Pair::Sort(left, right))?;
        loop {
            work.admit(1, size_of::<Option<Pair<'_>>>())?;
            let Some(pair) = self.tasks.pop() else {
                return Ok(true);
            };
            // Fixed exhaustive dispatch and at most three borrowed/scalar
            // continuations before their actual construction below.
            work.admit(7, 3 * size_of::<Pair<'_>>())?;
            match pair {
                Pair::Sort(a, b) => match (a, b) {
                    (ClauseSort::Bool, ClauseSort::Bool)
                    | (ClauseSort::Int, ClauseSort::Int)
                    | (ClauseSort::RoundingMode, ClauseSort::RoundingMode) => {}
                    (ClauseSort::BitVec(a), ClauseSort::BitVec(b)) => {
                        if a != b {
                            return Ok(false);
                        }
                    }
                    (ClauseSort::Float { eb: a, sb: b }, ClauseSort::Float { eb: c, sb: d }) => {
                        if a != c || b != d {
                            return Ok(false);
                        }
                    }
                    (ClauseSort::Array(a, b), ClauseSort::Array(c, d)) => {
                        work.push(&mut self.tasks, Pair::Sort(b, d))?;
                        work.push(&mut self.tasks, Pair::Sort(a, c))?;
                    }
                    (
                        ClauseSort::Datatype {
                            name: a,
                            constructors: b,
                        },
                        ClauseSort::Datatype {
                            name: c,
                            constructors: d,
                        },
                    ) => {
                        if !work.text(a, c)? || b.len() != d.len() {
                            return Ok(false);
                        }
                        work.push(&mut self.tasks, Pair::Ctors(b, d, 0))?;
                    }
                    // Exhaustive on the left: a future tag cannot silently
                    // inherit a different-tag false answer.
                    (
                        ClauseSort::Bool
                        | ClauseSort::Int
                        | ClauseSort::RoundingMode
                        | ClauseSort::BitVec(_)
                        | ClauseSort::Float { .. }
                        | ClauseSort::Array(..)
                        | ClauseSort::Datatype { .. },
                        _,
                    ) => return Ok(false),
                },
                Pair::Ctors(a, b, index) => {
                    if let Some((name, fields)) = work.at(a, index)? {
                        let (other, children) =
                            work.at(b, index)?.ok_or(ObservedValueError::InvalidRange)?;
                        if !work.text(name, other)? || fields.len() != children.len() {
                            return Ok(false);
                        }
                        let mut next = index;
                        work.next(&mut next)?;
                        work.push(&mut self.tasks, Pair::Ctors(a, b, next))?;
                        work.push(&mut self.tasks, Pair::Fields(fields, children, 0))?;
                    }
                }
                Pair::Fields(a, b, index) => {
                    if let Some((name, sort)) = work.at(a, index)? {
                        let (other, child) =
                            work.at(b, index)?.ok_or(ObservedValueError::InvalidRange)?;
                        if !work.text(name, other)? {
                            return Ok(false);
                        }
                        let mut next = index;
                        work.next(&mut next)?;
                        work.push(&mut self.tasks, Pair::Fields(a, b, next))?;
                        work.push(&mut self.tasks, Pair::Sort(sort, child))?;
                    }
                }
            }
        }
    }
}
