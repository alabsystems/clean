// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        table: &PredTable<'a>,
        id: PredId,
        expected: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.push(&mut self.tasks, Task::Pred(id, 0))?;
        loop {
            work.admit(1, size_of::<Option<Task<'_>>>())?;
            let Some(task) = self.tasks.pop() else { break };
            work.admit(8, size_of::<Task<'_>>())?;
            if !self.task(task, table, expected, work)? {
                return Ok(false);
            }
        }
        work.admit(1, 2 * size_of::<usize>())?;
        Ok(self.cursor == expected.len())
    }
    pub(super) fn task<O: ExecutionObserver>(
        &mut self,
        task: Task<'a>,
        table: &PredTable<'a>,
        expected: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        match task {
            Task::Text(value) => text(expected, &mut self.cursor, value, work),
            Task::Signed(value) => {
                work.admit(3, size_of::<u128>() + size_of::<bool>())?;
                if value < 0 && !text(expected, &mut self.cursor, "-", work)? {
                    return Ok(false);
                }
                self.number(value.unsigned_abs(), expected, work)
            }
            Task::Unsigned(value) => self.number(value, expected, work),
            Task::Constant(value) => {
                work.admit(1, size_of::<Option<String>>())?;
                if self.pending.is_some() {
                    return Err(ObservedValueError::InvalidRange);
                }
                // Full returned child text is retained before comparison/cleanup.
                // FiniteSet's special bool key spells the same true/false as
                // ordinary Constant Display; no other key has that bool tag.
                self.pending = Some(value.display_observed(work.session, work.site)?);
                let answer = text(
                    expected,
                    &mut self.cursor,
                    self.pending
                        .as_deref()
                        .ok_or(ObservedValueError::InvalidRange)?,
                    work,
                )?;
                self.retire_pending(work);
                work.admit(1, size_of::<bool>())?;
                Ok(answer)
            }
            Task::Children(children, at, depth) => {
                if let Some(child) = work.at(children, at)? {
                    if at > 0 && !text(expected, &mut self.cursor, " ", work)? {
                        return Ok(false);
                    }
                    let mut next = at;
                    work.next(&mut next)?;
                    work.admit(1, size_of::<u32>())?;
                    let child_depth = depth
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    work.push(&mut self.tasks, Task::Children(children, next, depth))?;
                    work.push(&mut self.tasks, Task::Pred(*child, child_depth))?;
                    Ok(true)
                } else {
                    text(expected, &mut self.cursor, ")", work)
                }
            }
            Task::Members(items, at) => {
                if let Some(value) = work.at(items, at)? {
                    if at > 0 && !text(expected, &mut self.cursor, " ", work)? {
                        return Ok(false);
                    }
                    if !text(expected, &mut self.cursor, "(= self ", work)? {
                        return Ok(false);
                    }
                    let mut next = at;
                    work.next(&mut next)?;
                    work.push(&mut self.tasks, Task::Members(items, next))?;
                    work.push(&mut self.tasks, Task::Text(")"))?;
                    work.push(&mut self.tasks, Task::Constant(value))?;
                    Ok(true)
                } else {
                    text(expected, &mut self.cursor, ")", work)
                }
            }
            Task::Pred(id, depth) => {
                work.admit(1, size_of::<u32>())?;
                if depth > MAX_PRED_DEPTH {
                    return Ok(false);
                }
                work.admit(1, size_of::<Option<&Pred>>())?;
                let Some(value) = table.pred(id) else {
                    return Ok(false);
                };
                self.predicate(value, depth, table, expected, work)
            }
        }
    }
    fn predicate<O: ExecutionObserver>(
        &mut self,
        value: &'a Pred,
        depth: u32,
        table: &PredTable<'a>,
        expected: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(9, size_of::<PredId>() + size_of::<Space>())?;
        match value {
            Pred::Interval { lo, hi } => self.range(*lo, *hi, work),
            Pred::FiniteSet(items) => {
                if !text(expected, &mut self.cursor, "(or ", work)? {
                    return Ok(false);
                }
                work.push(&mut self.tasks, Task::Members(items, 0))?;
                Ok(true)
            }
            Pred::InUniverse(id, space) => {
                work.admit(1, size_of::<Option<&Universe>>())?;
                let Some(universe) = table.universe(*id) else {
                    return Ok(false);
                };
                match space {
                    Space::Member => match universe {
                        Universe::IntRange { lo, hi } => self.range(*lo, *hi, work),
                        Universe::Members(items) => {
                            if !text(expected, &mut self.cursor, "(or ", work)? {
                                return Ok(false);
                            }
                            work.push(&mut self.tasks, Task::Members(items, 0))?;
                            Ok(true)
                        }
                    },
                    Space::Index => {
                        let Some(cardinality) = cardinality::cardinality(universe, work)? else {
                            return Ok(false);
                        };
                        if !text(
                            expected,
                            &mut self.cursor,
                            "(and (<= 0 self) (< self ",
                            work,
                        )? {
                            return Ok(false);
                        }
                        work.push(&mut self.tasks, Task::Text("))"))?;
                        work.push(&mut self.tasks, Task::Unsigned(cardinality))?;
                        Ok(true)
                    }
                }
            }
            Pred::NonZero => text(expected, &mut self.cursor, "(not (= self 0))", work),
            Pred::NonNull => text(expected, &mut self.cursor, "(not (= self null))", work),
            Pred::Conj(children) | Pred::Disj(children) => {
                let head = if matches!(value, Pred::Conj(_)) {
                    "(and "
                } else {
                    "(or "
                };
                if !text(expected, &mut self.cursor, head, work)? {
                    return Ok(false);
                }
                work.push(&mut self.tasks, Task::Children(children, 0, depth))?;
                Ok(true)
            }
            Pred::Top => text(expected, &mut self.cursor, "true", work),
            Pred::Bottom => text(expected, &mut self.cursor, "false", work),
        }
    }
    fn range<O: ExecutionObserver>(
        &mut self,
        lo: i128,
        hi: i128,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(5, 5 * size_of::<Task<'_>>())?;
        for task in [
            Task::Text("))"),
            Task::Signed(hi),
            Task::Text(" self) (<= self "),
            Task::Signed(lo),
            Task::Text("(and (<= "),
        ] {
            work.push(&mut self.tasks, task)?;
        }
        Ok(true)
    }
    fn number<O: ExecutionObserver>(
        &mut self,
        mut value: u128,
        expected: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(40, 40 + 2 * size_of::<usize>())?;
        let mut digits = [0u8; 40];
        let mut begin = digits.len();
        loop {
            work.admit(3, 1)?;
            begin = begin
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            digits[begin] =
                b'0' + u8::try_from(value % 10).map_err(|_| ObservedValueError::InvalidRange)?;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        work.admit(40, size_of::<&str>())?;
        let value =
            core::str::from_utf8(&digits[begin..]).map_err(|_| ObservedValueError::InvalidRange)?;
        text(expected, &mut self.cursor, value, work)
    }
}
