// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn run<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    ta: &'a Ty,
    b: &'a Module,
    tb: &'a Ty,
    w: &mut Work<'_, '_, O>,
) -> R {
    s.push(Task::Ty(ta, tb), w)?;
    loop {
        w.admit(1 + size_of::<Task<'a>>(), size_of::<Option<Task<'a>>>())?;
        let Some(task) = s.tasks.pop() else {
            return Ok(());
        };
        match task {
            Task::End(key, source) => s.end(key, source, w)?,
            Task::SetAny(ca, cb, direction, row, candidate) => {
                predicates::any(s, ca, cb, direction, row, candidate, w)?
            }
            _ if !s.last => (),
            Task::Ty(ta, tb) => types::pair(s, ta, tb, w)?,
            Task::Id(ta, tb) => {
                w.admit(1, 2 * size_of::<Option<&Ty>>())?;
                match (a.types.get(ta.as_usize()), b.types.get(tb.as_usize())) {
                    (Some(ta_ref), Some(tb_ref)) => {
                        if s.enter((Kind::TyId, ta.index(), tb.index()), None, w)? {
                            s.push(Task::Ty(ta_ref, tb_ref), w)?;
                        }
                    }
                    _ => s.last = false,
                }
            }
            Task::Nominal(kind, left, right) => nominal::pair(s, a, b, kind, left, right, w)?,
            Task::Pred(pa, pb) => predicates::pair(s, a, b, pa, pb, w)?,
            Task::Types(ta, tb) => types::tail(s, ta, tb, w)?,
            Task::Fields(fa, fb) => nominal::fields(s, fa, fb, w)?,
            Task::Variants(va, vb) => nominal::variants(s, va, vb, w)?,
            Task::EnumTail(da, db) => nominal::enum_tail(s, da, db, w)?,
            Task::SetRow(ca, cb, direction, row) => predicates::row(s, ca, cb, direction, row, w)?,
            Task::Constant(ca, cb) => constants::pair(s, ca, cb, w)?,
            Task::Constants(ca, cb) => constants::tail(s, ca, cb, w)?,
            Task::ConstantFields(ca, cb) => constants::fields(s, ca, cb, w)?,
        }
    }
}
