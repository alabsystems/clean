// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn pair<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Module,
    b: &'a Module,
    pa: PredId,
    pb: PredId,
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(
        1 + 2 * size_of::<Pred>() + 2 * size_of::<Universe>(),
        2 * size_of::<Option<&Pred>>(),
    )?;
    let (Some(ra), Some(rb)) = (
        a.predicates.get(pa.as_usize()),
        b.predicates.get(pb.as_usize()),
    ) else {
        s.last = false;
        return Ok(());
    };
    if !s.enter((Kind::Pred, pa.index(), pb.index()), None, w)? {
        return Ok(());
    }
    if tag(ra) != tag(rb) {
        s.last = false;
        return Ok(());
    }
    match (ra, rb) {
        (Pred::Interval { lo: a, hi: ha }, Pred::Interval { lo: b, hi: hb }) => {
            s.last = a == b && ha == hb
        }
        (Pred::FiniteSet(a), Pred::FiniteSet(b)) => s.push(Task::Constants(a, b), w)?,
        (Pred::InUniverse(ua, sa), Pred::InUniverse(ub, sb)) => {
            s.last = sa == sb;
            if s.last {
                w.admit(1, 2 * size_of::<Option<&Universe>>())?;
                match (
                    a.universes.get(ua.as_usize()),
                    b.universes.get(ub.as_usize()),
                ) {
                    (
                        Some(Universe::IntRange { lo: a, hi: ha }),
                        Some(Universe::IntRange { lo: b, hi: hb }),
                    ) => s.last = a == b && ha == hb,
                    (Some(Universe::Members(a)), Some(Universe::Members(b))) => {
                        s.push(Task::Constants(a, b), w)?
                    }
                    _ => s.last = false,
                }
            }
        }
        (Pred::NonZero, Pred::NonZero)
        | (Pred::NonNull, Pred::NonNull)
        | (Pred::Top, Pred::Top)
        | (Pred::Bottom, Pred::Bottom) => (),
        (Pred::Conj(a), Pred::Conj(b)) | (Pred::Disj(a), Pred::Disj(b)) => {
            s.last = a.len() == b.len();
            if s.last {
                s.push(Task::SetRow(a, b, Direction::Forward, 0), w)?;
            }
        }
        _ => s.last = false,
    }
    Ok(())
}
pub(super) fn row<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a [PredId],
    b: &'a [PredId],
    direction: Direction,
    row: usize,
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(1, size_of::<usize>())?;
    let count = match direction {
        Direction::Forward => a.len(),
        Direction::Reverse => b.len(),
    };
    if row == count {
        if matches!(direction, Direction::Forward) {
            s.push(Task::SetRow(a, b, Direction::Reverse, 0), w)?;
        }
    } else {
        s.push(Task::SetAny(a, b, direction, row, 0), w)?;
        s.last = false;
    }
    Ok(())
}
pub(super) fn any<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a [PredId],
    b: &'a [PredId],
    direction: Direction,
    row: usize,
    candidate: usize,
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(
        1 + 2 * size_of::<PredId>(),
        2 * size_of::<Option<&PredId>>(),
    )?;
    if s.last {
        let next = row
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        return s.push(Task::SetRow(a, b, direction, next), w);
    }
    let pair = match direction {
        Direction::Forward => (a.get(row), b.get(candidate)),
        Direction::Reverse => (a.get(candidate), b.get(row)),
    };
    if let (Some(x), Some(y)) = pair {
        let next = candidate
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        s.push(Task::SetAny(a, b, direction, row, next), w)?;
        s.push(Task::Pred(*x, *y), w)?;
        s.last = true;
    }
    Ok(())
}

fn tag(value: &Pred) -> u8 {
    match value {
        Pred::Interval { .. } => 0,
        Pred::FiniteSet(_) => 1,
        Pred::InUniverse(..) => 2,
        Pred::NonZero => 3,
        Pred::NonNull => 4,
        Pred::Conj(_) => 5,
        Pred::Disj(_) => 6,
        Pred::Top => 7,
        Pred::Bottom => 8,
    }
}
