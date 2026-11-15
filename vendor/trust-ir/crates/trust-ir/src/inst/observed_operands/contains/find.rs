// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use plan::Plan;
pub(super) fn in_plan<O: ExecutionObserver>(
    plan: Plan<'_>,
    needle: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<bool>())?;
    match plan {
        Plan::Empty => Ok(false),
        Plan::One(a) => one(a, needle, work),
        Plan::Two(a, b) => Ok(one(a, needle, work)? || one(b, needle, work)?),
        Plan::Three(a, b, c) => {
            Ok(one(a, needle, work)? || one(b, needle, work)? || one(c, needle, work)?)
        }
        Plan::Optional(value) => {
            work.admit(1, size_of::<ValueId>())?;
            match value {
                Some(value) => one(*value, needle, work),
                None => Ok(false),
            }
        }
        Plan::Lists {
            prefix,
            first,
            second,
        } => {
            work.admit(1, size_of::<Option<ValueId>>())?;
            if let Some(value) = prefix
                && one(value, needle, work)?
            {
                return Ok(true);
            }
            Ok(list(first, needle, work)? || list(second, needle, work)?)
        }
        Plan::Branch {
            condition,
            first,
            second,
        } => Ok(one(condition, needle, work)?
            || list(first, needle, work)?
            || list(second, needle, work)?),
        Plan::Switch {
            selector,
            default,
            cases,
        } => {
            if one(selector, needle, work)? || list(default, needle, work)? {
                return Ok(true);
            }
            let mut at = 0;
            loop {
                work.admit(1, size_of::<Option<&SwitchCase>>())?;
                let Some(case) = cases.get(at) else {
                    return Ok(false);
                };
                if list(&case.args, needle, work)? {
                    return Ok(true);
                }
                next(&mut at, work)?;
            }
        }
        Plan::Assert {
            condition,
            kind,
            site,
            normal,
        } => Ok(one(condition, needle, work)?
            || assertion(kind, site, needle, work)?
            || list(normal, needle, work)?),
    }
}
fn one<O: ExecutionObserver>(
    value: ValueId,
    needle: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, 2 * size_of::<ValueId>())?;
    Ok(value == needle)
}
fn next<O: ExecutionObserver>(at: &mut usize, work: &mut Work<'_, '_, O>) -> R {
    work.admit(1, size_of::<usize>())?;
    *at = at
        .checked_add(1)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    Ok(())
}
fn list<O: ExecutionObserver>(
    source: &[ValueId],
    needle: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut at = 0;
    loop {
        work.admit(1, size_of::<Option<&ValueId>>())?;
        let Some(value) = source.get(at) else {
            return Ok(false);
        };
        if one(*value, needle, work)? {
            return Ok(true);
        }
        next(&mut at, work)?;
    }
}
fn assertion<O: ExecutionObserver>(
    kind: &AssertKind,
    site: Option<&PanicSite>,
    needle: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(4, size_of::<AssertKind>())?;
    let found = match kind {
        AssertKind::BoundsCheck { index, len } => {
            one(*index, needle, work)? || one(*len, needle, work)?
        }
        AssertKind::MisalignedPtr { required, found } => {
            one(*required, needle, work)? || one(*found, needle, work)?
        }
        AssertKind::Unspecified
        | AssertKind::Overflow(_)
        | AssertKind::DivByZero
        | AssertKind::RemByZero
        | AssertKind::NullPtr => false,
    };
    if found {
        return Ok(true);
    }
    work.admit(
        1,
        size_of::<Option<&PanicSite>>() + size_of::<PanicLocation>(),
    )?;
    match site {
        Some(site) => match site.location {
            PanicLocation::Value(value) => one(value, needle, work),
            PanicLocation::Global(_) => Ok(false),
        },
        None => Ok(false),
    }
}
