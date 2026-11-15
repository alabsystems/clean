// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use plan::Plan;

pub(super) fn collect<O: ExecutionObserver>(
    plan: Plan<'_>,
    values: &mut Vec<ValueId>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, 0)?;
    match plan {
        Plan::Empty => Ok(()),
        Plan::One(value) => work.push(values, value),
        Plan::Two(first, second) => {
            work.push(values, first)?;
            work.push(values, second)
        }
        Plan::Three(first, second, third) => {
            work.push(values, first)?;
            work.push(values, second)?;
            work.push(values, third)
        }
        Plan::Optional(value) => {
            work.admit(1, 0)?;
            if let Some(value) = value {
                work.push(values, *value)?;
            }
            Ok(())
        }
        Plan::Lists {
            prefix,
            first,
            second,
        } => {
            work.admit(1, 0)?;
            if let Some(value) = prefix {
                work.push(values, value)?;
            }
            list(first, values, work)?;
            list(second, values, work)
        }
        Plan::Branch {
            condition,
            first,
            second,
        } => {
            work.push(values, condition)?;
            list(first, values, work)?;
            list(second, values, work)
        }
        Plan::Switch {
            selector,
            default,
            cases,
        } => {
            work.push(values, selector)?;
            list(default, values, work)?;
            let mut index = 0;
            while index < cases.len() {
                // Even a case with no operands performs an actual outer
                // iteration; it must not evade the original work budget.
                work.admit(1, 0)?;
                list(&cases[index].args, values, work)?;
                index += 1;
            }
            Ok(())
        }
        Plan::Assert {
            condition,
            kind,
            site,
            normal,
        } => {
            work.push(values, condition)?;
            assertion(kind, site, values, work)?;
            list(normal, values, work)
        }
    }
}

fn list<O: ExecutionObserver>(
    source: &[ValueId],
    values: &mut Vec<ValueId>,
    work: &mut Work<'_, '_, O>,
) -> R {
    let mut index = 0;
    loop {
        work.admit(1, 0)?;
        if index == source.len() {
            return Ok(());
        }
        work.push(values, source[index])?;
        index += 1;
    }
}

fn assertion<O: ExecutionObserver>(
    kind: &AssertKind,
    site: Option<&PanicSite>,
    values: &mut Vec<ValueId>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, 0)?;
    // Explicit fixed metadata inventory, not an opaque operands() visitor.
    match kind {
        AssertKind::BoundsCheck { index, len } => {
            work.push(values, *index)?;
            work.push(values, *len)?;
        }
        AssertKind::MisalignedPtr { required, found } => {
            work.push(values, *required)?;
            work.push(values, *found)?;
        }
        AssertKind::Unspecified
        | AssertKind::Overflow(_)
        | AssertKind::DivByZero
        | AssertKind::RemByZero
        | AssertKind::NullPtr => {}
    }
    work.admit(1, 0)?;
    if let Some(site) = site {
        work.admit(1, 0)?;
        match site.location {
            PanicLocation::Value(value) => work.push(values, value)?,
            PanicLocation::Global(_) => {}
        }
    }
    Ok(())
}
