// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use core::cmp::Ordering;

#[derive(Clone, Copy)]
pub(super) enum Key<'a> {
    Fn(&'a FnShape),
    DynMethod {
        principal: PrincipalKey,
        method: MethodKey,
    },
    DynDrop(PrincipalKey),
}

#[derive(Clone, Copy)]
pub(super) struct Row<'a> {
    pub(super) member: ReachNode,
    pub(super) key: Key<'a>,
    pub(super) confined: bool,
}

impl<'a> Key<'a> {
    pub(super) fn of(key: &'a PoolKey) -> Self {
        match key {
            PoolKey::Fn(shape) => Self::Fn(shape),
            PoolKey::DynMethod { principal, method } => Self::DynMethod {
                principal: *principal,
                method: *method,
            },
            PoolKey::DynDrop(principal) => Self::DynDrop(*principal),
        }
    }

    pub(super) fn principal(self) -> Option<PrincipalKey> {
        match self {
            Self::Fn(_) => None,
            Self::DynMethod { principal, .. } | Self::DynDrop(principal) => Some(principal),
        }
    }

    pub(super) fn with_principal(self, principal: PrincipalKey) -> Self {
        match self {
            Self::Fn(shape) => Self::Fn(shape),
            Self::DynMethod { method, .. } => Self::DynMethod { principal, method },
            Self::DynDrop(_) => Self::DynDrop(principal),
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Fn(_) => 0,
            Self::DynMethod { .. } => 1,
            Self::DynDrop(_) => 2,
        }
    }
}

pub(super) fn compare<O: ExecutionObserver>(
    left: Key<'_>,
    right: Key<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<Ordering> {
    admit(session, site, 1, 0)?;
    let tag = left.tag().cmp(&right.tag());
    if tag != Ordering::Equal {
        return Ok(tag);
    }
    match (left, right) {
        (Key::Fn(left), Key::Fn(right)) => compare_shape(left, right, session, site),
        (
            Key::DynMethod {
                principal: lp,
                method: lm,
            },
            Key::DynMethod {
                principal: rp,
                method: rm,
            },
        ) => Ok((lp, lm).cmp(&(rp, rm))),
        (Key::DynDrop(left), Key::DynDrop(right)) => Ok(left.cmp(&right)),
        _ => Err(ObservedValueError::InvalidRange),
    }
}

fn compare_shape<O: ExecutionObserver>(
    left: &FnShape,
    right: &FnShape,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<Ordering> {
    admit(session, site, 1, 0)?;
    let prefix = (left.abi, left.variadic).cmp(&(right.abi, right.variadic));
    if prefix != Ordering::Equal {
        return Ok(prefix);
    }
    let (left, right) = match (&left.params, &right.params) {
        (None, None) => return Ok(Ordering::Equal),
        (None, Some(_)) => return Ok(Ordering::Less),
        (Some(_), None) => return Ok(Ordering::Greater),
        (Some(left), Some(right)) => (left, right),
    };
    for (left, right) in left.iter().zip(right) {
        admit(session, site, 1, 0)?;
        let comparison = left.cmp(right);
        if comparison != Ordering::Equal {
            return Ok(comparison);
        }
    }
    admit(session, site, 1, 0)?;
    Ok(left.len().cmp(&right.len()))
}

pub(super) fn copy_key<O: ExecutionObserver>(
    key: Key<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<PoolKey> {
    admit(session, site, 1, size_of::<PoolKey>())?;
    Ok(match key {
        Key::Fn(shape) => PoolKey::Fn(copy_shape(shape, session, site)?),
        Key::DynMethod { principal, method } => PoolKey::DynMethod { principal, method },
        Key::DynDrop(principal) => PoolKey::DynDrop(principal),
    })
}

fn copy_shape<O: ExecutionObserver>(
    shape: &FnShape,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<FnShape> {
    let params = if let Some(source) = &shape.params {
        let mut values = Vec::new();
        for value in source {
            if let Err(error) = push(&mut values, *value, session, site) {
                retire_vec(&mut values, session, site);
                return if session.first_refusal().is_some() {
                    Err(ObservedValueError::AdmissionRefused)
                } else {
                    Err(error)
                };
            }
        }
        Some(values)
    } else {
        None
    };
    Ok(FnShape {
        abi: shape.abi,
        variadic: shape.variadic,
        params,
    })
}

pub(super) fn copy_carried<O: ExecutionObserver>(
    key: &CarriedKey,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<CarriedKey> {
    admit(session, site, 1, size_of::<CarriedKey>())?;
    Ok(match key {
        CarriedKey::Key(key) => CarriedKey::Key(copy_key(Key::of(key), session, site)?),
        CarriedKey::Principal(value) => CarriedKey::Principal(*value),
        CarriedKey::AnyFn => CarriedKey::AnyFn,
        CarriedKey::AnyDyn => CarriedKey::AnyDyn,
        CarriedKey::Any => CarriedKey::Any,
        CarriedKey::Untyped => CarriedKey::Untyped,
        CarriedKey::Laundered => CarriedKey::Laundered,
    })
}
