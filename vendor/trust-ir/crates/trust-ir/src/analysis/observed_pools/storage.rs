// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    bytes: usize,
) -> Observed {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Reachability,
            site,
            work,
            copy_bytes: bytes,
        })
        .map_err(Into::into)
}

pub(super) fn lookup<O: ExecutionObserver>(
    count: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed {
    admit(session, site, observed_btree::population_work(count)?, 0)
}

pub(super) fn tree_growth<K, V, O: ExecutionObserver>(
    count: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed {
    let cost = observed_btree::insertion_cost::<K, V>(count)?;
    admit(session, site, cost.work, cost.copy_bytes)
}

pub(super) fn insert<K: Copy + Ord, O: ExecutionObserver>(
    set: &mut BTreeSet<K>,
    key: K,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<bool> {
    lookup(set.len(), session, site)?;
    if set.contains(&key) {
        return Ok(false);
    }
    tree_growth::<K, (), O>(set.len(), session, site)?;
    Ok(set.insert(key))
}

pub(super) fn contains<K: Ord, O: ExecutionObserver>(
    set: &BTreeSet<K>,
    key: &K,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<bool> {
    lookup(set.len(), session, site)?;
    Ok(set.contains(key))
}

pub(super) fn reserve<T, O: ExecutionObserver>(
    values: &mut Vec<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed {
    admit(session, site, 1, 0)?;
    if values.len() == values.capacity() {
        let requested = values
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let images = requested
            .checked_add(values.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let bytes = images
            .checked_mul(size_of::<T>())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        admit(session, site, images, bytes)?;
        values
            .try_reserve_exact(requested - values.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    Ok(())
}

pub(super) fn push<T: Copy, O: ExecutionObserver>(
    values: &mut Vec<T>,
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed {
    reserve(values, session, site)?;
    admit(session, site, 1, size_of::<T>())?;
    values.push(value);
    Ok(())
}

pub(super) fn retire_value<T, O: ExecutionObserver>(
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_poll(site);
    drop(value);
    session.retirement_poll(site);
}

pub(super) fn retire_vec<T, O: ExecutionObserver>(
    values: &mut Vec<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    retire_value(core::mem::take(values), session, site);
}

pub(super) fn retire_set<K: Ord, O: ExecutionObserver>(
    set: &mut BTreeSet<K>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !set.is_empty() {
        session.retirement_poll(site);
        let value = set.pop_first();
        retire_value(value, session, site);
    }
    session.retirement_poll(site);
}

pub(super) fn retire_map_sets<O: ExecutionObserver>(
    map: &mut BTreeMap<PrincipalKey, BTreeSet<PrincipalKey>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !map.is_empty() {
        session.retirement_poll(site);
        if let Some((_, mut values)) = map.pop_first() {
            retire_set(&mut values, session, site);
            retire_value(values, session, site);
        }
    }
    session.retirement_poll(site);
}
