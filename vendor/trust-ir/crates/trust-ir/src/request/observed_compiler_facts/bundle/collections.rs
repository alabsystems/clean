// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn insert<K: Copy + Ord, V: Copy, O: ExecutionObserver>(
    map: &mut BTreeMap<K, V>,
    key: K,
    value: V,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<V>> {
    let cost = observed_btree::insertion_cost::<K, V>(map.len())?;
    admit(session, site, cost.work, cost.copy_bytes)?;
    let search = observed_btree::population_work(map.len())?
        .checked_mul(size_of::<K>().max(1))
        .ok_or(ObservedValueError::CapacityOverflow)?;
    admit(session, site, search, size_of::<(K, V)>())?;
    Ok(map.insert(key, value))
}

pub(super) fn get<K: Ord, V: Copy, O: ExecutionObserver>(
    map: &BTreeMap<K, V>,
    key: &K,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<V>> {
    // All keys here are fixed IDs/digests, with bounded Ord implementations.
    let work = observed_btree::population_work(map.len())?
        .checked_mul(size_of::<K>().max(1))
        .ok_or(ObservedValueError::CapacityOverflow)?;
    admit(session, site, work, size_of::<V>())?;
    Ok(map.get(key).copied())
}

pub(super) fn text_insert<'a, V: Copy, O: ExecutionObserver>(
    rows: &mut Vec<(&'a str, V)>,
    key: &'a str,
    value: V,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<V>> {
    let mut index = 0;
    while index < rows.len() {
        admit(session, site, 1, 0)?;
        if text_equal(rows[index].0, key, session, site)? {
            admit(session, site, 1, size_of::<V>())?;
            let old = rows[index].1;
            rows[index].1 = value;
            return Ok(Some(old));
        }
        index += 1;
    }
    reserve(rows, session, site)?;
    admit(session, site, 1, size_of::<(&str, V)>())?;
    rows.push((key, value));
    Ok(None)
}

pub(super) fn contains<K: Copy + Eq, O: ExecutionObserver>(
    values: &[K],
    key: K,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    for value in values {
        admit(session, site, 1, 0)?;
        if *value == key {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn retire_set<K: Copy + Ord, O: ExecutionObserver>(
    values: &mut BTreeSet<K>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !values.is_empty() {
        session.retirement_step(site, values.len().saturating_add(1));
        let _ = values.pop_first();
    }
    session.retirement_poll(site);
    drop(take(values));
    session.retirement_poll(site);
}

pub(super) fn retire_map<K: Copy + Ord, V: Copy, O: ExecutionObserver>(
    values: &mut BTreeMap<K, V>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !values.is_empty() {
        session.retirement_step(site, values.len().saturating_add(1));
        let _ = values.pop_first();
    }
    session.retirement_poll(site);
    drop(take(values));
    session.retirement_poll(site);
}

pub(super) fn retire_vec<T: Copy, O: ExecutionObserver>(
    values: &mut Vec<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !values.is_empty() {
        session.retirement_step(site, 1);
        let _ = values.pop();
    }
    session.retirement_poll(site);
    drop(take(values));
    session.retirement_poll(site);
}
