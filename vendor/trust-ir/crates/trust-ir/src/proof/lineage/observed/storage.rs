// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    bytes: usize,
) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work,
            copy_bytes: bytes,
        })
        .map_err(Into::into)
}
pub(super) fn lookup<O: ExecutionObserver>(
    len: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    admit(session, site, observed_btree::population_work(len)?, 0)
}
pub(super) fn map_insert<K: Copy + Ord, V: Copy, O: ExecutionObserver>(
    map: &mut BTreeMap<K, V>,
    key: K,
    value: V,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<V>> {
    lookup(map.len(), session, site)?;
    if !map.contains_key(&key) {
        let cost = observed_btree::insertion_cost::<K, V>(map.len())?;
        admit(session, site, cost.work, cost.copy_bytes)?;
    }
    admit(session, site, 1, size_of::<(K, V)>())?;
    Ok(map.insert(key, value))
}
pub(super) fn set_insert<K: Copy + Ord, O: ExecutionObserver>(
    set: &mut BTreeSet<K>,
    key: K,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    lookup(set.len(), session, site)?;
    if set.contains(&key) {
        return Ok(false);
    }
    let cost = observed_btree::insertion_cost::<K, ()>(set.len())?;
    admit(session, site, cost.work, cost.copy_bytes)?;
    Ok(set.insert(key))
}
pub(super) fn reserve<T, O: ExecutionObserver>(
    values: &mut Vec<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    admit(session, site, 1, 0)?;
    if values.len() == values.capacity() {
        let requested = values
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let work = requested
            .checked_add(values.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let bytes = work
            .checked_mul(size_of::<T>())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        admit(session, site, work, bytes)?;
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
) -> R {
    reserve(values, session, site)?;
    admit(session, site, 1, size_of::<T>())?;
    values.push(value);
    Ok(())
}
pub(super) fn text_equal<O: ExecutionObserver>(
    left: &str,
    right: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 1, 0)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (a, b) in left
        .as_bytes()
        .chunks(1024)
        .zip(right.as_bytes().chunks(1024))
    {
        admit(
            session,
            site,
            a.len()
                .checked_add(b.len())
                .ok_or(ObservedValueError::CapacityOverflow)?,
            0,
        )?;
        if a != b {
            return Ok(false);
        }
    }
    Ok(true)
}
pub(super) fn copy_text<O: ExecutionObserver>(
    source: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<String> {
    let mut text = String::new();
    let result = (|| {
        let mut tail = source;
        while !tail.is_empty() {
            admit(session, site, 4, 0)?;
            let mut end = tail.len().min(1024);
            while !tail.is_char_boundary(end) {
                end -= 1;
            }
            let chunk = &tail[..end];
            let needed = text
                .len()
                .checked_add(chunk.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > text.capacity() {
                let requested = text
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let bytes = requested
                    .checked_add(text.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                admit(session, site, bytes, bytes)?;
                text.try_reserve_exact(requested - text.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            admit(session, site, chunk.len(), chunk.len())?;
            text.push_str(chunk);
            tail = &tail[end..];
        }
        Ok(())
    })();
    if let Err(error) = result {
        retire_value(text, session, site);
        admit(session, site, 1, 0)?;
        return Err(error);
    }
    Ok(text)
}
pub(super) fn blank<O: ExecutionObserver>(
    value: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    for c in value.chars() {
        admit(session, site, 4, 0)?;
        if !c.is_whitespace() {
            return Ok(false);
        }
    }
    Ok(true)
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
pub(super) fn retire_map<K: Ord, V, O: ExecutionObserver>(
    map: &mut BTreeMap<K, V>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !map.is_empty() {
        session.retirement_poll(site);
        retire_value(map.pop_first(), session, site);
    }
    session.retirement_poll(site);
}
pub(super) fn retire_set<K: Ord, O: ExecutionObserver>(
    set: &mut BTreeSet<K>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !set.is_empty() {
        session.retirement_poll(site);
        retire_value(set.pop_first(), session, site);
    }
    session.retirement_poll(site);
}
