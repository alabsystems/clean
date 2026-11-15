// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const CHUNK: usize = 1024;

pub(super) fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work,
            copy_bytes,
        })
        .map_err(Into::into)
}

pub(super) fn publication<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })
        .map_err(Into::into)
}

pub(super) fn terminal<O: ExecutionObserver>(
    error: ObservedValueError,
    _session: &ObservedSession<'_, O>,
) -> ObservedValueError {
    // A traversal result is already held before cleanup. Keep it unchanged;
    // any later observer refusal remains independently sticky in the session.
    error
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
        // Requested new storage plus retained elements moved by growth. This
        // is logical prepayment, not an allocator/RSS or OOM guarantee.
        admit(session, site, work, bytes)?;
        values
            .try_reserve_exact(requested - values.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    Ok(())
}

pub(super) fn push_id<O: ExecutionObserver>(
    values: &mut Vec<FuncId>,
    id: FuncId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    reserve(values, session, site)?;
    admit(session, site, 1, size_of::<FuncId>())?;
    values.push(id);
    Ok(())
}

pub(super) fn checked_import_id<O: ExecutionObserver>(
    index: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ImportId> {
    admit(session, site, 1, 0)?;
    Ok(ImportId::new(
        u32::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)?,
    ))
}

pub(super) fn producer_equal<O: ExecutionObserver>(
    left: Option<&Producer>,
    right: Option<&Producer>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 1, 0)?;
    match (left, right) {
        (None, None)
        | (Some(Producer::TRust), Some(Producer::TRust))
        | (Some(Producer::Clean), Some(Producer::Clean))
        | (Some(Producer::TrustIr), Some(Producer::TrustIr))
        | (Some(Producer::TSwift), Some(Producer::TSwift))
        | (Some(Producer::TC), Some(Producer::TC)) => Ok(true),
        (Some(Producer::Other(a)), Some(Producer::Other(b))) => text_equal(a, b, session, site),
        _ => Ok(false),
    }
}

fn text_equal<O: ExecutionObserver>(
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
        .chunks(CHUNK)
        .zip(right.as_bytes().chunks(CHUNK))
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

pub(super) fn copy_producer<O: ExecutionObserver>(
    producer: Option<&Producer>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<Producer>> {
    admit(session, site, 1, size_of::<Option<Producer>>())?;
    Ok(match producer {
        None => None,
        Some(Producer::TRust) => Some(Producer::TRust),
        Some(Producer::Clean) => Some(Producer::Clean),
        Some(Producer::TrustIr) => Some(Producer::TrustIr),
        Some(Producer::TSwift) => Some(Producer::TSwift),
        Some(Producer::TC) => Some(Producer::TC),
        Some(Producer::Other(text)) => Some(Producer::Other(copy_text(text, session, site)?)),
    })
}

pub(super) fn copy_text<O: ExecutionObserver>(
    source: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<String> {
    admit(session, site, 1, size_of::<String>())?;
    let mut text = String::new();
    let result = (|| {
        let mut tail = source;
        while !tail.is_empty() {
            // At most three boundary probes precede a <=1024-byte UTF-8 copy.
            admit(session, site, 4, 0)?;
            let mut end = tail.len().min(CHUNK);
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
    match result {
        Ok(()) => Ok(text),
        Err(error) => {
            retire_value(text, session, site);
            Err(terminal(error, session))
        }
    }
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

pub(super) fn retire_producer<O: ExecutionObserver>(
    producer: Option<Producer>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_poll(site);
    match producer {
        Some(Producer::Other(text)) => retire_value(text, session, site),
        fixed => retire_value(fixed, session, site),
    }
    session.retirement_poll(site);
}

pub(super) fn retire_ids<O: ExecutionObserver>(
    ids: &mut Vec<FuncId>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !ids.is_empty() {
        session.retirement_poll(site);
        retire_value(ids.pop(), session, site);
    }
    retire_value(take(ids), session, site);
}
