// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn identity<O: ExecutionObserver>(
    value: &str,
    bounded: bool,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 2, 0)?;
    if value.is_empty()
        || (bounded && value.len() > crate::proof::PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES)
    {
        return Ok(false);
    }
    admit(session, site, 8, 0)?;
    if value.chars().next().is_some_and(char::is_whitespace) {
        return Ok(false);
    }
    admit(session, site, 8, 0)?;
    if value.chars().next_back().is_some_and(char::is_whitespace) {
        return Ok(false);
    }
    let mut chars = value.chars();
    loop {
        admit(session, site, 8, 0)?;
        let Some(character) = chars.next() else {
            return Ok(true);
        };
        if character.is_control() {
            return Ok(false);
        }
    }
}

pub(super) fn public_id<O: ExecutionObserver>(
    value: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 2, 0)?;
    if value.is_empty() || value.len() > crate::proof::PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES {
        return Ok(false);
    }
    for byte in value.bytes() {
        admit(session, site, 3, 0)?;
        if !byte.is_ascii_graphic() || matches!(byte, b'?' | b'#') {
            return Ok(false);
        }
    }
    Ok(true)
}

fn copy<O: ExecutionObserver>(
    value: &str,
    output: &mut String,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    admit(session, site, 1, 0)?;
    if !output.is_empty() {
        return Err(ObservedValueError::InvalidRange);
    }
    admit(session, site, value.len(), value.len())?;
    output
        .try_reserve_exact(value.len())
        .map_err(|_| ObservedValueError::AllocationFailed)?;
    let mut start = 0;
    while start < value.len() {
        let stop = start.saturating_add(1024).min(value.len());
        admit(session, site, stop - start + 4, stop - start)?;
        let mut end = stop;
        while !value.is_char_boundary(end) {
            end -= 1;
        }
        output.push_str(&value[start..end]);
        start = end;
    }
    Ok(())
}

impl Work {
    pub(super) fn duplicate_public<O: ExecutionObserver>(
        &mut self,
        value: &str,
        first_obligation: ProofId,
        duplicate_obligation: ProofId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        copy(value, &mut self.first_text, session, site)?;
        admit(session, site, 1, size_of::<E>())?;
        self.pending = Some(E::DuplicatePublicObligationSource {
            public_obligation_id: take(&mut self.first_text),
            first_obligation,
            duplicate_obligation,
        });
        self.push_pending(session, site)
    }

    pub(super) fn public_mismatch<O: ExecutionObserver>(
        &mut self,
        request: NativeRequestId,
        obligation: ProofId,
        expected: &str,
        actual: &str,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        copy(expected, &mut self.first_text, session, site)?;
        copy(actual, &mut self.second_text, session, site)?;
        admit(session, site, 1, size_of::<E>())?;
        self.pending = Some(E::EmbeddedPublicObligationIdMismatch {
            request,
            obligation,
            expected: take(&mut self.first_text),
            actual: take(&mut self.second_text),
        });
        self.push_pending(session, site)
    }
}
