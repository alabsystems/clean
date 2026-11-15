// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! The actual original two-text predicate; no parsing or proof capability.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
impl ProofFormula {
    /// The exact original `states_two_texts` boolean under the supplied
    /// original session/site. Schema recognition, canonical decimal citations,
    /// real bounded predicate spelling and raw text comparison are observed
    /// inside their actual work. Opaque schemas are unread and unparsed.
    ///
    /// Each claim schema's original Claim AND Unread outcomes both mean true
    /// whenever a rendering exists. No claim payload parser is needed to decide
    /// this boolean; this method does not classify, parse or admit a claim.
    /// No formula validity, source/kernel/proof authority or owner is created.
    /// The predicate child's Float support remains that child's explicit typed
    /// limitation until its separately reviewed implementation is composed.
    /// Successful input disposal and physical std/allocator/OOM/panic/hardtime
    /// remain OPEN. No owner, deadline, grant, TLS or fuel is reset.
    pub fn states_two_texts_observed<O: ExecutionObserver>(
        &self,
        predicates: &PredTable<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Work<'_, '_, O>>() + size_of::<Option<&str>>())?;
        let Some(rendering) = self.smtlib.as_deref() else {
            return work.publish(false);
        };
        work.admit(1, size_of::<&[OwnedFormulaSchema; 5]>())?;
        let schemas = &OwnedFormulaSchema::ALL;
        let mut index = 0usize;
        let schema = loop {
            work.admit(1, size_of::<Option<&OwnedFormulaSchema>>())?;
            let Some(candidate) = schemas.get(index) else {
                break None;
            };
            work.admit(1, size_of::<OwnedFormulaSchema>())?;
            if work.equal(&self.schema, candidate.name())? {
                break Some(*candidate);
            }
            work.admit(1, size_of::<usize>())?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        };
        work.admit(6, size_of::<Option<OwnedFormulaSchema>>())?;
        let answer = match schema {
            None => false,
            Some(OwnedFormulaSchema::Smtlib2) => !work.equal(&self.payload, rendering)?,
            Some(OwnedFormulaSchema::Pred) => {
                let matches = match citation(&self.payload, &mut work)? {
                    Some(id) => predicates.smtlib_matches_observed(
                        id,
                        rendering,
                        work.session,
                        work.site,
                    )?,
                    None => false,
                };
                work.admit(1, size_of::<bool>())?;
                !matches
            }
            Some(
                OwnedFormulaSchema::BvBlastGoal
                | OwnedFormulaSchema::SatRes
                | OwnedFormulaSchema::LineageTransformBinding,
            ) => true,
        };
        work.publish(answer)
    }
}
fn citation<O: ExecutionObserver>(payload: &str, work: &mut Work<'_, '_, O>) -> R<Option<PredId>> {
    work.admit(5, size_of::<Option<&str>>())?;
    let Some(digits) = payload.strip_prefix("pred.") else {
        return Ok(None);
    };
    work.admit(4, size_of::<usize>() + size_of::<u32>())?;
    if digits.is_empty() || (digits.len() > 1 && digits.as_bytes()[0] == b'0') {
        return Ok(None);
    }
    let mut index = 0usize;
    let mut value = 0u32;
    loop {
        work.admit(1, size_of::<Option<&u8>>())?;
        let Some(digit) = digits.as_bytes().get(index) else {
            break;
        };
        work.admit(5, size_of::<u32>() + size_of::<Option<u32>>())?;
        if !digit.is_ascii_digit() {
            return Ok(None);
        }
        let Some(next) = value
            .checked_mul(10)
            .and_then(|n| n.checked_add(u32::from(*digit - b'0')))
        else {
            return Ok(None);
        };
        value = next;
        work.admit(1, size_of::<usize>())?;
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
    work.admit(1, size_of::<Option<PredId>>())?;
    Ok(Some(PredId::new(value)))
}
