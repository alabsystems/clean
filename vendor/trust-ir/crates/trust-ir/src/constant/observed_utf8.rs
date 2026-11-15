// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Observed validity-only RFC3629 recognition for actual borrowed byte windows.
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
#[cfg(test)]
mod tests;

/// The exact validity predicate of `str::from_utf8`, under the original owner.
///
/// This safe scalar recognizer uses the same lead/second/continuation ranges as
/// pinned core/src/str/validations.rs run_utf8_validation (RFC3629). No error
/// offset, string, global-data validity or source/proof capability is produced.
/// The caller supplies exactly the original full bytes or already checked
/// window; its allocation/custody/disposal and physical runtime remain its duty.
/// Every visited byte is admitted before it is read. The finite 32-work fee
/// covers the finite scalar/range alternatives, state changes and loop header;
/// this is a logical source bound, not machine/allocator/hard-time evidence.
/// No instruction fuel, new observer, grant or deadline is created or changed.
/// Even a completed false result is withheld if final publication is refused.
pub fn utf8_is_valid_observed<O: ExecutionObserver>(
    bytes: &[u8],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<bool, ObservedValueError> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<core::slice::Iter<'_, u8>>() + size_of::<(u8, u8, u8, bool)>(),
    })?;
    let mut remaining = 0u8;
    let mut low = 0x80u8;
    let mut high = 0xbfu8;
    let mut valid = true;
    for byte in bytes {
        // The iterator yields a borrowed byte; no dereference/data decision is
        // made until this admission. State is finite scalar scratch only.
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 32,
            copy_bytes: size_of::<(u8, u8, u8, u8, bool)>(),
        })?;
        let byte = *byte;
        if remaining == 0 {
            (remaining, low, high) = match byte {
                0x00..=0x7f => (0, 0x80, 0xbf),
                0xc2..=0xdf => (1, 0x80, 0xbf),
                0xe0 => (2, 0xa0, 0xbf),
                0xe1..=0xec | 0xee..=0xef => (2, 0x80, 0xbf),
                0xed => (2, 0x80, 0x9f),
                0xf0 => (3, 0x90, 0xbf),
                0xf1..=0xf3 => (3, 0x80, 0xbf),
                0xf4 => (3, 0x80, 0x8f),
                _ => {
                    valid = false;
                    break;
                }
            };
        } else if byte < low || byte > high {
            valid = false;
            break;
        } else {
            remaining -= 1;
            low = 0x80;
            high = 0xbf;
        }
    }
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Publication,
        site,
        work: 1,
        copy_bytes: size_of::<bool>(),
    })?;
    Ok(valid && remaining == 0)
}
