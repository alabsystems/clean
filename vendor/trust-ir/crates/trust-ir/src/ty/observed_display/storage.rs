// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn reserve<T>(&mut self, values: &mut Vec<T>) -> R {
        self.admit(1, 0)?;
        if values.len() == values.capacity() {
            let requested = values
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(values.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            values
                .try_reserve_exact(requested - values.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn text(&mut self, mut source: &str, output: &mut String) -> R {
        while !source.is_empty() {
            self.admit(1, 0)?;
            let mut end = source.len().min(1024);
            loop {
                self.admit(1, 0)?;
                if source.is_char_boundary(end) {
                    break;
                }
                end -= 1;
            }
            let chunk = &source[..end];
            let needed = output
                .len()
                .checked_add(chunk.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > output.capacity() {
                let requested = output
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let images = requested
                    .checked_add(output.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.admit(images, images)?;
                output
                    .try_reserve_exact(requested - output.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(chunk.len(), chunk.len())?;
            output.push_str(chunk);
            source = &source[end..];
        }
        Ok(())
    }
    pub(super) fn number(&mut self, mut value: u128, output: &mut String) -> R {
        self.admit(40, 40)?;
        let mut digits = [0u8; 40];
        let mut start = digits.len();
        loop {
            self.admit(1, 1)?;
            start = start
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            digits[start] = b'0' + (value % 10) as u8;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        self.admit(digits.len() - start, 0)?;
        let text =
            core::str::from_utf8(&digits[start..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, output)
    }
    pub(super) fn quoted(&mut self, mut source: &str, output: &mut String) -> R {
        self.text("\"", output)?;
        loop {
            // Decoding a single UTF8 scalar is bounded by four source bytes.
            self.admit(4, 2 * size_of::<char>())?;
            let Some(character) = source.chars().next() else {
                break;
            };
            source = &source[character.len_utf8()..];
            if character == '\'' {
                // Debug(str) leaves apostrophes verbatim; char.escape_debug
                // escapes them because its public default also serves chars.
                self.text("'", output)?;
                continue;
            }
            // Scalar Unicode classification is a fixed std primitive, not a
            // string walk. Price eight u32-domain property searches before
            // construction; each escaped scalar then has its own admission.
            // This is logical pricing, never an installed-std/hard-time claim.
            // Exact pinned698 Unicode source: four skip_search tables have
            // (headers,offsets)=(33,767),(12,35),(11,43),(54,1461).
            // Each binary search probes at most its header count, and each
            // forward run reads at most its full offsets array. The 256-byte
            // whitespace table plus 8*u32::BITS cover its fixed cascade and
            // all scalar guards/extra header probes. See STD-BINDINGS and
            // the complete source-derived lemma; no opaque string traversal.
            const UNICODE_TABLE_VISITS: usize = 33 + 767 + 12 + 35 + 11 + 43 + 54 + 1461 + 256;
            self.admit(
                8 * u32::BITS as usize + UNICODE_TABLE_VISITS,
                size_of::<core::char::EscapeDebug>(),
            )?;
            let mut escaped = character.escape_debug();
            loop {
                self.admit(1, size_of::<Option<char>>())?;
                let Some(character) = escaped.next() else {
                    break;
                };
                self.admit(4, 4)?;
                let mut utf8 = [0u8; 4];
                self.text(character.encode_utf8(&mut utf8), output)?;
            }
        }
        self.text("\"", output)
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: size_of::<String>(),
            })
            .map_err(Into::into)
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        // The local result is already held before consuming cleanup. The
        // observer's separate original first cause remains sticky in session.
        error
    }
}
