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
    pub(super) fn number(&mut self, mut value: u64, output: &mut String) -> R {
        self.admit(20, 20)?;
        let mut digits = [0u8; 20];
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
            self.admit(4, 2 * size_of::<char>())?;
            let Some(character) = source.chars().next() else {
                break;
            };
            source = &source[character.len_utf8()..];
            if character == '\'' {
                // Debug(str) leaves apostrophes literal; escape_debug(char)
                // otherwise uses that same scalar spelling, including quotes.
                self.text("'", output)?;
                continue;
            }
            // Pinned698 escape_debug traverses four Unicode skip tables.
            // Bound every header/offset plus whitespace-table visit before
            // classification, as in observed Ty Display. This prices logical
            // source visits, not allocator, runtime or hard-time behavior.
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
    pub(super) fn publication(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn fixed<T: Copy>(&mut self, value: T) {
        // New owned fields cannot silently hide behind fixed-field disposal.
        self.step(size_of::<T>().saturating_add(1));
        let _ = value;
    }
    pub(super) fn retire_text(&mut self, text: String) {
        self.step(
            text.len()
                .saturating_add(size_of::<String>())
                .saturating_add(1),
        );
        drop(text);
        self.poll();
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
