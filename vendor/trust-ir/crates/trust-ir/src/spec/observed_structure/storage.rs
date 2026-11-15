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
    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], index: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(index))
    }
    pub(super) fn next(&mut self, index: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.admit(1, 0)?;
        if rows.len() == rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn push<T: Copy>(&mut self, rows: &mut Vec<T>, value: T) -> R {
        self.reserve(rows)?;
        self.admit(1, size_of::<T>())?;
        rows.push(value);
        Ok(())
    }
    pub(super) fn compare(&mut self, a: &str, b: &str) -> R<Ordering> {
        let mut index = 0;
        self.admit(2, 2 * size_of::<usize>())?;
        let end = a.len().min(b.len());
        while index < end {
            self.admit(3, 2 * size_of::<&[u8]>())?;
            let next = index.saturating_add(1024).min(end);
            self.admit(next - index, 0)?;
            let order = a.as_bytes()[index..next].cmp(&b.as_bytes()[index..next]);
            if order != Ordering::Equal {
                return Ok(order);
            }
            self.admit(1, size_of::<usize>())?;
            index = next;
        }
        self.admit(1, 2 * size_of::<usize>())?;
        Ok(a.len().cmp(&b.len()))
    }
    pub(super) fn equal(&mut self, a: &str, b: &str) -> R<bool> {
        let order = self.compare(a, b)?;
        self.admit(1, size_of::<bool>())?;
        Ok(order == Ordering::Equal)
    }
    pub(super) fn blank(&mut self, mut text: &str) -> R<bool> {
        loop {
            self.admit(4, size_of::<Option<char>>())?;
            let Some(ch) = text.chars().next() else {
                return Ok(true);
            };
            // Same reviewed fixed-scalar std Unicode boundary as observed Ty
            // Display. Logical pricing is not an installed-table/time proof.
            self.admit(8 * u32::BITS as usize, size_of::<bool>())?;
            if !ch.is_whitespace() {
                return Ok(false);
            }
            text = &text[ch.len_utf8()..];
        }
    }
    pub(super) fn text(&mut self, mut source: &str, out: &mut String) -> R {
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
            let needed = out
                .len()
                .checked_add(chunk.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > out.capacity() {
                let requested = out
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let images = requested
                    .checked_add(out.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.admit(images, images)?;
                out.try_reserve_exact(requested - out.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(chunk.len(), chunk.len())?;
            out.push_str(chunk);
            source = &source[end..];
        }
        Ok(())
    }
    pub(super) fn number(&mut self, mut n: u128, out: &mut String) -> R {
        self.admit(40, 40)?;
        let mut digits = [0u8; 40];
        let mut start = 40usize;
        loop {
            self.admit(1, 1)?;
            start = start
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            digits[start] = b'0' + (n % 10) as u8;
            n /= 10;
            if n == 0 {
                break;
            }
        }
        self.admit(40 - start, 0)?;
        let text =
            core::str::from_utf8(&digits[start..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.text(text, out)
    }
    pub(super) fn quoted(&mut self, mut text: &str, out: &mut String) -> R {
        self.text("\"", out)?;
        loop {
            self.admit(4, 2 * size_of::<char>())?;
            let Some(ch) = text.chars().next() else { break };
            text = &text[ch.len_utf8()..];
            if ch == '\'' {
                self.text("'", out)?;
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
            let mut escape = ch.escape_debug();
            loop {
                self.admit(1, size_of::<Option<char>>())?;
                let Some(ch) = escape.next() else { break };
                self.admit(4, 4)?;
                let mut buf = [0u8; 4];
                self.text(ch.encode_utf8(&mut buf), out)?;
            }
        }
        self.text("\"", out)
    }
    pub(super) fn step(&mut self, n: usize) {
        self.session.retirement_step(self.site, n);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn fixed<T: Copy>(&mut self, value: T) {
        self.step(size_of::<T>().saturating_add(1));
        let _ = value;
    }
    pub(super) fn retire_text(&mut self, text: &mut String) {
        self.step(
            text.len()
                .saturating_add(size_of::<String>())
                .saturating_add(1),
        );
        drop(take(text));
        self.poll();
    }
    pub(super) fn retire_fixed_vec<T: Copy>(&mut self, rows: &mut Vec<T>) {
        loop {
            self.step(size_of::<Option<T>>().saturating_add(1));
            let Some(row) = rows.pop() else { break };
            self.fixed(row);
        }
        self.step(size_of::<Vec<T>>().saturating_add(1));
        drop(take(rows));
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
