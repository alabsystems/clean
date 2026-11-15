// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use core::mem::size_of;

pub(super) struct Writer<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
    pub(super) text: String,
}
impl<'s, 'o, O: ExecutionObserver> Writer<'s, 'o, O> {
    pub(super) fn new(session: &'s mut ObservedSession<'o, O>, site: ExecutionSite) -> R<Self> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalSerialization,
            site,
            work: 1,
            copy_bytes: size_of::<Self>(),
        })?;
        Ok(Self {
            session,
            site,
            text: String::new(),
        })
    }
    pub(super) fn admit(&mut self, work: usize, bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::CanonicalSerialization,
                site: self.site,
                work,
                copy_bytes: bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn poll(&mut self) -> R {
        self.admit(1, 0)
    }
    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>, additional: usize) -> R {
        self.poll()?;
        let needed = rows
            .len()
            .checked_add(additional)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed > rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(additional))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let work = requested
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                work,
                work.checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn append_to(&mut self, output: &mut String, mut text: &str) -> R {
        self.poll()?;
        while !text.is_empty() {
            self.admit(4, 0)?;
            let mut end = text.len().min(1024);
            while !text.is_char_boundary(end) {
                end -= 1;
            }
            let chunk = &text[..end];
            let needed = output
                .len()
                .checked_add(chunk.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if needed > MAX_ABI_TEXT_BYTES {
                return Err(ObservedValueError::UnsupportedValue);
            }
            if needed > output.capacity() {
                let requested = output
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(chunk.len()))
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let bytes = requested
                    .checked_add(output.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                self.admit(bytes, bytes)?;
                output
                    .try_reserve_exact(requested - output.len())
                    .map_err(|_| ObservedValueError::AllocationFailed)?;
            }
            self.admit(chunk.len(), chunk.len())?;
            output.push_str(chunk);
            text = &text[end..];
        }
        Ok(())
    }
    pub(super) fn append(&mut self, text: &str) -> R {
        let mut output = core::mem::take(&mut self.text);
        let result = self.append_to(&mut output, text);
        self.text = output;
        result
    }
    pub(super) fn copy(&mut self, text: &str) -> R<String> {
        let mut output = String::new();
        let result = self.append_to(&mut output, text);
        if let Err(error) = result {
            self.retire(output);
            return Err(error);
        }
        Ok(output)
    }
    pub(super) fn character_to(&mut self, output: &mut String, value: char) -> R {
        let mut bytes = [0; 4];
        self.admit(4, 0)?;
        self.append_to(output, value.encode_utf8(&mut bytes))
    }
    pub(super) fn number(&mut self, mut value: u64) -> R {
        let mut buffer = [0u8; 20];
        let mut first = buffer.len();
        loop {
            self.poll()?;
            first -= 1;
            buffer[first] = b'0' + (value % 10) as u8;
            value /= 10;
            if value == 0 {
                break;
            }
        }
        self.admit(20, 0)?;
        let text =
            core::str::from_utf8(&buffer[first..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.append(text)
    }
    pub(super) fn boolean(&mut self, value: bool) -> R {
        self.append(if value { "true" } else { "false" })
    }
    pub(super) fn quoted(&mut self, value: &str) -> R {
        self.append("\"")?;
        for character in value.chars() {
            self.admit(4, 0)?;
            match character {
                '"' => self.append("\\\"")?,
                '\\' => self.append("\\\\")?,
                '\n' => self.append("\\n")?,
                '\r' => self.append("\\r")?,
                '\t' => self.append("\\t")?,
                c if c.is_control() => {
                    self.append("\\u{")?;
                    let mut number = c as u32;
                    let mut digits = [0u8; 6];
                    let mut start = digits.len();
                    loop {
                        self.poll()?;
                        start -= 1;
                        digits[start] = b"0123456789abcdef"[(number % 16) as usize];
                        number /= 16;
                        if number == 0 {
                            break;
                        }
                    }
                    self.admit(6, 0)?;
                    let text = core::str::from_utf8(&digits[start..])
                        .map_err(|_| ObservedValueError::InvalidRange)?;
                    self.append(text)?;
                    self.append("}")?;
                }
                c => {
                    let mut bytes = [0; 4];
                    self.append(c.encode_utf8(&mut bytes))?;
                }
            }
        }
        self.append("\"")
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        self.session.retirement_poll(self.site);
        drop(value);
        self.session.retirement_poll(self.site);
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}
