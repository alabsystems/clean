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
    pub(super) fn publish<T: Copy>(&mut self, value: T) -> R<T> {
        self.session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: self.site,
            work: 1,
            copy_bytes: size_of::<T>(),
        })?;
        Ok(value)
    }
    fn at(&mut self, bytes: &[u8], at: usize) -> R<Option<u8>> {
        self.admit(1, size_of::<Option<u8>>())?;
        Ok(bytes.get(at).copied())
    }
    fn name_byte(&mut self, byte: u8) -> R<bool> {
        self.admit(4, size_of::<bool>())?;
        Ok(byte.is_ascii_alphanumeric() || byte == b'_')
    }
    fn next(&mut self, index: &mut usize, amount: usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *index = index
            .checked_add(amount)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn segment(&mut self, text: &str) -> R<bool> {
        self.admit(2, size_of::<usize>() + size_of::<bool>())?;
        if text.is_empty() {
            return self.publish(false);
        }
        let mut at = 0usize;
        while let Some(byte) = self.at(text.as_bytes(), at)? {
            if !self.name_byte(byte)? {
                return self.publish(false);
            }
            self.next(&mut at, 1)?;
        }
        self.publish(true)
    }
    pub(super) fn runtime(&mut self, text: &str) -> R<bool> {
        self.admit(3, size_of::<usize>() + size_of::<bool>())?;
        let mut at = 0usize;
        let mut has_name = false;
        while let Some(byte) = self.at(text.as_bytes(), at)? {
            if self.name_byte(byte)? {
                self.admit(1, size_of::<bool>())?;
                has_name = true;
                self.next(&mut at, 1)?;
                continue;
            }
            self.admit(3, size_of::<usize>() + size_of::<bool>())?;
            if byte != b':' || !has_name {
                return self.publish(false);
            }
            let next = at
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if self.at(text.as_bytes(), next)? != Some(b':') {
                return self.publish(false);
            }
            self.admit(1, size_of::<bool>())?;
            has_name = false;
            self.next(&mut at, 2)?;
        }
        self.publish(has_name)
    }
}
