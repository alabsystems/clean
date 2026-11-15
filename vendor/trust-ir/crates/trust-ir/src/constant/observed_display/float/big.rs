// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Observed fixed-capacity arithmetic for the binary64 Dragon interval.
use super::*;
const WORDS: usize = 40;
pub(super) struct Big {
    words: [u32; WORDS],
    len: usize,
}
impl Big {
    pub(super) fn new<O: ExecutionObserver>(n: u64, work: &mut Work<'_, '_, O>) -> R<Self> {
        work.admit(WORDS + 2, size_of::<Self>())?;
        let mut words = [0; WORDS];
        words[0] = n as u32;
        words[1] = (n >> 32) as u32;
        Ok(Self {
            words,
            len: if words[1] == 0 { 1 } else { 2 },
        })
    }
    pub(super) fn copy<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R<Self> {
        work.admit(WORDS + 1, size_of::<Self>())?;
        Ok(Self {
            words: self.words,
            len: self.len,
        })
    }
    pub(super) fn compare<O: ExecutionObserver>(
        &self,
        other: &Self,
        work: &mut Work<'_, '_, O>,
    ) -> R<Ordering> {
        work.admit(1, 2 * size_of::<usize>())?;
        if self.len != other.len {
            return Ok(self.len.cmp(&other.len));
        }
        for i in (0..self.len).rev() {
            work.admit(1, 2 * size_of::<u32>())?;
            let order = self.words[i].cmp(&other.words[i]);
            if order != Ordering::Equal {
                return Ok(order);
            }
        }
        Ok(Ordering::Equal)
    }
    pub(super) fn add<O: ExecutionObserver>(
        &mut self,
        other: &Self,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 2 * size_of::<usize>())?;
        let length = self.len.max(other.len);
        let mut carry = 0u64;
        for i in 0..length {
            work.admit(3, 3 * size_of::<u64>() + size_of::<u32>())?;
            let n = u64::from(self.words[i]) + u64::from(other.words[i]) + carry;
            self.words[i] = n as u32;
            carry = n >> 32;
        }
        self.len = length;
        self.carry(carry, work)
    }
    pub(super) fn mul<O: ExecutionObserver>(&mut self, n: u32, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<u64>())?;
        if n == 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut carry = 0u64;
        for i in 0..self.len {
            work.admit(3, 3 * size_of::<u64>() + size_of::<u32>())?;
            let product = u64::from(self.words[i]) * u64::from(n) + carry;
            self.words[i] = product as u32;
            carry = product >> 32;
        }
        self.carry(carry, work)
    }
    fn carry<O: ExecutionObserver>(&mut self, carry: u64, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<usize>())?;
        if carry != 0 {
            let cell = self
                .words
                .get_mut(self.len)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            work.admit(1, size_of::<u32>())?;
            *cell = u32::try_from(carry).map_err(|_| ObservedValueError::CapacityOverflow)?;
            self.len += 1;
        }
        Ok(())
    }
    pub(super) fn sub<O: ExecutionObserver>(
        &mut self,
        other: &Self,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<u64>())?;
        if other.len > self.len {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut borrow = 0u64;
        for i in 0..self.len {
            work.admit(4, 3 * size_of::<u64>() + size_of::<u32>())?;
            let a = u64::from(self.words[i]);
            let b = u64::from(other.words[i]) + borrow;
            self.words[i] = a.wrapping_sub(b) as u32;
            borrow = u64::from(a < b);
        }
        if borrow != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        while self.len > 1 {
            work.admit(1, size_of::<usize>() + size_of::<u32>())?;
            if self.words[self.len - 1] != 0 {
                break;
            }
            self.len -= 1;
        }
        Ok(())
    }
    pub(super) fn shift<O: ExecutionObserver>(
        &mut self,
        bits: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            WORDS + 2,
            size_of::<[u32; WORDS]>() + 2 * size_of::<usize>(),
        )?;
        let mut shifted = [0u32; WORDS];
        let (whole, rem) = (bits / 32, bits % 32);
        let mut length = 1;
        for (i, &word) in self.words[..self.len].iter().enumerate() {
            work.admit(5, 2 * size_of::<usize>() + 2 * size_of::<u64>())?;
            let at = i
                .checked_add(whole)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let value = u64::from(word) << rem;
            if value == 0 {
                continue;
            }
            *shifted
                .get_mut(at)
                .ok_or(ObservedValueError::CapacityOverflow)? |= value as u32;
            length = length.max(at + 1);
            if value >> 32 != 0 {
                *shifted
                    .get_mut(at + 1)
                    .ok_or(ObservedValueError::CapacityOverflow)? |= (value >> 32) as u32;
                length = length.max(at + 2);
            }
        }
        work.admit(WORDS + 1, size_of::<Self>())?;
        self.words = shifted;
        self.len = length;
        Ok(())
    }
    pub(super) fn pow10<O: ExecutionObserver>(
        &mut self,
        exponent: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for _ in 0..exponent {
            work.admit(1, 0)?;
            self.mul(10, work)?;
        }
        Ok(())
    }
}
