// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Low-level byte reader for parsing OCaml Marshal binary data.
//!
//! Provides position-tracked reading of integers, floats, and byte slices
//! in big-endian format (OCaml's native marshal byte order).

use super::marshal_parser::{MarshalError, MarshalResult};

/// Low-level byte reader with position tracking.
pub(crate) struct Reader<'a> {
    pub(crate) data: &'a [u8],
    pub(crate) pos: usize,
}

impl<'a> Reader<'a> {
    pub(crate) fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    pub(crate) fn remaining(&self) -> usize {
        self.data.len().saturating_sub(self.pos)
    }

    pub(crate) fn ensure(&self, n: usize) -> MarshalResult<()> {
        if self.remaining() < n {
            return Err(MarshalError::UnexpectedEof {
                offset: self.pos,
                need: n,
                have: self.remaining(),
            });
        }
        Ok(())
    }

    pub(crate) fn read_u8(&mut self) -> MarshalResult<u8> {
        self.ensure(1)?;
        let v = self.data[self.pos];
        self.pos += 1;
        Ok(v)
    }

    pub(crate) fn read_u16_be(&mut self) -> MarshalResult<u16> {
        self.ensure(2)?;
        let v = u16::from_be_bytes([self.data[self.pos], self.data[self.pos + 1]]);
        self.pos += 2;
        Ok(v)
    }

    pub(crate) fn read_u32_be(&mut self) -> MarshalResult<u32> {
        self.ensure(4)?;
        let v = u32::from_be_bytes([
            self.data[self.pos],
            self.data[self.pos + 1],
            self.data[self.pos + 2],
            self.data[self.pos + 3],
        ]);
        self.pos += 4;
        Ok(v)
    }

    pub(crate) fn read_i32_be(&mut self) -> MarshalResult<i32> {
        Ok(self.read_u32_be()? as i32)
    }

    pub(crate) fn read_u64_be(&mut self) -> MarshalResult<u64> {
        self.ensure(8)?;
        let v = u64::from_be_bytes([
            self.data[self.pos],
            self.data[self.pos + 1],
            self.data[self.pos + 2],
            self.data[self.pos + 3],
            self.data[self.pos + 4],
            self.data[self.pos + 5],
            self.data[self.pos + 6],
            self.data[self.pos + 7],
        ]);
        self.pos += 8;
        Ok(v)
    }

    pub(crate) fn read_i64_be(&mut self) -> MarshalResult<i64> {
        Ok(self.read_u64_be()? as i64)
    }

    pub(crate) fn read_bytes(&mut self, n: usize) -> MarshalResult<&'a [u8]> {
        self.ensure(n)?;
        let slice = &self.data[self.pos..self.pos + n];
        self.pos += n;
        Ok(slice)
    }

    pub(crate) fn read_f64_big(&mut self) -> MarshalResult<f64> {
        let bits = self.read_u64_be()?;
        Ok(f64::from_bits(bits))
    }

    pub(crate) fn read_f64_little(&mut self) -> MarshalResult<f64> {
        self.ensure(8)?;
        let v = f64::from_le_bytes([
            self.data[self.pos],
            self.data[self.pos + 1],
            self.data[self.pos + 2],
            self.data[self.pos + 3],
            self.data[self.pos + 4],
            self.data[self.pos + 5],
            self.data[self.pos + 6],
            self.data[self.pos + 7],
        ]);
        self.pos += 8;
        Ok(v)
    }
}
