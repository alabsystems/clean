// Copyright 2026 Andrew Yates | Apache-2.0
//! Owned integer/framing grammar. No live serde implementation defines bytes.
use super::{error, DagCodecError, MAX_BYTES};

pub(super) type Result<T> = std::result::Result<T, DagCodecError>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Encoding {
    Legacy,
    V2,
}

/// Finite decoder/projection accounting, not a process-memory limit.
#[derive(Default)]
pub(super) struct Budget {
    allocated: usize,
    atoms: usize,
    depth: usize,
}
impl Budget {
    pub(super) fn remaining(&self) -> usize {
        MAX_BYTES.saturating_sub(self.allocated)
    }
    fn allocation_total(&self, count: usize, width: usize) -> Result<usize> {
        let bytes = count
            .checked_mul(width)
            .ok_or_else(|| error("allocation overflow"))?;
        let total = self
            .allocated
            .checked_add(bytes)
            .ok_or_else(|| error("allocation overflow"))?;
        if total > MAX_BYTES {
            return Err(error("allocation budget"));
        }
        Ok(total)
    }
    pub(super) fn can_allocate(&self, count: usize, width: usize) -> Result<()> {
        self.allocation_total(count, width).map(|_| ())
    }
    pub(super) fn allocate(&mut self, count: usize, width: usize) -> Result<()> {
        self.allocated = self.allocation_total(count, width)?;
        Ok(())
    }
    pub(super) fn enter(&mut self) -> Result<()> {
        self.atoms = self
            .atoms
            .checked_add(1)
            .ok_or_else(|| error("atom count overflow"))?;
        self.depth = self
            .depth
            .checked_add(1)
            .ok_or_else(|| error("atom depth overflow"))?;
        if self.atoms > 16_000_000 || self.depth > 256 {
            return Err(error("recursive atom budget"));
        }
        Ok(())
    }
    pub(super) fn leave(&mut self) {
        self.depth -= 1;
    }
}

pub(super) struct Decoder<'a> {
    input: &'a [u8],
    cursor: usize,
    pub(super) encoding: Encoding,
    pub(super) budget: Budget,
}

/// Plan requested capacity separately from allocator-reported spare capacity.
/// An allocator may return more than requested; those incidental slots cannot
/// silently become an earlier budget charge. This accounts requested storage,
/// including growth before incidental slots are used, not allocator overhead.
pub(super) fn collection_growth(
    accounted: usize,
    observed: usize,
    used: usize,
    declared: usize,
) -> Result<Option<(usize, usize)>> {
    if used >= declared {
        return Err(error("collection count mismatch"));
    }
    if used < accounted {
        return Ok(None);
    }
    let target = accounted
        .max(observed)
        .checked_mul(2)
        .unwrap_or(declared)
        .max(4)
        .max(
            used.checked_add(1)
                .ok_or_else(|| error("capacity overflow"))?,
        )
        .min(declared);
    let delta = target
        .checked_sub(accounted)
        .ok_or_else(|| error("capacity overflow"))?;
    Ok(Some((target, delta)))
}

impl<'a> Decoder<'a> {
    /// Reserve collection storage incrementally, only AFTER the next complete
    /// element has parsed. A huge declared count with no elements reserves
    /// neither physical nor accounted sequence capacity.
    pub(super) fn push<T>(
        &mut self,
        values: &mut Vec<T>,
        accounted: &mut usize,
        value: T,
        declared: usize,
    ) -> Result<()> {
        // Vec's ZST capacity is usize::MAX, not an allocation observation.
        let observed = if size_of::<T>() == 0 {
            *accounted
        } else {
            values.capacity()
        };
        if let Some((target, extra)) =
            collection_growth(*accounted, observed, values.len(), declared)?
        {
            self.budget.allocate(extra, size_of::<T>().max(1))?;
            values
                .try_reserve_exact(target - values.len())
                .map_err(|_| error("collection allocation refused"))?;
            *accounted = target;
        }
        values.push(value);
        Ok(())
    }
    pub(super) fn new(input: &'a [u8], encoding: Encoding) -> Result<Self> {
        Self::with_budget(input, encoding, Budget::default())
    }
    pub(super) fn with_budget(input: &'a [u8], encoding: Encoding, budget: Budget) -> Result<Self> {
        if input.len() > MAX_BYTES {
            return Err(error("encoded byte limit"));
        }
        Ok(Self {
            input,
            cursor: 0,
            encoding,
            budget,
        })
    }
    pub(super) fn take(&mut self, size: usize) -> Result<&'a [u8]> {
        let end = self
            .cursor
            .checked_add(size)
            .ok_or_else(|| error("input size overflow"))?;
        let bytes = self
            .input
            .get(self.cursor..end)
            .ok_or_else(|| error("truncated data"))?;
        self.cursor = end;
        Ok(bytes)
    }
    pub(super) fn done(&self) -> Result<()> {
        if self.cursor == self.input.len() {
            Ok(())
        } else {
            Err(error("trailing bytes"))
        }
    }
    pub(super) fn finish(self) -> Result<Budget> {
        self.done()?;
        Ok(self.budget)
    }
    pub(super) fn atom<T>(&mut self, read: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.budget.enter()?;
        let result = read(self);
        self.budget.leave();
        result
    }
    pub(super) fn u8(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    fn unsigned(&mut self, width: usize) -> Result<u64> {
        if self.encoding == Encoding::V2 {
            let mut bytes = [0; 8];
            bytes[..width].copy_from_slice(self.take(width)?);
            return Ok(u64::from_le_bytes(bytes));
        }
        let tag = self.u8()?;
        let count = match tag {
            0..=250 => return Ok(u64::from(tag)),
            251 => 2,
            252 => 4,
            253 => 8,
            _ => return Err(error("invalid legacy unsigned marker")),
        };
        if count > width {
            return Err(error("legacy unsigned marker exceeds declared type"));
        }
        let mut bytes = [0; 8];
        bytes[..count].copy_from_slice(self.take(count)?);
        Ok(u64::from_le_bytes(bytes))
    }
    pub(super) fn u32(&mut self) -> Result<u32> {
        u32::try_from(self.unsigned(4)?).map_err(|_| error("u32 overflow"))
    }
    pub(super) fn u64(&mut self) -> Result<u64> {
        self.unsigned(8)
    }
    pub(super) fn len(&mut self) -> Result<usize> {
        usize::try_from(self.u64()?).map_err(|_| error("length exceeds host usize"))
    }
    pub(super) fn boolean(&mut self) -> Result<bool> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(error("invalid bool")),
        }
    }
    pub(super) fn bytes(&mut self) -> Result<Vec<u8>> {
        self.bytes_bounded(MAX_BYTES)
    }
    pub(super) fn bytes_bounded(&mut self, limit: usize) -> Result<Vec<u8>> {
        let size = self.len()?;
        if size > limit {
            return Err(error("payload byte limit"));
        }
        let source = self.take(size)?;
        self.budget.allocate(size, 1)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(size)
            .map_err(|_| error("byte allocation refused"))?;
        bytes.extend_from_slice(source);
        Ok(bytes)
    }
    pub(super) fn string(&mut self) -> Result<String> {
        let bytes = self.bytes()?;
        String::from_utf8(bytes).map_err(|_| error("invalid UTF-8"))
    }
}

pub(super) struct Encoder {
    pub(super) encoding: Encoding,
    bytes: Vec<u8>,
    limit: usize,
}
impl Encoder {
    pub(super) fn new(encoding: Encoding) -> Self {
        Self::bounded(encoding, MAX_BYTES)
    }
    pub(super) fn bounded(encoding: Encoding, limit: usize) -> Self {
        Self {
            encoding,
            bytes: Vec::new(),
            limit: limit.min(MAX_BYTES),
        }
    }
    pub(super) fn raw(&mut self, bytes: &[u8]) -> Result<()> {
        let size = self
            .bytes
            .len()
            .checked_add(bytes.len())
            .ok_or_else(|| error("output size overflow"))?;
        if size > self.limit {
            return Err(error("encoded byte limit"));
        }
        self.bytes
            .try_reserve(bytes.len())
            .map_err(|_| error("output allocation refused"))?;
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }
    pub(super) fn finish(self) -> Vec<u8> {
        self.bytes
    }
    pub(super) fn u8(&mut self, value: u8) -> Result<()> {
        self.raw(&[value])
    }
    fn unsigned(&mut self, value: u64, width: usize) -> Result<()> {
        let bytes = value.to_le_bytes();
        if self.encoding == Encoding::V2 {
            return self.raw(&bytes[..width]);
        }
        if value <= 250 {
            self.u8(value as u8)
        } else if value <= u64::from(u16::MAX) {
            self.u8(251)?;
            self.raw(&bytes[..2])
        } else if value <= u64::from(u32::MAX) {
            self.u8(252)?;
            self.raw(&bytes[..4])
        } else {
            self.u8(253)?;
            self.raw(&bytes)
        }
    }
    pub(super) fn u32(&mut self, value: u32) -> Result<()> {
        self.unsigned(u64::from(value), 4)
    }
    pub(super) fn u64(&mut self, value: u64) -> Result<()> {
        self.unsigned(value, 8)
    }
    pub(super) fn len(&mut self, value: usize) -> Result<()> {
        self.u64(u64::try_from(value).map_err(|_| error("length exceeds u64"))?)
    }
    pub(super) fn bytes(&mut self, bytes: &[u8]) -> Result<()> {
        self.len(bytes.len())?;
        self.raw(bytes)
    }
    pub(super) fn string(&mut self, value: &str) -> Result<()> {
        self.bytes(value.as_bytes())
    }
}

pub(super) trait Wire: Sized {
    fn read(decoder: &mut Decoder<'_>) -> Result<Self>;
    fn write(&self, encoder: &mut Encoder) -> Result<()>;
}

macro_rules! scalar {
    ($ty:ty, $read:ident, $write:ident) => {
        impl Wire for $ty {
            fn read(r: &mut Decoder<'_>) -> Result<Self> {
                r.$read()
            }
            fn write(&self, w: &mut Encoder) -> Result<()> {
                w.$write(*self)
            }
        }
    };
}
scalar!(u8, u8, u8);
scalar!(u32, u32, u32);
scalar!(u64, u64, u64);
impl Wire for bool {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        r.boolean()
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.u8(u8::from(*self))
    }
}
impl Wire for usize {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        r.len()
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.len(*self)
    }
}
impl Wire for String {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        r.string()
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.string(self)
    }
}
impl<T: Wire> Wire for Option<T> {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u8()? {
            0 => Ok(None),
            1 => Ok(Some(T::read(r)?)),
            _ => Err(error("invalid option tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            None => w.u8(0),
            Some(v) => {
                w.u8(1)?;
                v.write(w)
            }
        }
    }
}
impl<T: Wire> Wire for Vec<T> {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        let len = r.len()?;
        r.budget.can_allocate(len, size_of::<T>().max(1))?;
        let mut values = Vec::new();
        let mut accounted = 0;
        for _ in 0..len {
            let value = T::read(r)?;
            r.push(&mut values, &mut accounted, value, len)?;
        }
        Ok(values)
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.len(self.len())?;
        for value in self {
            value.write(w)?;
        }
        Ok(())
    }
}
impl<T: Wire> Wire for Box<T> {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        r.budget.can_allocate(1, size_of::<T>())?;
        let value = T::read(r)?;
        r.budget.allocate(1, size_of::<T>())?;
        Ok(Box::new(value))
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        (**self).write(w)
    }
}
impl<A: Wire, B: Wire> Wire for (A, B) {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok((A::read(r)?, B::read(r)?))
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.0.write(w)?;
        self.1.write(w)
    }
}
