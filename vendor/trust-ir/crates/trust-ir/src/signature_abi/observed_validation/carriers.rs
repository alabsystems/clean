// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn claim<O: ExecutionObserver>(
        &mut self,
        kind: Kind,
        index: u32,
        b: &AbiBinding,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(4, 0)?;
        let census = match kind {
            Kind::Result => &mut self.results,
            _ => &mut self.parameters,
        };
        w.admit(1, size_of::<Option<&mut Vec<(u64, u64)>>>())?;
        let Some(ranges) = census.get_mut(index as usize) else {
            w.text(kind.label(), &mut self.reason)?;
            w.text(" binding ", &mut self.reason)?;
            w.unsigned(u128::from(index), &mut self.reason)?;
            w.text(" is out of range", &mut self.reason)?;
            return Ok(false);
        };
        w.admit(6, size_of::<u64>())?;
        let Some(end) = b.carrier_offset.checked_add(b.carrier_bytes) else {
            return self.fail("carrier binding extent overflows", w);
        };
        if b.carrier_bytes == 0 {
            return self.fail("carrier binding extent is empty", w);
        }
        let mut i = 0;
        while let Some(&(start, stop)) = w.at(ranges, i)? {
            w.admit(3, 0)?;
            if b.carrier_offset < stop && start < end {
                w.text(kind.label(), &mut self.reason)?;
                w.text(" binding ", &mut self.reason)?;
                w.unsigned(u128::from(index), &mut self.reason)?;
                w.text(" overlaps or is duplicated", &mut self.reason)?;
                return Ok(false);
            }
            w.next(&mut i)?;
        }
        w.push(ranges, (b.carrier_offset, end))?;
        Ok(true)
    }
    fn sort_ranges<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        let mut i = 1;
        loop {
            w.admit(1, 0)?;
            if i >= self.ranges.len() {
                return Ok(());
            }
            let mut j = i;
            while j > 0 {
                w.admit(3, 2 * size_of::<(u64, u64)>())?;
                if self.ranges[j - 1] <= self.ranges[j] {
                    break;
                }
                w.admit(1, 3 * size_of::<(u64, u64)>())?;
                self.ranges.swap(j - 1, j);
                j -= 1;
            }
            w.next(&mut i)?;
        }
    }
    pub(super) fn covered<O: ExecutionObserver>(
        &mut self,
        arg: &AbiArgument,
        start: u64,
        bytes: u64,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        self.retire_ranges(w);
        let mut i = 0;
        while let Some(b) = w.at(&arg.bindings, i)? {
            w.admit(4, 2 * size_of::<u64>())?;
            if let (Some(source_end), Some(carrier_end)) = (
                b.source_offset.checked_add(b.source_bytes),
                b.source_offset.checked_add(b.carrier_bytes),
            ) {
                w.push(
                    &mut self.ranges,
                    (b.source_offset, source_end.min(carrier_end)),
                )?;
            }
            w.next(&mut i)?;
        }
        self.sort_ranges(w)?;
        let mut cursor = start;
        i = 0;
        while let Some(&(low, high)) = w.at(&self.ranges, i)? {
            w.admit(3, size_of::<u64>())?;
            if low <= cursor && cursor < high {
                cursor = high
            }
            w.next(&mut i)?;
        }
        w.admit(2, size_of::<bool>())?;
        Ok(start.checked_add(bytes).is_some_and(|end| cursor >= end))
    }
    pub(super) fn carrier_bounds<O: ExecutionObserver>(
        &mut self,
        kind: Kind,
        types: &[Ty],
        pointer_bytes: u8,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut i = 0;
        while let Some(ty) = w.at(types, i)? {
            w.admit(32, size_of::<Option<u64>>())?;
            let bytes = match ty {
                Ty::Ptr
                | Ty::Func(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Isize
                | Ty::Usize => Some(u64::from(pointer_bytes)),
                Ty::Bool => Some(1),
                _ => ty
                    .bit_width_observed(w.session, w.site)?
                    .map(|bits| u64::from(bits).div_ceil(8)),
            };
            if let Some(bytes) = bytes {
                self.retire_ranges(w);
                let mut j = 0;
                loop {
                    w.admit(2, size_of::<Option<(u64, u64)>>())?;
                    let census = match kind {
                        Kind::Result => &self.results,
                        _ => &self.parameters,
                    };
                    let rows = w.at(census, i)?.ok_or(ObservedValueError::InvalidRange)?;
                    let row = w.at(rows, j)?.copied();
                    let Some(row) = row else { break };
                    w.push(&mut self.ranges, row)?;
                    w.next(&mut j)?;
                }
                self.sort_ranges(w)?;
                let mut cursor = 0;
                let mut j = 0;
                while let Some(&(start, end)) = w.at(&self.ranges, j)? {
                    w.admit(3, size_of::<u64>())?;
                    if start != cursor || end > bytes {
                        return self
                            .fail("scalar carrier census has a gap or exceeds its width", w);
                    }
                    cursor = end;
                    w.next(&mut j)?;
                }
                w.admit(1, 0)?;
                if cursor != bytes {
                    return self.fail("scalar carrier census omits bytes", w);
                }
            }
            w.next(&mut i)?;
        }
        Ok(true)
    }
}
