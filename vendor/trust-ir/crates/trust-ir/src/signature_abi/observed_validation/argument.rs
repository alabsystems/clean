// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn argument<O: ExecutionObserver>(
        &mut self,
        arg: &AbiArgument,
        kind: Kind,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        self.retire_ranges(w);
        w.admit(16, 0)?;
        if !arg.align.is_power_of_two() {
            return self.fail("source alignment is not a nonzero power of two", w);
        }
        if matches!(arg.mode, AbiPassMode::Ignore) {
            return if arg.bindings.is_empty() {
                Ok(true)
            } else {
                self.fail("Ignore requires no lowered bindings", w)
            };
        }
        if arg.bindings.is_empty() || arg.size == 0 {
            return self.fail("non-ignored source value has no storage or no binding", w);
        }
        let mut i = 0;
        while let Some(b) = w.at(&arg.bindings, i)? {
            w.admit(8, 2 * size_of::<u64>())?;
            let Some(end) = b.source_offset.checked_add(b.source_bytes) else {
                return self.fail("source binding extent overflows", w);
            };
            if b.source_bytes == 0 || end > arg.size {
                return self.fail("source binding extent is empty or exceeds storage", w);
            }
            let mut j = 0;
            while let Some(&(start, stop)) = w.at(&self.ranges, j)? {
                w.admit(3, 0)?;
                if b.source_offset < stop && start < end {
                    return self.fail("source binding extents overlap", w);
                }
                w.next(&mut j)?;
            }
            w.push(&mut self.ranges, (b.source_offset, end))?;
            w.next(&mut i)?;
        }
        w.admit(32, 0)?;
        match &arg.mode {
            AbiPassMode::Ignore => return Err(ObservedValueError::InvalidRange),
            AbiPassMode::Direct(a) => {
                if !self.scalar(a, arg.size, w)? {
                    return Ok(false);
                }
            }
            AbiPassMode::Pair(a, b) => {
                if !self.scalar(a, arg.size, w)? || !self.scalar(b, arg.size, w)? {
                    return Ok(false);
                }
                w.admit(8, 0)?;
                // Both exact scalar guards already checked these extents.
                let a_end = a
                    .source_offset
                    .checked_add(a.source_bytes)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                let b_end = b
                    .source_offset
                    .checked_add(b.source_bytes)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                if a.source_offset < b_end && b.source_offset < a_end {
                    return self.fail("pair source lanes overlap", w);
                }
            }
            AbiPassMode::Cast {
                prefix,
                rest_offset,
                rest,
                attributes,
                ..
            } => {
                if !self.attributes(attributes, w)? {
                    return Ok(false);
                }
                let mut end = 0u64;
                let mut i = 0;
                while let Some(reg) = w.at(prefix, i)? {
                    if !self.register(reg, w)? {
                        return Ok(false);
                    }
                    w.admit(1, size_of::<u64>())?;
                    let Some(next) = end.checked_add(reg.bytes) else {
                        return self.fail("cast prefix extent overflows", w);
                    };
                    end = next;
                    w.next(&mut i)?;
                }
                if !self.register(&rest.unit, w)? {
                    return Ok(false);
                }
                w.admit(12, 0)?;
                let offset = rest_offset.unwrap_or(end);
                if offset < end {
                    return self.fail("cast rest overlaps its prefix", w);
                }
                let Some(end) = offset.checked_add(rest.total) else {
                    return self.fail("cast extent overflows", w);
                };
                if end == 0 || offset > arg.size || end > arg.size {
                    return self.fail("cast live extent exceeds source storage", w);
                }
                if rest.total % rest.unit.bytes != 0 && rest.unit.class != AbiRegisterClass::Integer
                {
                    return self.fail("only a final integer cast carrier may be partially live", w);
                }
            }
            AbiPassMode::Indirect {
                attributes,
                metadata_attributes,
                on_stack,
                caller_copy,
            } => {
                if !self.attributes(attributes, w)? {
                    return Ok(false);
                }
                if let Some(attrs) = metadata_attributes {
                    if !self.attributes(attrs, w)? {
                        return Ok(false);
                    }
                    return self.fail("unsized indirect metadata transport requires explicit data/metadata bindings and a dynamic source extent",w);
                }
                w.admit(16, 0)?;
                if matches!(kind, Kind::Result) && (*on_stack || *caller_copy) {
                    return self.fail("indirect result cannot be an argument stack copy", w);
                }
                if metadata_attributes.is_none()
                    && (arg.bindings.len() != 1
                        || arg.bindings[0].source_offset != 0
                        || arg.bindings[0].source_bytes != arg.size)
                {
                    return self.fail(
                        "indirect binding must describe the complete source storage",
                        w,
                    );
                }
            }
        }
        match &arg.mode {
            AbiPassMode::Direct(a) => {
                if !self.covered(arg, a.source_offset, a.source_bytes, w)? {
                    return self.fail("binding census omits a direct source lane", w);
                }
            }
            AbiPassMode::Pair(a, b) => {
                if !self.covered(arg, a.source_offset, a.source_bytes, w)?
                    || !self.covered(arg, b.source_offset, b.source_bytes, w)?
                {
                    return self.fail("binding census omits a pair source lane", w);
                }
            }
            AbiPassMode::Cast {
                prefix,
                rest_offset,
                rest,
                ..
            } => {
                let mut total = 0u64;
                let mut i = 0;
                while let Some(reg) = w.at(prefix, i)? {
                    w.admit(1, size_of::<u64>())?;
                    total = total
                        .checked_add(reg.bytes)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    w.next(&mut i)?;
                }
                if (total != 0 && !self.covered(arg, 0, total, w)?)
                    || (rest.total != 0
                        && !self.covered(arg, rest_offset.unwrap_or(total), rest.total, w)?)
                {
                    return self.fail("binding census omits a cast source lane", w);
                }
            }
            _ => {}
        }
        Ok(true)
    }
    fn register<O: ExecutionObserver>(
        &mut self,
        reg: &AbiRegister,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(3, 0)?;
        if reg.bytes == 0 || reg.bytes > 256 {
            self.fail("ABI carrier has an invalid width", w)
        } else {
            Ok(true)
        }
    }
    fn attributes<O: ExecutionObserver>(
        &mut self,
        attrs: &AbiAttributes,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(3, 0)?;
        if attrs
            .pointee_align
            .is_some_and(|align| !align.is_power_of_two())
        {
            self.fail("pointee alignment is not a nonzero power of two", w)
        } else {
            Ok(true)
        }
    }
    fn scalar<O: ExecutionObserver>(
        &mut self,
        a: &AbiScalar,
        size: u64,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        if !self.register(&a.register, w)? || !self.attributes(&a.attributes, w)? {
            return Ok(false);
        }
        w.admit(32, 0)?;
        if a.value_bits == 0 || u64::from(a.value_bits) > a.source_bytes.saturating_mul(8) {
            return self.fail(
                "scalar defined-bit width is empty or exceeds live storage",
                w,
            );
        }
        if a.source_bytes == 0
            || a.source_bytes > a.register.bytes
            || a.source_offset
                .checked_add(a.source_bytes)
                .is_none_or(|end| end > size)
        {
            return self.fail(
                "scalar live extent is empty, wider than its carrier, or outside storage",
                w,
            );
        }
        if a.attributes.extension != AbiExtension::None
            && a.register.class != AbiRegisterClass::Integer
        {
            return self.fail("integer extension is recorded on a non-integer carrier", w);
        }
        Ok(true)
    }
}
