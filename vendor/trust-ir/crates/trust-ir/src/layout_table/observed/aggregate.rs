// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[derive(Clone, Copy)]
enum Spec<'q> {
    Struct(&'q StructDef),
    Tuple(&'q TupleLayoutDescriptor, &'q [Ty]),
    Closure(&'q ClosureLayoutDescriptor, &'q [Ty]),
}

pub(super) struct Aggregate<'q> {
    pub(super) key: Key,
    spec: Spec<'q>,
    size: u64,
    align: u64,
    clamp: u64,
    fields: Vec<FieldOffsetShape>,
    ranges: Vec<(u64, u64)>,
    carrier: Option<(u64, u64, u64)>,
    nontrivial: usize,
}

impl<'q> Aggregate<'q> {
    pub(super) fn begin(module: &'q Module, key: Key) -> R<Self> {
        let (spec, size, align, clamp) = match key {
            (0, index) => {
                let def = &module.structs[index];
                let size = def.size.ok_or(LayoutError::MissingStructSize(def.id))?;
                let align = def.align.ok_or(LayoutError::MissingStructAlign(def.id))?;
                if align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align) {
                    return Err(LayoutError::StructLayoutIncoherent(def.id).into());
                }
                let clamp = match def.repr {
                    StructRepr::Packed(packed) if packed != 0 && packed.is_power_of_two() => {
                        u64::from(packed)
                    }
                    StructRepr::Packed(_) => {
                        return Err(LayoutError::StructLayoutIncoherent(def.id).into());
                    }
                    _ => u64::MAX,
                };
                if align > clamp {
                    return Err(LayoutError::StructLayoutIncoherent(def.id).into());
                }
                (Spec::Struct(def), size, align, clamp)
            }
            (3, index) => {
                let desc = &module.tuple_layouts[index];
                let Some(Ty::Tuple(elems)) = module.types.get(desc.tuple_type.as_usize()) else {
                    return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type).into());
                };
                if desc.align == 0
                    || !desc.align.is_power_of_two()
                    || !desc.size.is_multiple_of(desc.align)
                    || desc.field_offsets.len() != elems.len()
                {
                    return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type).into());
                }
                (Spec::Tuple(desc, elems), desc.size, desc.align, u64::MAX)
            }
            (4, index) => {
                let desc = &module.closure_layouts[index];
                let captures = module
                    .closure_types
                    .get(desc.closure.as_usize())
                    .ok_or(LayoutError::ClosureLayoutIncoherent(desc.closure))?
                    .captures
                    .as_slice();
                if desc.align == 0
                    || !desc.align.is_power_of_two()
                    || !desc.size.is_multiple_of(desc.align)
                    || desc.capture_offsets.len() != captures.len()
                {
                    return Err(LayoutError::ClosureLayoutIncoherent(desc.closure).into());
                }
                (
                    Spec::Closure(desc, captures),
                    desc.size,
                    desc.align,
                    u64::MAX,
                )
            }
            _ => return Err(ObservedValueError::UnsupportedValue.into()),
        };
        Ok(Self {
            key,
            spec,
            size,
            align,
            clamp,
            fields: Vec::new(),
            ranges: Vec::new(),
            carrier: None,
            nontrivial: 0,
        })
    }

    fn bad(&self) -> LayoutError {
        match self.spec {
            Spec::Struct(def) => LayoutError::StructLayoutIncoherent(def.id),
            Spec::Tuple(desc, _) => LayoutError::TupleLayoutIncoherent(desc.tuple_type),
            Spec::Closure(desc, _) => LayoutError::ClosureLayoutIncoherent(desc.closure),
        }
    }

    pub(super) fn next(&self) -> Option<&'q Ty> {
        match self.spec {
            Spec::Struct(def) => def.fields.get(self.fields.len()).map(|field| &field.ty),
            Spec::Tuple(_, elems) | Spec::Closure(_, elems) => elems.get(self.fields.len()),
        }
    }

    pub(super) fn take<O: ExecutionObserver>(
        &mut self,
        layout: &TyLayoutShape,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.poll()?;
        let index = self.fields.len();
        let ty = self.next().ok_or(ObservedValueError::UnsupportedValue)?;
        let size = layout.size_bytes().ok_or_else(|| self.bad())?;
        let natural = layout
            .align_bits
            .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            .map(|bits| bits / 8)
            .ok_or_else(|| self.bad())?;
        let align = if matches!(self.spec, Spec::Struct(_)) {
            natural.max(1).min(self.clamp)
        } else {
            natural
        };
        let offset = match self.spec {
            Spec::Struct(def) => match def.fields[index].offset {
                Some(offset) => offset,
                None if size == 0 => 0,
                None => {
                    return Err(LayoutError::MissingFieldOffset {
                        struct_id: def.id,
                        field: index as u32,
                    }
                    .into());
                }
            },
            Spec::Tuple(desc, _) => desc.field_offsets[index],
            Spec::Closure(desc, _) => desc.capture_offsets[index],
        };
        if !offset.is_multiple_of(align)
            || align > self.align
            || offset.checked_add(size).is_none_or(|end| end > self.size)
        {
            return Err(self.bad().into());
        }
        let field = if matches!(self.spec, Spec::Struct(_)) {
            index as u32
        } else {
            u32::try_from(index).map_err(|_| self.bad())?
        };
        let offset_bits = offset.checked_mul(8).ok_or(LayoutError::SizeOverflow)?;
        work.reserve(&mut self.ranges)?;
        work.reserve(&mut self.fields)?;
        work.admit(1, size_of::<(u64, u64)>())?;
        work.admit(1, size_of::<FieldOffsetShape>())?;
        let name = match self.spec {
            Spec::Struct(def) => work.copy_text(&def.fields[index].name)?,
            _ => work.index_name(index)?,
        };
        if matches!(self.spec, Spec::Struct(def) if def.repr == StructRepr::Transparent)
            && (size != 0 || align != 1)
        {
            self.nontrivial += 1;
            self.carrier = Some((size, align, offset));
        }
        self.ranges.push((offset, size));
        self.fields.push(FieldOffsetShape {
            field,
            name,
            ty_shape: ty.shape(),
            offset_bits: Some(offset_bits),
        });
        Ok(())
    }

    pub(super) fn finish<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<TyLayoutShape> {
        work.poll()?;
        if work.overlap(&self.ranges)? {
            return Err(self.bad().into());
        }
        if matches!(self.spec, Spec::Struct(def) if def.repr == StructRepr::Transparent) {
            let (size, align, offset) = self.carrier.unwrap_or((0, 1, 0));
            if self.nontrivial > 1 || self.size != size || self.align != align || offset != 0 {
                return Err(self.bad().into());
            }
        }
        let size_bits = self.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?;
        let align_bits = Some(self.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?);
        let fields = core::mem::take(&mut self.fields);
        let kind = match self.spec {
            Spec::Struct(def) => TyLayoutKind::Struct { id: def.id, fields },
            Spec::Tuple(_, _) => TyLayoutKind::Tuple { fields },
            Spec::Closure(desc, _) => TyLayoutKind::Closure {
                id: desc.closure,
                captures: fields,
            },
        };
        Ok(TyLayoutShape {
            size_bits,
            align_bits,
            kind,
        })
    }

    pub(super) fn retire<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) {
        let Self {
            key,
            spec,
            size,
            align,
            clamp,
            fields,
            ranges,
            carrier,
            nontrivial,
        } = self;
        work.retire_fields(fields);
        work.retire_copy_vec(ranges);
        work.retire_fixed((key, spec, size, align, clamp, carrier, nontrivial));
    }
}

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn overlap(&mut self, ranges: &[(u64, u64)]) -> R<bool> {
        self.clear_spans();
        self.poll()?;
        let result = (|| {
            let (mut overflowing, mut nonempty, mut duplicate) = (0usize, 0usize, false);
            for &(offset, size) in ranges {
                self.poll()?;
                if size == 0 {
                    continue;
                }
                nonempty += 1;
                if let Some(end) = offset.checked_add(size) {
                    self.lookup(self.spans.len())?;
                    if self.spans.contains(&(offset, end)) {
                        duplicate = true;
                    } else {
                        self.tree::<(u64, u64), ()>(self.spans.len())?;
                        self.spans.insert((offset, end));
                    }
                } else {
                    overflowing += 1;
                }
            }
            if overflowing > 0 {
                return Ok(nonempty >= 2);
            }
            if duplicate {
                return Ok(true);
            }
            let mut reach = None;
            for &(start, end) in &self.spans {
                storage::admit(self.session, self.site, 1, 0)?;
                if let Some(previous) = reach
                    && start < previous
                {
                    return Ok(true);
                }
                reach = Some(reach.map_or(end, |previous: u64| previous.max(end)));
            }
            Ok(false)
        })();
        self.clear_spans();
        self.poll()?;
        result
    }
}
