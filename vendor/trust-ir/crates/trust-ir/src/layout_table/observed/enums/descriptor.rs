// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

mod niche;

pub(super) fn validate<O: ExecutionObserver>(
    frame: &Frame<'_>,
    module: &Module,
    desc: &EnumLayoutDescriptor,
    work: &mut Work<'_, '_, O>,
) -> R<(u64, u64)> {
    work.poll()?;
    if desc.align == 0
        || !desc.align.is_power_of_two()
        || !desc.size.is_multiple_of(desc.align)
        || desc.variant_field_offsets.len() != frame.def.variants.len()
    {
        return Err(frame.unavailable().into());
    }
    for variant in 0..desc.variant_field_offsets.len() {
        work.poll()?;
        row(frame, desc, variant, work)?;
    }
    match &desc.encoding {
        EnumTagEncoding::Untagged => {
            if frame.def.variants.len() != 1 {
                return Err(frame.unavailable().into());
            }
        }
        EnumTagEncoding::SingleInhabited { variant } => {
            let active = usize::try_from(*variant).map_err(|_| frame.unavailable())?;
            let selected = frame
                .def
                .variants
                .get(active)
                .ok_or_else(|| frame.unavailable())?;
            if super::super::inhabit::some(module, selected.fields.iter(), work)? {
                return Err(frame.unavailable().into());
            }
            for (index, item) in frame.def.variants.iter().enumerate() {
                work.poll()?;
                if index != active
                    && !super::super::inhabit::some(module, item.fields.iter(), work)?
                {
                    return Err(frame.unavailable().into());
                }
            }
        }
        EnumTagEncoding::Direct { tag_offset } => direct(frame, desc, *tag_offset, work)?,
        EnumTagEncoding::Niche { .. } => niche::validate(frame, module, desc, work)?,
    }
    Ok((
        desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
        desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
    ))
}

fn row<O: ExecutionObserver>(
    frame: &Frame<'_>,
    desc: &EnumLayoutDescriptor,
    variant: usize,
    work: &mut Work<'_, '_, O>,
) -> R {
    let offsets = &desc.variant_field_offsets[variant];
    let sizes = &frame.variant_field_sizes[variant];
    let aligns = &frame.variant_field_aligns[variant];
    if offsets.len() != sizes.len() || offsets.len() != aligns.len() {
        return Err(frame.unavailable().into());
    }
    for index in 0..offsets.len() {
        work.poll()?;
        if !offsets[index].is_multiple_of(aligns[index])
            || aligns[index] > desc.align
            || offsets[index]
                .checked_add(sizes[index])
                .is_none_or(|end| end > desc.size)
        {
            return Err(frame.unavailable().into());
        }
    }
    let mut ranges = Vec::new();
    let result = (|| {
        for index in 0..offsets.len() {
            work.push(&mut ranges, (offsets[index], sizes[index]))?;
        }
        if work.overlap(&ranges)? {
            return Err(frame.unavailable().into());
        }
        Ok(())
    })();
    work.retire_copy_vec(ranges);
    work.poll()?;
    result
}

fn direct<O: ExecutionObserver>(
    frame: &Frame<'_>,
    desc: &EnumLayoutDescriptor,
    offset: u64,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.poll()?;
    let size = frame.tag_size_bits / 8;
    let align = frame.lane_align_bits.ok_or_else(|| frame.unavailable())? / 8;
    if align > desc.align
        || !offset.is_multiple_of(align)
        || offset.checked_add(size).is_none_or(|end| end > desc.size)
    {
        return Err(frame.unavailable().into());
    }
    for (offsets, sizes) in desc
        .variant_field_offsets
        .iter()
        .zip(&frame.variant_field_sizes)
    {
        work.poll()?;
        for (&field_offset, &field_size) in offsets.iter().zip(sizes) {
            work.poll()?;
            if byte_ranges_overlap(offset, size, field_offset, field_size) {
                return Err(frame.unavailable().into());
            }
        }
    }
    Ok(())
}

pub(super) fn copy<O: ExecutionObserver>(
    desc: &EnumLayoutDescriptor,
    work: &mut Work<'_, '_, O>,
) -> R<EnumLayoutDescriptor> {
    let mut rows = Vec::new();
    let result = (|| {
        for source in &desc.variant_field_offsets {
            work.empty_row(&mut rows)?;
            let row = rows
                .last_mut()
                .ok_or(ObservedValueError::UnsupportedValue)?;
            for &offset in source {
                work.push(row, offset)?;
            }
        }
        work.admit(1, size_of::<EnumLayoutDescriptor>())
    })();
    if let Err(error) = result {
        work.retire_rows(rows);
        work.poll()?;
        return Err(error);
    }
    // The encoding contains only bounded scalar payloads; no derived clone of
    // the recursively owned offset rows occurs.
    let encoding = match &desc.encoding {
        EnumTagEncoding::Untagged => EnumTagEncoding::Untagged,
        EnumTagEncoding::SingleInhabited { variant } => {
            EnumTagEncoding::SingleInhabited { variant: *variant }
        }
        EnumTagEncoding::Direct { tag_offset } => EnumTagEncoding::Direct {
            tag_offset: *tag_offset,
        },
        EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } => EnumTagEncoding::Niche {
            untagged_variant: *untagged_variant,
            niche_variants_start: *niche_variants_start,
            niche_variants_end: *niche_variants_end,
            niche_start: *niche_start,
            niche_offset: *niche_offset,
            niche_ty: *niche_ty,
        },
    };
    Ok(EnumLayoutDescriptor {
        encoding,
        size: desc.size,
        align: desc.align,
        variant_field_offsets: rows,
    })
}
