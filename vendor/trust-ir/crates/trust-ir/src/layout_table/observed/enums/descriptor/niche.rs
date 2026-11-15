// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

pub(super) fn validate<O: ExecutionObserver>(
    frame: &Frame<'_>,
    module: &Module,
    desc: &EnumLayoutDescriptor,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.poll()?;
    let EnumTagEncoding::Niche {
        untagged_variant,
        niche_variants_start,
        niche_variants_end,
        niche_start,
        niche_offset,
        niche_ty,
    } = &desc.encoding
    else {
        return Err(ObservedValueError::UnsupportedValue.into());
    };
    let count = u32::try_from(frame.def.variants.len()).map_err(|_| frame.unavailable())?;
    let size = niche_ty.size_bytes();
    let align = frame.lane_align_bits.ok_or_else(|| frame.unavailable())? / 8;
    let bits = u32::try_from(size * 8).map_err(|_| frame.unavailable())?;
    let mask = match bits {
        0 => return Err(frame.unavailable().into()),
        128 => u128::MAX,
        bits if bits < 128 => (1u128 << bits) - 1,
        _ => return Err(frame.unavailable().into()),
    };
    let span = niche_variants_end
        .checked_sub(*niche_variants_start)
        .map(u128::from)
        .ok_or_else(|| frame.unavailable())?;
    if *untagged_variant >= count || *niche_variants_end >= count {
        return Err(frame.unavailable().into());
    }
    if inhabit::unencoded(
        module,
        frame.def,
        *untagged_variant,
        *niche_variants_start,
        *niche_variants_end,
        work,
    )?
    .is_some()
    {
        return Err(frame.unavailable().into());
    }
    if span > mask
        || *niche_start > mask
        || align > desc.align
        || !niche_offset.is_multiple_of(align)
        || niche_offset
            .checked_add(size)
            .is_none_or(|end| end > desc.size)
    {
        return Err(frame.unavailable().into());
    }
    let untagged = *untagged_variant as usize;
    let end = niche_offset
        .checked_add(size)
        .ok_or_else(|| frame.unavailable())?;
    let mut covered = false;
    for (&offset, &field_size) in desc.variant_field_offsets[untagged]
        .iter()
        .zip(&frame.variant_field_sizes[untagged])
    {
        work.poll()?;
        if field_size > 0
            && offset <= *niche_offset
            && offset
                .checked_add(field_size)
                .is_some_and(|field_end| field_end >= end)
        {
            covered = true;
            break;
        }
    }
    if !covered {
        return Err(frame.unavailable().into());
    }
    for variant in *niche_variants_start..=*niche_variants_end {
        work.poll()?;
        if variant == *untagged_variant {
            continue;
        }
        let variant = variant as usize;
        for (&offset, &field_size) in desc.variant_field_offsets[variant]
            .iter()
            .zip(&frame.variant_field_sizes[variant])
        {
            work.poll()?;
            if byte_ranges_overlap(*niche_offset, size, offset, field_size) {
                return Err(frame.unavailable().into());
            }
        }
    }
    Ok(())
}
