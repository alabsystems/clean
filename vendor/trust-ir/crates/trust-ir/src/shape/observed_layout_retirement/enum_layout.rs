// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn consume<O: ExecutionObserver>(shape: EnumLayoutShape, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<EnumLayoutShape>().saturating_add(1));
    let EnumLayoutShape {
        id,
        tag,
        tag_size_bits,
        payload_offset_bits,
        payload_size_bits,
        size_bits,
        align_bits,
        discriminants,
        descriptor,
    } = shape;
    work.fixed(id);
    work.fixed(tag);
    work.fixed(tag_size_bits);
    work.fixed(payload_offset_bits);
    work.fixed(payload_size_bits);
    work.fixed(size_bits);
    work.fixed(align_bits);
    work.scalars(discriminants);
    work.step(size_of::<Option<EnumLayoutDescriptor>>().saturating_add(1));
    match descriptor {
        Some(descriptor) => consume_descriptor(descriptor, work),
        None => work.fixed(()),
    }
    work.poll();
}

fn consume_descriptor<O: ExecutionObserver>(
    descriptor: EnumLayoutDescriptor,
    work: &mut Work<'_, '_, O>,
) {
    work.step(size_of::<EnumLayoutDescriptor>().saturating_add(1));
    let EnumLayoutDescriptor {
        encoding,
        size,
        align,
        variant_field_offsets,
    } = descriptor;
    consume_encoding(encoding, work);
    work.fixed(size);
    work.fixed(align);
    consume_rows(variant_field_offsets, work);
}

fn consume_encoding<O: ExecutionObserver>(encoding: EnumTagEncoding, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<EnumTagEncoding>().saturating_add(1));
    match encoding {
        EnumTagEncoding::Direct { tag_offset } => work.fixed(tag_offset),
        EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } => {
            work.fixed(untagged_variant);
            work.fixed(niche_variants_start);
            work.fixed(niche_variants_end);
            work.fixed(niche_start);
            work.fixed(niche_offset);
            work.fixed(niche_ty);
        }
        EnumTagEncoding::Untagged => work.fixed(()),
        EnumTagEncoding::SingleInhabited { variant } => work.fixed(variant),
    }
}

fn consume_rows<O: ExecutionObserver>(mut rows: Vec<Vec<u64>>, work: &mut Work<'_, '_, O>) {
    loop {
        work.step(size_of::<Option<Vec<u64>>>().saturating_add(1));
        let Some(row) = rows.pop() else { break };
        work.scalars(row);
    }
    work.empty(rows);
}
