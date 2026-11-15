// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The original enum algorithm, with its real variable work made fallible.

use super::*;
use crate::ty::EnumLayoutDescriptor;

mod descriptor;
mod tag;

pub(super) struct Frame<'q> {
    pub(super) index: usize,
    def: &'q EnumDef,
    discriminants: Vec<i128>,
    tag: EnumTagRepr,
    tag_size_bits: u64,
    lane_align_bits: Option<u64>,
    variant: usize,
    field: usize,
    offset_bits: u64,
    variant_align_bits: u64,
    field_sizes: Vec<u64>,
    field_aligns: Vec<u64>,
    payload_size_bits: u64,
    payload_align_bits: u64,
    variant_field_sizes: Vec<Vec<u64>>,
    variant_field_aligns: Vec<Vec<u64>>,
    never_field: bool,
}

impl<'q> Frame<'q> {
    pub(super) fn begin<O: ExecutionObserver>(
        table: &'q LayoutTable<'_>,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Self> {
        work.poll()?;
        let def = &table.module.enums[index];
        let discriminants = tag::discriminants(def, work)?;
        let prepared = (|| {
            let tag = tag::canonical(def, &discriminants, work)?;
            let lane = match def.layout.as_ref().map(|desc| &desc.encoding) {
                None | Some(EnumTagEncoding::Direct { .. }) => {
                    Some(tag::alignment(table, tag, work)?)
                }
                Some(EnumTagEncoding::Niche { niche_ty, .. }) => {
                    Some(tag::alignment(table, *niche_ty, work)?)
                }
                Some(EnumTagEncoding::Untagged | EnumTagEncoding::SingleInhabited { .. }) => None,
            };
            Ok((tag, lane))
        })();
        let (tag, lane_align_bits) = match prepared {
            Ok(prepared) => prepared,
            Err(error) => {
                work.retire_copy_vec(discriminants);
                if let Err(stop) = work.poll() {
                    work.retire_error(error);
                    return Err(stop);
                }
                return Err(error);
            }
        };
        Ok(Self {
            index,
            def,
            discriminants,
            tag,
            tag_size_bits: tag.size_bytes() * 8,
            lane_align_bits,
            variant: 0,
            field: 0,
            offset_bits: 0,
            variant_align_bits: 8,
            field_sizes: Vec::new(),
            field_aligns: Vec::new(),
            payload_size_bits: 0,
            payload_align_bits: 8,
            variant_field_sizes: Vec::new(),
            variant_field_aligns: Vec::new(),
            never_field: false,
        })
    }

    fn unavailable(&self) -> LayoutError {
        LayoutError::EnumLayoutUnavailable(self.def.id)
    }

    pub(super) fn next<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'q Ty>> {
        while let Some(variant) = self.def.variants.get(self.variant) {
            work.poll()?;
            let inactive = matches!(&self.def.layout, Some(layout) if matches!(layout.encoding,
                EnumTagEncoding::SingleInhabited { variant } if usize::try_from(variant).ok() != Some(self.variant)));
            if !inactive && let Some(field) = variant.fields.get(self.field) {
                return Ok(Some(field));
            }
            let size = align_up_bits(self.offset_bits, self.variant_align_bits)?;
            work.reserve(&mut self.variant_field_sizes)?;
            work.reserve(&mut self.variant_field_aligns)?;
            work.admit(2, 2 * size_of::<Vec<u64>>())?;
            self.payload_size_bits = self.payload_size_bits.max(size);
            self.payload_align_bits = self.payload_align_bits.max(self.variant_align_bits);
            self.variant_field_sizes
                .push(core::mem::take(&mut self.field_sizes));
            self.variant_field_aligns
                .push(core::mem::take(&mut self.field_aligns));
            self.offset_bits = 0;
            self.variant_align_bits = 8;
            self.variant += 1;
            self.field = 0;
        }
        Ok(None)
    }

    pub(super) fn take<O: ExecutionObserver>(
        &mut self,
        layout: &TyLayoutShape,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.poll()?;
        let ty = &self.def.variants[self.variant].fields[self.field];
        let size = layout.size_bytes().ok_or_else(|| self.unavailable())?;
        let align = if matches!(ty, Ty::Never) {
            self.never_field = true;
            8
        } else {
            layout.align_bits.ok_or_else(|| self.unavailable())?.max(8)
        };
        let offset = align_up_bits(self.offset_bits, align)?;
        let offset = offset
            .checked_add(layout.size_bits)
            .ok_or(LayoutError::SizeOverflow)?;
        work.reserve(&mut self.field_sizes)?;
        work.reserve(&mut self.field_aligns)?;
        work.admit(2, 2 * size_of::<u64>())?;
        self.offset_bits = offset;
        self.variant_align_bits = self.variant_align_bits.max(align);
        self.field_sizes.push(size);
        self.field_aligns.push(align / 8);
        self.field += 1;
        Ok(())
    }

    pub(super) fn finish<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R<EnumLayoutShape> {
        work.poll()?;
        if self.never_field && self.def.layout.is_none() {
            return Err(self.unavailable().into());
        }
        let payload_offset_bits = align_up_bits(self.tag_size_bits, self.payload_align_bits)?;
        let (size_bits, align_bits) = if let Some(desc) = &self.def.layout {
            descriptor::validate(self, module, desc, work)?
        } else {
            let tag_align = self.lane_align_bits.ok_or_else(|| self.unavailable())?;
            let align = tag_align.max(self.payload_align_bits);
            let size = align_up_bits(
                payload_offset_bits
                    .checked_add(self.payload_size_bits)
                    .ok_or(LayoutError::SizeOverflow)?,
                align,
            )?;
            (size, align)
        };
        let descriptor = match &self.def.layout {
            Some(desc) => Some(descriptor::copy(desc, work)?),
            None => None,
        };
        Ok(EnumLayoutShape {
            id: self.def.id,
            tag: self.tag,
            tag_size_bits: self.tag_size_bits,
            payload_offset_bits,
            payload_size_bits: self.payload_size_bits,
            size_bits,
            align_bits,
            discriminants: core::mem::take(&mut self.discriminants),
            descriptor,
        })
    }

    pub(super) fn retire<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) {
        let Self {
            index,
            def,
            discriminants,
            tag,
            tag_size_bits,
            lane_align_bits,
            variant,
            field,
            offset_bits,
            variant_align_bits,
            field_sizes,
            field_aligns,
            payload_size_bits,
            payload_align_bits,
            variant_field_sizes,
            variant_field_aligns,
            never_field,
        } = self;
        work.retire_copy_vec(discriminants);
        work.retire_copy_vec(field_sizes);
        work.retire_copy_vec(field_aligns);
        work.retire_rows(variant_field_sizes);
        work.retire_rows(variant_field_aligns);
        work.retire_fixed((
            index,
            def,
            tag,
            tag_size_bits,
            lane_align_bits,
            variant,
            field,
        ));
        work.retire_fixed((
            offset_bits,
            variant_align_bits,
            payload_size_bits,
            payload_align_bits,
            never_field,
        ));
    }
}
