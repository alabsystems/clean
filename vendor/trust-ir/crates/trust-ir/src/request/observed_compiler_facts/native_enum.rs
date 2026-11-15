// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Work {
    pub(super) fn native_enum<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        definition: &EnumDef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        let mut index = 0;
        while index < layout.variants.len() {
            admit(session, site, 1, 0)?;
            let variant = &layout.variants[index];
            if !set_insert(
                &mut self.seen_variants,
                variant.variant_index,
                session,
                site,
            )? {
                self.invalid(reference, "enum_layout.variant_index", session, site)?;
            }
            admit(session, site, 1, 0)?;
            let Some(expected) = definition.variants.get(variant.variant_index as usize) else {
                self.invalid(reference, "enum_layout.variant", session, site)?;
                index += 1;
                continue;
            };
            if !text_equal(&expected.name, &variant.name, session, site)? {
                self.invalid(reference, "enum_layout.variant", session, site)?;
            }
            admit(session, site, 1, 0)?;
            if variant.fields.len() != expected.fields.len() {
                self.invalid(reference, "enum_layout.variant.fields", session, site)?;
            }
            let mut field_index = 0;
            while field_index < variant.fields.len() {
                admit(session, site, 2, 0)?;
                let field = &variant.fields[field_index];
                if let Some(expected) = expected.fields.get(field_index) {
                    if u32::try_from(field_index) != Ok(field.field) {
                        self.invalid(reference, "enum_layout.variant.fields", session, site)?;
                    }
                    // Ty::shape is a fixed discriminant classification, not a
                    // recursive type walk or equality over a variable payload.
                    admit(session, site, 4, size_of::<crate::TyShape>())?;
                    if field.ty_shape != expected.shape() {
                        self.invalid(
                            reference,
                            "enum_layout.variant.fields.ty_shape",
                            session,
                            site,
                        )?;
                    }
                }
                field_index += 1;
            }
            admit(session, site, 1, 0)?;
            if variant.size_bits > fact.layout.size_bits {
                self.invalid(reference, "layout.size_bits", session, site)?;
            }
            admit(session, site, 4, 0)?;
            match (fact.layout.align_bits, variant.align_bits) {
                (_, Some(0)) => {
                    self.invalid(reference, "enum_layout.variant.align_bits", session, site)?
                }
                (Some(outer), Some(inner))
                    if outer == 0 || outer < inner || !outer.is_multiple_of(inner) =>
                {
                    self.invalid(reference, "layout.align_bits", session, site)?;
                }
                _ => {}
            }
            index += 1;
        }
        admit(session, site, 1, 0)?;
        match layout.tag_encoding {
            NativeEnumTagEncoding::Direct => self.direct(fact, layout, session, site),
            NativeEnumTagEncoding::Niche => self.niche(fact, layout, definition, session, site),
            NativeEnumTagEncoding::Untagged => self.untagged(fact, layout, session, site),
        }
    }

    fn direct<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 1, 0)?;
        if layout.niche.is_some() {
            self.invalid(reference, "enum_layout.niche", session, site)?;
        }
        admit(session, site, 4, 0)?;
        match (layout.tag_bits, layout.discriminant_offset_bits) {
            (Some(bits), Some(offset)) => {
                if bits == 0 {
                    return self.invalid(reference, "enum_layout.tag_bits", session, site);
                }
                if offset
                    .checked_add(u64::from(bits))
                    .is_none_or(|end| end > fact.layout.size_bits)
                {
                    self.invalid(
                        reference,
                        "enum_layout.discriminant_offset_bits",
                        session,
                        site,
                    )?;
                }
            }
            (None, _) => self.invalid(reference, "enum_layout.tag_bits", session, site)?,
            (_, None) => self.invalid(
                reference,
                "enum_layout.discriminant_offset_bits",
                session,
                site,
            )?,
        }
        let mut index = 0;
        while index < layout.variants.len() {
            admit(session, site, 1, 0)?;
            match layout.variants[index].discriminant {
                None => {
                    self.invalid(reference, "enum_layout.variant.discriminant", session, site)?
                }
                Some(value) => {
                    if !set_insert(&mut self.discriminants, value, session, site)? {
                        self.invalid(reference, "enum_layout.variant.discriminant", session, site)?;
                    }
                }
            }
            index += 1;
        }
        Ok(())
    }

    fn niche<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        definition: &EnumDef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 1, 0)?;
        if layout.tag_bits.is_some() {
            self.invalid(reference, "enum_layout.tag_bits", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if layout.discriminant_offset_bits.is_some() {
            self.invalid(
                reference,
                "enum_layout.discriminant_offset_bits",
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        let Some(niche) = &layout.niche else {
            return self.invalid(reference, "enum_layout.niche", session, site);
        };
        admit(session, site, 1, 0)?;
        if niche.valid_range.start > niche.valid_range.end {
            self.invalid(reference, "enum_layout.niche.valid_range", session, site)?;
        }
        admit(session, site, 1, 0)?;
        let Some(variant) = definition.variants.get(niche.variant_index as usize) else {
            return self.invalid(reference, "enum_layout.niche.variant_index", session, site);
        };
        admit(session, site, 2, 0)?;
        if let Some(field) = niche.field
            && variant.fields.get(field as usize).is_none()
        {
            self.invalid(reference, "enum_layout.niche.field", session, site)?;
        }
        Ok(())
    }

    fn untagged<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 1, 0)?;
        if layout.tag_bits.is_some() {
            self.invalid(reference, "enum_layout.tag_bits", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if layout.discriminant_offset_bits.is_some() {
            self.invalid(
                reference,
                "enum_layout.discriminant_offset_bits",
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if layout.niche.is_some() {
            self.invalid(reference, "enum_layout.niche", session, site)?;
        }
        let mut index = 0;
        while index < layout.variants.len() {
            admit(session, site, 1, 0)?;
            if layout.variants[index].discriminant.is_some() {
                self.invalid(reference, "enum_layout.variant.discriminant", session, site)?;
                break;
            }
            index += 1;
        }
        Ok(())
    }
}
