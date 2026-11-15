// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_divergence<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    d: &Divergence,
) -> R {
    buf.poll()?;
    let tag: u8 = match d {
        Divergence::Uniform => 0,
        Divergence::Low => 1,
        Divergence::High => 2,
    };
    observed_write_u8(buf, tag)?;

    Ok(())
}

pub(super) fn observed_write_effect_place<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    place: &crate::EffectPlace,
) -> R {
    buf.poll()?;
    match place {
        crate::EffectPlace::ParamPointee { index } => {
            observed_write_u8(buf, 0)?;
            observed_write_v32(buf, *index)?;
        }
        crate::EffectPlace::Global(global) => {
            observed_write_u8(buf, 1)?;
            observed_write_v32(buf, global.index())?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_effect_set<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    set: &crate::EffectSet,
) -> R {
    buf.poll()?;
    match set {
        crate::EffectSet::Nothing => observed_write_u8(buf, 0)?,
        crate::EffectSet::Places(places) => {
            observed_write_u8(buf, 1)?;
            observed_write_count(buf, "EffectSet::Places places", places.len())?;
            for place in places {
                buf.poll()?;
                observed_write_effect_place(buf, place)?;
            }
        }
        crate::EffectSet::Everything => observed_write_u8(buf, 2)?,
    }

    Ok(())
}

pub(super) fn observed_write_effect_summary<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    effects: &crate::EffectSummary,
) -> R {
    buf.poll()?;
    observed_write_effect_set(buf, &effects.reads)?;
    observed_write_effect_set(buf, &effects.writes)?;
    observed_write_u8(buf, u8::from(effects.allocates))?;
    observed_write_u8(buf, u8::from(effects.frees))?;
    observed_write_u8(buf, u8::from(effects.may_unwind))?;
    observed_write_u8(buf, u8::from(effects.io))?;

    Ok(())
}

pub(super) fn observed_write_endianness<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &Endianness,
) -> R {
    buf.poll()?;
    let tag = match value {
        Endianness::Little => 0,
        Endianness::Big => 1,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_enum_def<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    ed: &EnumDef,
) -> R {
    buf.poll()?;
    observed_write_enum_id(buf, ed.id)?;
    observed_write_str(buf, pool, &ed.name)?;
    observed_write_count(buf, "EnumDef.variants", ed.variants.len())?;
    for v in &ed.variants {
        buf.poll()?;
        observed_write_enum_variant(buf, pool, v)?;
    }
    // Explicit discriminants + tag-repr hint (VERSION >= 19). Written
    // verbatim (the vector may be shorter than `variants`; entries are
    // Option-tagged 0=implicit 1=explicit i128).
    observed_write_count(buf, "EnumDef.discriminants", ed.discriminants.len())?;
    for d in &ed.discriminants {
        buf.poll()?;
        match d {
            None => observed_write_u8(buf, 0)?,
            Some(value) => {
                observed_write_u8(buf, 1)?;
                observed_write_i128(buf, *value)?;
            }
        }
    }
    // Tag: 0=no hint, 1..=8 map to EnumTagRepr U8/U16/U32/U64/I8/I16/I32/I64.
    match ed.repr {
        None => observed_write_u8(buf, 0)?,
        Some(repr) => observed_write_u8(buf, enum_tag_repr_byte(repr))?,
    }
    match &ed.layout {
        None => observed_write_u8(buf, 0)?,
        Some(layout) => {
            observed_write_u8(buf, 1)?;
            match &layout.encoding {
                EnumTagEncoding::Direct { tag_offset } => {
                    observed_write_u8(buf, 0)?;
                    observed_write_v64(buf, *tag_offset)?;
                }
                EnumTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    niche_ty,
                } => {
                    observed_write_u8(buf, 1)?;
                    observed_write_v32(buf, *untagged_variant)?;
                    observed_write_v32(buf, *niche_variants_start)?;
                    observed_write_v32(buf, *niche_variants_end)?;
                    observed_write_u128(buf, *niche_start)?;
                    observed_write_v64(buf, *niche_offset)?;
                    observed_write_u8(buf, enum_tag_repr_byte(*niche_ty))?;
                }
                // v37. The tag byte is the whole encoding — there is no tag
                // lane to place, so nothing follows it. The reader side IS
                // version-gated, so a v36 blob carrying this byte is refused.
                EnumTagEncoding::Untagged => observed_write_u8(buf, 2)?,
                EnumTagEncoding::SingleInhabited { variant } => {
                    observed_write_u8(buf, 3)?;
                    observed_write_v32(buf, *variant)?;
                }
            }
            observed_write_v64(buf, layout.size)?;
            observed_write_v64(buf, layout.align)?;
            observed_write_count(
                buf,
                "EnumLayoutDescriptor.variant_field_offsets",
                layout.variant_field_offsets.len(),
            )?;
            for offsets in &layout.variant_field_offsets {
                buf.poll()?;
                observed_write_count(
                    buf,
                    "EnumLayoutDescriptor.variant_field_offsets row",
                    offsets.len(),
                )?;
                for offset in offsets {
                    buf.poll()?;
                    observed_write_v64(buf, *offset)?;
                }
            }
        }
    }
    // v58 nominal identity key (trailing, presence-tagged).
    if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
        observed_write_type_origin(buf, pool, ed.origin.as_ref())?;
    }

    Ok(())
}

pub(super) fn observed_write_enum_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: EnumId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_enum_variant<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    ev: &EnumVariant,
) -> R {
    buf.poll()?;
    observed_write_str(buf, pool, &ev.name)?;
    observed_write_count(buf, "EnumVariant.fields", ev.fields.len())?;
    for f in &ev.fields {
        buf.poll()?;
        observed_write_ty(buf, pool, f)?;
    }
    observed_write_count(buf, "EnumVariant.field_names", ev.field_names.len())?;
    for name in &ev.field_names {
        buf.poll()?;
        observed_write_str(buf, pool, name)?;
    }

    Ok(())
}

pub(super) fn observed_write_extern_ref<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    reference: &crate::ExternRef,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, reference.module.index())?;
    observed_write_str(buf, pool, &reference.symbol)?;
    match reference.obligation {
        None => observed_write_u8(buf, 0)?,
        Some(obligation) => {
            observed_write_u8(buf, 1)?;
            observed_write_proof_id(buf, obligation)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_f64<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: f64) -> R {
    buf.poll()?;
    buf.extend_from_slice(&v.to_le_bytes())?;

    Ok(())
}

pub(super) fn observed_write_fat_ptr_kind<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    _pool: &SealedPool,
    kind: &FatPtrKind,
) -> R {
    buf.poll()?;
    match kind {
        FatPtrKind::Slice(elem) => {
            observed_write_u8(buf, 0)?;
            observed_write_ty_id(buf, *elem)?;
        }
        FatPtrKind::Str => observed_write_u8(buf, 1)?,
        FatPtrKind::TraitObject { trait_id } => {
            observed_write_u8(buf, 2)?;
            observed_write_v32(buf, *trait_id)?;
        }
        // v38. Read-gated below: an unknown tag already fails closed with
        // `InvalidTag`, so the gate is not what makes this safe — it is what
        // keeps a v37-LABELLED blob carrying tag 3 from being accepted as
        // well-formed by a reader that would otherwise take it.
        FatPtrKind::ContainerLen => observed_write_u8(buf, 3)?,
        // v40. Read-gated below on the same terms as tag 3: the gate keeps a
        // v39-or-older-LABELLED blob carrying tag 4 from being taken as
        // well-formed. The writer raises the header to 40 for it in
        // `collect_type_identity_strings`.
        FatPtrKind::ContainerVtable => observed_write_u8(buf, 4)?,
    }

    Ok(())
}

pub(super) fn observed_write_fcmp_op<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &FCmpOp,
) -> R {
    buf.poll()?;
    let tag = match value {
        FCmpOp::OEq => 0,
        FCmpOp::ONe => 1,
        FCmpOp::OLt => 2,
        FCmpOp::OLe => 3,
        FCmpOp::OGt => 4,
        FCmpOp::OGe => 5,
        FCmpOp::UEq => 6,
        FCmpOp::UNe => 7,
        FCmpOp::ULt => 8,
        FCmpOp::ULe => 9,
        FCmpOp::UGt => 10,
        FCmpOp::UGe => 11,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_field_def<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    fd: &FieldDef,
) -> R {
    buf.poll()?;
    observed_write_str(buf, pool, &fd.name)?;
    observed_write_ty(buf, pool, &fd.ty)?;
    match fd.offset {
        None => observed_write_u8(buf, 0)?,
        Some(o) => {
            observed_write_u8(buf, 1)?;
            observed_write_u64(buf, o)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_func_attrs<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    fa: &FuncAttrs,
    param_count: Option<usize>,
) -> R {
    buf.poll()?;
    let mut flags: u8 = 0;
    if fa.readonly {
        flags |= 0b0001;
    }
    if fa.readnone {
        flags |= 0b0010;
    }
    if fa.inlinehint {
        flags |= 0b0100;
    }
    if fa.cold {
        flags |= 0b1000;
    }
    // v41: `naked` rides bit 4. Setting it raised the writer to v41 in the
    // collection walk, so no pre-v41 blob ever carries the bit.
    if fa.naked {
        flags |= 0b1_0000;
    }
    observed_write_u8(buf, flags)?;
    let param_count = param_count.unwrap_or(fa.params.len());
    observed_write_count(buf, "FuncAttrs.params", param_count)?;
    for pa in &fa.params[..param_count] {
        buf.poll()?;
        observed_write_param_attrs(buf, pool, pa)?;
    }
    // v41: target features, a trailing block.
    if contract_surface(pool) {
        observed_write_count(buf, "FuncAttrs.target_features", fa.target_features.len())?;
        for feature in &fa.target_features {
            buf.poll()?;
            observed_write_str(buf, pool, feature)?;
        }
    }
    // v45 (WS3.11): the return slot, the same record as a parameter's.
    if abi_surface(pool) {
        observed_write_param_attrs(buf, pool, &fa.ret)?;
    }

    Ok(())
}

pub(super) fn observed_write_func_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: FuncId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_func_ty_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: FuncTyId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}
