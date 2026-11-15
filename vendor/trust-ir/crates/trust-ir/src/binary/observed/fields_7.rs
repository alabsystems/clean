// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_spec_module<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    sm: &crate::spec::SpecModule,
) -> R {
    buf.poll()?;
    use crate::spec::SpecOrigin;

    observed_write_str(buf, pool, &sm.name)?;

    observed_write_count(buf, "SpecModule.vars", sm.vars.len())?;
    for v in &sm.vars {
        buf.poll()?;
        observed_write_str(buf, pool, &v.name)?;
        observed_write_str(buf, pool, &v.ty)?;
        // v46: the declared wire sort, inside the per-variable record (the
        // same shape v26's per-anchor `function` took).
        if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
            match &v.sort {
                None => observed_write_u8(buf, 0)?,
                Some(sort) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_clause_sort(buf, pool, sort)?;
                }
            }
        }
    }

    observed_write_count(buf, "SpecModule.actions", sm.actions.len())?;
    for a in &sm.actions {
        buf.poll()?;
        observed_write_str(buf, pool, a)?;
    }

    observed_write_count(buf, "SpecModule.invariants", sm.invariants.len())?;
    for inv in &sm.invariants {
        buf.poll()?;
        observed_write_str(buf, pool, &inv.name)?;
        observed_write_str(buf, pool, &inv.formula)?;
        // v46: the typed first-order carrier.
        if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
            match &inv.typed {
                None => observed_write_u8(buf, 0)?,
                Some(typed) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_proof_formula(buf, pool, typed)?;
                }
            }
        }
    }

    observed_write_count(buf, "SpecModule.anchors", sm.anchors.len())?;
    for anchor in &sm.anchors {
        buf.poll()?;
        observed_write_str(buf, pool, &anchor.machine)?;
        observed_write_str(buf, pool, &anchor.action)?;
        observed_write_str(buf, pool, &anchor.rust_symbol)?;
        observed_write_str(buf, pool, &anchor.span)?;
        match &anchor.project {
            None => observed_write_u8(buf, 0)?,
            Some(p) => {
                observed_write_u8(buf, 1)?;
                observed_write_str(buf, pool, p)?;
            }
        }
        match anchor.function {
            None => observed_write_u8(buf, 0)?,
            Some(function) => {
                observed_write_u8(buf, 1)?;
                observed_write_v32(buf, function.index())?;
            }
        }
        match anchor.projection_target {
            None => observed_write_u8(buf, 0)?,
            Some(crate::spec::SpecProjectionTarget::Function(function)) => {
                observed_write_u8(buf, 1)?;
                observed_write_v32(buf, function.index())?;
            }
            Some(crate::spec::SpecProjectionTarget::TemporalFieldPathsV1) => {
                observed_write_u8(buf, 2)?
            }
            Some(crate::spec::SpecProjectionTarget::ExternalUnresolved) => {
                observed_write_u8(buf, 3)?
            }
        }
    }

    observed_write_count(buf, "SpecModule.waivers", sm.waivers.len())?;
    for w in &sm.waivers {
        buf.poll()?;
        observed_write_str(buf, pool, &w.machine)?;
        observed_write_str(buf, pool, &w.action)?;
        observed_write_str(buf, pool, &w.reason)?;
    }

    match &sm.origin {
        SpecOrigin::Embedded => observed_write_u8(buf, 0)?,
        SpecOrigin::External(path) => {
            observed_write_u8(buf, 1)?;
            observed_write_str(buf, pool, path)?;
        }
    }

    // Proofs (v14+). Appended after the v13 body so the v13 prefix layout is
    // byte-identical; a v13 reader simply stops here. The reader only consumes
    // this block when `version >= 14`.
    observed_write_proofs(buf, pool, &sm.proofs)?;
    match sm.enforcement {
        crate::spec::SpecEnforcementMode::DesignOnly => observed_write_u8(buf, 0)?,
        crate::spec::SpecEnforcementMode::Linked => observed_write_u8(buf, 1)?,
    }
    // Temporal properties (v46). Appended after the v27 enforcement byte so
    // every older prefix stays byte-identical; the reader only consumes this
    // block when `version >= 46`.
    if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
        observed_write_temporal(buf, pool, &sm.temporal)?;
    }

    Ok(())
}

pub(super) fn observed_write_str<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    s: &str,
) -> R {
    buf.poll()?;
    // `observed_write_v64` of a pool id is the `observed_write_v32` spelling for every id the
    // format can carry; an id past `u32::MAX` needs a string table past the
    // format's count, which `observed_write_count` reports.
    let id = pool.id_of(s, buf)?;
    observed_write_v64(buf, id)?;

    Ok(())
}

pub(super) fn observed_write_struct_def<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    sd: &StructDef,
) -> R {
    buf.poll()?;
    observed_write_struct_id(buf, sd.id)?;
    observed_write_str(buf, pool, &sd.name)?;
    observed_write_count(buf, "StructDef.fields", sd.fields.len())?;
    for f in &sd.fields {
        buf.poll()?;
        observed_write_field_def(buf, pool, f)?;
    }
    match sd.size {
        None => observed_write_u8(buf, 0)?,
        Some(s) => {
            observed_write_u8(buf, 1)?;
            observed_write_u64(buf, s)?;
        }
    }
    match sd.align {
        None => observed_write_u8(buf, 0)?,
        Some(a) => {
            observed_write_u8(buf, 1)?;
            observed_write_u64(buf, a)?;
        }
    }
    // Struct ABI repr (VERSION >= 10). Tag: 0=Rust 1=C 2=Transparent 3=Packed(align).
    match sd.repr {
        StructRepr::Rust => observed_write_u8(buf, 0)?,
        StructRepr::C => observed_write_u8(buf, 1)?,
        StructRepr::Transparent => observed_write_u8(buf, 2)?,
        StructRepr::Packed(align) => {
            observed_write_u8(buf, 3)?;
            observed_write_v32(buf, align)?;
        }
    }
    // v58 nominal identity key (trailing, presence-tagged).
    if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
        observed_write_type_origin(buf, pool, sd.origin.as_ref())?;
    }

    Ok(())
}

pub(super) fn observed_write_struct_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: StructId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_temporal<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    temporal: &[crate::spec::SpecTemporal],
) -> R {
    buf.poll()?;
    use crate::spec::TemporalForm;
    observed_write_count(buf, "SpecModule.temporal", temporal.len())?;
    for property in temporal {
        buf.poll()?;
        observed_write_str(buf, pool, &property.name)?;
        match &property.form {
            TemporalForm::Always(p) => {
                observed_write_u8(buf, 0)?;
                observed_write_proof_formula(buf, pool, p)?;
            }
            TemporalForm::Eventually(p) => {
                observed_write_u8(buf, 1)?;
                observed_write_proof_formula(buf, pool, p)?;
            }
            TemporalForm::LeadsTo(p, q) => {
                observed_write_u8(buf, 2)?;
                observed_write_proof_formula(buf, pool, p)?;
                observed_write_proof_formula(buf, pool, q)?;
            }
            TemporalForm::WeakFair { action, relation }
            | TemporalForm::StrongFair { action, relation } => {
                observed_write_u8(
                    buf,
                    if matches!(property.form, TemporalForm::WeakFair { .. }) {
                        3
                    } else {
                        4
                    },
                )?;
                observed_write_str(buf, pool, action)?;
                match relation {
                    None => observed_write_u8(buf, 0)?,
                    Some(relation) => {
                        observed_write_u8(buf, 1)?;
                        observed_write_proof_formula(buf, pool, relation)?;
                    }
                }
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_tls_model<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &TlsModel,
) -> R {
    buf.poll()?;
    let tag = match value {
        TlsModel::LocalExec => 0,
        TlsModel::InitialExec => 1,
        TlsModel::GeneralDynamic => 2,
        TlsModel::LocalDynamic => 3,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_ty_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: TyId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_type_origin<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    origin: Option<&TypeOrigin>,
) -> R {
    buf.poll()?;
    match origin {
        None => observed_write_u8(buf, 0)?,
        Some(TypeOrigin::Rust {
            stable_crate_id,
            def_path_hash,
            args_digest,
        }) => {
            observed_write_u8(buf, 1)?;
            observed_write_u8(buf, 0)?;
            observed_write_u64(buf, *stable_crate_id)?;
            buf.extend_from_slice(def_path_hash)?;
            observed_write_proof_digest(buf, args_digest)?;
        }
        Some(TypeOrigin::Clean { decl, env_digest }) => {
            observed_write_u8(buf, 1)?;
            observed_write_u8(buf, 1)?;
            observed_write_str(buf, pool, decl)?;
            observed_write_proof_digest(buf, env_digest)?;
        }
    }

    Ok(())
}

pub(super) fn observed_write_u128<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: u128) -> R {
    buf.poll()?;
    buf.extend_from_slice(&v.to_le_bytes())?;

    Ok(())
}

pub(super) fn observed_write_u32<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: u32) -> R {
    buf.poll()?;
    buf.extend_from_slice(&v.to_le_bytes())?;

    Ok(())
}

pub(super) fn observed_write_u64<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: u64) -> R {
    buf.poll()?;
    buf.extend_from_slice(&v.to_le_bytes())?;

    Ok(())
}

pub(super) fn observed_write_u8<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: u8) -> R {
    buf.poll()?;
    buf.push(v)?;

    Ok(())
}

pub(super) fn observed_write_universe<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    u: &crate::pred::Universe,
) -> R {
    buf.poll()?;
    match u {
        crate::pred::Universe::IntRange { lo, hi } => {
            observed_write_u8(buf, 0)?;
            observed_write_i128(buf, *lo)?;
            observed_write_i128(buf, *hi)?;
        }
        crate::pred::Universe::Members(items) => {
            observed_write_u8(buf, 1)?;
            observed_write_count(buf, "Universe::Members items", items.len())?;
            for c in items {
                buf.poll()?;
                observed_write_constant(buf, pool, c)?;
            }
        }
    }

    Ok(())
}

pub(super) fn observed_write_unop<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &UnOp,
) -> R {
    buf.poll()?;
    let tag = match value {
        UnOp::Neg => 0,
        UnOp::FNeg => 1,
        UnOp::Not => 2,
        UnOp::CtPop => 3,
        UnOp::FAbs => 4,
        UnOp::FSqrt => 5,
        UnOp::FFloor => 6,
        UnOp::FCeil => 7,
        UnOp::FTrunc => 8,
        UnOp::CtLz => 9,
        UnOp::CtTz => 10,
        UnOp::BSwap => 11,
        UnOp::BitReverse => 12,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}

pub(super) fn observed_write_v32<O: ExecutionObserver>(buf: &mut Output<'_, '_, O>, v: u32) -> R {
    buf.poll()?;
    observed_write_v64(buf, v as u64)?;

    Ok(())
}

pub(super) fn observed_write_v64<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    mut v: u64,
) -> R {
    buf.poll()?;
    while v >= 0x80 {
        buf.poll()?;
        buf.push((v as u8) | 0x80)?;
        v >>= 7;
    }
    buf.push(v as u8)?;

    Ok(())
}

pub(super) fn observed_write_value_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    id: ValueId,
) -> R {
    buf.poll()?;
    observed_write_v32(buf, id.index())?;

    Ok(())
}

pub(super) fn observed_write_vec_value_id<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    canonical: Option<Canonical<'_>>,
    ids: &[ValueId],
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    observed_write_count(buf, "value-id list", ids.len())?;
    for id in ids {
        buf.poll()?;
        observed_write_projected_value_id(buf, canonical, *id)?;
    }

    Ok(())
}

pub(super) fn observed_write_visibility<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    value: &Visibility,
) -> R {
    buf.poll()?;
    let tag = match value {
        Visibility::Default => 0,
        Visibility::Hidden => 1,
        Visibility::Protected => 2,
    };
    observed_write_u8(buf, tag)?;
    Ok(())
}
