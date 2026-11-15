// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

pub(super) fn discriminants<O: ExecutionObserver>(
    def: &EnumDef,
    work: &mut Work<'_, '_, O>,
) -> R<Vec<i128>> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    let result = (|| {
        let mut next = Some(0i128);
        for index in 0..def.variants.len() {
            work.poll()?;
            let value = def
                .discriminants
                .get(index)
                .copied()
                .flatten()
                .or(next)
                .ok_or(LayoutError::EnumLayoutUnavailable(def.id))?;
            work.lookup(seen.len())?;
            if seen.contains(&value) {
                return Err(LayoutError::EnumLayoutUnavailable(def.id).into());
            }
            work.tree::<i128, ()>(seen.len())?;
            seen.insert(value);
            work.push(&mut out, value)?;
            next = value.checked_add(1);
        }
        Ok(())
    })();
    work.retire_set(seen);
    if let Err(stop) = work.poll() {
        work.retire_copy_vec(out);
        if let Err(error) = result {
            work.retire_error(error);
        }
        return Err(stop);
    }
    if let Err(error) = result {
        work.retire_copy_vec(out);
        work.poll()?;
        return Err(error);
    }
    Ok(out)
}

// The immutable resolved list is reused: the ordinary method recomputes the
// same discriminants, with no different refusal possible on this module.
pub(super) fn canonical<O: ExecutionObserver>(
    def: &EnumDef,
    discs: &[i128],
    work: &mut Work<'_, '_, O>,
) -> R<EnumTagRepr> {
    work.poll()?;
    let unavailable = || LayoutError::EnumLayoutUnavailable(def.id);
    let Some(&first) = discs.first() else {
        return Err(unavailable().into());
    };
    if let Some(hint) = def.repr {
        for &disc in discs {
            work.poll()?;
            if !hint.fits(disc) {
                return Err(unavailable().into());
            }
        }
        return Ok(hint);
    }
    let (mut min, mut max) = (first, first);
    for &disc in discs {
        work.poll()?;
        min = min.min(disc);
        max = max.max(disc);
    }
    let candidates = if min >= 0 {
        [
            EnumTagRepr::U8,
            EnumTagRepr::U16,
            EnumTagRepr::U32,
            EnumTagRepr::U64,
        ]
    } else {
        [
            EnumTagRepr::I8,
            EnumTagRepr::I16,
            EnumTagRepr::I32,
            EnumTagRepr::I64,
        ]
    };
    for repr in candidates {
        work.poll()?;
        if repr.fits(min) && repr.fits(max) {
            return Ok(repr);
        }
    }
    Err(unavailable().into())
}

pub(super) fn alignment<O: ExecutionObserver>(
    table: &LayoutTable<'_>,
    repr: EnumTagRepr,
    work: &mut Work<'_, '_, O>,
) -> R<u64> {
    work.poll()?;
    let ty = repr.ty();
    let shape = work
        .leaf(table, &ty)?
        .ok_or(LayoutError::UnsupportedTyShape(ty.shape()))?;
    let result = shape
        .align_bits
        .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
        .ok_or_else(|| Error::Layout(LayoutError::UnsupportedTyShape(ty.shape())));
    work.retire_layout(shape);
    work.poll()?;
    result
}
