// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::ty::EnumLayoutDescriptor;
pub(super) fn tail<O: ExecutionObserver>(
    s: &mut State<'_>,
    a: &EnumDef,
    b: &EnumDef,
    w: &mut Work<'_, '_, O>,
) -> R {
    s.discs_a = a.effective_discriminants_observed(w.session, w.site)?;
    s.discs_b = b.effective_discriminants_observed(w.session, w.site)?;
    s.last = values(s.discs_a.as_deref(), s.discs_b.as_deref(), w)?;
    s.discriminants(w);
    if !s.last {
        return Ok(());
    }
    s.last = a.canonical_tag_repr_observed(w.session, w.site)?
        == b.canonical_tag_repr_observed(w.session, w.site)?;
    if s.last {
        s.last = layout(a.layout.as_ref(), b.layout.as_ref(), w)?;
    }
    Ok(())
}
fn values<O: ExecutionObserver>(
    a: Option<&[i128]>,
    b: Option<&[i128]>,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    w.admit(1, 2 * size_of::<Option<&[i128]>>())?;
    let (mut a, mut b) = match (a, b) {
        (None, None) => return Ok(true),
        (Some(a), Some(b)) => (a, b),
        _ => return Ok(false),
    };
    if a.len() != b.len() {
        return Ok(false);
    }
    loop {
        w.admit(
            1 + 2 * size_of::<i128>(),
            2 * size_of::<Option<(&i128, &[i128])>>(),
        )?;
        let (Some((va, ra)), Some((vb, rb))) = (a.split_first(), b.split_first()) else {
            return Ok(true);
        };
        if va != vb {
            return Ok(false);
        }
        a = ra;
        b = rb;
    }
}
fn layout<O: ExecutionObserver>(
    a: Option<&EnumLayoutDescriptor>,
    b: Option<&EnumLayoutDescriptor>,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    w.admit(
        1 + 2 * size_of::<EnumLayoutDescriptor>(),
        2 * size_of::<Option<&EnumLayoutDescriptor>>(),
    )?;
    let (a, b) = match (a, b) {
        (None, None) => return Ok(true),
        (Some(a), Some(b)) => (a, b),
        _ => return Ok(false),
    };
    if a.encoding != b.encoding
        || a.size != b.size
        || a.align != b.align
        || a.variant_field_offsets.len() != b.variant_field_offsets.len()
    {
        return Ok(false);
    }
    let mut a = a.variant_field_offsets.as_slice();
    let mut b = b.variant_field_offsets.as_slice();
    loop {
        w.admit(1, 2 * size_of::<Option<(&Vec<u64>, &[Vec<u64>])>>())?;
        let (Some((va, ra)), Some((vb, rb))) = (a.split_first(), b.split_first()) else {
            return Ok(true);
        };
        if !offsets(va, vb, w)? {
            return Ok(false);
        }
        a = ra;
        b = rb;
    }
}
fn offsets<O: ExecutionObserver>(mut a: &[u64], mut b: &[u64], w: &mut Work<'_, '_, O>) -> R<bool> {
    w.admit(1, 2 * size_of::<&[u64]>())?;
    if a.len() != b.len() {
        return Ok(false);
    }
    loop {
        w.admit(
            1 + 2 * size_of::<u64>(),
            2 * size_of::<Option<(&u64, &[u64])>>(),
        )?;
        let (Some((va, ra)), Some((vb, rb))) = (a.split_first(), b.split_first()) else {
            return Ok(true);
        };
        if va != vb {
            return Ok(false);
        }
        a = ra;
        b = rb;
    }
}
