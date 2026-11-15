// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::signature_abi::{AbiArgument, AbiBinding, SignatureAbi};

pub(super) fn compare<O: ExecutionObserver>(
    a: &SignatureAbi,
    b: &SignatureAbi,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    // All variable payloads are traversed below, not delegated to derived Eq
    // or a canonical writer that can reject malformed-but-equal raw DATA.
    if !target(&a.target, &b.target, w)?
        || !w.text(a.frontend.name.as_bytes(), b.frontend.name.as_bytes())?
        || !w.text(
            a.frontend.revision.as_bytes(),
            b.frontend.revision.as_bytes(),
        )?
        || !w.text(a.convention.as_bytes(), b.convention.as_bytes())?
    {
        return Ok(false);
    }
    w.admit(32, 2 * size_of::<crate::CallingConv>())?;
    if a.lowered_convention != b.lowered_convention
        || !w.text(a.source_abi.as_bytes(), b.source_abi.as_bytes())?
    {
        return Ok(false);
    }
    w.admit(4, 2 * size_of::<(bool, bool, u32)>())?;
    if a.can_unwind != b.can_unwind || a.variadic != b.variadic || a.fixed_count != b.fixed_count {
        return Ok(false);
    }
    if !arguments(&a.arguments, &b.arguments, w)? {
        return Ok(false);
    }
    argument(&a.result, &b.result, w)
}

fn target<O: ExecutionObserver>(
    a: &crate::signature_abi::AbiTarget,
    b: &crate::signature_abi::AbiTarget,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    if !w.text(a.triple.as_bytes(), b.triple.as_bytes())?
        || !w.text(a.data_layout.as_bytes(), b.data_layout.as_bytes())?
        || !w.text(a.abi.as_bytes(), b.abi.as_bytes())?
        || !w.text(a.cpu.as_bytes(), b.cpu.as_bytes())?
        || !w.strings(&a.features, &b.features)?
        || !w.text(a.target_spec.as_bytes(), b.target_spec.as_bytes())?
    {
        return Ok(false);
    }
    w.admit(2, 2 * size_of::<(u8, bool)>())?;
    Ok(a.pointer_bytes == b.pointer_bytes && a.little_endian == b.little_endian)
}

fn arguments<O: ExecutionObserver>(
    mut a: &[AbiArgument],
    mut b: &[AbiArgument],
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    w.admit(1, 2 * size_of::<&[AbiArgument]>())?;
    if a.len() != b.len() {
        return Ok(false);
    }
    loop {
        w.admit(1, 2 * size_of::<Option<(&AbiArgument, &[AbiArgument])>>())?;
        let (Some((left, rest_a)), Some((right, rest_b))) = (a.split_first(), b.split_first())
        else {
            return Ok(true);
        };
        if !argument(left, right, w)? {
            return Ok(false);
        }
        a = rest_a;
        b = rest_b;
    }
}

fn argument<O: ExecutionObserver>(
    a: &AbiArgument,
    b: &AbiArgument,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    w.admit(2, 2 * size_of::<(u64, u64)>())?;
    if a.size != b.size || a.align != b.align || !modes::compare(&a.mode, &b.mode, w)? {
        return Ok(false);
    }
    let (mut left, mut right) = (a.bindings.as_slice(), b.bindings.as_slice());
    w.admit(1, 2 * size_of::<&[AbiBinding]>())?;
    if left.len() != right.len() {
        return Ok(false);
    }
    loop {
        w.admit(1, 2 * size_of::<Option<(&AbiBinding, &[AbiBinding])>>())?;
        let (Some((a, tail_a)), Some((b, tail_b))) = (left.split_first(), right.split_first())
        else {
            return Ok(true);
        };
        // AbiBinding is exactly a fixed tagged u32 and four u64 scalars.
        w.admit(64, 2 * size_of::<&AbiBinding>())?;
        if a != b {
            return Ok(false);
        }
        left = tail_a;
        right = tail_b;
    }
}
