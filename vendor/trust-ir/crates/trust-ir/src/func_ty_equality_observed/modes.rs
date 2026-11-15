// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::signature_abi::{AbiPassMode, AbiRegister};

pub(super) fn compare<O: ExecutionObserver>(
    a: &AbiPassMode,
    b: &AbiPassMode,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    w.admit(12, 2 * size_of::<&AbiPassMode>())?;
    if tag(a) != tag(b) {
        return Ok(false);
    }
    match (a, b) {
        (AbiPassMode::Ignore, AbiPassMode::Ignore) => Ok(true),
        (AbiPassMode::Direct(a), AbiPassMode::Direct(b)) => {
            w.admit(128, 2 * size_of::<&crate::signature_abi::AbiScalar>())?;
            Ok(a == b)
        }
        (AbiPassMode::Pair(a, c), AbiPassMode::Pair(b, d)) => {
            w.admit(256, 4 * size_of::<&crate::signature_abi::AbiScalar>())?;
            Ok(a == b && c == d)
        }
        (
            AbiPassMode::Cast {
                pad_i32: a,
                prefix: ap,
                rest_offset: ao,
                rest: ar,
                attributes: aa,
            },
            AbiPassMode::Cast {
                pad_i32: b,
                prefix: bp,
                rest_offset: bo,
                rest: br,
                attributes: ba,
            },
        ) => {
            w.admit(1, 2 * size_of::<bool>())?;
            if a != b || !registers(ap, bp, w)? {
                return Ok(false);
            }
            // Option<u64>, AbiUniform and AbiAttributes contain fixed scalar
            // fields only. They own no strings, vectors, callbacks or cycles.
            w.admit(256, 6 * size_of::<usize>())?;
            Ok(ao == bo && ar == br && aa == ba)
        }
        (
            AbiPassMode::Indirect {
                attributes: a,
                metadata_attributes: am,
                on_stack: ast,
                caller_copy: ac,
            },
            AbiPassMode::Indirect {
                attributes: b,
                metadata_attributes: bm,
                on_stack: bst,
                caller_copy: bc,
            },
        ) => {
            // Both optional attribute carriers are fixed, non-owning scalar
            // records; equality must retain None versus explicit Some claims.
            w.admit(256, size_of::<[usize; 8]>())?;
            Ok(a == b && am == bm && ast == bst && ac == bc)
        }
        _ => Ok(false),
    }
}

fn registers<O: ExecutionObserver>(
    mut a: &[AbiRegister],
    mut b: &[AbiRegister],
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    w.admit(1, 2 * size_of::<&[AbiRegister]>())?;
    if a.len() != b.len() {
        return Ok(false);
    }
    loop {
        w.admit(1, 2 * size_of::<Option<(&AbiRegister, &[AbiRegister])>>())?;
        let (Some((left, tail_a)), Some((right, tail_b))) = (a.split_first(), b.split_first())
        else {
            return Ok(true);
        };
        w.admit(8, 2 * size_of::<&AbiRegister>())?;
        if left != right {
            return Ok(false);
        }
        a = tail_a;
        b = tail_b;
    }
}

// Exhaustive: any future mode needs an explicit identity decision.
fn tag(mode: &AbiPassMode) -> u8 {
    match mode {
        AbiPassMode::Ignore => 0,
        AbiPassMode::Direct(_) => 1,
        AbiPassMode::Pair(..) => 2,
        AbiPassMode::Cast { .. } => 3,
        AbiPassMode::Indirect { .. } => 4,
    }
}
