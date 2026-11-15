// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Raw function-signature identity, including malformed recorded ABI DATA.

use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{FuncTy, Ty};
use core::mem::size_of;

mod abi;
mod modes;
#[cfg(test)]
mod tests;
mod work;
use work::Work;
type R<T = ()> = Result<T, ObservedValueError>;

impl FuncTy {
    /// Compare every raw signature field under the original observer.
    ///
    /// This agrees with derived structural equality, including recorded ABI
    /// strings, order, duplicates and contradictory descriptors. No encoding,
    /// target, signature validity or call-edge authority is established. An
    /// observer refusal is an outer error, never inequality or missing ABI.
    /// Borrowed source is untouched; only the existing Ty comparison may own
    /// temporary scratch, retired by that child using this same session/site.
    /// Instruction fuel is unchanged. Logical admission is not a physical
    /// allocator, callback, kernel, stack or hard-time bound.
    pub fn structural_eq_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Work<'_, '_, O>>())?;
        let result = compare(self, other, &mut work);
        work.session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })?;
        result
    }
}

fn compare<O: ExecutionObserver>(a: &FuncTy, b: &FuncTy, work: &mut Work<'_, '_, O>) -> R<bool> {
    if !types(&a.params, &b.params, work)? || !types(&a.returns, &b.returns, work)? {
        return Ok(false);
    }
    work.admit(1, size_of::<bool>())?;
    if a.is_vararg != b.is_vararg {
        return Ok(false);
    }
    work.admit(
        1,
        2 * size_of::<Option<&crate::signature_abi::SignatureAbi>>(),
    )?;
    match (&a.abi, &b.abi) {
        (None, None) => Ok(true),
        (Some(a), Some(b)) => abi::compare(a, b, work),
        _ => Ok(false),
    }
}

fn types<O: ExecutionObserver>(mut a: &[Ty], mut b: &[Ty], w: &mut Work<'_, '_, O>) -> R<bool> {
    w.admit(1, 2 * size_of::<&[Ty]>())?;
    if a.len() != b.len() {
        return Ok(false);
    }
    loop {
        w.admit(1, size_of::<Option<(&Ty, &[Ty])>>() * 2)?;
        let (Some((left, rest_a)), Some((right, rest_b))) = (a.split_first(), b.split_first())
        else {
            return Ok(true);
        };
        if !left.structural_eq_observed(right, w.session, w.site)? {
            return Ok(false);
        }
        a = rest_a;
        b = rest_b;
    }
}

/// Internal raw ABI-only child: cross-module TyEq supplies its own type-ID
/// expansion and ordering. Existing whole FuncTy comparison is unchanged.
pub(crate) fn signature_abi_eq_observed<O: ExecutionObserver>(
    a: Option<&crate::signature_abi::SignatureAbi>,
    b: Option<&crate::signature_abi::SignatureAbi>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let mut work = Work { session, site };
    work.admit(
        1,
        size_of::<Work<'_, '_, O>>() + 2 * size_of::<Option<&crate::signature_abi::SignatureAbi>>(),
    )?;
    let result = match (a, b) {
        (None, None) => Ok(true),
        (Some(a), Some(b)) => abi::compare(a, b, &mut work),
        _ => Ok(false),
    };
    work.session.admit(ExecutionProgress {
        phase: ExecutionPhase::Publication,
        site,
        work: 0,
        copy_bytes: 0,
    })?;
    result
}
