// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The actual raw observed writer as a complete first-per-class check sink.
use super::*;
use core::mem::{size_of, take};
mod record;
mod retirement;
#[cfg(test)]
mod tests;
#[derive(Default)]
pub(super) struct Refusals {
    first: [Option<BinaryProjectionError>; WIRE_REFUSAL_RANKS],
    pending: Option<WireRefusal>,
    converted: Option<(usize, BinaryProjectionError)>,
    result: Vec<BinaryProjectionError>,
    pub(super) len: usize,
}
pub(crate) fn observed_wire_image_refusals<O: ExecutionObserver>(
    module: &Module,
    s: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<BinaryProjectionError>> {
    s.admit(ExecutionProgress {
        phase: ExecutionPhase::CanonicalSerialization,
        site,
        work: 1,
        copy_bytes: size_of::<Refusals>(),
    })?;
    let mut held = Refusals::default();
    let result = {
        let mut out = Output::checker(s, site, &mut held)?;

        (|| {
            out.admit(1, size_of::<Builder>())?;
            let mut builder = Builder::new(false);
            let collected = observed_collect_strings_into(module, None, &mut builder, &mut out);
            if let Err(error) = collected {
                builder.retire(&mut out);
                return Err(error);
            }
            let pool = builder.seal();
            let written = observed_write_module_with_pool(module, None, &pool, &mut out);
            pool.retire(&mut out);
            written?;
            out.take_refusals()
        })()
    };
    if result.is_err() {
        held.retire(s, site);
    }
    result
}
/// Consume all owned diagnostic detail/backing storage on the original owner.
pub fn retire_wire_image_refusals_observed<O: ExecutionObserver>(
    rows: Vec<BinaryProjectionError>,
    s: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    retirement::rows(rows, s, site);
    s.admit(ExecutionProgress {
        phase: ExecutionPhase::Publication,
        site,
        work: 0,
        copy_bytes: 0,
    })
    .map_err(Into::into)
}
