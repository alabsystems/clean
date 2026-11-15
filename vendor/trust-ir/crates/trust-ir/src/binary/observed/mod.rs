// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual fallible ground-module identity collection/count/hash traversal.
//! Identity only, not validation or source authority. Signature ABI encoding
//! limits and the complete canonical text round-trip share the original session.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};

type R<T = ()> = core::result::Result<T, ObservedValueError>;
mod refusals;
use refusals::Refusals;
pub(crate) use refusals::observed_wire_image_refusals;
pub use refusals::retire_wire_image_refusals_observed;
mod body;
use body::Canonical;
mod output;
use output::{CountPolicy, FunctionSelection, Output};
mod pool;
use pool::{Builder, SealedPool};
mod collect_0;
use collect_0::*;
mod collect_1;
use collect_1::*;
mod fields_0;
use fields_0::*;
mod fields_1;
use fields_1::*;
mod fields_2;
use fields_2::*;
mod fields_3;
use fields_3::*;
mod fields_4;
use fields_4::*;
mod fields_5;
use fields_5::*;
mod fields_6;
use fields_6::*;
mod fields_7;
use fields_7::*;
mod recursive;
use recursive::*;
mod collector;
use collector::*;

pub(crate) fn observed_module_identity<O: ExecutionObserver>(
    module: &Module,
    scheme: IdentityScheme,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ProofDigest> {
    module_identity(module, scheme, CountPolicy::IdentityTotal, session, site)
}

pub(crate) fn observed_checked_module_identity<O: ExecutionObserver>(
    module: &Module,
    scheme: IdentityScheme,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ProofDigest> {
    module_identity(module, scheme, CountPolicy::RequireWireImage, session, site)
}

fn module_identity<O: ExecutionObserver>(
    module: &Module,
    scheme: IdentityScheme,
    counts: CountPolicy,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ProofDigest> {
    module_identity_selected(
        module,
        scheme,
        counts,
        FunctionSelection::Whole,
        session,
        site,
    )
}

/// Exact original source body projection: all module fields/tables remain,
/// only this function is emitted and its provenance is absent in both walks.
/// This is identity only; the caller must observe full uniqueness beforehand.
pub(crate) fn observed_source_function_identity<O: ExecutionObserver>(
    module: &Module,
    index: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ProofDigest> {
    module_identity_selected(
        module,
        IdentityScheme::V3,
        CountPolicy::IdentityTotal,
        FunctionSelection::SourceBody(index),
        session,
        site,
    )
}

fn module_identity_selected<O: ExecutionObserver>(
    module: &Module,
    scheme: IdentityScheme,
    counts: CountPolicy,
    functions: FunctionSelection,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ProofDigest> {
    let mut out = Output::counter(session, site)?;
    out.select_functions(functions)?;
    if matches!(counts, CountPolicy::RequireWireImage) {
        out.require_wire_image();
    }
    out.admit(1, core::mem::size_of::<Builder>())?;
    let mut builder = Builder::new(scheme.blanks_debug_file_paths());
    let collected = observed_collect_strings_into(module, None, &mut builder, &mut out);
    if let Err(error) = collected {
        builder.retire(&mut out);
        return Err(error);
    }
    let pool = builder.seal();
    let result = (|| {
        observed_write_module_with_pool(module, None, &pool, &mut out)?;
        let length = out.count()?;
        out.start_hash(scheme.domain(), length)?;
        observed_write_module_with_pool(module, None, &pool, &mut out)?;
        out.finish_hash()
    })();
    pool.retire(&mut out);
    let value = result?;
    out.publication()?;
    Ok(value)
}

fn contract_surface(pool: &SealedPool) -> bool {
    pool.minimum_version() >= CONTRACT_SURFACE_FORMAT_VERSION
}
fn abi_surface(pool: &SealedPool) -> bool {
    pool.minimum_version() >= ABI_SURFACE_FORMAT_VERSION
}
fn observed_write_raw_bytes<O: ExecutionObserver>(out: &mut Output<'_, '_, O>, bytes: &[u8]) -> R {
    observed_write_count(out, "string length", bytes.len())?;
    out.extend_from_slice(bytes)
}
fn uses_abi_surface_observed<O: ExecutionObserver>(
    attrs: &FuncAttrs,
    out: &mut Output<'_, '_, O>,
) -> R<bool> {
    out.poll()?;
    if !attrs.ret.is_empty() {
        return Ok(true);
    }
    for param in &attrs.params {
        out.poll()?;
        if param.ext != ArgExt::None || param.pass.is_some() {
            return Ok(true);
        }
    }
    Ok(false)
}

mod types;
use types::*;
mod constants;
use constants::*;
mod sorts;
use sorts::*;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod called_error_custody;
#[cfg(test)]
mod held_result_tests;
