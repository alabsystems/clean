// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact minimal licensed-body image, never source-body or authority currency.
use super::*;
use crate::inst::Inst;
use crate::node::InstrNode;
use crate::{Block, Function};
use core::mem::size_of;
mod plan;
mod preflight;
mod state;
mod wire;
use plan::Plan;
use state::{Row, State};
#[cfg(test)]
mod tests;

/// Old view plans remain explicitly unsupported; only the body-only source
/// planner below can reach the newly implemented canonical wire route.
#[derive(Clone, Copy)]
pub(super) enum Canonical<'a> {
    Ordinary(&'a FunctionCanonicalPlan),
    Body(&'a Plan),
}
impl<'a> Canonical<'a> {
    pub(super) fn block_order<O: ExecutionObserver>(
        self,
        out: &mut Output<'_, '_, O>,
    ) -> R<&'a [usize]> {
        out.admit(1, size_of::<&[usize]>())?;
        match self {
            Self::Body(plan) => Ok(&plan.blocks),
            Self::Ordinary(_) => Err(ObservedValueError::UnsupportedValue),
        }
    }
    pub(super) fn param_attrs_len<O: ExecutionObserver>(
        self,
        out: &mut Output<'_, '_, O>,
    ) -> R<usize> {
        out.admit(1, size_of::<usize>())?;
        match self {
            Self::Body(plan) => Ok(plan.params),
            Self::Ordinary(_) => Err(ObservedValueError::UnsupportedValue),
        }
    }
    pub(super) fn map_value<O: ExecutionObserver>(
        self,
        value: ValueId,
        out: &mut Output<'_, '_, O>,
    ) -> R<ValueId> {
        match self {
            Self::Body(plan) => plan.map(value, out),
            Self::Ordinary(_) => Err(ObservedValueError::UnsupportedValue),
        }
    }
    pub(super) fn map_binding_value<O: ExecutionObserver>(
        self,
        value: ValueId,
        out: &mut Output<'_, '_, O>,
    ) -> R<ValueId> {
        match self {
            Self::Body(plan) => plan.binding(value, out),
            Self::Ordinary(_) => Err(ObservedValueError::UnsupportedValue),
        }
    }
}
impl Module {
    /// The exact ordinary function_body_digest relation, with every variable
    /// projection/plan/wire/hash operation under this original session/site.
    /// A semantic body-identity refusal is the complete inner String; an
    /// operational stop is outer and never publishes a digest or partial text.
    /// The returned inner String remains caller-owned; no authority is minted.
    pub fn function_body_digest_observed<O: ExecutionObserver>(
        &self,
        function: FuncId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<core::result::Result<ProofDigest, String>> {
        let mut out = Output::counter(session, site)?;
        out.admit(1, 2 * size_of::<State<'_>>())?;
        let mut state = State::new();
        let result = state.run(self, function, &mut out);
        finish(state, result, out)
    }
    /// Consume the entire actual returned result, including every String byte,
    /// under the original caller even after refusal. No result is republished.
    pub fn retire_function_body_digest_result_observed<O: ExecutionObserver>(
        result: core::result::Result<ProofDigest, String>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        session.retirement_record(
            site,
            size_of::<core::result::Result<ProofDigest, String>>() + 1,
            size_of::<core::result::Result<ProofDigest, String>>(),
        );
        match result {
            Ok(digest) => {
                session.retirement_record(
                    site,
                    size_of::<ProofDigest>() + 1,
                    size_of::<ProofDigest>(),
                );
                let _ = digest;
            }
            Err(text) => {
                session.retirement_record(
                    site,
                    size_of::<String>() + size_of::<Vec<u8>>() + 1,
                    size_of::<String>() + size_of::<Vec<u8>>(),
                );
                let mut bytes = text.into_bytes();
                while !bytes.is_empty() {
                    let chunk = bytes.len().min(1024);
                    session.retirement_record(site, chunk.saturating_add(1), chunk);
                    bytes.truncate(bytes.len() - chunk);
                }
                session.retirement_record(site, size_of::<Vec<u8>>() + 1, size_of::<Vec<u8>>());
                drop(bytes);
            }
        }
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}
fn finish<O: ExecutionObserver>(
    mut state: State<'_>,
    result: R,
    mut out: Output<'_, '_, O>,
) -> R<core::result::Result<ProofDigest, String>> {
    // All partial plans, borrowed roots/rows and returned display Strings
    // stay owned through the next fallible operation and complete cleanup.
    state.retire_scratch(&mut out);
    if let Err(error) = result {
        state.retire_output(&mut out);
        return Err(error);
    }
    let published = out
        .admit(1, size_of::<core::result::Result<ProofDigest, String>>())
        .and_then(|()| out.publication());
    if let Err(error) = published {
        state.retire_output(&mut out);
        return Err(error);
    }
    if let Some(digest) = state.digest {
        Ok(Ok(digest))
    } else {
        Ok(Err(core::mem::take(&mut state.reason)))
    }
}
