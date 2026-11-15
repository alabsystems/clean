// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Fallible actual ABI wire-text encoder and complete bounded reader checks.
//! Identity/capacity checks only; no target ABI or producer authority is issued.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};

type R<T = ()> = core::result::Result<T, ObservedValueError>;
mod writer;
use writer::Writer;
mod arena;
mod check;
mod encode;
mod limits;
mod parser;

impl SignatureAbi {
    /// Produce the exact canonical text after all existing encoding-limit,
    /// bounded-reader, typed-shape and canonical-round-trip checks, using the
    /// caller's original observation session/site throughout. This verifies
    /// encodability only, never the truth of a target ABI or producer claim.
    pub fn canonical_text_for_wire_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        let mut out = Writer::new(session, site)?;
        let result = (|| {
            identity_budget(self, &mut out)?;
            node_budget(self, &mut out)?;
            encode::signature(self, &mut out)?;
            round_trip(&mut out)
        })();
        let residue = core::mem::take(&mut out.text);
        out.retire(residue);
        match result {
            Ok(text) => {
                if let Err(error) = out.publication() {
                    out.retire(text);
                    return Err(error);
                }
                Ok(text)
            }
            Err(error) => Err(error),
        }
    }
}

fn identity_budget<O: ExecutionObserver>(a: &SignatureAbi, out: &mut Writer<'_, '_, O>) -> R {
    let identities = [
        &a.target.triple,
        &a.target.data_layout,
        &a.target.abi,
        &a.target.cpu,
        &a.target.target_spec,
        &a.frontend.name,
        &a.frontend.revision,
        &a.convention,
        &a.source_abi,
    ];
    let mut bytes = 0usize;
    for text in identities.into_iter().chain(a.target.features.iter()) {
        out.poll()?;
        bytes = bytes
            .checked_add(text.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if bytes > MAX_ABI_TEXT_BYTES {
            return Err(ObservedValueError::UnsupportedValue);
        }
    }
    Ok(())
}
fn node_budget<O: ExecutionObserver>(a: &SignatureAbi, out: &mut Writer<'_, '_, O>) -> R {
    let mut nodes = 20usize;
    add_nodes(&mut nodes, a.target.features.len(), out)?;
    for argument in a.arguments.iter().chain(core::iter::once(&a.result)) {
        out.poll()?;
        let mode_nodes = match &argument.mode {
            AbiPassMode::Ignore => 2,
            AbiPassMode::Direct(_) => 21,
            AbiPassMode::Pair(_, _) => 40,
            AbiPassMode::Cast { prefix, .. } => 23usize
                .checked_add(
                    prefix
                        .len()
                        .checked_mul(3)
                        .ok_or(ObservedValueError::CapacityOverflow)?,
                )
                .ok_or(ObservedValueError::CapacityOverflow)?,
            AbiPassMode::Indirect {
                metadata_attributes,
                ..
            } => {
                if metadata_attributes.is_some() {
                    28
                } else {
                    17
                }
            }
        };
        add_nodes(
            &mut nodes,
            4usize
                .checked_add(mode_nodes)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            out,
        )?;
        add_nodes(
            &mut nodes,
            argument
                .bindings
                .len()
                .checked_mul(7)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            out,
        )?;
    }
    Ok(())
}
fn add_nodes<O: ExecutionObserver>(
    nodes: &mut usize,
    count: usize,
    out: &mut Writer<'_, '_, O>,
) -> R {
    out.poll()?;
    *nodes = nodes
        .checked_add(count)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    if *nodes > MAX_NODES {
        return Err(ObservedValueError::UnsupportedValue);
    }
    Ok(())
}
fn round_trip<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>) -> R<String> {
    let text = core::mem::take(&mut out.text);
    let result = (|| {
        let (arena, root) = parser::parse(&text, out)?;
        let checked = (|| {
            check::validate_signature(&arena, root, out)?;
            arena.emit_canonical(root, out)?;
            let recoded = core::mem::take(&mut out.text);
            let equal = equal_text(&text, &recoded, out);
            out.retire(recoded);
            equal?;
            out.poll()
        })();
        arena.retire(out);
        checked?;
        out.poll()
    })();
    if let Err(error) = result {
        out.retire(text);
        return Err(error);
    }
    Ok(text)
}
fn equal_text<O: ExecutionObserver>(left: &str, right: &str, out: &mut Writer<'_, '_, O>) -> R {
    out.poll()?;
    if left.len() != right.len() {
        return Err(ObservedValueError::UnsupportedValue);
    }
    for (a, b) in left
        .as_bytes()
        .chunks(1024)
        .zip(right.as_bytes().chunks(1024))
    {
        out.admit(
            a.len()
                .checked_add(b.len())
                .ok_or(ObservedValueError::CapacityOverflow)?,
            0,
        )?;
        if a != b {
            return Err(ObservedValueError::UnsupportedValue);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
