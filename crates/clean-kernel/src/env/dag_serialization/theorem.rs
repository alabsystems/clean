// Copyright 2026 Andrew Yates | Apache-2.0
//! Theorem-only transport using the frozen G2 syntax and bounded graph grammar.
//! No environment, checking provenance, gate token or proof grade crosses here.

use super::containers::{FromWire, ToWire};
use super::graph::{Projection, Ref, Restoration};
use super::primitive::{Decoder, Encoder, Encoding, Result, Wire};
use super::syntax::WName;
use super::types::WExprKind;
use super::{error, read_nodes, MAX_NODE_BYTES};
use crate::{Declaration, Expr, Name};

const MAGIC: &[u8; 8] = b"CLENTHG1";

/// Encode a supplied theorem as untrusted data, never a checking result.
/// The four theorem fields are explicit. Axioms, definitions and all other
/// declaration variants refuse rather than changing their authority class.
/// Shared expressions retain DAG references with the G2 finite budgets.
pub fn encode_theorem_dag(theorem: &Declaration) -> Result<Vec<u8>> {
    let Declaration::Theorem {
        name,
        level_params,
        type_,
        value,
    } = theorem
    else {
        return Err(error("theorem carrier requires a theorem declaration"));
    };
    let mut projection = Projection::default();
    let name = name.to_wire(&mut projection)?;
    let level_params = level_params.to_wire(&mut projection)?;
    let type_ = type_.to_wire(&mut projection)?;
    let value = value.to_wire(&mut projection)?;
    let mut payload = Encoder::new(Encoding::V2);
    name.write(&mut payload)?;
    level_params.write(&mut payload)?;
    type_.write(&mut payload)?;
    value.write(&mut payload)?;
    let mut out = Encoder::new(Encoding::V2);
    out.raw(MAGIC)?;
    out.u32(1)?;
    out.u32(0)?;
    out.bytes(&payload.finish())?;
    out.len(projection.nodes.len())?;
    for node in projection.nodes {
        let mut kind = Encoder::bounded(Encoding::V2, MAX_NODE_BYTES);
        node.kind.write(&mut kind)?;
        out.u32(node.id)?;
        out.bytes(&kind.finish())?;
    }
    Ok(out.finish())
}

/// Restore a theorem as untrusted syntax. Successful decoding establishes
/// neither well-typedness nor a true proposition: the consumer must replay
/// this exact supplied witness against its own checked environment and goal.
/// Wrong domains, versions, flags, trailing bytes and malformed graphs refuse.
pub fn decode_theorem_dag(bytes: &[u8]) -> Result<Declaration> {
    let mut decoder = Decoder::new(bytes, Encoding::V2)?;
    if decoder.take(8)? != MAGIC || decoder.u32()? != 1 || decoder.u32()? != 0 {
        return Err(error("wrong theorem carrier format/version/flags"));
    }
    let payload = decoder.bytes()?;
    let nodes = read_nodes(&mut decoder)?;
    let mut budget = decoder.finish()?;
    let mut restoration = Restoration::new(nodes.len())?;
    for node in nodes {
        let mut decoder = Decoder::with_budget(&node.kind, Encoding::V2, budget)?;
        let kind = WExprKind::read(&mut decoder)?;
        budget = decoder.finish()?;
        restoration.node(node.id, kind)?;
    }
    let mut decoder = Decoder::with_budget(&payload, Encoding::V2, budget)?;
    let name = WName::read(&mut decoder)?;
    let level_params = Vec::<WName>::read(&mut decoder)?;
    let type_ = Ref::read(&mut decoder)?;
    let value = Ref::read(&mut decoder)?;
    decoder.finish()?;
    Ok(Declaration::Theorem {
        name: Name::from_wire(name, &mut restoration)?,
        level_params: Vec::<Name>::from_wire(level_params, &mut restoration)?,
        type_: Expr::from_wire(type_, &mut restoration)?,
        value: Expr::from_wire(value, &mut restoration)?,
    })
}

#[cfg(test)]
mod tests;
