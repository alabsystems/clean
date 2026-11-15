// Copyright 2026 Andrew Yates | Apache-2.0
//! Versioned, lossless persisted Environment data, never proof authority.
//!
//! V2 owns its complete recursive schema and primitive byte grammar. It does
//! not serialize live kernel types through serde. The globally ambiguous G1
//! format requires an explicit source epoch, established by its caller.
use super::Environment;
use containers::{FromWire, ToWire};
use environment::{Legacy3faEnvironment, LegacyC4Environment, WireEnvironment};
use graph::{Projection, Restoration};
use primitive::{Budget, Decoder, Encoder, Encoding, Result, Wire};
use types::WExprKind;

mod containers;
mod environment;
mod graph;
mod primitive;
mod syntax;
mod theorem;
pub use theorem::{decode_theorem_dag, encode_theorem_dag};
mod types;

const MAGIC_V1: [u8; 8] = *b"CLENEDG1";
const MAGIC_V2: [u8; 8] = *b"CLENEDG2";
const MAX_BYTES: usize = 256 * 1024 * 1024;
const MAX_NODES: usize = 1_000_000;
const MAX_EDGES: usize = 8_000_000;
const MAX_DEPTH: usize = 4096;
const MAX_NODE_BYTES: usize = 1024 * 1024;

/// A carrier refusal, never a kernel verdict.
#[derive(Debug, thiserror::Error)]
pub enum DagCodecError {
    /// Framing, source schema, structural limits or allocation was invalid.
    #[error("Environment DAG carrier refused: {0}")]
    Refused(String),
}
fn error(message: impl Into<String>) -> DagCodecError {
    DagCodecError::Refused(message.into())
}

/// Fixed data-schema choices for the ambiguous G1 carrier, not permissions or
/// checker policies. Source identity must be established by the caller.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LegacyEnvironmentDagEpoch {
    /// Exact 554-field producer schema at Clean3fa, whose level algebra is
    /// currently named Lean430. This does not claim whole-checker equivalence.
    Clean3fa,
    /// Exact 555-field C4 schema, retaining its explicit Lean48/Lean430 field.
    CleanC4,
}

struct PayloadNode {
    id: u32,
    kind: Vec<u8>,
}
struct Envelope {
    environment: Vec<u8>,
    nodes: Vec<PayloadNode>,
    budget: Budget,
}

fn envelope(data: &[u8], encoding: Encoding) -> Result<Envelope> {
    let mut r = Decoder::new(data, encoding)?;
    let magic = r.take(8)?;
    match encoding {
        Encoding::V2 => {
            if magic == MAGIC_V1 {
                return Err(error("legacy G1 requires an explicit source epoch"));
            }
            if magic != MAGIC_V2 {
                return Err(error("wrong format/version/flags"));
            }
            let version = r.u32()?;
            let flags = r.u32()?;
            if version != 2 || flags != 0 {
                return Err(error("wrong format/version/flags"));
            }
        }
        Encoding::Legacy => {
            if magic != MAGIC_V1 {
                return Err(error("wrong legacy format/version"));
            }
        }
    }
    let environment = r.bytes()?;
    let nodes = read_nodes(&mut r)?;
    Ok(Envelope {
        environment,
        nodes,
        budget: r.finish()?,
    })
}

fn read_nodes(r: &mut Decoder<'_>) -> Result<Vec<PayloadNode>> {
    let count = r.len()?;
    if count > MAX_NODES {
        return Err(error("expression node limit"));
    }
    r.budget.can_allocate(count, size_of::<PayloadNode>())?;
    let mut nodes = Vec::new();
    let mut accounted = 0;
    for _ in 0..count {
        let id = r.u32()?;
        let kind = r.bytes_bounded(MAX_NODE_BYTES)?;
        r.push(&mut nodes, &mut accounted, PayloadNode { id, kind }, count)?;
    }
    Ok(nodes)
}

fn restore(data: &[u8], epoch: Option<LegacyEnvironmentDagEpoch>) -> Result<Environment> {
    let encoding = if epoch.is_some() {
        Encoding::Legacy
    } else {
        Encoding::V2
    };
    let Envelope {
        environment,
        nodes,
        mut budget,
    } = envelope(data, encoding)?;
    let mut restoration = Restoration::new(nodes.len())?;
    for PayloadNode { id, kind } in nodes {
        let mut decoder = Decoder::with_budget(&kind, encoding, budget)?;
        let node = WExprKind::read(&mut decoder)?;
        budget = decoder.finish()?;
        restoration.node(id, node)?;
    }
    let mut decoder = Decoder::with_budget(&environment, encoding, budget)?;
    let wire = match epoch {
        None => WireEnvironment::read(&mut decoder)?,
        Some(LegacyEnvironmentDagEpoch::Clean3fa) => {
            Legacy3faEnvironment::read(&mut decoder)?.into_current()
        }
        Some(LegacyEnvironmentDagEpoch::CleanC4) => {
            LegacyC4Environment::read(&mut decoder)?.into_current()
        }
    };
    decoder.finish()?;
    Environment::from_wire(wire, &mut restoration)
}

impl Environment {
    /// Write only V2 using fixed recursive DTOs and owned primitive encoding.
    /// Every current persisted field is explicit; transient caches and checking
    /// provenance remain absent. A successful write is not kernel admission.
    pub fn to_dag_bincode(&self) -> Result<Vec<u8>> {
        let mut projection = Projection::default();
        let wire = self.to_wire(&mut projection)?;
        let mut payload = Encoder::new(Encoding::V2);
        wire.write(&mut payload)?;
        let payload = payload.finish();
        let mut out = Encoder::new(Encoding::V2);
        out.raw(&MAGIC_V2)?;
        out.u32(2)?;
        out.u32(0)?;
        out.bytes(&payload)?;
        out.len(projection.nodes.len())?;
        for node in projection.nodes {
            let mut kind = Encoder::bounded(Encoding::V2, MAX_NODE_BYTES);
            node.kind
                .write(&mut kind)
                .map_err(|e| error(format!("node payload: {e}")))?;
            out.u32(node.id)?;
            out.bytes(&kind.finish())?;
        }
        Ok(out.finish())
    }

    /// Restore only V2 as untrusted data. G1 refuses here because its two
    /// historical schemas cannot be distinguished reliably from magic alone.
    /// No flag, origin or name supplies checking authority; replay is separate.
    pub fn from_dag_bincode(data: &[u8]) -> Result<Self> {
        restore(data, None)
    }

    /// Restore a caller-identified G1 source schema as untrusted data.
    ///
    /// This never trial-decodes, guesses the profile, or weakens fresh replay.
    /// Some G1 byte strings may inhabit both grammars: this API is a schema
    /// selection, not an authenticator of arbitrary legacy producer identity.
    pub fn from_legacy_dag_bincode(data: &[u8], epoch: LegacyEnvironmentDagEpoch) -> Result<Self> {
        restore(data, Some(epoch))
    }
}

#[cfg(test)]
mod tests;
