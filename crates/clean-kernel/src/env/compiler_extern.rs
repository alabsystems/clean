// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lossless compiler annotations, never permission to execute an extern.
//! The existing symbol table still drives the existing refusal paths. Typed
//! records use the Environment's persisted plain-data extension channel, so
//! cloning, effect capture, fact deltas and both owned DAG epochs retain them
//! without changing the frozen Environment schema or adding an interior cell.

use super::{EnvExtensionEntry, EnvExtensionEntryData, Environment};
use crate::serde_budget::{with_decode_resource_limits, DecodeResourceLimits};
use crate::Name;
use serde::{Deserialize, Serialize};

/// Whether the producer's format represents an explicit extern arity field.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CompilerExternArity {
    /// A producer form without a separate arity field, including the
    /// represented modern Lean and standard source forms.
    Unspecified,
    /// Older Lean's actual `arity?` field, including an explicit `none`.
    Legacy(Option<u64>),
}

/// An entry in producer order. Unsupported entry kinds stay visible.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CompilerExternEntry {
    Adhoc { backend: Name },
    Inline { backend: Name, pattern: String },
    Standard { backend: Name, symbol: String },
    Foreign { backend: Name, symbol: String },
    Opaque,
}

/// The complete represented descriptor. Completeness is not native authority.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompilerExternDescriptor {
    pub arity: CompilerExternArity,
    pub entries: Vec<CompilerExternEntry>,
}

/// Why a legacy record cannot supply a full native contract.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CompilerExternIncomplete {
    SymbolOnly,
    UnspecifiedSourceBinding,
}

/// Compiler metadata supplied by a frontend or importer, without admission.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CompilerExternMetadata {
    Complete(CompilerExternDescriptor),
    Incomplete {
        diagnostic: String,
        reason: CompilerExternIncomplete,
    },
}

impl From<String> for CompilerExternMetadata {
    fn from(diagnostic: String) -> Self {
        Self::Incomplete {
            diagnostic,
            reason: CompilerExternIncomplete::SymbolOnly,
        }
    }
}

impl CompilerExternMetadata {
    /// Preserve the existing diagnostic spelling. This string grants no
    /// backend, signature, ownership or implementation authority.
    pub fn diagnostic(&self) -> String {
        match self {
            Self::Incomplete { diagnostic, .. } => diagnostic.clone(),
            Self::Complete(descriptor) => descriptor.diagnostic(),
        }
    }
}

impl CompilerExternDescriptor {
    /// A human-facing refusal label, retaining the old first-standard label.
    /// Consumers requiring metadata must use the typed descriptor instead.
    pub fn diagnostic(&self) -> String {
        if let Some(symbol) = self.entries.iter().find_map(|entry| match entry {
            CompilerExternEntry::Standard { symbol, .. } => Some(symbol),
            _ => None,
        }) {
            return symbol.clone();
        }
        self.entries
            .iter()
            .map(|entry| match entry {
                CompilerExternEntry::Adhoc { backend } => format!("adhoc {backend}"),
                CompilerExternEntry::Inline { backend, pattern } => {
                    format!("inline {backend} {pattern}")
                }
                CompilerExternEntry::Standard { backend, symbol } => {
                    format!("standard {backend} {symbol}")
                }
                CompilerExternEntry::Foreign { backend, symbol } => {
                    format!("foreign {backend} {symbol}")
                }
                CompilerExternEntry::Opaque => "opaque".to_owned(),
            })
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// A malformed or conflicting carrier must never become a guessed descriptor.
#[derive(Debug, thiserror::Error)]
pub enum CompilerExternMetadataError {
    #[error("extern metadata exceeds the bounded carrier")]
    Resource,
    #[error("extern metadata has no entry")]
    Empty,
    #[error("extern metadata encoding: {0}")]
    Encoding(#[source] serde_json::Error),
    #[error("extern metadata uses an unknown or malformed carrier")]
    Malformed,
    #[error("extern metadata has conflicting records or diagnostic binding")]
    Conflict,
}

const STORAGE_KEY: &str = "Clean.compilerExtern.v1";
const PREFIX: &[u8] = b"Clean.compilerExtern.v1\0";
const MAX_BYTES: usize = 1 << 20;
const MAX_ENTRIES: usize = 64;
const DECODE_LIMITS: DecodeResourceLimits = DecodeResourceLimits {
    max_nodes: MAX_BYTES,
    max_depth: MAX_BYTES,
};

pub(super) fn storage_key() -> Name {
    Name::from_string(STORAGE_KEY)
}

fn validate(metadata: &CompilerExternMetadata) -> Result<(), CompilerExternMetadataError> {
    if let CompilerExternMetadata::Complete(descriptor) = metadata {
        if descriptor.entries.is_empty() {
            return Err(CompilerExternMetadataError::Empty);
        }
        if descriptor.entries.len() > MAX_ENTRIES {
            return Err(CompilerExternMetadataError::Resource);
        }
    }
    Ok(())
}

fn encode(metadata: &CompilerExternMetadata) -> Result<Vec<u8>, CompilerExternMetadataError> {
    validate(metadata)?;
    let payload = serde_json::to_vec(metadata).map_err(CompilerExternMetadataError::Encoding)?;
    if payload.len() > MAX_BYTES - PREFIX.len() {
        return Err(CompilerExternMetadataError::Resource);
    }
    let mut bytes = Vec::with_capacity(PREFIX.len() + payload.len());
    bytes.extend_from_slice(PREFIX);
    bytes.extend_from_slice(&payload);
    Ok(bytes)
}

fn decode(
    entry: &EnvExtensionEntry,
) -> Result<CompilerExternMetadata, CompilerExternMetadataError> {
    let EnvExtensionEntryData::Object(bytes) = &entry.data else {
        return Err(CompilerExternMetadataError::Malformed);
    };
    if bytes.len() > MAX_BYTES {
        return Err(CompilerExternMetadataError::Resource);
    }
    let payload = bytes
        .strip_prefix(PREFIX)
        .ok_or(CompilerExternMetadataError::Malformed)?;
    let metadata = with_decode_resource_limits(DECODE_LIMITS, || {
        serde_json::from_slice::<CompilerExternMetadata>(payload)
    })
    .map_err(CompilerExternMetadataError::Encoding)?;
    validate(&metadata)?;
    if serde_json::to_vec(&metadata)
        .map_err(CompilerExternMetadataError::Encoding)?
        .as_slice()
        != payload
    {
        return Err(CompilerExternMetadataError::Malformed);
    }
    Ok(metadata)
}

impl Environment {
    /// Register a represented compiler annotation, without changing any native
    /// admission policy. A later symbol-only registration invalidates this row.
    pub fn register_extern_metadata(
        &mut self,
        name: Name,
        metadata: CompilerExternMetadata,
    ) -> Result<(), CompilerExternMetadataError> {
        let entry = EnvExtensionEntry {
            name: name.clone(),
            data: EnvExtensionEntryData::Object(encode(&metadata)?),
        };
        // Serialization and deserialization have different recursion limits.
        // Validate with the actual reader before replacing any previous row.
        if decode(&entry)? != metadata {
            return Err(CompilerExternMetadataError::Malformed);
        }
        let diagnostic = metadata.diagnostic();
        self.clear_extern_metadata(&name);
        self.persistent_extensions
            .append(&storage_key(), 0, vec![entry]);
        self.extern_bindings.insert(name, diagnostic);
        Ok(())
    }

    /// Read metadata as data only. A legacy symbol is explicitly incomplete;
    /// malformed, unknown-version, disagreeing or duplicate-conflicting rows
    /// refuse. No canonical source name or native symbol fills missing fields.
    pub fn extern_metadata(
        &self,
        name: &Name,
    ) -> Result<Option<CompilerExternMetadata>, CompilerExternMetadataError> {
        let diagnostic = self.extern_bindings.get(name);
        let mut selected = None;
        for entry in self
            .persistent_extensions
            .get(&storage_key())
            .into_iter()
            .flat_map(|state| state.imported_entries.iter().flatten())
            .filter(|entry| &entry.name == name)
        {
            let metadata = decode(entry)?;
            if selected
                .as_ref()
                .is_some_and(|previous| previous != &metadata)
            {
                return Err(CompilerExternMetadataError::Conflict);
            }
            selected = Some(metadata);
        }
        match (diagnostic, selected) {
            (None, None) => Ok(None),
            (Some(symbol), None) => Ok(Some(CompilerExternMetadata::from(symbol.clone()))),
            (Some(symbol), Some(metadata)) if *symbol == metadata.diagnostic() => {
                Ok(Some(metadata))
            }
            _ => Err(CompilerExternMetadataError::Conflict),
        }
    }

    pub(super) fn clear_extern_metadata(&mut self, name: &Name) {
        let key = storage_key();
        if let Some(mut state) = self.persistent_extensions.get(&key).cloned() {
            for entries in &mut state.imported_entries {
                entries.retain(|entry| &entry.name != name);
            }
            self.persistent_extensions.set_state(&key, Some(state));
        }
    }
}

#[cfg(test)]
mod tests;
