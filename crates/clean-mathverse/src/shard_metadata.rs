// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metadata sidecar format for `.mathverse` shards.
//!
//! Each `.mathverse` binary shard can be accompanied by a `.mathverse.json` sidecar
//! containing human-readable metadata about the declarations it stores.
//! This module defines the sidecar schema and provides read/write functions.

use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Kind of a declaration (theorem, definition, axiom, etc.).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DeclKind {
    Theorem,
    Definition,
    Axiom,
    Opaque,
    Inductive,
    Constructor,
    Recursor,
    Quotient,
}

impl DeclKind {
    /// Parse from a lowercase string (e.g. `"theorem"`, `"def"`).
    #[must_use]
    pub fn from_str_loose(s: &str) -> Option<Self> {
        match s {
            "theorem" | "thm" => Some(Self::Theorem),
            "definition" | "def" => Some(Self::Definition),
            "axiom" | "ax" => Some(Self::Axiom),
            "opaque" => Some(Self::Opaque),
            "inductive" | "ind" => Some(Self::Inductive),
            "constructor" | "ctor" => Some(Self::Constructor),
            "recursor" | "rec" => Some(Self::Recursor),
            "quotient" | "quot" => Some(Self::Quotient),
            _ => None,
        }
    }

    /// Convert to the shard-header [`crate::types::DeclKind`] u8 discriminant.
    ///
    /// The two enums are structurally aligned (same order, same meaning); the
    /// only naming difference is `Quotient` (metadata) vs `Quot` (shard). This
    /// method is the single source of truth for that mapping and is used by
    /// all shard writers that carry `MetadataEntry` alongside
    /// `MathverseConstantHeader`. See #3532.
    #[must_use]
    pub fn to_shard_kind(self) -> crate::types::DeclKind {
        use crate::types::DeclKind as Shard;
        match self {
            Self::Theorem => Shard::Theorem,
            Self::Definition => Shard::Definition,
            Self::Axiom => Shard::Axiom,
            Self::Opaque => Shard::Opaque,
            Self::Inductive => Shard::Inductive,
            Self::Constructor => Shard::Constructor,
            Self::Recursor => Shard::Recursor,
            Self::Quotient => Shard::Quot,
        }
    }
}

/// Metadata for a single declaration within a shard.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetadataEntry {
    /// Fully qualified name (e.g. `Nat.add_comm`).
    pub name: String,

    /// Declaration kind, if known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<DeclKind>,

    /// Pretty-printed type signature, if available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_signature: Option<String>,

    /// Source file path relative to library root, if known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_file: Option<String>,

    /// Line number in source file, if known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_number: Option<u32>,
}

/// Shard metadata sidecar: summary + per-declaration entries.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ShardMetadata {
    /// Metadata format version.
    pub version: String,

    /// Name of the source system (e.g. `"Lean4"`, `"Metamath"`).
    pub system_name: String,

    /// Total number of declarations in the shard.
    pub declaration_count: usize,

    /// Per-declaration metadata entries.
    pub declarations: Vec<MetadataEntry>,
}

impl ShardMetadata {
    /// Create new metadata for a system with an empty declaration list.
    #[must_use]
    pub fn new(system_name: &str) -> Self {
        Self {
            version: "0.1.0".to_string(),
            system_name: system_name.to_string(),
            declaration_count: 0,
            declarations: Vec::new(),
        }
    }

    /// Add a declaration entry and update the count.
    pub fn push(&mut self, entry: MetadataEntry) {
        self.declarations.push(entry);
        self.declaration_count = self.declarations.len();
    }

    /// Serialize to pretty-printed JSON.
    pub fn to_json(&self) -> MathverseResult<String> {
        serde_json::to_string_pretty(self).map_err(MathverseError::from)
    }

    /// Deserialize from a JSON string.
    pub fn from_json(json: &str) -> MathverseResult<Self> {
        serde_json::from_str(json).map_err(MathverseError::from)
    }
}

// ---------------------------------------------------------------------------
// I/O helpers
// ---------------------------------------------------------------------------

/// Write shard metadata as a `.mathverse.json` sidecar next to the given shard path.
///
/// Given `/data/lean4/Init.mathverse`, writes to `/data/lean4/Init.mathverse.json`.
pub fn write_metadata(shard_path: &Path, metadata: &ShardMetadata) -> MathverseResult<()> {
    let sidecar_path = sidecar_path_for(shard_path);
    let json = metadata.to_json()?;
    fs::write(&sidecar_path, json)?;
    Ok(())
}

/// Load shard metadata from a `.mathverse.json` sidecar next to the given shard path.
pub fn load_metadata(shard_path: &Path) -> MathverseResult<ShardMetadata> {
    let sidecar_path = sidecar_path_for(shard_path);
    let json = fs::read_to_string(&sidecar_path)?;
    ShardMetadata::from_json(&json)
}

/// Compute the sidecar path for a given shard path.
///
/// Appends `.json` to the shard filename: `foo.mathverse` -> `foo.mathverse.json`.
#[must_use]
pub fn sidecar_path_for(shard_path: &Path) -> std::path::PathBuf {
    let mut p = shard_path.as_os_str().to_owned();
    p.push(".json");
    std::path::PathBuf::from(p)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shard_metadata_new_defaults() {
        let m = ShardMetadata::new("Lean4");
        assert_eq!(m.version, "0.1.0");
        assert_eq!(m.system_name, "Lean4");
        assert_eq!(m.declaration_count, 0);
        assert!(m.declarations.is_empty());
    }

    #[test]
    fn test_shard_metadata_push_updates_count() {
        let mut m = ShardMetadata::new("Coq");
        m.push(MetadataEntry {
            name: "Nat.add".to_string(),
            kind: Some(DeclKind::Definition),
            type_signature: Some("Nat -> Nat -> Nat".to_string()),
            source_file: None,
            line_number: None,
        });
        assert_eq!(m.declaration_count, 1);
        assert_eq!(m.declarations.len(), 1);
        assert_eq!(m.declarations[0].name, "Nat.add");
    }

    #[test]
    fn test_serde_roundtrip() {
        let mut m = ShardMetadata::new("Metamath");
        m.push(MetadataEntry {
            name: "ax-mp".to_string(),
            kind: Some(DeclKind::Axiom),
            type_signature: None,
            source_file: Some("set.mm".to_string()),
            line_number: Some(42),
        });
        m.push(MetadataEntry {
            name: "th-add-comm".to_string(),
            kind: Some(DeclKind::Theorem),
            type_signature: Some("|- ( A + B ) = ( B + A )".to_string()),
            source_file: Some("set.mm".to_string()),
            line_number: Some(100),
        });

        let json = m.to_json().expect("should serialize");
        let deserialized = ShardMetadata::from_json(&json).expect("should deserialize");

        assert_eq!(deserialized.version, m.version);
        assert_eq!(deserialized.system_name, m.system_name);
        assert_eq!(deserialized.declaration_count, 2);
        assert_eq!(deserialized.declarations.len(), 2);
        assert_eq!(deserialized.declarations[0].name, "ax-mp");
        assert_eq!(deserialized.declarations[1].name, "th-add-comm");
        assert_eq!(deserialized.declarations[0].kind, Some(DeclKind::Axiom));
        assert_eq!(
            deserialized.declarations[1].type_signature,
            Some("|- ( A + B ) = ( B + A )".to_string())
        );
    }

    #[test]
    fn test_serde_optional_fields_omitted() {
        let entry = MetadataEntry {
            name: "foo".to_string(),
            kind: None,
            type_signature: None,
            source_file: None,
            line_number: None,
        };
        let json = serde_json::to_string(&entry).expect("serialize entry");
        assert!(!json.contains("kind"));
        assert!(!json.contains("type_signature"));
        assert!(!json.contains("source_file"));
        assert!(!json.contains("line_number"));
    }

    #[test]
    fn test_write_and_load_metadata() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let shard_path = dir.path().join("test.mathverse");
        fs::write(&shard_path, b"fake shard").expect("write fake shard");

        let mut meta = ShardMetadata::new("TestSystem");
        meta.push(MetadataEntry {
            name: "TestDecl".to_string(),
            kind: Some(DeclKind::Theorem),
            type_signature: Some("Prop".to_string()),
            source_file: None,
            line_number: None,
        });

        write_metadata(&shard_path, &meta).expect("write metadata");

        let sidecar = sidecar_path_for(&shard_path);
        assert!(sidecar.exists(), "sidecar file should exist");
        assert_eq!(sidecar, dir.path().join("test.mathverse.json"));

        let loaded = load_metadata(&shard_path).expect("load metadata");
        assert_eq!(loaded.system_name, "TestSystem");
        assert_eq!(loaded.declaration_count, 1);
        assert_eq!(loaded.declarations[0].name, "TestDecl");
    }

    #[test]
    fn test_load_metadata_missing_file() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let shard_path = dir.path().join("nonexistent.mathverse");
        let result = load_metadata(&shard_path);
        assert!(result.is_err());
    }

    #[test]
    fn test_sidecar_path_for() {
        use std::path::PathBuf;
        let p = PathBuf::from("/data/lean4/Init.mathverse");
        assert_eq!(
            sidecar_path_for(&p),
            PathBuf::from("/data/lean4/Init.mathverse.json")
        );
    }

    #[test]
    fn test_decl_kind_from_str_loose() {
        assert_eq!(DeclKind::from_str_loose("theorem"), Some(DeclKind::Theorem));
        assert_eq!(DeclKind::from_str_loose("thm"), Some(DeclKind::Theorem));
        assert_eq!(DeclKind::from_str_loose("def"), Some(DeclKind::Definition));
        assert_eq!(DeclKind::from_str_loose("axiom"), Some(DeclKind::Axiom));
        assert_eq!(
            DeclKind::from_str_loose("constructor"),
            Some(DeclKind::Constructor)
        );
        assert_eq!(DeclKind::from_str_loose("unknown"), None);
    }

    #[test]
    fn test_decl_kind_serde_roundtrip() {
        for kind in [
            DeclKind::Theorem,
            DeclKind::Definition,
            DeclKind::Axiom,
            DeclKind::Opaque,
            DeclKind::Inductive,
            DeclKind::Constructor,
            DeclKind::Recursor,
            DeclKind::Quotient,
        ] {
            let json = serde_json::to_string(&kind).expect("serialize");
            let back: DeclKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(kind, back);
        }
    }
}
