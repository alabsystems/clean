// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured spec-annotation extraction for 15 verification tool sources.
//!
//! This module provides extractors that produce `Vec<StructuredDecl>` records
//! from source files of various verification tools, plus a shared shard
//! writer that converts those records into `.mathverse` shard files.
//!
//! ## Tool families
//!
//! - **Rust verification** (7 tools): Verus, Creusot, Kani, Prusti, Aeneas, Hax, CreuSAT
//! - **Scala verification** (3 sources): Stainless, Stainless-Bolts, LISA
//! - **Move Prover** (1 source): Move specification language
//! - **IVL / Separation logic** (3 sources): Boogie, Viper, VeriFast

pub mod ivl;
pub mod moveprover;
pub mod rustverif;
pub mod scalaverif;
pub mod types;

// Re-export core types at module level.
pub use types::{DeclKind, StructuredDecl};

use std::fs;
use std::path::Path;

use clean_kernel::flat::{FlatExpr, FlatLevel};

use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ---------------------------------------------------------------------------
// Shard writer for StructuredDecl records
// ---------------------------------------------------------------------------

/// Write a `Vec<StructuredDecl>` to a `.mathverse` shard file.
///
/// Each declaration becomes an `MathverseConstantHeader` entry with:
/// - `name_idx` — the declaration name (or a synthetic name for unnamed specs)
/// - `type_idx` — a `LitStr` expression encoding the spec content
/// - `value_idx` — `NO_VALUE` for pure specs, placeholder for implementations
/// - `source_system` — from the `StructuredDecl`
/// - `import_confidence` — `Translated` for all structured extractions
/// - `content_domain` — `Software` (these are program verification specs)
pub fn write_specannot_shard(decls: &[StructuredDecl], output_path: &Path) -> MathverseResult<u32> {
    if decls.is_empty() {
        return Ok(0);
    }
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)?;
    }

    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let placeholder_expr = writer.add_expr(FlatExpr::sort(l0));

    for (i, decl) in decls.iter().enumerate() {
        // Build a meaningful name: "<source>.<name>" or "<source>.spec_<line>"
        let display_name = if decl.name.is_empty() {
            let line_str = decl
                .source_line
                .map(|l| l.to_string())
                .unwrap_or_else(|| i.to_string());
            format!("{:?}.spec_{line_str}", decl.source_system)
        } else {
            format!("{:?}.{}", decl.source_system, decl.name)
        };

        let name_idx = writer.add_string(&display_name);

        // Encode the spec content as a LitStr expression.
        let type_expr_idx = if decl.spec_content.is_empty() {
            placeholder_expr
        } else {
            let spec_str_idx = writer.add_string(&decl.spec_content);
            writer.add_expr(FlatExpr::lit_str(spec_str_idx))
        };

        // Pure specs (requires, ensures, axioms, etc.) have no value.
        // Implementations (functions, procedures) get a placeholder.
        let is_pure_spec = matches!(
            decl.kind,
            DeclKind::Requires
                | DeclKind::Ensures
                | DeclKind::Assume
                | DeclKind::Assert
                | DeclKind::Variant
                | DeclKind::AbortsIf
                | DeclKind::Axiom
                | DeclKind::ScalaRequire
                | DeclKind::ScalaEnsuring
                | DeclKind::SpecComment
                | DeclKind::StainlessAnnotation
                | DeclKind::LogicAnnotation
        );

        // Pure spec annotations are axiomatic obligations (pre/post/invariants);
        // proof functions are Theorems; everything else with a body is a Definition.
        let shard_kind = match decl.kind {
            DeclKind::ProofFn | DeclKind::BroadcastProofFn | DeclKind::ProofHarness => {
                crate::types::DeclKind::Theorem
            }
            _ if is_pure_spec => crate::types::DeclKind::Axiom,
            _ => crate::types::DeclKind::Definition,
        };
        let header = MathverseConstantHeader {
            name_idx,
            type_idx: type_expr_idx,
            value_idx: if is_pure_spec {
                NO_VALUE
            } else {
                placeholder_expr
            },
            source_system: decl.source_system as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::Software as u8,
            decl_kind: shard_kind as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };
        writer.add_constant(header);
    }

    let count = decls.len() as u32;
    writer.write_to_file(output_path)?;
    Ok(count)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardReader;

    #[test]
    fn test_write_specannot_shard_round_trip() {
        let decls = vec![
            StructuredDecl {
                name: "my_proof".to_string(),
                kind: DeclKind::ProofFn,
                spec_content: "proof fn my_proof(x: int)".to_string(),
                source_file: "test.rs".to_string(),
                source_line: Some(10),
                source_system: SourceSystem::Verus,
            },
            StructuredDecl {
                name: String::new(),
                kind: DeclKind::Requires,
                spec_content: "x > 0".to_string(),
                source_file: "test.rs".to_string(),
                source_line: Some(11),
                source_system: SourceSystem::Verus,
            },
            StructuredDecl {
                name: "Increment".to_string(),
                kind: DeclKind::Procedure,
                spec_content: "procedure Increment(x: int) returns (y: int)".to_string(),
                source_file: "example.bpl".to_string(),
                source_line: Some(5),
                source_system: SourceSystem::Boogie,
            },
        ];

        let dir = tempfile::tempdir().unwrap();
        let shard_path = dir.path().join("test_specannot.mathverse");
        let count = write_specannot_shard(&decls, &shard_path).unwrap();
        assert_eq!(count, 3);

        let reader = ShardReader::from_file(&shard_path).unwrap();
        assert_eq!(reader.header.constant_count, 3);

        // First constant: named proof fn
        let c0 = &reader.constants[0];
        let name0 = &reader.strings[c0.name_idx as usize];
        assert!(name0.contains("my_proof"));
        assert_eq!(c0.source_system, SourceSystem::Verus as u8);
        assert!(c0.has_value()); // ProofFn is not pure spec

        // Second constant: unnamed requires spec
        let c1 = &reader.constants[1];
        let name1 = &reader.strings[c1.name_idx as usize];
        assert!(name1.contains("spec_11"));
        assert!(!c1.has_value()); // Requires is pure spec

        // Third constant: Boogie procedure
        let c2 = &reader.constants[2];
        assert_eq!(c2.source_system, SourceSystem::Boogie as u8);
        assert!(c2.has_value()); // Procedure has implementation
    }

    #[test]
    fn test_write_specannot_shard_empty() {
        let dir = tempfile::tempdir().unwrap();
        let shard_path = dir.path().join("empty.mathverse");
        let count = write_specannot_shard(&[], &shard_path).unwrap();
        assert_eq!(count, 0);
        assert!(!shard_path.exists());
    }
}
