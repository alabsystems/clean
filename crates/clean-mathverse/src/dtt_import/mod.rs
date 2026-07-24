// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DTT (Dependent Type Theory) importers for Agda, Idris 2, and F*.
//!
//! These three systems share a core design:
//! - All are based on dependent type theory (CIC family or Martin-Lof)
//! - All support inductive types, pattern matching, and universe polymorphism
//! - Each has unique features that clean axiomatizes:
//!   - **Agda**: cubical type theory (`PathP`, `Glue`, `hcomp`, `transp`)
//!   - **Idris 2**: quantitative type theory (linear `1` and erased `0` binders)
//!   - **F***: effect system (`ST`, `ML`, `Lemma`, `Div`)
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────┐  ┌──────────────┐  ┌──────────────────┐
//! │ agda.rs      │  │ idris2.rs    │  │ fstar.rs         │
//! │ JSON export  │  │ TT2 IR       │  │ Extraction       │
//! └──────┬───────┘  └──────┬───────┘  └────────┬─────────┘
//!        │                 │                    │
//!        ▼                 ▼                    ▼
//! ┌──────────────────────────────────────────────────────┐
//! │              types.rs: DttDeclaration                 │
//! │  name, type_expr, value_expr, axiom_profile, system  │
//! └──────────────────────┬───────────────────────────────┘
//!                        │
//!                        ▼
//! ┌──────────────────────────────────────────────────────┐
//! │          shard_writer.rs: write to dtt.mathverse          │
//! │  DttDeclaration -> MathverseConstantHeader + FlatExpr    │
//! └──────────────────────────────────────────────────────┘
//! ```
//!
//! ## Usage
//!
//! ```text
//! use clean_mathverse::dtt_import::{agda, idris2, fstar, shard_writer};
//!
//! // Parse system-specific formats
//! let agda_decls = agda::parse_agda_json(agda_json)?;
//! let idris_decls = idris2::parse_idris_tt(idris_json)?;
//! let fstar_decls = fstar::parse_fstar_extraction(fstar_json)?;
//!
//! // Write to shard
//! let mut writer = ShardWriter::new();
//! let meta = shard_writer::write_dtt_decls_by_system(
//!     &agda_decls, &idris_decls, &fstar_decls, &mut writer,
//! );
//! ```

pub mod agda;
pub mod fstar;
pub mod idris2;
pub mod shard_writer;
pub mod types;

// Re-export key types for convenience.
pub use types::{DttDeclaration, DttExpr, DttImportStats, DttModule, DttSystem};

/// Split a type string on the first top-level `->` or `→` not inside brackets.
///
/// Shared by Agda, Idris 2, and F* parsers for arrow-type splitting.
pub(crate) fn split_top_level_arrow(s: &str) -> Option<(&str, &str)> {
    let mut depth: u32 = 0;
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    while i < len {
        match bytes[i] {
            b'(' | b'{' | b'[' => depth += 1,
            b')' | b'}' | b']' => depth = depth.saturating_sub(1),
            b'-' if depth == 0 && i + 1 < len && bytes[i + 1] == b'>' => {
                let domain = s[..i].trim();
                let codomain = s[i + 2..].trim();
                if !domain.is_empty() && !codomain.is_empty() {
                    return Some((domain, codomain));
                }
            }
            _ => {
                // Check for Unicode arrow →.
                if depth == 0 && s[i..].starts_with('\u{2192}') {
                    let domain = s[..i].trim();
                    let arrow_len = '\u{2192}'.len_utf8();
                    let codomain = s[i + arrow_len..].trim();
                    if !domain.is_empty() && !codomain.is_empty() {
                        return Some((domain, codomain));
                    }
                }
            }
        }
        i += 1;
    }
    None
}
