// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle theorem importer via `.yxml` export format.
//!
//! Provides parsing of Isabelle's YXML export format and AST types for
//! representing Isabelle types, terms, theorems, and theory exports.
//!
//! # Usage
//!
//! ```text
//! use clean_mathverse::hol::isabelle::{parse_theory_export, IsaTheoryExport};
//!
//! let yxml_bytes: &[u8] = /* ... */;
//! let export: IsaTheoryExport = parse_theory_export(yxml_bytes)?;
//! ```

pub mod importer;
pub mod translate;
pub mod types;
pub mod yxml_parser;

#[cfg(test)]
mod tests;

// Re-export primary types for convenience.
pub use importer::{
    IsaImportedConstant, IsabelleImportConfig, IsabelleImportConfigBuilder, IsabelleImportError,
    IsabelleImportResult, IsabelleImporter, IsabelleStatistics,
};
pub use translate::{IsabelleTranslator, TranslateError, TranslatedTheorem};
pub use types::{IsaTerm, IsaTheorem, IsaTheoryExport, IsaType, ProofStatus};
pub use yxml_parser::{
    parse_term, parse_theorem, parse_theory_export, parse_type, parse_yxml, parse_yxml_tree,
    YxmlError, YxmlTree,
};
