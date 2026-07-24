// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TPTP (Thousands of Problems for Theorem Provers) importer.
//!
//! Parses TPTP `.p` and `.ax` files (FOF, CNF, TFF, THF) and translates
//! them into clean kernel expressions via a shallow embedding:
//!
//! - `TPTP.individual` as the domain of individuals (Sort 0)
//! - Predicates as functions into Prop
//! - Functions as functions on individuals
//! - Standard logical connectives mapped to kernel Pi, And, Or, etc.
//!
//! # Modules
//!
//! - [`types`] — AST types for TPTP formulas, roles, and type expressions
//! - [`parser`] — TPTP file parser (handles comments, includes, all sub-languages)
//! - [`translate`] — TPTP → clean kernel Expr translation
//! - [`importer`] — Batch import with statistics

pub mod importer;
pub mod parser;
pub mod translate;
pub mod types;

// Re-export primary entry points.
pub use importer::{TptpImportError, TptpImportResult, TptpImporter};
pub use parser::{parse_tptp, parse_tptp_file, TptpParseError};
pub use translate::{
    translate_tptp_formula, translate_tptp_term, translate_tptp_term_fresh, TptpConstantKind,
    TptpImportedConstant, TptpTranslateError, TptpTranslationContext,
};
pub use types::{TptpFile, TptpFormula, TptpInclude, TptpLanguage, TptpRole, TptpTerm, TptpType};
