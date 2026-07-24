// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB2 (Satisfiability Modulo Theories) importer.
//!
//! Parses `.smt2` files in the standard SMT-LIB2 S-expression format and
//! translates them into clean kernel expressions via a shallow embedding:
//!
//! - SMT sorts → clean type constants (`SMT.Int`, `SMT.Real`, `SMT.BitVec`, etc.)
//! - Declarations → axiomatized constants with function types
//! - Assertions → propositions (Prop-valued expressions)
//! - Quantifiers → Pi/Exists in the kernel
//!
//! # Modules
//!
//! - [`types`] — AST types for SMT-LIB2 sorts, terms, commands, and scripts
//! - [`parser`] — S-expression parser for `.smt2` files
//! - [`translate`] — SMT-LIB2 → clean kernel Expr translation
//! - [`importer`] — Batch import with statistics

pub mod importer;
pub mod parser;
pub mod translate;
pub mod types;

// Re-export primary entry points.
pub use importer::{SmtlibImportError, SmtlibImportResult, SmtlibImporter};
pub use parser::{parse_smtlib, parse_smtlib_file, SmtParseError};
pub use translate::{
    translate_script, translate_sort, translate_term, SmtConstantKind, SmtImportedConstant,
    SmtTranslateError, SmtTranslationContext,
};
pub use types::{SmtCommand, SmtScript, SmtSort, SmtTerm};
