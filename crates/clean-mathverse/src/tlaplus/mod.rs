// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ (Temporal Logic of Actions) importer.
//!
//! Parses `.tla` TLA+ specification files and `.qnt` Quint files and
//! translates them into clean kernel expressions via a shallow embedding:
//!
//! - Constants and variables → axiomatized `TLA.Value` / `TLA.Var` types
//! - Operators → function-typed constants
//! - Theorems/lemmas → `Prop`-valued constants
//! - Temporal operators → axiomatized TLA temporal logic primitives
//!
//! # Modules
//!
//! - [`types`] — AST types for TLA+ modules, declarations, and expressions
//! - [`parser`] — TLA+ and Quint file parsers
//! - [`translate`] — TLA+ → clean kernel Expr translation
//! - [`importer`] — Batch import with statistics

pub mod importer;
pub mod parser;
pub mod translate;
pub mod types;

// Re-export primary entry points.
pub use importer::{TlaPlusImportError, TlaPlusImportResult, TlaPlusImporter};
pub use parser::{parse_quint, parse_tlaplus, parse_tlaplus_file, TlaParseError};
pub use translate::{
    translate_module, translate_tla_expr, TlaConstantKind, TlaImportedConstant, TlaTranslateError,
    TlaTranslationContext,
};
pub use types::{TlaDecl, TlaDeclKind, TlaExpr, TlaModule};
