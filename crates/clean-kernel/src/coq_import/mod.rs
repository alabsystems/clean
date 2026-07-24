// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq import scaffolding built around SerAPI-style S-expressions.
//!
//! This module provides:
//! - a small Coq kernel IR (`types`)
//! - a normalized S-expression parser for declarations (`parser`)
//! - translation from Coq `Constr` terms into clean kernel `Expr` (`translate`)

mod import_batch;
mod import_collect;
mod parser;
mod stdlib;
mod translate;
mod types;
mod verify;

#[cfg(test)]
mod tests;

pub use import_batch::{BatchImportSource, CoqBatchImporter, ImportStats};
pub use import_collect::{
    add_to_environment, add_to_environment_into, collect_declarations, collect_declarations_with,
    import_and_verify, AddResult, CollectedDeclarations,
};
pub use parser::{parse_constr, parse_declaration, parse_declarations, parse_sexp, Sexp};
pub use stdlib::{CoqStdlibTypeMapping, COQ_STDLIB_TYPE_MAPPINGS};
pub use translate::{
    translate_constant_decl, translate_global_decl, translate_inductive_decl, translate_term,
    translate_term_with_context, InductiveMapping, TranslatedGlobalDecl, TranslationContext,
};
pub use types::{
    Binder, CaseBranch, CaseInfo, CastKind, CoFixTerm, ConstantDecl, ConstantDeclKind, Constr,
    ConstructRef, ConstructorDecl, CoqBinderKind, CoqName, CoqSort, FixBody, FixTerm, GlobalDecl,
    InductiveBody, InductiveKind, InductiveRef, MutualInductiveDecl, ProjectionRef,
    UniverseInstance, UniverseLevel,
};
pub use verify::{verify_declarations, verify_declarations_into, VerifyResult, VerifyStats};

use thiserror::Error;

/// Result type shared by Coq import parsing and translation.
pub type CoqImportResult<T> = Result<T, CoqImportError>;

/// Errors raised while parsing or translating Coq artifacts.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CoqImportError {
    #[error("unexpected end of input while parsing {context}")]
    UnexpectedEof { context: &'static str },
    #[error("unexpected token `{token}` while parsing {context}")]
    UnexpectedToken {
        context: &'static str,
        token: String,
    },
    #[error("expected atom while parsing {context}")]
    ExpectedAtom { context: &'static str },
    #[error("expected list while parsing {context}")]
    ExpectedList { context: &'static str },
    #[error("missing field `{field}` while parsing {context}")]
    MissingField {
        context: &'static str,
        field: &'static str,
    },
    #[error("invalid numeric literal `{value}` while parsing {context}")]
    InvalidNumber {
        context: &'static str,
        value: String,
    },
    #[error("invalid boolean literal `{value}` while parsing {context}")]
    InvalidBoolean {
        context: &'static str,
        value: String,
    },
    #[error("invalid declaration kind `{kind}`")]
    InvalidDeclarationKind { kind: String },
    #[error("invalid inductive kind `{kind}`")]
    InvalidInductiveKind { kind: String },
    #[error("invalid sort `{sort}`")]
    InvalidSort { sort: String },
    #[error("invalid binder info `{info}`")]
    InvalidBinderInfo { info: String },
    #[error("invalid cast kind `{kind}`")]
    InvalidCastKind { kind: String },
    #[error("unsupported JSON wrapper for Coq declarations")]
    UnsupportedJsonShape,
    #[error("JSON parse error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("invalid de Bruijn index {index}; Coq Rel indices are 1-based")]
    InvalidRelIndex { index: u32 },
    #[error("unbound de Bruijn index {index} at binder depth {depth}")]
    UnboundRel { index: u32, depth: usize },
    #[error("application nodes must carry at least one argument")]
    EmptyApplication,
    #[error("max universe must contain at least one level")]
    EmptyMaxUniverse,
    #[error("recursive block index {index} is out of bounds for {len} bodies")]
    InvalidFixIndex { index: usize, len: usize },
    #[error("Coq node `{node}` is not yet lowered to a Lean kernel Expr")]
    UnsupportedNode { node: &'static str },
}
