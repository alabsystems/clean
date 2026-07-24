// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq `.vo` import scaffolding and Gallina term translation.

mod ast;
mod parser;
mod translate;

#[cfg(test)]
mod tests;

pub use ast::{
    Binder, CaseBranch, CaseInfo, CastKind, CoFixTerm, Constr, ConstructRef, CoqBinderKind,
    CoqName, CoqSort, FixBody, FixTerm, InductiveRef, UniverseInstance, UniverseLevel,
};
pub use parser::{
    parse_vo, parse_vo_file, VoFile, VoHeader, VoSection, VoSectionKind, OCAML_MARSHAL_HEADER_LEN,
    OCAML_MARSHAL_MAGIC,
};
pub use translate::{translate_term, translate_term_with_context, TranslationContext};

use thiserror::Error;

/// Result type for Coq import operations.
pub type CoqImportResult<T> = Result<T, CoqImportError>;

/// Errors raised while parsing or translating Coq artifacts.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CoqImportError {
    #[error("unexpected end of input while parsing {context}")]
    UnexpectedEof { context: &'static str },
    #[error(
        "invalid OCaml marshal magic in .vo file: expected 0x{expected:08x}, found 0x{actual:08x}"
    )]
    InvalidMarshalMagic { expected: u32, actual: u32 },
    #[error(
        "marshal payload truncated: header declares {declared} bytes, but only {available} bytes remain"
    )]
    TruncatedMarshalPayload { declared: usize, available: usize },
    #[error("invalid de Bruijn index {index}; Coq Rel indices are 1-based")]
    InvalidRelIndex { index: u32 },
    #[error("unbound de Bruijn index {index} at binder depth {depth}")]
    UnboundRel { index: u32, depth: usize },
    #[error("application nodes must carry at least one argument")]
    EmptyApplication,
    #[error("max universe must contain at least one level")]
    EmptyMaxUniverse,
    #[error("Coq sort `{sort}` is not representable as a Lean kernel Expr")]
    UnsupportedSort { sort: &'static str },
    #[error("case translation requires an eliminator name")]
    MissingCaseEliminator,
    #[error("Coq node `{node}` is not yet lowered to Lean kernel Expr")]
    UnsupportedNode { node: &'static str },
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}
