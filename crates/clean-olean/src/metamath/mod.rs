// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metamath `.mm` parsing and structural translation.
//!
//! This module parses Metamath source files, resolves active frames
//! (floating/essential hypotheses and distinct-variable conditions), verifies
//! proof scripts structurally, and emits clean kernel `Declaration` values that
//! encode assertions and proof trees as kernel `Expr`s.

mod ast;
mod encode;
mod kernel_verify;
mod parser;
mod resolve;
mod translate;

#[cfg(test)]
mod tests;

pub use ast::{
    CompressedProof, Database, EssentialHyp, Formula, Proof, ResolvedAssertion, ResolvedDatabase,
    ResolvedStatement, Statement,
};
pub use kernel_verify::{
    kernel_verify_database, kernel_verify_database_prefix,
    kernel_verify_database_prefix_count_only, kernel_verify_database_prefix_streaming,
    kernel_verify_pass1_types, kernel_verify_theorem, kernel_verify_two_pass_range,
    KernelVerifyOutcome, KernelVerifyReport,
};
pub use parser::{parse_database, parse_database_file};
pub use resolve::resolve_database;
pub use translate::translate_database;

use thiserror::Error;

/// Result type for Metamath parsing and translation.
pub type MetamathResult<T> = Result<T, MetamathError>;

/// Errors that can arise while handling Metamath source.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MetamathError {
    #[error("unexpected end of input while parsing {context}")]
    UnexpectedEof { context: &'static str },
    #[error("unexpected token: expected {expected}, found {found}")]
    UnexpectedToken {
        expected: &'static str,
        found: String,
    },
    #[error("unterminated comment")]
    UnterminatedComment,
    #[error("include directive requires a source file base directory: {0}")]
    IncludeWithoutBase(String),
    #[error("cyclic include detected at {0}")]
    CyclicInclude(String),
    #[error("invalid statement: {0}")]
    InvalidStatement(String),
    #[error("duplicate label: {0}")]
    DuplicateLabel(String),
    #[error("unknown proof label {label} in theorem {theorem}")]
    UnknownLabel { theorem: String, label: String },
    #[error("proof stack underflow applying {label} in theorem {theorem}")]
    StackUnderflow { theorem: String, label: String },
    #[error("type mismatch in theorem {theorem} at {label}: expected {expected}, got {actual}")]
    TypeMismatch {
        theorem: String,
        label: String,
        expected: String,
        actual: String,
    },
    #[error("essential hypothesis mismatch in theorem {theorem} at {label}")]
    EssentialMismatch { theorem: String, label: String },
    #[error("distinct-variable violation in theorem {theorem} at {label}: {left} vs {right}")]
    DisjointViolation {
        theorem: String,
        label: String,
        left: String,
        right: String,
    },
    #[error("saved proof step {index} out of range in theorem {theorem}")]
    InvalidSavedStep { theorem: String, index: usize },
    #[error("invalid compressed proof in theorem {theorem}: {message}")]
    InvalidCompressedProof { theorem: String, message: String },
    #[error("final proof result mismatch in theorem {theorem}")]
    FinalResultMismatch { theorem: String },
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}
