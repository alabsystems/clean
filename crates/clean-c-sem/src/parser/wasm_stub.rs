// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! wasm32 stand-in for the C parser.
//!
//! The native parser wraps tree-sitter-c, whose build script compiles C with
//! a host sysroot that wasm32-wasip1 builds do not have, so tree-sitter is a
//! native-only dependency. This stub keeps the public `parser` surface
//! (`CParser`, `ParseError`, `ParseResult`) compiling on wasm; every parse
//! entry point returns [`ParseError::NativeOnly`].

use crate::stmt::FuncDef;
use crate::verified::VerifiedFunction;
use thiserror::Error;

/// Parse errors for C source code (wasm mirror of the native enum, plus
/// [`ParseError::NativeOnly`], the only variant this stub ever returns).
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ParseError {
    /// Tree-sitter failed to initialize the C grammar parser
    #[error("Tree-sitter parser initialization failed")]
    ParserInit,

    /// Parser ran but produced no syntax tree (usually indicates severe syntax error)
    #[error("Parse failed: no tree produced")]
    NoTree,

    /// C syntax error at a specific location
    #[error("Syntax error at {line}:{column}: {message}")]
    SyntaxError {
        /// Line number (1-indexed)
        line: usize,
        /// Column number (1-indexed)
        column: usize,
        /// Description of the syntax error
        message: String,
    },

    /// C construct not supported by the semantic model
    #[error("Unsupported construct at {line}:{column}: {kind}")]
    Unsupported {
        /// Line number (1-indexed)
        line: usize,
        /// Column number (1-indexed)
        column: usize,
        /// Name of the unsupported construct (e.g., "goto", "inline asm")
        kind: String,
    },

    /// Required AST field missing in tree-sitter node
    #[error("Missing required field: {field} in {node_kind}")]
    MissingField {
        /// Name of the missing field
        field: String,
        /// Type of the parent node
        node_kind: String,
    },

    /// Type checking failed during parse
    #[error("Type error: {message}")]
    TypeError {
        /// Description of the type error
        message: String,
    },

    /// Integer literal could not be parsed
    #[error("Invalid integer literal: {value}")]
    InvalidInt {
        /// The malformed literal string
        value: String,
    },

    /// Float literal could not be parsed
    #[error("Invalid float literal: {value}")]
    InvalidFloat {
        /// The malformed literal string
        value: String,
    },

    /// C parsing requires the native tree-sitter backend
    #[error("C parsing is native-only: tree-sitter is unavailable on wasm")]
    NativeOnly,
}

/// Result type for parsing operations
pub type ParseResult<T> = Result<T, ParseError>;

/// C Parser (wasm stub: every parse returns [`ParseError::NativeOnly`])
pub struct CParser {}

impl Default for CParser {
    fn default() -> Self {
        Self::new()
    }
}

impl CParser {
    /// Create a new C parser
    pub fn new() -> Self {
        Self {}
    }

    /// Parse all function definitions in a C translation unit.
    ///
    /// pub(crate): the native twin is `pub`, but no crate outside clean-c-sem
    /// calls this on the wasm surface (clean-cli's C verbs go through
    /// [`CParser::parse_translation_unit_with_specs`]); stub internals carry
    /// no wider visibility than their callers require. Allowed dead: kept for
    /// shape parity with the native `CParser`.
    #[allow(dead_code)]
    pub(crate) fn parse_translation_unit(&mut self, _source: &str) -> ParseResult<Vec<FuncDef>> {
        Err(ParseError::NativeOnly)
    }

    /// Parse all functions with their ACSL specifications
    pub fn parse_translation_unit_with_specs(
        &mut self,
        _source: &str,
    ) -> ParseResult<Vec<VerifiedFunction>> {
        Err(ParseError::NativeOnly)
    }

    /// Parse a single function with its ACSL specification.
    /// pub(crate) + allowed dead: see [`CParser::parse_translation_unit`].
    #[allow(dead_code)]
    pub(crate) fn parse_function_with_spec(
        &mut self,
        _source: &str,
    ) -> ParseResult<VerifiedFunction> {
        Err(ParseError::NativeOnly)
    }

    /// Parse a single C function definition.
    /// pub(crate) + allowed dead: see [`CParser::parse_translation_unit`].
    #[allow(dead_code)]
    pub(crate) fn parse_function(&mut self, _source: &str) -> ParseResult<FuncDef> {
        Err(ParseError::NativeOnly)
    }
}
