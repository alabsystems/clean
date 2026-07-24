// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C Parser using tree-sitter-c
//!
//! This module provides parsing of C source code into clean-c-sem AST structures.
//! It uses tree-sitter-c for incremental, error-tolerant parsing.
//!
//! ## Features
//!
//! - Parse C source files into `FuncDef`, `CStmt`, `CExpr`, `CType`
//! - Handle standard C11 constructs
//! - Extract ACSL-style comments for specifications (/* @requires ... */)
//! - Error reporting with source locations
//!
//! ## Usage
//!
//! ```
//! use clean_c_sem::parser::CParser;
//!
//! let mut parser = CParser::new();
//! let code = r#"
//!     int abs(int x) {
//!         if (x < 0) return -x;
//!         return x;
//!     }
//! "#;
//!
//! let result = parser.parse_function(code).expect("parse failed");
//! assert_eq!(&result.name, "abs");
//! ```

mod common;
mod expr;
mod expr_ops;
mod function;
mod spec;
mod statements;
mod types;

#[cfg(test)]
mod tests;

pub use spec::parse_acsl_spec;

use crate::stmt::FuncDef;
use crate::verified::VerifiedFunction;
use thiserror::Error;
use tree_sitter::{Node, Parser, Tree};

/// Parse errors for C source code
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
}

/// Result type for parsing operations
pub type ParseResult<T> = Result<T, ParseError>;

trait NodeExt<'tree> {
    fn child_at(&self, index: usize) -> Option<Node<'tree>>;
}

impl<'tree> NodeExt<'tree> for Node<'tree> {
    fn child_at(&self, index: usize) -> Option<Node<'tree>> {
        self.child(index as u32)
    }
}

/// C Parser
///
/// Wraps tree-sitter-c for parsing C source code.
pub struct CParser {
    parser: Parser,
}

impl Default for CParser {
    fn default() -> Self {
        Self::new()
    }
}

impl CParser {
    /// Create a new C parser
    pub fn new() -> Self {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_c::LANGUAGE.into())
            .expect("Error loading C grammar");
        Self { parser }
    }

    /// Parse a C source string
    pub fn parse(&mut self, source: &str) -> ParseResult<Tree> {
        self.parser.parse(source, None).ok_or(ParseError::NoTree)
    }

    /// Parse a complete translation unit (multiple functions)
    pub fn parse_translation_unit(&mut self, source: &str) -> ParseResult<Vec<FuncDef>> {
        let tree = self.parse(source)?;
        let root = tree.root_node();
        let mut functions = Vec::new();

        for i in 0..root.child_count() {
            if let Some(child) = root.child_at(i) {
                if child.kind() == "function_definition" {
                    functions.push(self.parse_function_node(child, source)?);
                }
            }
        }

        Ok(functions)
    }

    /// Parse a complete translation unit and attach ACSL specs when present
    pub fn parse_translation_unit_with_specs(
        &mut self,
        source: &str,
    ) -> ParseResult<Vec<VerifiedFunction>> {
        let tree = self.parse(source)?;
        let root = tree.root_node();
        let mut functions = Vec::new();

        for i in 0..root.child_count() {
            if let Some(child) = root.child_at(i) {
                if child.kind() == "function_definition" {
                    let func = self.parse_function_node(child, source)?;
                    let spec = self.extract_func_spec(child, source).unwrap_or_default();
                    functions.push(VerifiedFunction {
                        name: func.name.clone(),
                        description: format!("Parsed function {}", func.name),
                        func,
                        spec,
                        sep_spec: None,
                    });
                }
            }
        }

        Ok(functions)
    }

    /// Parse a single function along with an optional ACSL spec
    pub fn parse_function_with_spec(&mut self, source: &str) -> ParseResult<VerifiedFunction> {
        let tree = self.parse(source)?;
        let root = tree.root_node();

        for i in 0..root.child_count() {
            if let Some(child) = root.child_at(i) {
                if child.kind() == "function_definition" {
                    let func = self.parse_function_node(child, source)?;
                    let spec = self.extract_func_spec(child, source).unwrap_or_default();
                    return Ok(VerifiedFunction {
                        name: func.name.clone(),
                        description: format!("Parsed function {}", func.name),
                        func,
                        spec,
                        sep_spec: None,
                    });
                }
            }
        }

        Err(ParseError::SyntaxError {
            line: 0,
            column: 0,
            message: "No function definition found".to_string(),
        })
    }

    /// Parse a single function definition from source
    pub fn parse_function(&mut self, source: &str) -> ParseResult<FuncDef> {
        let tree = self.parse(source)?;
        let root = tree.root_node();

        // Find function_definition node
        for i in 0..root.child_count() {
            if let Some(child) = root.child_at(i) {
                if child.kind() == "function_definition" {
                    return self.parse_function_node(child, source);
                }
            }
        }

        Err(ParseError::SyntaxError {
            line: 0,
            column: 0,
            message: "No function definition found".to_string(),
        })
    }
}
