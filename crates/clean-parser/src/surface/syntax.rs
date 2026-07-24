// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro and notation syntax types for surface declarations.

use super::{Span, SurfaceExpr};

// ============================================================================
// Macro system types
// ============================================================================

/// An item in a syntax pattern
///
/// Syntax patterns consist of:
/// - Literal strings: `"if"`, `"+"`, `"=>"`
/// - Identifiers with category: `cond:term`, `body:tactic`
/// - Optional items: `("," expr)?`
/// - Repetitions: `expr,*` or `expr,+`
/// - Syntax category references: `term`, `tactic`
#[derive(Debug, Clone)]
pub enum SyntaxPatternItem {
    /// Literal string: `"if"`, `"then"`, `"+"`
    Literal(String),
    /// Variable binding with optional category: `x`, `cond:term`, `body:tactic`
    Variable {
        name: String,
        /// The syntax category (e.g., "term", "tactic"), if specified
        category: Option<String>,
    },
    /// Syntax category reference: `term`, `tactic`, `command`
    CategoryRef(String),
    /// Optional group: `(pattern)?`
    Optional(Vec<SyntaxPatternItem>),
    /// Repetition with separator: `pattern,*` or `pattern,+`
    Repetition {
        pattern: Vec<SyntaxPatternItem>,
        separator: Option<String>,
        at_least_one: bool,
    },
    /// Precedence specifier: `:50` or `:max`
    Precedence(PrecedenceLevel),
}

/// Precedence level for syntax declarations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrecedenceLevel {
    /// Numeric precedence level (0-1024)
    Num(u32),
    /// Maximum precedence (for function application)
    Max,
    /// Minimum precedence (for low-priority operators)
    Min,
    /// Argument precedence (for function arguments)
    Arg,
    /// Lead precedence (for leading tokens)
    Lead,
}

/// A single arm in a `macro_rules` declaration
#[derive(Debug, Clone)]
pub struct MacroArm {
    pub span: Span,
    /// The pattern to match (typically a syntax quotation)
    pub pattern: Box<SurfaceExpr>,
    /// The expansion template (typically a syntax quotation)
    pub expansion: Box<SurfaceExpr>,
}

/// Kind of notation declaration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotationKind {
    /// Left-associative infix: `infixl`
    Infixl,
    /// Right-associative infix: `infixr`
    Infixr,
    /// Non-associative infix: `infix`. Parses a single `a op b` application;
    /// chaining `a op b op c` is a parse error (Lean rejects it).
    Infix,
    /// Prefix operator: `prefix`
    Prefix,
    /// Postfix operator: `postfix`
    Postfix,
    /// General notation: `notation`
    Notation,
}

/// An item in a notation pattern
#[derive(Debug, Clone)]
pub enum NotationItem {
    /// Literal token: `"+"`, `"⟨"`, `","`
    Literal(String),
    /// Variable to be filled: `a`, `b`
    Variable(String),
}
