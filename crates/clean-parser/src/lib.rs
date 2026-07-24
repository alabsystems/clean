// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean Parser
//!
//! Lean 4 recursive-descent parser producing surface AST with source spans.

use serde::{Deserialize, Serialize};

pub mod grammar;
pub mod interpolation;
pub mod lexer;
pub mod surface;
pub mod surface_tactic;
pub mod surface_tactic_types;
pub mod tactic_patterns;

#[cfg(test)]
mod lean4_compat;
#[cfg(test)]
mod lean4_features;
#[cfg(test)]
mod putnam_bench_compat;
#[cfg(test)]
mod syntax_boundary_regressions;

pub use grammar::Parser;
pub use interpolation::InterpolationPart;
pub use lexer::InterpolatedStringKind;
pub use surface::{
    AesopAttr, AesopBuilder, AesopIndexMode, AesopPhase, Attribute, AttributeCommandAttr,
    ConvEnterArg, DeclModifiers, DeclScope, DecreasingBy, DoCatchClause, DoElem, DoLetExprKind,
    DoMatchArm, LevelExpr, MacroArm, NotationItem, NotationKind, OpenPath, OpenRename,
    PrecedenceLevel, Projection, QAntiquotContent, QQuotationKind, SimpPriority, Span, SurfaceArg,
    SurfaceBinder, SurfaceBinderInfo, SurfaceCalcJustification, SurfaceCalcStep, SurfaceCtor,
    SurfaceDecl, SurfaceExpr, SurfaceField, SurfaceFieldAssign, SurfaceInductionAlt, SurfaceLit,
    SurfaceMatchArm, SurfacePattern, SurfaceRwRule, SurfaceTactic, SurfaceTacticLocation,
    SyntaxPatternItem, TacticMatchArm, TerminationBy, TerminationHints, TerminationKind,
    UniverseExpr, Visibility, WhereLocalDef,
};
pub use tactic_patterns::{TacticArgPattern, TacticPatterns};

/// Common imports for parser users.
pub mod prelude {
    pub use crate::{parse_decl, parse_expr, parse_file, ParseError, ParseReport, Parser};
    pub use crate::{Span, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr};
}

/// Parse a string into a surface expression
///
/// # REQUIRES
/// - `input` is valid UTF-8 (enforced by Rust's `&str` type)
///
/// # ENSURES
/// - On success, returns `SurfaceExpr` representing the parsed expression
/// - On success, all spans in the returned AST are within `0..input.len()`
/// - On error, returns `ParseError` with location information
/// - Parsing is deterministic: same input always produces same result
///
/// # Errors
///
/// Returns a `ParseError` if the input is not a valid expression.
pub fn parse_expr(input: &str) -> Result<SurfaceExpr, ParseError> {
    Parser::parse_expr(input)
}

/// Parse a string into a surface declaration
///
/// # REQUIRES
/// - `input` is valid UTF-8
///
/// # ENSURES
/// - On success, returns `SurfaceDecl` (Def, Theorem, Axiom, etc.)
/// - On success, declaration name is non-empty for named declarations
/// - On error, returns `ParseError` with location information
///
/// # Errors
///
/// Returns a `ParseError` if the input is not a valid declaration.
pub fn parse_decl(input: &str) -> Result<SurfaceDecl, ParseError> {
    Parser::parse_decl(input)
}

/// Parse the body of a syntax quotation (`` `(...) ``) into a surface
/// expression, handling antiquotations and infix-operator desugaring.
///
/// See [`Parser::parse_quotation_body`] for the full contract. `content` is the
/// raw text captured by the lexer, still including the outer delimiter pair.
///
/// # Errors
///
/// Returns a `ParseError` if the quotation body is malformed.
pub fn parse_quotation_body(content: &str) -> Result<SurfaceExpr, ParseError> {
    Parser::parse_quotation_body(content)
}

/// Parse a file containing multiple declarations
///
/// # REQUIRES
/// - `input` is valid UTF-8
///
/// # ENSURES
/// - On success, returns `Vec<SurfaceDecl>` in source order
/// - Empty input returns empty vector
/// - Each declaration satisfies `parse_decl` postconditions
///
/// # Errors
///
/// Returns a `ParseError` if the input contains invalid declarations.
pub fn parse_file(input: &str) -> Result<Vec<SurfaceDecl>, ParseError> {
    Parser::parse_file(input)
}

/// Parse a file and return declarations plus parser recovery diagnostics.
///
/// This is a non-breaking companion to [`parse_file`]. File-level parser
/// recovery still returns `RawDecl` placeholders in the declaration stream,
/// while this API exposes where recovery started and resumed.
pub fn parse_file_with_diagnostics(input: &str) -> Result<ParseReport, ParseError> {
    Parser::parse_file_with_diagnostics(input)
}

/// Parse a string into a surface expression with tactic-pattern-aware parsing.
///
/// Like [`parse_expr`], but accepts a [`TacticPatterns`] table so the parser
/// can use argument-pattern-aware parsing for `SurfaceTactic::Named` tactics.
///
/// # Errors
///
/// Returns a `ParseError` if the input is not a valid expression.
pub fn parse_expr_with_tactics(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<SurfaceExpr, ParseError> {
    Parser::parse_expr_with_tactics(input, patterns)
}

/// Like [`parse_expr_with_tactics`], but rejects trailing tokens after
/// the expression. Use for RPC endpoints where partial parsing is unsound.
pub fn parse_expr_with_tactics_exact(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<SurfaceExpr, ParseError> {
    Parser::parse_expr_with_tactics_exact(input, patterns)
}

/// Like [`parse_decl`], but with tactic-pattern-aware parsing.
pub fn parse_decl_with_tactics(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<SurfaceDecl, ParseError> {
    Parser::parse_decl_with_tactics(input, patterns)
}

/// Like [`parse_decl_with_tactics`], but rejects trailing tokens. Part of #2553.
pub fn parse_decl_with_tactics_exact(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<SurfaceDecl, ParseError> {
    Parser::parse_decl_with_tactics_exact(input, patterns)
}

/// Parse a file containing multiple declarations with tactic-pattern-aware parsing.
///
/// Like [`parse_file`], but accepts a [`TacticPatterns`] table so the parser
/// can use argument-pattern-aware parsing for `SurfaceTactic::Named` tactics.
///
/// # Errors
///
/// Returns a `ParseError` if the input contains invalid declarations.
pub fn parse_file_with_tactics(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<Vec<SurfaceDecl>, ParseError> {
    Parser::parse_file_with_tactics(input, patterns)
}

/// Strictly parse a file with tactic-pattern-aware parsing and return an
/// authoritative byte offset when parsing fails.
///
/// The `col` field of [`ParseError::UnexpectedToken`] predates the parser's
/// byte-span model and is not a uniform coordinate: older error
/// sites use either a line-relative byte column or an absolute byte offset.
/// Source-mapped consumers must use this API instead of guessing which form a
/// particular error carried. Unlike the compatibility file parser, this entry
/// point also rejects every parser-recovery placeholder: a source-mapped proof
/// consumer must never mistake a recovered `RawDecl` for accepted source.
pub fn parse_file_with_tactics_located(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<Vec<SurfaceDecl>, LocatedParseError> {
    Parser::parse_file_with_tactics_located(input, patterns)
}

/// Parse a file with tactic-pattern-aware parsing and recovery diagnostics.
pub fn parse_file_with_tactics_diagnostics(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<ParseReport, ParseError> {
    Parser::parse_file_with_tactics_diagnostics(input, patterns)
}

/// Source location for parser recovery diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ParseSourceLocation {
    /// 1-based line number.
    pub line: usize,
    /// 0-based token column.
    pub column: usize,
    /// Byte offset.
    pub byte: usize,
}

/// Severity for parser recovery diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ParserDiagnosticSeverity {
    /// Parsing failed and recovery was required.
    Error,
    /// Parsing recovered from a non-fatal condition.
    Warning,
    /// Informational parser context.
    Info,
}

/// A parser recovery event designed for automation agents.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ParserRecoveryDiagnostic {
    /// Stable diagnostic code.
    pub code: String,
    /// Diagnostic severity.
    pub severity: ParserDiagnosticSeverity,
    /// Indentation-sensitive construct being parsed, when known.
    pub construct: String,
    /// Start location of the indentation-sensitive block, when known.
    pub block_start: Option<ParseSourceLocation>,
    /// Location where parsing failed or recovery started.
    pub recovery_start: ParseSourceLocation,
    /// Location where parsing resumed.
    pub recovered_at: ParseSourceLocation,
    /// Token text/kind at the resume point.
    pub resumed_token: String,
    /// Expected block indentation column.
    pub expected_indent: Option<u32>,
    /// Actual token indentation column.
    pub actual_indent: Option<u32>,
    /// Original parser error message.
    pub message: String,
}

/// File parse result with recovery diagnostics.
#[derive(Debug, Clone)]
pub struct ParseReport {
    /// Parsed declarations, including `RawDecl` placeholders for recovered regions.
    pub decls: Vec<SurfaceDecl>,
    /// Recovery events observed while parsing.
    pub diagnostics: Vec<ParserRecoveryDiagnostic>,
}

/// Errors from parsing Lean 4 source code into a surface AST.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ParseError {
    /// Parser encountered a token that is not valid in the current context.
    #[error("Unexpected token at {line}:{col}: {message}")]
    UnexpectedToken {
        line: usize,
        col: usize,
        message: String,
    },
    /// Input ended before a complete syntax construct was parsed.
    #[error("Unexpected end of input")]
    UnexpectedEof,
    /// Numeric literal exceeds the maximum representable value.
    #[error("Numeric literal {value} is too large (max {max})")]
    NumericOverflow { value: u64, max: u64 },
    /// Expression nesting exceeds the maximum depth (#2556).
    #[error("Expression nesting too deep at {col} (depth {depth}, max {max})")]
    NestingTooDeep { col: usize, depth: u32, max: u32 },
    /// Universe level offset `u + n` exceeds Lean's `maxUniverseOffset`.
    ///
    /// Lean 4 caps a syntactic universe offset (`Sort (u + n)` / `Type (u + n)`)
    /// at `maxUniverseOffset = 32` (`src/Lean/Elab/Level.lean` `checkUniverseOffset`,
    /// `unless n <= max`). Clean previously desugared `+ n` into `n` nested
    /// `Succ` nodes with no bound, so a pathological `Sort (u + 9999)` either
    /// over-accepted (33..depth-limit) or blew the macro-expansion depth. Reject
    /// `n > 32` here, matching Lean's loud rejection.
    #[error("universe level offset `{offset}` exceeds maximum offset `{max}`")]
    UniverseOffsetTooLarge { offset: u64, max: u64 },
}

/// Lean's `maxUniverseOffset` (default 32): the largest syntactic universe
/// offset accepted in `Sort (u + n)` / `Type (u + n)`
/// (`src/Lean/Elab/Level.lean`).
pub(crate) const MAX_UNIVERSE_OFFSET: u64 = 32;

/// A parser failure paired with an authoritative absolute UTF-8 byte offset:
/// the current token for hard failures or the start of a rejected recovery
/// region.
#[derive(Debug, thiserror::Error)]
#[error("{error}")]
pub struct LocatedParseError {
    /// Absolute UTF-8 byte offset, clamped to the input length.
    pub byte_offset: usize,
    /// The original structured parser error.
    #[source]
    pub error: ParseError,
}

/// Domain-prefixed alias for collision-free imports.
///
/// Use `ParserParseError` when importing from multiple crates with `ParseError` types.
pub type ParserParseError = ParseError;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn located_file_error_reports_absolute_utf8_byte_offset() {
        let source = "def café : Nat := 0\ndef bad : Nat := )\n";
        let patterns = TacticPatterns::default();
        let failure = parse_file_with_tactics_located(source, &patterns)
            .expect_err("the unmatched close delimiter must be rejected");
        assert_eq!(failure.byte_offset, source.find("def bad").unwrap());
    }

    #[test]
    fn test_parse_identity() {
        let expr = parse_expr("fun x => x").unwrap();
        assert!(matches!(expr, SurfaceExpr::Lambda(_, _, _)));
    }

    #[test]
    fn test_parse_def() {
        let decl = parse_decl("def id (x : Type) := x").unwrap();
        match decl {
            SurfaceDecl::Def { name, .. } => assert_eq!(name, "id"),
            _ => panic!("expected Def"),
        }
    }

    /// Head identifier of a binary `App` (the operator that was lowered to).
    fn binop_head(expr: &SurfaceExpr) -> &str {
        match expr {
            SurfaceExpr::App(_, head, args) => {
                assert_eq!(args.len(), 2, "expected a binary application: {expr:?}");
                match head.as_ref() {
                    SurfaceExpr::Ident(_, name) => name.as_str(),
                    other => panic!("expected ident head, got {other:?}"),
                }
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_bitwise_operators_lower_to_h_ops() {
        assert_eq!(binop_head(&parse_expr("a &&& b").unwrap()), "HAnd.hAnd");
        assert_eq!(binop_head(&parse_expr("a ||| b").unwrap()), "HOr.hOr");
        assert_eq!(binop_head(&parse_expr("a ^^^ b").unwrap()), "HXor.hXor");
        assert_eq!(
            binop_head(&parse_expr("a <<< b").unwrap()),
            "HShiftLeft.hShiftLeft"
        );
        assert_eq!(
            binop_head(&parse_expr("a >>> b").unwrap()),
            "HShiftRight.hShiftRight"
        );
        // Bool `&&`/`||` lower to `and`/`or`.
        assert_eq!(binop_head(&parse_expr("a && b").unwrap()), "and");
        assert_eq!(binop_head(&parse_expr("a || b").unwrap()), "or");
    }

    #[test]
    fn test_parse_bitwise_precedence() {
        // `+`(65) binds tighter than `&&&`(60): `a &&& b + c` = `a &&& (b + c)`.
        let e = parse_expr("a &&& b + c").unwrap();
        assert_eq!(binop_head(&e), "HAnd.hAnd");
        if let SurfaceExpr::App(_, _, args) = &e {
            assert_eq!(binop_head(&args[1].expr), "HAdd.hAdd");
        }

        // `&&&`(60) binds tighter than `=`(50): `a = b &&& c` = `a = (b &&& c)`.
        let e = parse_expr("a = b &&& c").unwrap();
        assert_eq!(binop_head(&e), "Eq");
        if let SurfaceExpr::App(_, _, args) = &e {
            assert_eq!(binop_head(&args[1].expr), "HAnd.hAnd");
        }

        // `&&&`(60) binds tighter than `|||`(55): `a ||| b &&& c` = `a ||| (b &&& c)`.
        let e = parse_expr("a ||| b &&& c").unwrap();
        assert_eq!(binop_head(&e), "HOr.hOr");
        if let SurfaceExpr::App(_, _, args) = &e {
            assert_eq!(binop_head(&args[1].expr), "HAnd.hAnd");
        }

        // `<<<`(75) binds tighter than `+`(65): `a + b <<< c` = `a + (b <<< c)`.
        let e = parse_expr("a + b <<< c").unwrap();
        assert_eq!(binop_head(&e), "HAdd.hAdd");
        if let SurfaceExpr::App(_, _, args) = &e {
            assert_eq!(binop_head(&args[1].expr), "HShiftLeft.hShiftLeft");
        }
    }

    #[test]
    fn test_parse_arrow_chain() {
        let expr = parse_expr("A -> B -> C").unwrap();
        // Right associative: A -> (B -> C)
        match expr {
            SurfaceExpr::Arrow(_, left, right) => {
                assert!(matches!(*left, SurfaceExpr::Ident(_, _)));
                assert!(matches!(*right, SurfaceExpr::Arrow(_, _, _)));
            }
            _ => panic!("expected Arrow"),
        }
    }

    #[test]
    fn test_parse_projection_index() {
        let expr = parse_expr("x.1").unwrap();
        match expr {
            SurfaceExpr::Proj(_, base, Projection::Index(1)) => {
                assert!(matches!(*base, SurfaceExpr::Ident(_, ref name) if name == "x"));
            }
            other => panic!("expected projection, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_projection_named_after_app() {
        let expr = parse_expr("(f x).field").unwrap();
        match expr {
            SurfaceExpr::Proj(_, base, Projection::Named(ref field)) => {
                assert_eq!(field, "field");
                let inner = match base.as_ref() {
                    SurfaceExpr::Paren(_, inner) => inner.as_ref(),
                    other => other,
                };
                assert!(
                    matches!(inner, SurfaceExpr::App(_, _, _)),
                    "expected application base, got {inner:?}"
                );
            }
            other => panic!("expected named projection, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_syntax_quote_preserved() {
        let expr = parse_expr("`(x)").unwrap();
        match expr {
            SurfaceExpr::SyntaxQuote(_, content) => assert!(content.contains('x')),
            other => panic!("expected syntax quote, got {other:?}"),
        }
    }

    // =========================================================================
    // Aesop attribute parsing tests
    //
    // These tests verify that @[aesop] attributes produce Attribute::Aesop
    // variants with correct phase, builder, and priority.
    // =========================================================================

    /// Test @[aesop safe] produces correct Aesop variant
    #[test]
    fn test_parse_aesop_safe_attribute() {
        // Test basic parsing - declaration name should be correct
        let decl = parse_decl("@[aesop safe] theorem my_thm : True := trivial").unwrap();
        match decl {
            SurfaceDecl::Theorem { name, .. } => assert_eq!(name, "my_thm"),
            _ => panic!("expected Theorem"),
        }
    }

    /// Test @[aesop unsafe 30%] parses correctly
    #[test]
    fn test_parse_aesop_unsafe_attribute_with_priority() {
        let decl = parse_decl("@[aesop unsafe 30%] def my_def := 42").unwrap();
        match decl {
            SurfaceDecl::Def { name, .. } => assert_eq!(name, "my_def"),
            _ => panic!("expected Def"),
        }
    }

    /// Test @[aesop safe apply] parses correctly
    #[test]
    fn test_parse_aesop_safe_apply_attribute() {
        let decl = parse_decl("@[aesop safe apply] theorem intro_rule : True := trivial").unwrap();
        match decl {
            SurfaceDecl::Theorem { name, .. } => assert_eq!(name, "intro_rule"),
            _ => panic!("expected Theorem"),
        }
    }

    /// Test @[aesop norm simp] parses correctly
    #[test]
    fn test_parse_aesop_norm_simp_attribute() {
        let decl = parse_decl("@[aesop norm simp] theorem simp_rule : True := trivial").unwrap();
        match decl {
            SurfaceDecl::Theorem { name, .. } => assert_eq!(name, "simp_rule"),
            _ => panic!("expected Theorem"),
        }
    }

    /// Test that grammar produces Aesop variant (not Unknown)
    ///
    /// This test directly exercises the attribute parser to verify it returns
    /// Attribute::Aesop, not Attribute::Unknown.
    #[test]
    fn test_aesop_attribute_produces_aesop_variant() {
        use crate::grammar::Parser;

        // Parse just the attribute part to verify correct variant
        let mut parser = Parser::new("@[aesop safe] x");
        let attrs = parser.attributes().unwrap();
        assert_eq!(attrs.len(), 1);
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert_eq!(attr.phase, AesopPhase::Safe);
                assert_eq!(attr.builder, AesopBuilder::Apply); // default
                assert_eq!(attr.priority, None);
            }
            Attribute::Unknown(name) => {
                panic!("Expected Attribute::Aesop, got Attribute::Unknown({name})")
            }
            _ => panic!("Expected Attribute::Aesop"),
        }
    }

    /// Test unsafe attribute with priority parses to correct values
    #[test]
    fn test_aesop_unsafe_priority_values() {
        use crate::grammar::Parser;

        let mut parser = Parser::new("@[aesop unsafe 30%] x");
        let attrs = parser.attributes().unwrap();
        assert_eq!(attrs.len(), 1);
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert_eq!(attr.phase, AesopPhase::Unsafe);
                assert_eq!(attr.builder, AesopBuilder::Apply);
                assert_eq!(attr.priority, Some(30));
            }
            _ => panic!("Expected Attribute::Aesop"),
        }
    }

    /// Test norm phase with simp builder
    #[test]
    fn test_aesop_norm_simp_values() {
        use crate::grammar::Parser;

        let mut parser = Parser::new("@[aesop norm simp] x");
        let attrs = parser.attributes().unwrap();
        assert_eq!(attrs.len(), 1);
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert_eq!(attr.phase, AesopPhase::Norm);
                assert_eq!(attr.builder, AesopBuilder::Simp);
            }
            _ => panic!("Expected Attribute::Aesop"),
        }
    }

    /// Test all builder types
    #[test]
    fn test_aesop_all_builders() {
        use crate::grammar::Parser;

        let cases = [
            ("@[aesop safe apply] x", AesopBuilder::Apply),
            ("@[aesop safe cases] x", AesopBuilder::Cases),
            ("@[aesop safe constructors] x", AesopBuilder::Constructors),
            ("@[aesop safe destruct] x", AesopBuilder::Destruct),
            ("@[aesop safe forward] x", AesopBuilder::Forward),
            ("@[aesop norm simp] x", AesopBuilder::Simp),
            ("@[aesop safe tactic] x", AesopBuilder::Tactic),
            ("@[aesop safe unfold] x", AesopBuilder::Unfold),
        ];

        for (input, expected_builder) in cases {
            let mut parser = Parser::new(input);
            let attrs = parser.attributes().unwrap();
            match &attrs[0] {
                Attribute::Aesop(attr) => {
                    assert_eq!(attr.builder, expected_builder, "Failed for input: {input}");
                }
                _ => panic!("Expected Attribute::Aesop for input: {input}"),
            }
        }
    }

    /// Test parsing rule set names in aesop attribute
    #[test]
    fn test_aesop_rule_set_single() {
        use crate::grammar::Parser;

        let mut parser = Parser::new("@[aesop safe apply, Measurable] x");
        let attrs = parser.attributes().unwrap();
        assert_eq!(attrs.len(), 1);
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert_eq!(attr.phase, AesopPhase::Safe);
                assert_eq!(attr.builder, AesopBuilder::Apply);
                assert_eq!(attr.rule_sets, vec!["Measurable"]);
            }
            _ => panic!("Expected Attribute::Aesop"),
        }
    }

    /// Test parsing multiple rule sets
    #[test]
    fn test_aesop_rule_set_multiple() {
        use crate::grammar::Parser;

        let mut parser = Parser::new("@[aesop safe, Measurable, Continuous] x");
        let attrs = parser.attributes().unwrap();
        assert_eq!(attrs.len(), 1);
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert_eq!(attr.phase, AesopPhase::Safe);
                assert_eq!(attr.builder, AesopBuilder::Apply); // default
                assert_eq!(attr.rule_sets, vec!["Measurable", "Continuous"]);
            }
            _ => panic!("Expected Attribute::Aesop"),
        }
    }

    /// Test that no rule sets results in empty vec
    #[test]
    fn test_aesop_no_rule_sets() {
        use crate::grammar::Parser;

        let mut parser = Parser::new("@[aesop safe apply] x");
        let attrs = parser.attributes().unwrap();
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert!(attr.rule_sets.is_empty());
            }
            _ => panic!("Expected Attribute::Aesop"),
        }
    }

    /// Test unsafe with priority and rule set
    #[test]
    fn test_aesop_unsafe_priority_with_rule_set() {
        use crate::grammar::Parser;

        let mut parser = Parser::new("@[aesop unsafe 50% apply, GCongr] x");
        let attrs = parser.attributes().unwrap();
        match &attrs[0] {
            Attribute::Aesop(attr) => {
                assert_eq!(attr.phase, AesopPhase::Unsafe);
                assert_eq!(attr.priority, Some(50));
                assert_eq!(attr.builder, AesopBuilder::Apply);
                assert_eq!(attr.rule_sets, vec!["GCongr"]);
            }
            _ => panic!("Expected Attribute::Aesop"),
        }
    }

    /// Test parsing declare_aesop_rule_sets command
    #[test]
    fn test_parse_declare_aesop_rule_sets() {
        let decl = parse_decl("declare_aesop_rule_sets [Measurable, Continuous]").unwrap();
        match decl {
            SurfaceDecl::DeclareAesopRuleSets { names, .. } => {
                assert_eq!(names, vec!["Measurable", "Continuous"]);
            }
            _ => panic!("expected DeclareAesopRuleSets, got {:?}", decl),
        }
    }

    /// Test parsing declare_aesop_rule_sets with single name
    #[test]
    fn test_parse_declare_aesop_rule_sets_single() {
        let decl = parse_decl("declare_aesop_rule_sets [GCongr]").unwrap();
        match decl {
            SurfaceDecl::DeclareAesopRuleSets { names, .. } => {
                assert_eq!(names, vec!["GCongr"]);
            }
            _ => panic!("expected DeclareAesopRuleSets"),
        }
    }
}
