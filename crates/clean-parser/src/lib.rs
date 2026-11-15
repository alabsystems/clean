// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean Parser
//!
//! Lean 4 recursive-descent parser producing surface AST with source spans.

use serde::{Deserialize, Serialize};

pub mod grammar;
pub mod interpolation;
pub mod lean_keywords;
pub mod lexer;
pub mod notation_seed;
pub mod origins;
#[cfg(test)]
mod parse_world;
pub mod surface;
pub mod surface_tactic;
pub mod surface_tactic_types;
pub mod tactic_patterns;

#[cfg(test)]
mod include_omit_tests;
#[cfg(test)]
mod keyword_headed_instance_name_tests;
#[cfg(test)]
mod lean4_compat;
#[cfg(test)]
mod lean4_features;
#[cfg(test)]
mod putnam_bench_compat;
#[cfg(test)]
mod reduce_command_tests;
#[cfg(test)]
mod syntax_boundary_regressions;

pub use clean_kernel::lean_world::{LeanWorld, UnknownLeanWorld};
pub use grammar::Parser;
pub use interpolation::InterpolationPart;
pub use lexer::InterpolatedStringKind;
pub use notation_seed::{NotationSeed, SeededNotation};
pub use surface::{
    anonymous_constructor_head, is_anonymous_constructor_head, is_type_ascription_without_type,
    AesopAttr, AesopBuilder, AesopIndexMode, AesopPhase, Attribute, AttributeCommandAttr,
    CodataBody, ConvEnterArg, DeclModifiers, DeclScope, DecreasingBy, DoCatchClause, DoElem,
    DoLetExprKind, DoMatchArm, GrindAttrKind, GuardMsgsOrdering, GuardMsgsSeverity,
    GuardMsgsSpecElt, GuardMsgsWhitespace, LevelExpr, MacroArm, NotationItem, NotationKind,
    OpenPath, OpenRename, PrecedenceLevel, Projection, QAntiquotContent, QQuotationKind, SimpPhase,
    SimpPriority, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceCalcJustification,
    SurfaceCalcStep, SurfaceCtor, SurfaceDecl, SurfaceExpr, SurfaceField, SurfaceFieldAssign,
    SurfaceInductionAlt, SurfaceLit, SurfaceMatchArm, SurfacePattern, SurfaceRCasesTarget,
    SurfaceRwRule, SurfaceSimpArg, SurfaceTactic, SurfaceTacticLocation, SyntaxPatternItem,
    TacticMatchArm, TerminationBy, TerminationHints, TerminationKind, UniverseExpr, Visibility,
    WhereLocalDef, TYPE_ASCRIPTION_WITHOUT_TYPE,
};
pub use surface::{
    instantiate_notation_template, instantiate_tactic_template,
    instantiate_unhygienic_notation_template, mark_template_free_references,
    template_free_reference_spellings, NameComponentSyntax, SurfaceName, SurfaceNameError,
    TemplateOrigin, TemplateRefusal, TemplateScope, TemplateSiteId,
};
pub use tactic_patterns::{TacticArgPattern, TacticPatterns, GRIND_ONLY_MARKER};

/// Common imports for parser users.
pub mod prelude {
    pub use crate::{
        parse_decl, parse_decl_exact, parse_expr, parse_file, ParseError, ParseReport, Parser,
    };
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

/// Parse a declaration prefix. Use [`parse_decl_exact`] to require complete input.
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

/// Parse exactly one surface declaration, allowing trailing whitespace and comments.
///
/// # Errors
///
/// Returns a `ParseError` if parsing fails or tokens remain after the declaration.
pub fn parse_decl_exact(input: &str) -> Result<SurfaceDecl, ParseError> {
    Parser::parse_decl_exact(input)
}

/// Parse one exact structural source identifier, including quoted components.
/// This is not the kernel's lossy dotted-display parser and rejects trailing input.
pub fn parse_name(input: &str) -> Result<SurfaceName, ParseError> {
    Parser::parse_name(input)
}

/// Parse the body of a syntax quotation (`` `(...) ``) into a surface
/// expression, handling antiquotations and infix-operator desugaring.
///
/// See `Parser::parse_quotation_body` for the full contract. `content` is the
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

/// Parse a file in an explicitly selected known Lean source world.
///
/// # Errors
/// Returns the first parse refusal, with the same recovery policy as [`parse_file`].
pub fn parse_file_in_world(input: &str, world: LeanWorld) -> Result<Vec<SurfaceDecl>, ParseError> {
    Parser::parse_file_in_world(input, world)
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
///
/// # Errors
///
/// Returns a `ParseError` if the input cannot be parsed at file level.
pub fn parse_file_with_tactics_diagnostics(
    input: &str,
    patterns: &TacticPatterns,
) -> Result<ParseReport, ParseError> {
    Parser::parse_file_with_tactics_diagnostics(input, patterns)
}

/// Parse a file with tactic-pattern-aware parsing, recovery diagnostics, and
/// the notation registry pre-populated from the file's imports.
///
/// See [`notation_seed`] for how a seed is built. An empty seed makes this
/// identical to [`parse_file_with_tactics_diagnostics`].
///
/// # Errors
///
/// Returns a `ParseError` if the input cannot be parsed at file level.
pub fn parse_file_seeded(
    input: &str,
    patterns: &TacticPatterns,
    seed: &NotationSeed,
) -> Result<ParseReport, ParseError> {
    Parser::parse_file_seeded(input, patterns, seed)
}

/// The notation-seeded file parser in a selected source world. Default APIs
/// still use [`LeanWorld::ORACLE`].
///
/// # Errors
/// Returns a `ParseError` if file parsing fails.
pub fn parse_file_seeded_in_world(
    input: &str,
    patterns: &TacticPatterns,
    seed: &NotationSeed,
    world: LeanWorld,
) -> Result<ParseReport, ParseError> {
    Parser::parse_file_seeded_in_world(input, patterns, seed, world)
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
    /// The tactic token whose grammar failed, when the recovery happened inside
    /// a `by` block.
    ///
    /// Measurement integrity (T0, `docs/plans/TACTICS_TO_100_2026-07-29.md`
    /// §RC-Q): a tactic-block recovery degrades the declaration to a synthetic
    /// sorry. Without this field nothing in the whole pipeline names the tactic
    /// that did nothing, so any coverage script keyed on `UnknownTactic`
    /// under-reports the real gap. `None` for non-tactic recoveries.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tactic: Option<String>,
}

/// File parse result with recovery diagnostics.
#[derive(Debug, Clone)]
pub struct ParseReport {
    /// Parsed declarations, including `RawDecl` placeholders for recovered regions.
    pub decls: Vec<SurfaceDecl>,
    /// Recovery events observed while parsing.
    pub diagnostics: Vec<ParserRecoveryDiagnostic>,
    /// The file's header: whether it is a module, and its header imports.
    /// The header's imports are ALSO in `decls`, as the `SurfaceDecl::Import`
    /// nodes they always were, in the same order.
    pub header: FileHeader,
}

/// A Lean file's header as pinned Lean v4.30.0-rc2 reads it
/// (`Lean.Parser.Module.header`: `module`? `prelude`? `import`*), recorded as
/// `Lean.Elab.HeaderSyntax.toModuleHeader` records it (plan item
/// `formats-module-spelling-refusals`).
///
/// Lean's implicit `Init` imports (`HeaderSyntax.imports`, `includeInit`) are
/// not listed: these are the imports the file writes. A file Clean refuses for
/// its header (a `public`, `meta` or `all` import without `module`, `public
/// import all`, or a doc comment inside an import) has no report. A header
/// import whose module name does not parse otherwise (`import all` with no
/// name after it) is recovered as a `RawDecl` placeholder in `decls` and is
/// not listed, and pinned Lean refuses that file too. The header ends there,
/// as Lean's header parser stops at its first error: the imports after it are
/// not listed either. When `decls` holds no placeholder, a recorded header is
/// one pinned Lean reads without a header error.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct FileHeader {
    /// Explicit `prelude`: do not supply implicit Init or builtin declarations.
    pub is_prelude: bool,
    /// The file begins with `module` (`HeaderSyntax.isModule`): it is a
    /// module-system module.
    pub is_module: bool,
    /// The header's imports, in source order.
    pub imports: Vec<ImportSpec>,
}

/// One header import: Lean's `Lean.Import` (`Lean/Setup.lean`), filled as
/// `HeaderSyntax.imports` fills it from `public? meta? import all? <name>`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ImportSpec {
    /// The imported module.
    pub module: SurfaceName,
    /// Lean's `isExported := publicTk.isSome || moduleTk.isNone`: the import
    /// is re-exported to the file's importers. Every import of a file that is
    /// not a module is; in a module only a `public import` is.
    pub is_exported: bool,
    /// `meta import`: the module's definitions are imported for compile-time
    /// execution too.
    pub is_meta: bool,
    /// `import all`: the module's private data is imported as well.
    pub import_all: bool,
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
    ///
    /// `file()` refuses the whole file on it instead of recovering at the next
    /// command (`ParseError::refuses_file`; a `namespace`/`section` body
    /// recovers it like any other error). The exception is a file whose header
    /// recovered an import whose module name does not parse: Lean's first
    /// message is that header error and pinned Lean reads no command after it,
    /// so `file()` recovers this error as a `RawDecl` too (`module` / `import
    /// all` / `def big (X : Sort (u + 9999)) : Nat := 0`).
    #[error("universe level offset `{offset}` exceeds maximum offset `{max}`")]
    UniverseOffsetTooLarge { offset: u64, max: u64 },
    /// A use of a notation whose template Clean refuses, or an operand the
    /// template cannot take where it stands (`TemplateRefusal`). The use is
    /// refused; it is never read with another meaning.
    #[error("Notation refused at {line}:{col}: {message}")]
    NotationRefused {
        line: usize,
        col: usize,
        message: String,
    },
    /// A module-system spelling pinned Lean refuses (plan item
    /// `formats-module-spelling-refusals`): a `public`, `meta` or `all`
    /// header import in a file with no `module` header, `public import all`,
    /// or a modifier Lean's grammar does not take in front of `import`,
    /// `section` or `variable` (`private import`, `private section`,
    /// `public variable` before v4.36.0-rc1, ...), a doc comment among those
    /// modifiers or inside a header import (`public /-- d -/ import`, `import
    /// /-! d -/ X`). `line` (1-based) and `col` (0-based, in codepoints) are
    /// Lean's position and `message` its words, so the error prints exactly as
    /// `lean` prints it after the file name (the default stream: no end
    /// position is carried).
    /// Like [`ParseError::UniverseOffsetTooLarge`] it refuses the whole file,
    /// in a `namespace`/`section` body too, with the same exception: after
    /// the header recovered an import whose module name does not parse,
    /// `file()` and the block body recover it as a `RawDecl` like any other
    /// error, since Lean's first message is that header error and pinned
    /// Lean reads no command after it.
    #[error("{line}:{col}: error: {message}")]
    ModuleSyntaxRefused {
        line: usize,
        col: usize,
        message: String,
    },
}

impl ParseError {
    /// Whether the file parser refuses the whole file on this error instead
    /// of recovering at the next command, unless the file header already
    /// recovered an import (whose error is then the file's first): `file()`
    /// then recovers both variants (`Parser::header_recovered`).
    pub(crate) fn refuses_file(&self) -> bool {
        matches!(
            self,
            Self::UniverseOffsetTooLarge { .. } | Self::ModuleSyntaxRefused { .. }
        )
    }
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

/// Ordinary parser output alongside independently fallible observations.
#[derive(Debug)]
pub struct ParsedWithOrigins<T> {
    pub parsed: T,
    pub origins: Result<SourceOrigins, OriginCaptureError>,
}

/// Observation failure, never a semantic parser refusal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("source-origin capture unavailable: {0}")]
pub struct OriginCaptureError(pub(crate) &'static str);

/// An opaque, capture-owned source node identity.
#[derive(Debug, Clone)]
pub struct OriginId {
    owner: std::sync::Arc<()>,
    index: usize,
}

impl PartialEq for OriginId {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.owner, &other.owner) && self.index == other.index
    }
}

impl Eq for OriginId {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OriginKind {
    DeclarationName,
    Identifier,
    Literal,
    Hole,
    NamedHole,
    Parentheses,
    Application,
}

/// Edges describe the actual written expression, not elaborated arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OriginChildRole {
    Parenthesized,
    ApplicationHead,
    ApplicationArgument(usize),
}

#[derive(Debug, Clone)]
enum OriginCore {
    DeclarationName(SurfaceName),
    Ident(SurfaceName),
    Lit(SurfaceLit),
    Hole,
    NamedHole(SurfaceName),
    Paren(usize),
    App {
        head: usize,
        args: Vec<(Span, usize)>,
    },
}

/// A genuine source span, with the old semantic AST span retained separately.
#[derive(Debug, Clone)]
pub struct OriginNode {
    span: Span,
    ast_span: Span,
    core: OriginCore,
}

impl OriginNode {
    #[must_use]
    pub fn span(&self) -> Span {
        self.span
    }

    #[must_use]
    pub fn kind(&self) -> OriginKind {
        match self.core {
            OriginCore::DeclarationName(_) => OriginKind::DeclarationName,
            OriginCore::Ident(_) => OriginKind::Identifier,
            OriginCore::Lit(_) => OriginKind::Literal,
            OriginCore::Hole => OriginKind::Hole,
            OriginCore::NamedHole(_) => OriginKind::NamedHole,
            OriginCore::Paren(_) => OriginKind::Parentheses,
            OriginCore::App { .. } => OriginKind::Application,
        }
    }

    fn edges(&self) -> Vec<(OriginChildRole, usize)> {
        match &self.core {
            OriginCore::Paren(inner) => vec![(OriginChildRole::Parenthesized, *inner)],
            OriginCore::App { head, args } => {
                std::iter::once((OriginChildRole::ApplicationHead, *head))
                    .chain(
                        args.iter()
                            .enumerate()
                            .map(|(i, (_, node))| (OriginChildRole::ApplicationArgument(i), *node)),
                    )
                    .collect()
            }
            _ => Vec::new(),
        }
    }
}

/// Missing syntax and unsupported syntax are deliberately distinct.
#[derive(Debug, Clone)]
pub enum OriginAvailability {
    NotPresent,
    Unavailable,
    Located(OriginId),
}

#[derive(Debug, Clone)]
pub enum OriginRoot {
    Expression(OriginAvailability),
    Declaration {
        name: OriginId,
        ty: OriginAvailability,
        value: OriginAvailability,
    },
}

/// Immutable observations reachable from successful returned declarations or
/// the returned expression. Discarded parse attempts are not exposed.
#[derive(Debug, Clone)]
pub struct SourceOrigins {
    source: std::sync::Arc<str>,
    owner: std::sync::Arc<()>,
    nodes: Vec<OriginNode>,
    roots: Vec<OriginRoot>,
}

impl SourceOrigins {
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    #[must_use]
    pub fn roots(&self) -> &[OriginRoot] {
        &self.roots
    }

    #[must_use]
    pub fn node(&self, id: &OriginId) -> Option<&OriginNode> {
        std::sync::Arc::ptr_eq(&self.owner, &id.owner)
            .then(|| self.nodes.get(id.index))
            .flatten()
    }

    #[must_use]
    pub fn text(&self, id: &OriginId) -> Option<&str> {
        let span = self.node(id)?.span;
        self.source.get(span.start..span.end)
    }

    #[must_use]
    pub fn children(&self, id: &OriginId) -> Option<Vec<(OriginChildRole, OriginId)>> {
        Some(
            self.node(id)?
                .edges()
                .into_iter()
                .map(|(role, index)| {
                    (
                        role,
                        OriginId {
                            owner: self.owner.clone(),
                            index,
                        },
                    )
                })
                .collect(),
        )
    }

    /// Transfer an existing origin only on exact supported surface-tree
    /// agreement, including AST/argument spans and all name hygiene metadata.
    /// A clone is a valid pass-through. Rewritten/generated syntax requires a
    /// separate explicit provenance contract, which this API does not supply.
    #[must_use]
    pub fn pass_through(&self, id: &OriginId, expr: &SurfaceExpr) -> Option<OriginId> {
        self.node(id)?;
        origins::agrees(&self.nodes, id.index, expr).then(|| id.clone())
    }
}

impl SurfaceName {
    /// Compare spelling, hygiene marks and global-reference policy for
    /// source-origin pass-through, preserving semantic equality and hashing.
    #[must_use]
    pub fn same_origin_metadata(&self, other: &Self) -> bool {
        self.same_origin_metadata_for_capture(other)
    }
}

impl Parser {
    /// Parse with original-source observations for the documented core subset.
    /// The parse verdict and semantic AST use the ordinary parser unchanged.
    pub fn parse_expr_with_origins(
        input: &str,
    ) -> Result<ParsedWithOrigins<SurfaceExpr>, ParseError> {
        Self::parse_expr_with_origin_capture(input)
    }

    /// File companion with actual declaration-name token origins for
    /// def/theorem/axiom/opaque and core type/value origins when available.
    /// Recovery invalidates the sidecar, while preserving the ordinary AST.
    pub fn parse_file_with_origins(
        input: &str,
    ) -> Result<ParsedWithOrigins<Vec<SurfaceDecl>>, ParseError> {
        Self::parse_file_with_origin_capture(input)
    }
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
