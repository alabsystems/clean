// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursive descent parser for Lean 4 syntax
//!
//! Parses tokens into a surface syntax AST.

use crate::lexer::{Lexer, Token, TokenKind};
use crate::surface::{DocComment, SurfaceDecl, SurfaceExpr};
use crate::tactic_patterns::{TacticArgPattern, TacticPatterns};
use crate::{LocatedParseError, ParseError, ParseReport, ParserRecoveryDiagnostic};

#[derive(Debug, Clone)]
pub(super) struct IndentContext {
    pub(super) construct: String,
    pub(super) line: usize,
    pub(super) column: u32,
    pub(super) byte: usize,
}

#[derive(Debug, Clone)]
pub(super) struct PendingRecoveryDiagnostic {
    pub(super) code: String,
    pub(super) construct: String,
    pub(super) block_start: Option<crate::ParseSourceLocation>,
    pub(super) recovery_start: crate::ParseSourceLocation,
    pub(super) expected_indent: Option<u32>,
    pub(super) actual_indent: Option<u32>,
    pub(super) message: String,
    /// Tactic token whose grammar failed (T0 measurement integrity); see
    /// [`crate::ParserRecoveryDiagnostic::tactic`].
    pub(super) tactic: Option<String>,
}

/// Display symbol for a binary operator token that has NO rule in the
/// hand-written precedence chain and would therefore silently truncate an
/// expression if left unconsumed at the top level. Returns `None` for every
/// other token (separators, delimiters, atoms) so the base parser stays lenient
/// about ordinary trailing input. See [`Parser::reject_truncating_operator`].
fn unhandled_binary_operator_symbol(kind: &TokenKind) -> Option<&'static str> {
    match kind {
        // `>>` — HAndThen.hAndThen (`seq_expr` handles it; this is a defensive
        // fallback for a `>>` left stranded by an associativity conflict).
        TokenKind::Seq => Some(">>"),
        // `$` — low-precedence application. `seq_expr`/`pipe_expr` consume the
        // real operator; a stranded `$` (e.g. the no-whitespace `f $x`
        // pseudo-antiquotation in plain term position) is rejected here.
        TokenKind::Dollar => Some("$"),
        // `$>` / `<$` — Functor.mapConst siblings of the handled `<$>`.
        TokenKind::DollarArrow => Some("$>"),
        TokenKind::LeftDollar => Some("<$"),
        // `×'` (anonymous PSigma) only exists with a typed binder-group left
        // (`(x : T) ×' b`, handled in `prod_expr`); anywhere else it is a gap.
        TokenKind::TimesPrime => Some("×'"),
        // `<;>` is a TACTIC sequencing combinator, not a term operator; Lean
        // rejects it in term position. Without this, `parse_expr` would return
        // just the left tactic-name expression and silently drop the rest.
        TokenKind::SeqFocusOp => Some("<;>"),
        _ => None,
    }
}

// Types used only in tests (imported via super::*)
#[cfg(test)]
use crate::surface::{
    ConvEnterArg, DoElem, DoLetExprKind, NotationKind, Projection, QAntiquotContent,
    QQuotationKind, SurfaceBinderInfo, SurfaceCalcJustification, SurfaceLit, SurfacePattern,
    SurfaceTactic, SurfaceTacticLocation, TerminationKind, UniverseExpr,
};

/// Parser state
///
/// Recursive descent parser for Lean 4 syntax. The parser consumes tokens
/// produced by the lexer and builds a surface syntax AST.
pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    /// Lean declaration doc comments (`/-- ... -/`) captured by the lexer while
    /// skipping trivia, in source order. The token stream is unchanged; these
    /// are associated with the declarations that follow them by
    /// [`Parser::parse_file_with_docs`]. Empty for inputs without doc comments.
    doc_comments: Vec<DocComment>,
    stop_app_at_newline_lparen: bool,
    stop_app_at_newline_outer_indent: bool,
    /// When true, `atom_expr` treats `do` as an identifier instead of a keyword.
    /// Used by `parse_do_for` to prevent the collection expression from consuming
    /// the `do` keyword that delimits the loop body.
    forbid_do: bool,
    /// When true, `catch` and `finally` identifiers are not considered atom starts.
    /// Used by `parse_do_try` to prevent the try body expression parser from
    /// consuming `catch`/`finally` as function application arguments on single-line
    /// `do try expr catch e => expr` forms. See #2969.
    stop_at_catch_finally: bool,
    /// When true, identifiers followed by `:=` (or binders then `:=`) are not
    /// considered atom starts. Used by `parse_where_local_defs` to prevent the
    /// expression parser for one where-clause body from consuming the next
    /// where-clause definition's name as a function argument.
    in_where_block: bool,
    /// When true, a `by` tactic block is not consumed as an application
    /// argument. Used by `show_body` so that `show t by tac` parses the type
    /// `t` and leaves `by` for the `show` parser to dispatch into a tactic
    /// block, matching Lean 4's `Term.show` precedence (the `by` term has lower
    /// precedence than an application argument). Without this, `show True by
    /// trivial` would parse the type as the application `True (by trivial)`.
    stop_app_at_by: bool,
    /// When true, the `generalizing` and `using` identifiers are not consumed as
    /// application arguments. Used by `parse_tactic_cases_induction` so the
    /// major premise `e` in `induction e using r generalizing x with …` stops at
    /// the `using` / `generalizing` clause keywords instead of greedily parsing
    /// `e using r generalizing x` as a function application. Both are ordinary
    /// identifier tokens to the lexer, so without this the target parse absorbs
    /// them (and `r`/`x`) as arguments, yielding `TacticFailed(UnknownIdent)`.
    stop_app_at_generalizing_using: bool,
    /// When true, identifiers immediately followed by `:=` are not considered
    /// atom starts. Used by `struct_field_value_expr` so that full-expression
    /// parsing of a struct-literal field value stops at the next field's name
    /// rather than consuming it as an application argument. Without this, the
    /// comma-less Lean 4 style `{ x := 1 y := 2 }` would parse the value of `x`
    /// as `1 y` (application) and then fail to find `}`. See #3517.
    in_struct_field: bool,
    /// When true, identifiers immediately followed by `:=` are not considered
    /// atom starts. Used by `instance_field_value_expr` so that full-expression
    /// parsing of an instance `where`-field value stops at the next field's
    /// name rather than consuming it as an application argument. This matters
    /// when the value is a `fun .. => body` lambda: the lambda body is parsed
    /// via the general `expr` grammar (not the boundary-aware
    /// `instance_field_*_expr` helpers), so without this flag
    /// `render := fun _ => Nat.succ Nat.zero` followed by `tag := 3` parses the
    /// body as `fun _ => Nat.succ Nat.zero tag` and drops the `tag` field.
    /// Mirrors `in_struct_field` for `{ x := 1 y := 2 }`. See B53.
    in_instance_field: bool,
    /// When true, the application/operator spine of a structure or class field
    /// TYPE stops at the next field — a newline-leading identifier immediately
    /// followed by `:`. Set by `field_type_expr`, which parses field types with
    /// the full operator grammar (so dependent fields like `h : n = n` and
    /// `property : 0 < val` parse) rather than the old app+arrow-only
    /// sub-grammar. The newline requirement keeps a same-line `(f x : T)`
    /// ascription / `(x y : T)` binder group inside the type intact (those are
    /// never a field boundary), mirroring Lean's layout-sensitive
    /// `structExplicitBinder` grouping in `src/Lean/Elab/Structure.lean`. See
    /// brick B11.
    in_field_type: bool,
    /// Stack of block-opening reference columns for indentation-sensitive parsing.
    /// Each entry is the column of the **first child element** in the block (not the keyword).
    /// Matches Lean 4's `withPosition` + `sepBy1Indent` pattern.
    indent_stack: Vec<u32>,
    /// Metadata parallel to `indent_stack`, used only for recovery diagnostics.
    indent_context_stack: Vec<IndentContext>,
    /// Parser recovery diagnostics accumulated by non-breaking report APIs.
    recovery_diagnostics: Vec<ParserRecoveryDiagnostic>,
    /// Indentation diagnostics waiting for the skip/resume location.
    pending_recovery_diagnostics: Vec<PendingRecoveryDiagnostic>,
    /// Outer-to-inner chain of tactic tokens whose parse is still in progress.
    ///
    /// Measurement integrity (T0, `docs/plans/TACTICS_TO_100_2026-07-29.md`
    /// §RC-Q): when a tactic's argument grammar fails, `by_body` recovers the
    /// whole block to a `SyntheticSorry` and the *only* thing the user ever saw
    /// was `declaration uses synthetic sorry` — with nothing naming the tactic
    /// that failed to parse. `Parser::tactic` pushes on entry and pops on
    /// success, so on failure this holds the full nesting chain, outermost
    /// first. Purely diagnostic: it never changes what parses.
    tactic_chain: Vec<String>,
    /// Whole source text, kept so a diagnostic can quote a token's exact
    /// spelling (`module`, `:=`, `·`) instead of a `TokenKind` debug name.
    /// Diagnostics only.
    source: String,
    /// Tactic argument patterns for registry-known tactics.
    /// When present, `parse_ident_tactic`'s `Named` fallback uses these patterns
    /// for argument-aware parsing instead of generic expression-list parsing.
    tactic_patterns: Option<TacticPatterns>,
    /// Current expression nesting depth. Incremented on each `expr()` call,
    /// decremented on return. Prevents stack overflow on deeply nested input
    /// like `[[[[...` or `((((...)`. See #2556.
    expr_depth: u32,
    /// User-declared fixed-arity operators (`infixl`/`infixr`/`prefix`/`postfix`)
    /// registered while parsing a file, so later expressions can use them.
    /// Empty for single-shot `parse_expr`/`parse_decl` and whenever a file
    /// declares no operators — in which case `custom_op_expr` is a transparent
    /// pass-through to `app_expr`.
    custom_operators: Vec<custom_notation::CustomOperator>,
    /// User-declared CLOSED multi-hole `notation` patterns (leading + trailing
    /// literal, e.g. `notation:max "⟪" a ", " b "⟫" => …`). Registered and
    /// consumed alongside `custom_operators`; see `custom_notation.rs`.
    custom_mixfixes: Vec<custom_notation::CustomMixfix>,
    /// The Lean precedence of the operand slot currently being parsed — the
    /// context a user-declared operator must bind at least as tightly as to be
    /// consumed. Set by every builtin right-operand parse in the operator
    /// chain (`with_custom_min_prec`), reset to `CUSTOM_PREC_FLOOR` at each
    /// full-expression entry (`expr()`), and only read when the file declared
    /// custom notation. See `custom_notation.rs` (B100).
    custom_min_prec: u32,
    /// Guards harvested from PARENTHESIZED bounded quantifier binders
    /// (`∀ (x ∈ s), p`, `∃ (n > 0), p`) while `explicit_binders` parses them.
    /// Lean desugars `∀ (x ∈ s), p` to `∀ x, x ∈ s → p` (and `∃ (x ∈ s), p`
    /// to `∃ x, x ∈ s ∧ p`) — the guard must survive the binder parse so the
    /// enclosing quantifier can wrap the body. Previously the guard was parsed
    /// and DISCARDED, silently dropping the hypothesis. Each entry is the
    /// desugared guard proposition (`Membership.mem s x`, `GT.gt n 0`, …),
    /// already referencing the bound name; the enclosing quantifier drains
    /// this via [`Parser::quant_binders`]. Non-quantifier callers of
    /// `binders()` clear it, so a stale guard can never leak between binders.
    pending_binder_guards: Vec<SurfaceExpr>,
}

impl Parser {
    /// Create a new parser for the given input string.
    ///
    /// # ENSURES
    /// - `pos == 0` (parser starts at beginning)
    /// - `tokens` contains at least one token (EOF if input is empty)
    #[must_use]
    pub fn new(input: &str) -> Self {
        Self::build(input, None)
    }

    /// Create a parser with tactic argument patterns for pattern-aware parsing.
    ///
    /// When patterns are provided, the `Named` tactic fallback uses them to
    /// choose the correct argument parser (nullary, term, ident list, etc.)
    /// instead of the generic comma-separated expression list.
    #[must_use]
    pub fn new_with_tactics(input: &str, patterns: &TacticPatterns) -> Self {
        Self::build(input, Some(patterns.clone()))
    }

    /// Shared constructor backing [`Parser::new`] and [`Parser::new_with_tactics`];
    /// holds the single canonical field initializer so the two entry points
    /// cannot drift.
    fn build(input: &str, tactic_patterns: Option<TacticPatterns>) -> Self {
        let (tokens, doc_comments) = Lexer::tokenize_with_docs(input);
        Self {
            tokens,
            doc_comments,
            pos: 0,
            stop_app_at_newline_lparen: false,
            stop_app_at_newline_outer_indent: false,
            forbid_do: false,
            stop_at_catch_finally: false,
            stop_app_at_by: false,
            stop_app_at_generalizing_using: false,
            in_where_block: false,
            in_struct_field: false,
            in_instance_field: false,
            in_field_type: false,
            indent_stack: Vec::new(),
            indent_context_stack: Vec::new(),
            recovery_diagnostics: Vec::new(),
            pending_recovery_diagnostics: Vec::new(),
            tactic_chain: Vec::new(),
            source: input.to_owned(),
            tactic_patterns,
            expr_depth: 0,
            custom_operators: Vec::new(),
            custom_mixfixes: Vec::new(),
            custom_min_prec: custom_notation::CUSTOM_PREC_FLOOR,
            pending_binder_guards: Vec::new(),
        }
    }

    /// Look up a tactic argument pattern by name.
    pub(crate) fn tactic_pattern(&self, name: &str) -> Option<&TacticArgPattern> {
        self.tactic_patterns.as_ref().and_then(|p| p.get(name))
    }

    /// Parse an expression
    ///
    /// # REQUIRES
    /// - `input` is valid UTF-8
    ///
    /// # ENSURES
    /// - On success, returns `SurfaceExpr` with valid spans
    /// - On error, returns `ParseError` indicating failure location
    /// - Does not panic on malformed input
    ///
    /// # Errors
    ///
    /// Returns an error if tokenization or parsing fails.
    pub fn parse_expr(input: &str) -> Result<SurfaceExpr, ParseError> {
        let mut parser = Parser::new(input);
        let expr = parser.expr()?;
        parser.reject_truncating_operator()?;
        Ok(expr)
    }

    /// Parse an expression with tactic-pattern-aware parsing.
    pub fn parse_expr_with_tactics(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<SurfaceExpr, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        let expr = parser.expr()?;
        parser.reject_truncating_operator()?;
        Ok(expr)
    }

    /// After a top-level expression parse, reject a leftover binary operator
    /// token that Clean's grammar has no rule for and would therefore silently
    /// DROP along with its right operand.
    ///
    /// `>>` (`Seq`, `SeqRight.seqRight`) and `$` (`Dollar`, low-precedence
    /// application), plus the functor-sequencing siblings `$>`/`<$`, have no
    /// operator level in the hand-written precedence chain. `parse_expr("m >> n")`
    /// used to return just `m`, dropping `>> n` — a fully silent truncation in
    /// term positions (quotation bodies, tactic arguments, nested exprs) where
    /// no enclosing `expect` catches the orphaned tail (audit P0-6). Turning it
    /// into a loud `ParseError` keeps the base `parse_expr`'s intentional
    /// leniency for genuine separators (`,`, `)`, `:=` — the caller consumes
    /// those) while refusing to hand back a half-consumed operator expression.
    /// Real `>>`/`$` parses land in Brick 3.
    ///
    /// Only fires when the parse actually stopped ON such an operator; ordinary
    /// trailing tokens still parse leniently (use `parse_expr_with_tactics_exact`
    /// to reject all trailing input).
    fn reject_truncating_operator(&mut self) -> Result<(), ParseError> {
        if let Some(op) = unhandled_binary_operator_symbol(self.current_kind()) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "unhandled operator '{op}' — its left operand was parsed \
                     but Clean has no rule for '{op}', so the rest of the \
                     expression would be silently dropped"
                ),
            });
        }
        Ok(())
    }

    /// Parse an expression requiring all input to be consumed.
    ///
    /// Like `parse_expr_with_tactics`, but returns an error if there are
    /// trailing tokens after the parsed expression. Use this for RPC
    /// endpoints where partial parsing would silently accept malformed input.
    pub fn parse_expr_with_tactics_exact(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<SurfaceExpr, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        let expr = parser.expr()?;
        if !matches!(parser.current_kind(), TokenKind::Eof) {
            return Err(ParseError::UnexpectedToken {
                line: parser.current_line(),
                col: parser.current().col as usize,
                message: format!(
                    "trailing input after expression: {:?}",
                    parser.current_kind()
                ),
            });
        }
        Ok(expr)
    }

    /// Parse the *body* of a syntax quotation into a `SurfaceExpr`.
    ///
    /// `content` is the raw text captured by the lexer for a `` `(...) ``,
    /// `` `[...] `` or `` `{...} `` quotation — it still carries the outer
    /// delimiter pair (e.g. `"(twice $x)"`, `"[rfl]"`, `"{def f := 1}"`). The
    /// matching outer delimiters are stripped and the inner text is parsed with
    /// the antiquotation-aware quotation grammar ([`Parser::parse_q_body`]),
    /// so antiquotations (`$x`, `$(e)`, `$[xs]*`) and infix operator
    /// desugaring (`$x + $y` ⇒ `HAdd.hAdd $x $y`) are handled the same way the
    /// surface parser handles them elsewhere.
    ///
    /// This is the faithful path for `macro`/`macro_rules` patterns and
    /// templates: a bare-string reconstruction would silently drop tokens after
    /// the first antiquotation (e.g. parse `$x + $x` as just `$x`).
    ///
    /// # Errors
    ///
    /// Returns an error if tokenization or parsing fails, or if there is
    /// trailing input after the quotation body.
    pub fn parse_quotation_body(content: &str) -> Result<SurfaceExpr, ParseError> {
        let trimmed = content.trim();
        // Strip a single balanced outer delimiter pair, if present.
        let inner = match trimmed.chars().next() {
            Some('(') if trimmed.ends_with(')') => &trimmed[1..trimmed.len() - 1],
            Some('[') if trimmed.ends_with(']') => &trimmed[1..trimmed.len() - 1],
            Some('{') if trimmed.ends_with('}') => &trimmed[1..trimmed.len() - 1],
            // No surrounding delimiter (e.g. a bare quoted identifier `` `foo ``).
            _ => trimmed,
        };

        let mut parser = Parser::new(inner);
        let expr = parser.parse_q_body()?;
        if !matches!(parser.current_kind(), TokenKind::Eof) {
            return Err(ParseError::UnexpectedToken {
                line: parser.current_line(),
                col: parser.current().col as usize,
                message: format!(
                    "trailing input after quotation body: {:?}",
                    parser.current_kind()
                ),
            });
        }
        Ok(expr)
    }

    /// Parse a declaration
    ///
    /// # REQUIRES
    /// - `input` is valid UTF-8
    ///
    /// # ENSURES
    /// - On success, returns `SurfaceDecl` variant matching input
    /// - Named declarations have non-empty names
    /// - Attributes are parsed and attached to declaration
    ///
    /// # Errors
    ///
    /// Returns an error if tokenization or parsing fails.
    pub fn parse_decl(input: &str) -> Result<SurfaceDecl, ParseError> {
        let mut parser = Parser::new(input);
        parser.decl()
    }

    /// Parse a declaration with tactic-pattern-aware parsing.
    pub fn parse_decl_with_tactics(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        parser.decl()
    }

    /// Like `parse_decl_with_tactics`, but returns an error if there are
    /// trailing tokens after the parsed declaration. Use this for RPC
    /// endpoints where partial parsing would silently accept malformed input.
    /// Part of #2553.
    pub fn parse_decl_with_tactics_exact(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        let decl = parser.decl()?;
        if !matches!(parser.current_kind(), TokenKind::Eof) {
            return Err(ParseError::UnexpectedToken {
                line: parser.current_line(),
                col: parser.current().col as usize,
                message: format!(
                    "trailing input after declaration: {:?}",
                    parser.current_kind()
                ),
            });
        }
        Ok(decl)
    }

    /// Parse a file containing multiple declarations
    ///
    /// # REQUIRES
    /// - `input` is valid UTF-8
    ///
    /// # ENSURES
    /// - Returns declarations in source order
    /// - Empty input yields empty vector
    /// - Stops parsing at EOF
    ///
    /// # Errors
    ///
    /// Returns an error if tokenization or parsing fails.
    pub fn parse_file(input: &str) -> Result<Vec<SurfaceDecl>, ParseError> {
        let mut parser = Parser::new(input);
        parser.file()
    }

    /// Parse a file and also return captured declaration doc comments
    /// (`/-- ... -/`), each already associated by source span with the
    /// declaration that immediately follows it.
    ///
    /// This is a non-breaking companion to [`Parser::parse_file`]: the parsed
    /// declarations are identical, and the doc comments are returned as a
    /// side-table for IDE hover / documentation generation. Capture is purely
    /// syntactic — it does not change how any declaration elaborates.
    ///
    /// Each [`DocComment`] in the returned vector carries the span of the
    /// **declaration** it attaches to (not the comment's own span), so callers
    /// can match a doc to a decl by comparing `doc.span` to `decl_span(decl)`.
    /// Doc comments with no following declaration are dropped.
    ///
    /// # Errors
    ///
    /// Returns an error if tokenization or parsing fails.
    pub fn parse_file_with_docs(
        input: &str,
    ) -> Result<(Vec<SurfaceDecl>, Vec<DocComment>), ParseError> {
        let mut parser = Parser::new(input);
        let raw_docs = std::mem::take(&mut parser.doc_comments);
        let decls = parser.file()?;
        let docs = associate_docs(&decls, raw_docs);
        Ok((decls, docs))
    }

    pub fn parse_file_with_diagnostics(input: &str) -> Result<ParseReport, ParseError> {
        let mut parser = Parser::new(input);
        let decls = parser.file()?;
        Ok(ParseReport {
            decls,
            diagnostics: parser.recovery_diagnostics,
        })
    }

    /// Parse a file with tactic-pattern-aware parsing.
    pub fn parse_file_with_tactics(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<Vec<SurfaceDecl>, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        parser.file()
    }

    /// Tactic-aware file parser with one unambiguous absolute byte coordinate
    /// for source-mapped callers.
    pub fn parse_file_with_tactics_located(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<Vec<SurfaceDecl>, LocatedParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        let decls = parser.file().map_err(|error| LocatedParseError {
            byte_offset: parser.current_span().start.min(input.len()),
            error,
        })?;
        if let Some(diagnostic) = parser.recovery_diagnostics.first() {
            return Err(LocatedParseError {
                byte_offset: diagnostic.recovery_start.byte.min(input.len()),
                error: ParseError::UnexpectedToken {
                    line: diagnostic.recovery_start.line,
                    col: diagnostic.recovery_start.column,
                    message: format!(
                        "strict file parsing rejected recovery `{}`: {}",
                        diagnostic.code, diagnostic.message
                    ),
                },
            });
        }
        Ok(decls)
    }

    pub fn parse_file_with_tactics_diagnostics(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<ParseReport, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        let decls = parser.file()?;
        Ok(ParseReport {
            decls,
            diagnostics: parser.recovery_diagnostics,
        })
    }
}

/// Associate captured doc comments with the declarations they precede.
///
/// A `/-- ... -/` doc comment attaches to the first declaration that begins at
/// or after the comment's end. The returned [`DocComment`]s carry the span of
/// the **declaration** they attach to (so callers can match on `decl.span()`),
/// and the original comment text. When several doc comments precede the same
/// declaration, the last one wins (matching Lean). Doc comments with no
/// following declaration are dropped.
///
/// Both inputs are in source order, so a single forward scan suffices.
fn associate_docs(decls: &[SurfaceDecl], raw_docs: Vec<DocComment>) -> Vec<DocComment> {
    let mut result = Vec::new();
    let mut decl_idx = 0usize;
    for doc in raw_docs {
        // Advance to the first declaration that begins at or after this doc's
        // end. Declarations before the doc cannot own it.
        while decl_idx < decls.len() && decls[decl_idx].span().start < doc.span.end {
            decl_idx += 1;
        }
        let Some(decl) = decls.get(decl_idx) else {
            // No following declaration: this doc is trailing; drop it.
            break;
        };
        let decl_span = decl.span();
        // A later doc preceding the same declaration overrides an earlier one.
        if let Some(last) = result.last_mut() {
            let last: &mut DocComment = last;
            if last.span == decl_span {
                last.text = doc.text;
                continue;
            }
        }
        result.push(DocComment::new(decl_span, doc.text));
    }
    result
}

mod custom_notation;
mod decl;
mod expr;
mod expr_app;
mod expr_binders;
mod expr_do;
mod expr_do_compat;
mod expr_do_try;
mod expr_lambda_let;
mod expr_match;
mod expr_mul;
mod expr_operators;
mod helpers;
mod macros;
mod qq;
mod tactic;
mod tactic_extra;
mod tactic_sub;
mod tokens;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_do;
#[cfg(test)]
mod tests_do_try;
#[cfg(test)]
mod tests_error_recovery;
#[cfg(test)]
mod tests_exact;
#[cfg(test)]
mod tests_interpolation;
#[cfg(test)]
mod tests_tactic;
#[cfg(test)]
mod tests_tactic_calc_do;
#[cfg(test)]
mod tests_tactic_dispatch;
#[cfg(test)]
mod tests_tactic_generalize;
#[cfg(test)]
mod tests_tactic_seq_conv;
#[cfg(test)]
mod tests_tactic_silence;
#[cfg(test)]
mod tests_termination;
#[cfg(test)]
mod tests_where;
