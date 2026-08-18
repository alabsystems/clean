// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Parser, PendingRecoveryDiagnostic};
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::{ParseError, ParseSourceLocation, ParserDiagnosticSeverity, ParserRecoveryDiagnostic};

impl Parser {
    // ========================================================================
    // Macro system parsing
    // ========================================================================

    /// Parse a syntax declaration: `syntax [name]? [prec]? pattern... : category`
    ///
    /// Examples:
    /// - `syntax term "+" term : term`
    /// - `syntax:50 term "+" term : term`
    /// - `syntax [myAdd] term "+" term : term`
    pub(super) fn syntax_decl(&mut self, start_span: Span) -> Result<SurfaceDecl, ParseError> {
        // Check for optional precedence: syntax:50
        let precedence = self.parse_precedence_suffix();

        // Check for optional name: [name]
        let name = if self.eat(&TokenKind::LBracket) {
            let n = self.ident()?;
            self.expect(&TokenKind::RBracket)?;
            Some(n)
        } else {
            None
        };

        // Check for optional priority: (priority := N)
        let priority = self.parse_priority_attr();

        // Parse the syntax pattern until we hit `:` (category delimiter)
        let pattern = self.parse_syntax_pattern()?;

        // Expect `: category`
        self.expect(&TokenKind::Colon)?;
        let category = self.ident()?;

        Ok(SurfaceDecl::Syntax {
            span: start_span,
            name,
            precedence,
            priority,
            pattern,
            category,
        })
    }

    /// Parse `declare_syntax_cat`: `declare_syntax_cat name`
    pub(super) fn declare_syntax_cat_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.ident()?;
        Ok(SurfaceDecl::DeclareSyntaxCat {
            span: start_span,
            name,
        })
    }

    /// Parse a macro declaration: `macro pattern... : category => expansion`
    ///
    /// Examples:
    /// - `macro "unless" cond:term "then" body:term : term => ...`
    pub(super) fn macro_decl(&mut self, start_span: Span) -> Result<SurfaceDecl, ParseError> {
        // Parse the syntax pattern until we hit `:` (category delimiter)
        let pattern = self.parse_syntax_pattern()?;

        // Expect `: category`
        self.expect(&TokenKind::Colon)?;
        let category = self.ident()?;

        // Expect `=>`
        self.expect(&TokenKind::FatArrow)?;

        // Parse the expansion (a syntax quotation or expression)
        let expansion = self.expr()?;

        Ok(SurfaceDecl::Macro {
            span: start_span,
            doc: None,
            pattern,
            category,
            expansion: Box::new(expansion),
        })
    }

    /// Parse `macro_rules` declaration with multiple arms
    ///
    /// Examples:
    /// - `macro_rules | `(...) => `(...) | `(...) => `(...)`
    pub(super) fn macro_rules_decl(&mut self, start_span: Span) -> Result<SurfaceDecl, ParseError> {
        // Optional name
        let name = if let TokenKind::Ident(_) = self.current_kind() {
            if self.check(&TokenKind::Pipe) {
                None
            } else {
                Some(self.ident()?)
            }
        } else {
            None
        };

        // Parse arms: | pattern => expansion
        let mut arms = Vec::new();
        while self.eat(&TokenKind::Pipe) {
            let arm_span = self.current_span();

            // Parse pattern (typically a syntax quotation)
            let pattern = self.expr()?;

            // Expect =>
            self.expect(&TokenKind::FatArrow)?;

            // Parse expansion
            let expansion = self.expr()?;

            arms.push(MacroArm {
                span: arm_span,
                pattern: Box::new(pattern),
                expansion: Box::new(expansion),
            });
        }

        Ok(SurfaceDecl::MacroRules {
            span: start_span,
            name,
            arms,
        })
    }

    /// Parse elab declaration: `elab <pattern> : <category> => <body>`
    ///
    /// Structure: `elab` pattern... `:` category `=>` body
    pub(super) fn elab_decl(&mut self, start_span: Span) -> Result<SurfaceDecl, ParseError> {
        // Parse the syntax pattern until we hit `:` (category delimiter)
        let pattern = self.parse_syntax_pattern()?;

        // Expect `: category`
        self.expect(&TokenKind::Colon)?;
        let category = self.ident()?;

        // Expect `=>`
        let arrow_span = self.current_span();
        self.expect(&TokenKind::FatArrow)?;

        // Parse the elaboration body.
        //
        // For tactic-category elaborators the body IS a tactic block (e.g.
        // `elab "myexact" e:term : tactic => exact e` has body `exact e`, and
        // `elab "mytac" : tactic => intro h; exact h` is a flat tactic
        // sequence). A bare `self.expr()` only captures the first tactic and
        // drops everything after the first `;`, so for `tactic` we parse a full
        // tactic sequence and wrap it in `SurfaceExpr::ByTactic` — the same node
        // a `by` block produces — so the elaborator can run the body as tactics.
        //
        // Non-tactic categories (term/command) keep the expression body; their
        // execution is deferred to a later phase.
        let body = if category == "tactic" {
            self.by_body(arrow_span)
        } else {
            self.expr()?
        };

        Ok(SurfaceDecl::Elab {
            span: start_span,
            pattern,
            category,
            body: Box::new(body),
        })
    }

    /// Parse notation declaration: `infixl:65 " + " => Add.add`
    ///
    /// `scope` carries the `scoped` / `local` command modifier (parsed by the
    /// declaration dispatcher before the notation keyword) into the surface
    /// tree so the elaborator can honor — or loudly reject — it instead of
    /// silently treating every notation as global (gap sweep B13).
    pub(super) fn notation_decl(
        &mut self,
        start_span: Span,
        kind: NotationKind,
        scope: DeclScope,
    ) -> Result<SurfaceDecl, ParseError> {
        // Check for optional precedence: infixl:65
        let precedence = self.parse_precedence_suffix();

        // Parse the notation pattern
        let pattern = self.parse_notation_pattern();

        // Expect `=>`
        self.expect(&TokenKind::FatArrow)?;

        // Parse the expansion
        let expansion = self.expr()?;

        // Register fixed-arity operators (infixl/infixr/prefix/postfix) so that
        // later expressions in the same file can use the declared symbol. The
        // general `notation` mixfix form is not registered here. `scoped`
        // notation is tagged with its declaring namespace and consulted only
        // while that namespace is active (current / ancestor / opened).
        self.register_custom_operator(kind, precedence, &pattern, &expansion, scope);

        Ok(SurfaceDecl::Notation {
            span: start_span,
            kind,
            precedence,
            pattern,
            expansion: Box::new(expansion),
            scope,
        })
    }

    /// Parse optional precedence suffix `:N` or `:max`
    pub(super) fn parse_precedence_suffix(&mut self) -> Option<u32> {
        if self.eat(&TokenKind::Colon) {
            match self.current_kind().clone() {
                TokenKind::NatLit(n) => {
                    self.advance();
                    Some(
                        n.to_u64()
                            .and_then(|v| u32::try_from(v).ok())
                            .unwrap_or(u32::MAX),
                    )
                }
                TokenKind::Ident(s) if s == "max" => {
                    self.advance();
                    Some(1024) // max precedence
                }
                TokenKind::Ident(s) if s == "min" => {
                    self.advance();
                    Some(0)
                }
                TokenKind::Ident(s) if s == "arg" => {
                    self.advance();
                    Some(1023) // arg precedence
                }
                TokenKind::Ident(s) if s == "lead" => {
                    self.advance();
                    Some(1024) // lead = max
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Parse optional priority attribute: (priority := N)
    pub(super) fn parse_priority_attr(&mut self) -> Option<u32> {
        if self.check(&TokenKind::LParen) {
            let pos = self.pos;
            self.advance();
            if let TokenKind::Ident(s) = self.current_kind().clone() {
                if s == "priority" {
                    self.advance();
                    if self.eat(&TokenKind::ColonEq) {
                        if let TokenKind::NatLit(n) = self.current_kind().clone() {
                            self.advance();
                            if self.eat(&TokenKind::RParen) {
                                return Some(
                                    n.to_u64()
                                        .and_then(|v| u32::try_from(v).ok())
                                        .unwrap_or(u32::MAX),
                                );
                            }
                        }
                    }
                }
            }
            // Backtrack if not a priority attr
            self.pos = pos;
        }
        None
    }

    /// Parse a syntax pattern (sequence of items until `: category`)
    pub(super) fn parse_syntax_pattern(&mut self) -> Result<Vec<SyntaxPatternItem>, ParseError> {
        let mut items = Vec::new();

        while !matches!(self.current_kind(), TokenKind::Eof) {
            // Check if we're at the end: last identifier followed by `: category`
            // We need to look ahead to detect `ident : ident` at the end
            if self.at_syntax_pattern_end() {
                break;
            }

            let item = self.parse_syntax_pattern_item()?;
            items.push(item);
        }

        Ok(items)
    }

    /// Check if we're at the end of a syntax pattern (` : category`)
    pub(super) fn at_syntax_pattern_end(&self) -> bool {
        // Pattern ends at `: category` where category is a single identifier
        // and nothing follows (or EOF, or `=>` for macros, or a new declaration)
        if self.check(&TokenKind::Colon) {
            // `: ident` at end - this is the category delimiter
            if let Some(TokenKind::Ident(_)) = self.peek_kind(1) {
                // Check that nothing meaningful follows the category
                let peek2 = self.peek_kind(2);
                if matches!(peek2, None | Some(TokenKind::Eof)) {
                    return true;
                }
                // Check if what follows is a declaration start (new declaration)
                // or `=>` for macro expansion
                if let Some(tok) = peek2 {
                    if matches!(tok, TokenKind::FatArrow) || Self::is_decl_keyword(tok) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Parse a single syntax pattern item
    pub(super) fn parse_syntax_pattern_item(&mut self) -> Result<SyntaxPatternItem, ParseError> {
        match self.current_kind().clone() {
            // String literal: "if", "then", "+"
            TokenKind::StringLit(s) => {
                self.advance();
                Ok(SyntaxPatternItem::Literal(s))
            }

            // Identifier with optional category: `cond:term` or just `term`
            TokenKind::Ident(name) => {
                self.advance();

                // Check for `:category` suffix (variable binding like `x:term`)
                // But NOT if this is the final `: category` delimiter
                if self.check(&TokenKind::Colon) {
                    if let Some(TokenKind::Ident(cat)) = self.peek_kind(1).cloned() {
                        // Check if this is `var:cat` followed by more pattern items
                        // or if this is the end delimiter (followed by EOF, =>, or decl-start)
                        let peek2 = self.peek_kind(2);
                        let is_end = matches!(peek2, None | Some(TokenKind::Eof))
                            || peek2.is_some_and(|t| {
                                matches!(t, TokenKind::FatArrow) || Self::is_decl_keyword(t)
                            });
                        if !is_end {
                            // More pattern follows - this is a variable binding
                            self.advance(); // eat :
                            self.advance(); // eat category
                            return Ok(SyntaxPatternItem::Variable {
                                name,
                                category: Some(cat),
                            });
                        }
                    }
                }

                // Check for repetition suffix: `,*` or `,+`
                if self.check(&TokenKind::Comma) {
                    let pos = self.pos;
                    self.advance();
                    if self.check(&TokenKind::Star) {
                        self.advance();
                        return Ok(SyntaxPatternItem::Repetition {
                            pattern: vec![SyntaxPatternItem::Variable {
                                name,
                                category: None,
                            }],
                            separator: Some(",".to_string()),
                            at_least_one: false,
                        });
                    } else if self.check(&TokenKind::Plus) {
                        self.advance();
                        return Ok(SyntaxPatternItem::Repetition {
                            pattern: vec![SyntaxPatternItem::Variable {
                                name,
                                category: None,
                            }],
                            separator: Some(",".to_string()),
                            at_least_one: true,
                        });
                    }
                    // Not a repetition, backtrack
                    self.pos = pos;
                }

                // Just a variable or category reference
                Ok(SyntaxPatternItem::Variable {
                    name,
                    category: None,
                })
            }

            // Atomic/keyword prefix: &"keyword"
            TokenKind::Amp => {
                self.advance();
                if let TokenKind::StringLit(s) = self.current_kind().clone() {
                    self.advance();
                    Ok(SyntaxPatternItem::Literal(s))
                } else {
                    // Treat bare & as opaque token in syntax pattern
                    Ok(SyntaxPatternItem::Literal("&".to_string()))
                }
            }

            // Alternation operator in syntax patterns: pattern <|> pattern
            TokenKind::OrElse => {
                self.advance();
                Ok(SyntaxPatternItem::Literal("<|>".to_string()))
            }

            // Optional group: (pattern)?  or  (name := value)  or  (priority := N)
            TokenKind::LParen => {
                self.advance();
                // Skip balanced parenthesized content for syntax patterns.
                // This handles (name := ...), (priority := ...), (docComment)?,
                // sepByIndentSemicolon(item), and other complex syntax combinators.
                let mut depth = 1;
                while depth > 0 && !matches!(self.current_kind(), TokenKind::Eof) {
                    match self.current_kind() {
                        TokenKind::LParen => depth += 1,
                        TokenKind::RParen => depth -= 1,
                        _ => {}
                    }
                    if depth > 0 {
                        self.advance();
                    }
                }
                if depth == 0 {
                    self.advance(); // consume final RParen
                }

                // Check for `?` suffix (optional)
                if let TokenKind::Ident(s) = self.current_kind() {
                    if s == "?" {
                        self.advance();
                        return Ok(SyntaxPatternItem::Optional(vec![]));
                    }
                }

                // Treat the entire parenthesized group as an opaque pattern element
                Ok(SyntaxPatternItem::Literal("(...)".to_string()))
            }

            // Syntax quotation
            TokenKind::SyntaxQuote(content) => {
                self.advance();
                // For now, treat as a literal pattern
                Ok(SyntaxPatternItem::Literal(format!("`({content})")))
            }

            // Underscore as a syntax pattern element (e.g., in `ident <|> "_"`)
            TokenKind::Underscore => {
                self.advance();
                Ok(SyntaxPatternItem::Variable {
                    name: "_".to_string(),
                    category: None,
                })
            }

            // Dollar sign for antiquotation in syntax patterns
            TokenKind::Dollar => {
                self.advance();
                // Skip the antiquotation content
                if self.check(&TokenKind::LBracket) {
                    // $[...] repetition
                    self.advance();
                    let mut depth = 1;
                    while depth > 0 && !matches!(self.current_kind(), TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LBracket => depth += 1,
                            TokenKind::RBracket => depth -= 1,
                            _ => {}
                        }
                        if depth > 0 {
                            self.advance();
                        }
                    }
                    if depth == 0 {
                        self.advance();
                    }
                    // Check for suffix like ?,* ,+
                    while matches!(
                        self.current_kind(),
                        TokenKind::Star | TokenKind::Plus | TokenKind::Comma
                    ) {
                        self.advance();
                    }
                    if let TokenKind::Ident(s) = self.current_kind() {
                        if s == "?" {
                            self.advance();
                        }
                    }
                }
                Ok(SyntaxPatternItem::Literal("$".to_string()))
            }

            _ => {
                // For any other token in a syntax pattern, skip it gracefully
                // rather than failing. Lean 4 syntax patterns can contain
                // a wide variety of tokens (operators, keywords, etc.)
                self.advance();
                Ok(SyntaxPatternItem::Literal("_".to_string()))
            }
        }
    }

    /// Parse a notation pattern (alternating literals and variables)
    pub(super) fn parse_notation_pattern(&mut self) -> Vec<NotationItem> {
        let mut items = Vec::new();

        while !self.check(&TokenKind::FatArrow) && !matches!(self.current_kind(), TokenKind::Eof) {
            match self.current_kind().clone() {
                TokenKind::StringLit(s) => {
                    self.advance();
                    items.push(NotationItem::Literal(s));
                }
                TokenKind::Ident(name) => {
                    self.advance();
                    items.push(NotationItem::Variable(name));
                }
                _ => {
                    // Skip unknown tokens in notation patterns
                    self.advance();
                }
            }
        }

        items
    }

    /// Skip to next declaration (for unrecognized syntax)
    pub(super) fn skip_to_next_decl(&mut self, kind: &str, start_span: Span) -> SurfaceDecl {
        self.skip_to_next_decl_impl(kind, start_span, None)
    }

    /// Skip to next declaration and record where recovery resumed.
    pub(super) fn skip_to_next_decl_with_recovery(
        &mut self,
        kind: &str,
        start_span: Span,
        err: &ParseError,
    ) -> SurfaceDecl {
        self.skip_to_next_decl_impl(kind, start_span, Some(err))
    }

    fn skip_to_next_decl_impl(
        &mut self,
        kind: &str,
        start_span: Span,
        err: Option<&ParseError>,
    ) -> SurfaceDecl {
        // Collect the raw content until we hit a recognizable declaration token
        let mut content = kind.to_string();
        // Defense-in-depth: if this recovery routine is entered while the
        // cursor is already on a declaration-start token (e.g. a stray `end`
        // at the top level), the `while` below would exit without advancing,
        // and `file()` would re-dispatch the same token forever. Force at
        // least one token of progress on entry unless we are already at EOF.
        // The token-specific dispatch in `decl_with_modifiers` is the
        // preferred fix for any individual culprit; this guard ensures any
        // future addition to `is_decl_keyword` cannot regress into a hang.
        //
        // The forced advance is gated on the failed declaration having made no
        // progress (cursor still parked at `start_span.start`). When the failed
        // `decl()` already consumed tokens — e.g. a malformed `do`/`by` block
        // that resynced the cursor onto the *next* top-level declaration — the
        // cursor sits on a fresh decl-start that we must NOT consume: leaving it
        // in place lets `file()` re-dispatch and parse it as its own decl rather
        // than swallowing it into the malformed region. Progress was already
        // made, so there is no risk of a no-advance hang.
        let made_no_progress = self.current_span().start == start_span.start;
        if made_no_progress
            && self.is_decl_start()
            && !matches!(self.current_kind(), TokenKind::Eof)
        {
            match self.current_kind().clone() {
                TokenKind::Ident(s) => {
                    content.push(' ');
                    content.push_str(&s);
                }
                TokenKind::NatLit(n) => {
                    use std::fmt::Write;
                    write!(content, " {n}").unwrap();
                }
                TokenKind::StringLit(s) => {
                    use std::fmt::Write;
                    write!(content, " \"{s}\"").unwrap();
                }
                _ => content.push(' '),
            }
            self.advance();
        }
        while !self.is_decl_start() && !matches!(self.current_kind(), TokenKind::Eof) {
            // Just advance through tokens
            match self.current_kind().clone() {
                TokenKind::Ident(s) => {
                    content.push(' ');
                    content.push_str(&s);
                }
                TokenKind::NatLit(n) => {
                    use std::fmt::Write;
                    write!(content, " {n}").unwrap();
                }
                TokenKind::StringLit(s) => {
                    use std::fmt::Write;
                    write!(content, " \"{s}\"").unwrap();
                }
                _ => content.push(' '),
            }
            self.advance();
        }

        if let Some(err) = err {
            self.flush_pending_parser_recoveries();
            self.record_parser_recovery(kind, start_span, err);
        }

        // Return as RawDecl for unrecognized commands
        SurfaceDecl::RawDecl {
            span: start_span,
            content,
        }
    }

    pub(super) fn record_parser_recovery(
        &mut self,
        construct: &str,
        start_span: Span,
        err: &ParseError,
    ) {
        let pending = self.pending_parser_recovery(construct, err, start_span.start);
        self.push_completed_parser_recovery(pending);
    }

    pub(super) fn defer_parser_recovery(&mut self, construct: &str, err: &ParseError) {
        let failure_byte = self.current_span().start;
        let pending = self.pending_parser_recovery(construct, err, failure_byte);
        self.pending_recovery_diagnostics.push(pending);
    }

    /// Defer a recovery diagnostic that NAMES the tactic whose grammar failed.
    ///
    /// Measurement integrity (T0): a tactic-block recovery degrades the whole
    /// declaration to a synthetic sorry. Without the tactic's name in the
    /// message the user is told only that the declaration "uses synthetic
    /// sorry" — no diagnostic anywhere names the construct that did nothing.
    /// The name comes from `tactic_in_progress`, set by `Parser::tactic`.
    pub(super) fn defer_tactic_parser_recovery(&mut self, construct: &str, err: &ParseError) {
        let failure_byte = self.current_span().start;
        let mut pending = self.pending_parser_recovery(construct, err, failure_byte);
        if let Some(head) = self.tactic_chain.first().cloned() {
            let chain = self
                .tactic_chain
                .iter()
                .map(|t| format!("`{t}`"))
                .collect::<Vec<_>>()
                .join(" > ");
            pending.message = format!("unsupported tactic syntax {chain}: {}", pending.message);
            pending.tactic = Some(head);
        }
        self.pending_recovery_diagnostics.push(pending);
    }

    pub(super) fn flush_pending_parser_recoveries(&mut self) {
        let pending = std::mem::take(&mut self.pending_recovery_diagnostics);
        for diag in pending {
            self.push_completed_parser_recovery(diag);
        }
    }

    fn pending_parser_recovery(
        &self,
        construct: &str,
        err: &ParseError,
        failure_byte: usize,
    ) -> PendingRecoveryDiagnostic {
        let token = self.current();
        let failure_col = token.col;
        let recovery_start = match err {
            ParseError::UnexpectedToken { line, col, .. } => ParseSourceLocation {
                line: *line,
                column: *col,
                byte: failure_byte,
            },
            ParseError::NestingTooDeep { col, .. } => ParseSourceLocation {
                line: self.current_line(),
                column: *col,
                byte: failure_byte,
            },
            _ => ParseSourceLocation {
                line: self.current_line(),
                column: self.current().col as usize,
                byte: failure_byte,
            },
        };
        let indent_ctx = self.indent_context_stack.last().cloned();
        let construct = indent_ctx
            .as_ref()
            .map(|ctx| ctx.construct.clone())
            .unwrap_or_else(|| construct.to_owned());
        let code = if indent_ctx.is_some() {
            "parser.indent_recovery"
        } else {
            "parser.recovery"
        };
        PendingRecoveryDiagnostic {
            code: code.to_owned(),
            construct,
            block_start: indent_ctx.as_ref().map(|ctx| ParseSourceLocation {
                line: ctx.line,
                column: ctx.column as usize,
                byte: ctx.byte,
            }),
            recovery_start,
            expected_indent: indent_ctx.as_ref().map(|ctx| ctx.column),
            actual_indent: Some(failure_col),
            message: err.to_string(),
            tactic: None,
        }
    }

    fn push_completed_parser_recovery(&mut self, pending: PendingRecoveryDiagnostic) {
        let token = self.current();
        let recovered_at = ParseSourceLocation {
            line: token.line as usize,
            column: token.col as usize,
            byte: token.span.start,
        };
        let resumed_token = format!("{:?}", self.current_kind());
        self.recovery_diagnostics.push(ParserRecoveryDiagnostic {
            code: pending.code,
            severity: ParserDiagnosticSeverity::Error,
            construct: pending.construct,
            block_start: pending.block_start,
            recovery_start: pending.recovery_start,
            recovered_at,
            resumed_token,
            expected_indent: pending.expected_indent,
            actual_indent: pending.actual_indent,
            message: pending.message,
            tactic: pending.tactic,
        });
    }

    /// Check if a token kind is a declaration-start keyword (excluding Hash,
    /// which needs peek-ahead disambiguation).
    fn is_decl_keyword(tok: &TokenKind) -> bool {
        matches!(
            tok,
            TokenKind::Def
                | TokenKind::Theorem
                | TokenKind::Lemma
                | TokenKind::Axiom
                | TokenKind::Example
                | TokenKind::Inductive
                | TokenKind::Codata
                | TokenKind::Codef
                | TokenKind::Structure
                | TokenKind::Class
                | TokenKind::Instance
                | TokenKind::Import
                | TokenKind::Namespace
                | TokenKind::Section
                | TokenKind::Universe
                | TokenKind::Variable
                | TokenKind::Open
                | TokenKind::Mutual
                | TokenKind::End
                | TokenKind::At
                | TokenKind::Hash
                | TokenKind::Private
                | TokenKind::Protected
                | TokenKind::Public
                | TokenKind::Module
                | TokenKind::Partial
                | TokenKind::Unsafe
                | TokenKind::Noncomputable
                | TokenKind::Abbrev
                | TokenKind::Attribute
                | TokenKind::SetOption
                | TokenKind::Syntax
                | TokenKind::Macro
                | TokenKind::MacroRules
                | TokenKind::Elab
                | TokenKind::Notation
                | TokenKind::Infixl
                | TokenKind::Infixr
                | TokenKind::Prefix
                | TokenKind::Postfix
        )
    }

    /// Check if current token starts a declaration
    pub(super) fn is_decl_start(&self) -> bool {
        // Hash commands (#check, #eval) are declaration starters,
        // but #[ is an array literal, not a declaration
        if matches!(self.current_kind(), TokenKind::Hash) {
            return !matches!(self.peek_kind(1), Some(TokenKind::LBracket));
        }
        Self::is_decl_keyword(self.current_kind())
    }

    /// Skip to next recognizable declaration token
    pub(super) fn skip_to_next_decl_token(&mut self) {
        while !self.is_decl_start() && !matches!(self.current_kind(), TokenKind::Eof) {
            self.advance();
        }
    }
}
