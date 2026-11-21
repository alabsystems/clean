// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The parser's entry points: an expression, a declaration or a file parsed
//! over a fresh [`Parser`], with or without tactic patterns, notation seeds,
//! a source world, origin capture or an exact-consumption check.

use super::*;

impl Parser {
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

    /// Parse with original-source observations for the documented core subset.
    /// The parse verdict and semantic AST use the ordinary parser unchanged.
    pub(crate) fn parse_expr_with_origin_capture(
        input: &str,
    ) -> Result<crate::origins::ParsedWithOrigins<SurfaceExpr>, ParseError> {
        let mut parser = Parser::new(input);
        parser.origins = Some(crate::origins::OriginBuilder::new(input));
        let expr = parser.expr()?;
        parser.reject_truncating_operator()?;
        if let Some(origins) = &mut parser.origins {
            origins.expression_root(&expr);
        }
        Ok(crate::origins::ParsedWithOrigins {
            parsed: expr,
            origins: parser.finish_origins(),
        })
    }

    /// File companion with actual declaration-name token origins for
    /// def/theorem/axiom/opaque and core type/value origins when available.
    /// Recovery invalidates the sidecar, while preserving the ordinary AST.
    pub(crate) fn parse_file_with_origin_capture(
        input: &str,
    ) -> Result<crate::origins::ParsedWithOrigins<Vec<SurfaceDecl>>, ParseError> {
        let mut parser = Parser::new(input);
        parser.origins = Some(crate::origins::OriginBuilder::new(input));
        let parsed = parser.file()?;
        if !parser.recovery_diagnostics.is_empty() || parser.header_recovered {
            if let Some(origins) = &mut parser.origins {
                origins.invalidate("file contains parser recovery");
            }
        }
        Ok(crate::origins::ParsedWithOrigins {
            parsed,
            origins: parser.finish_origins(),
        })
    }

    fn finish_origins(
        &mut self,
    ) -> Result<crate::origins::SourceOrigins, crate::origins::OriginCaptureError> {
        match self.origins.take() {
            Some(origins) => origins.finish(),
            None => Err(crate::origins::OriginCaptureError(
                "capture was not enabled",
            )),
        }
    }

    pub(super) fn observe_declaration_name(
        &mut self,
        declaration_span: Span,
        token_start: usize,
        name: &crate::SurfaceName,
    ) {
        if self.origins.is_none() {
            return;
        }
        let span = self
            .tokens
            .get(token_start)
            .zip(self.pos.checked_sub(1).and_then(|p| self.tokens.get(p)))
            .map(|(first, last)| first.span.merge(last.span));
        if let Some(origins) = &mut self.origins {
            origins.declaration_name(declaration_span, span, name);
        }
    }

    /// Parse an expression with tactic-pattern-aware parsing.
    pub(crate) fn parse_expr_with_tactics(
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
    ///
    /// Public because the Trust superproject's `targo-trust` reads Lean-build
    /// runtime expressions with it (`targo-trust/src/lean_build/runtime.rs`).
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
    pub(crate) fn parse_quotation_body(content: &str) -> Result<SurfaceExpr, ParseError> {
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
        let decl = parser.decl();
        parser.with_latched_refusal(decl)
    }

    /// Parse one declaration and reject any trailing tokens.
    pub fn parse_decl_exact(input: &str) -> Result<SurfaceDecl, ParseError> {
        let mut parser = Parser::new(input);
        let decl = parser.decl();
        parser.finish_exact_decl(decl)
    }

    /// Parse a declaration with tactic-pattern-aware parsing.
    pub(crate) fn parse_decl_with_tactics(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        let decl = parser.decl();
        parser.with_latched_refusal(decl)
    }

    /// `decl`, the result of one top-level [`Parser::decl`], unless a
    /// whole-file refusal was latched in `file_refusal` inside a `namespace` /
    /// `section` body it parsed (plan item `formats-module-spelling-refusals`).
    /// The block that latched it stops there and still returns `Ok`, the
    /// refused command and everything after it dropped, and only
    /// [`Parser::file`] drained the latch: `parse_decl("section\nprivate
    /// section\nend")` was `Ok(Section { decls: [] })`. The latched refusal is
    /// the first error in source order, so it wins over whatever `decl`
    /// returned after it.
    fn with_latched_refusal(
        &mut self,
        decl: Result<SurfaceDecl, ParseError>,
    ) -> Result<SurfaceDecl, ParseError> {
        match self.file_refusal.take() {
            Some(refusal) => Err(refusal),
            None => decl,
        }
    }

    /// Like `parse_decl_with_tactics`, but returns an error if there are
    /// trailing tokens after the parsed declaration. Use this for RPC
    /// endpoints where partial parsing would silently accept malformed input.
    /// Part of #2553.
    pub(crate) fn parse_decl_with_tactics_exact(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        let decl = parser.decl();
        parser.finish_exact_decl(decl)
    }

    fn finish_exact_decl(
        &mut self,
        decl: Result<SurfaceDecl, ParseError>,
    ) -> Result<SurfaceDecl, ParseError> {
        let decl = self.with_latched_refusal(decl)?;
        if !matches!(self.current_kind(), TokenKind::Eof) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "trailing input after declaration: {:?}",
                    self.current_kind()
                ),
            });
        }
        if let Some(err) = self.eof_declaration_doc_refusal() {
            return Err(err);
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
    pub(crate) fn parse_file(input: &str) -> Result<Vec<SurfaceDecl>, ParseError> {
        let mut parser = Parser::new(input);
        parser.file()
    }

    /// Parse a file and also return captured declaration doc comments
    /// (`/-- ... -/`), each already associated by source span with the
    /// declaration that immediately follows it.
    ///
    /// This is a non-breaking companion to [`crate::parse_file`]: the parsed
    /// declarations are identical, and the doc comments are returned as a
    /// side-table for IDE hover / documentation generation. Capture is purely
    /// syntactic — it does not change how any declaration elaborates.
    ///
    /// Each [`DocComment`] in the returned vector carries the span of the
    /// **declaration** it attaches to (not the comment's own span), so callers
    /// can match a doc to a decl by comparing `doc.span` to `decl_span(decl)`.
    /// A declaration doc comment with no following declaration is a syntax error.
    ///
    /// # Errors
    ///
    /// Returns an error if tokenization or parsing fails.
    pub fn parse_file_with_docs(
        input: &str,
    ) -> Result<(Vec<SurfaceDecl>, Vec<DocComment>), ParseError> {
        let mut parser = Parser::new(input);
        // Cloned, not taken: `#guard_msgs` reads the doc comment before it
        // while the file is parsed.
        let raw_docs = parser.doc_comments.clone();
        let decls = parser.file()?;
        let docs = associate_docs(&decls, raw_docs);
        Ok((decls, docs))
    }

    pub(crate) fn parse_file_with_diagnostics(input: &str) -> Result<ParseReport, ParseError> {
        let mut parser = Parser::new(input);
        let decls = parser.file()?;
        Ok(ParseReport {
            decls,
            diagnostics: parser.recovery_diagnostics,
            has_doc_comments: !parser.doc_comments.is_empty() || !parser.module_docs.is_empty(),
            header: parser.file_header,
        })
    }

    /// Parse a file with tactic-pattern-aware parsing.
    pub(crate) fn parse_file_with_tactics(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<Vec<SurfaceDecl>, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns);
        parser.file()
    }

    /// Tactic-aware file parser with one unambiguous absolute byte coordinate
    /// for source-mapped callers.
    pub(crate) fn parse_file_with_tactics_located(
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

    pub(crate) fn parse_file_with_tactics_diagnostics(
        input: &str,
        patterns: &TacticPatterns,
    ) -> Result<ParseReport, ParseError> {
        Self::parse_file_seeded(
            input,
            patterns,
            &crate::notation_seed::NotationSeed::default(),
        )
    }

    /// Tactic-aware file parse with the parser's notation registry
    /// pre-populated from `seed` — the notation the file's imports declare.
    ///
    /// With an empty seed this is exactly
    /// [`Parser::parse_file_with_tactics_diagnostics`], which delegates here so
    /// the two cannot drift.
    ///
    /// # Errors
    ///
    /// Returns a `ParseError` if the input cannot be parsed at file level.
    pub(crate) fn parse_file_seeded(
        input: &str,
        patterns: &TacticPatterns,
        seed: &crate::notation_seed::NotationSeed,
    ) -> Result<ParseReport, ParseError> {
        Self::parse_file_seeded_in_world(
            input,
            patterns,
            seed,
            clean_kernel::lean_world::LeanWorld::ORACLE,
        )
    }

    pub(crate) fn parse_file_seeded_in_world(
        input: &str,
        patterns: &TacticPatterns,
        seed: &crate::notation_seed::NotationSeed,
        world: clean_kernel::lean_world::LeanWorld,
    ) -> Result<ParseReport, ParseError> {
        Self::parse_file_seeded_in_world_with_imported_terms(input, patterns, seed, world, None)
    }

    pub(crate) fn parse_file_seeded_in_world_with_imported_terms(
        input: &str,
        patterns: &TacticPatterns,
        seed: &crate::notation_seed::NotationSeed,
        world: clean_kernel::lean_world::LeanWorld,
        imported_terms: Option<&crate::ImportedTermPrefixes>,
    ) -> Result<ParseReport, ParseError> {
        let mut parser = Parser::new_with_tactics(input, patterns).with_lean_world(world);
        parser.seed_notation(seed);
        if let Some(imported_terms) = imported_terms {
            parser.imported_term_prefixes.clone_from(imported_terms);
        }
        let decls = parser.file()?;
        Ok(ParseReport {
            decls,
            diagnostics: parser.recovery_diagnostics,
            has_doc_comments: !parser.doc_comments.is_empty() || !parser.module_docs.is_empty(),
            header: parser.file_header,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn report_distinguishes_documentation_from_ordinary_comments_and_strings() {
        for (source, expected) in [
            ("/-- Documented declaration. -/\naxiom x : Prop", true),
            ("/-! Module documentation. -/\naxiom x : Prop", true),
            ("/- Ordinary comment. -/\naxiom x : Prop", false),
            ("#check \"/-- text -/ /-! text -/\"", false),
        ] {
            let report = Parser::parse_file_with_diagnostics(source).expect("parse fixture");
            assert_eq!(report.has_doc_comments, expected, "{source}");
            let seeded = Parser::parse_file_seeded(
                source,
                &crate::TacticPatterns::default(),
                &crate::NotationSeed::default(),
            )
            .expect("parse fixture with seed");
            assert_eq!(seeded.has_doc_comments, expected, "{source}");
        }
    }
}
