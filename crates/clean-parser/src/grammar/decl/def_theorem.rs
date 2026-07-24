// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for def, theorem, axiom, and opaque declarations,
//! including termination hints and def-match-body desugaring.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::DeclModifiers;
use crate::surface::*;
use crate::ParseError;

enum ParsedTerminationHint {
    TerminationBy(TerminationBy),
    DecreasingBy(DecreasingBy),
}

/// How the equation-arm list of a def-match body is bounded (B101).
///
/// - `Declaration`: top-level `def`/`theorem`/`where` context — after each arm
///   body the parser must sit on a declaration-level boundary token
///   (`|`, `where`, `end`, EOF, or a termination hint).
/// - `LetValue`: term-level equation-style `let rec` context — the enclosing
///   let-value layout gate (dedent to the `let` keyword's column) terminates
///   the final arm body, so the following token starts the let's body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::grammar) enum EquationArmBoundary {
    Declaration,
    LetValue,
}

impl Parser {
    /// Parse a def declaration with explicit modifiers.
    pub(in crate::grammar) fn def_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;

        // Optional universe params
        let universe_params = self.universe_params()?;

        // Optional binders
        let binders = self.optional_binders()?;

        // Optional type annotation
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        // Definition value can be provided with:
        // - := expr
        // - | pattern => expr (pattern matching)
        // - where | pattern => expr (where clause syntax)
        let val = if self.eat(&TokenKind::ColonEq) {
            self.expr()?
        } else if self.check(&TokenKind::Pipe) {
            // Pattern matching definition
            self.def_match_body(start_span)?
        } else if self.eat(&TokenKind::Where) {
            if self.check(&TokenKind::Pipe) {
                // Where clause: def foo : Nat → Nat where | 0 => 1 | n => n
                self.def_match_body(start_span)?
            } else if self.is_field_assign_start() {
                // Structure-instance sugar: `def x : S where\n  f := v` is a
                // struct literal `{ f := v }` elaborated at the annotated type
                // (Lean `Command.declValStruct`). Same field-assign grammar as
                // an instance `where` body. (B90)
                let assigns = self.parse_where_field_assigns()?;
                SurfaceExpr::StructLit {
                    span: start_span,
                    struct_type: None,
                    base: None,
                    fields: assigns,
                }
            } else {
                // Where clause: def foo : Nat → Nat where | 0 => 1 | n => n
                self.def_match_body(start_span)?
            }
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected := or |, got {:?}", self.current_kind()),
            });
        };

        // Parse optional termination_by and decreasing_by clauses
        let termination = self.parse_termination_hints();

        // Parse optional where clause with local definitions
        let where_decls = self.parse_where_local_defs();

        Ok(SurfaceDecl::Def {
            span: start_span,
            name,
            universe_params,
            binders,
            ty,
            val: Box::new(val),
            attrs,
            termination,
            modifiers,
            where_decls,
        })
    }

    /// Parse `termination_by` and `decreasing_by` clauses that follow function definitions
    ///
    /// Lean 4 syntax variants:
    /// - `termination_by args => measure` (well-founded with params)
    /// - `termination_by measure` (well-founded, new syntax)
    /// - `termination_by structural x` (structural recursion on param x) - Lean 4.11.0+
    /// - `termination_by?` (query: show inferred termination)
    /// - `decreasing_by tactic`
    ///
    /// Reference: <https://lean-lang.org/doc/reference/latest/releases/v4.11.0/>
    ///
    /// These clauses are optional and may appear in any order after recursive definitions.
    pub(in crate::grammar) fn parse_termination_hints(&mut self) -> TerminationHints {
        let mut hints = TerminationHints::default();

        loop {
            let construct = match self.current_kind() {
                TokenKind::Ident(name) if name == "termination_by" || name == "termination_by?" => {
                    "termination_by"
                }
                TokenKind::Ident(name) if name == "decreasing_by" => "decreasing_by",
                _ => break,
            };

            let parsed = if construct == "termination_by" {
                self.parse_termination_by_clause(&hints)
                    .map(ParsedTerminationHint::TerminationBy)
            } else {
                self.parse_decreasing_by_clause(&hints)
                    .map(ParsedTerminationHint::DecreasingBy)
            };

            match parsed {
                Ok(ParsedTerminationHint::TerminationBy(hint)) => {
                    hints.termination_by = Some(hint);
                }
                Ok(ParsedTerminationHint::DecreasingBy(hint)) => {
                    hints.decreasing_by = Some(hint);
                }
                Err(err) => {
                    // File parsing is intentionally recovery-capable for IDEs, but
                    // a malformed optional hint must never be represented by a
                    // fabricated `Hole`. Record the exact failed construct, skip
                    // only its malformed tail, and omit the hint. The strict
                    // located file API rejects every recorded recovery.
                    let err = self.termination_hint_recovery_error(err);
                    self.defer_parser_recovery(construct, &err);
                    self.skip_to_termination_hint_boundary();
                    self.flush_pending_parser_recoveries();
                }
            }
        }
        hints
    }

    fn parse_termination_by_clause(
        &mut self,
        hints: &TerminationHints,
    ) -> Result<TerminationBy, ParseError> {
        let start_span = self.current_span();
        let query =
            matches!(self.current_kind(), TokenKind::Ident(name) if name == "termination_by?");
        self.advance();

        // Consume the clause keyword before reporting a duplicate. Recovery
        // must make progress even when the duplicate is immediately followed
        // by another hint or declaration boundary.
        if hints.termination_by.is_some() {
            return Err(self.termination_hint_error("duplicate `termination_by` clause"));
        }

        if query {
            self.ensure_termination_hint_boundary("`termination_by?` takes no arguments")?;
            return Ok(TerminationBy {
                span: start_span,
                kind: TerminationKind::Query,
                params: Vec::new(),
                measure: None,
            });
        }

        if matches!(self.current_kind(), TokenKind::Ident(name) if name == "structural") {
            self.advance();
            let (param_name, param_span) = match self.current_kind().clone() {
                TokenKind::Ident(param) => {
                    let param_span = self.current_span();
                    self.advance();
                    (param, param_span)
                }
                _ => {
                    return Err(self.termination_hint_error(
                        "`termination_by structural` requires a parameter name",
                    ));
                }
            };
            self.ensure_termination_hint_boundary(
                "unexpected token after `termination_by structural` parameter",
            )?;
            return Ok(TerminationBy {
                span: Span::new(start_span.start, param_span.end),
                kind: TerminationKind::Structural(param_name),
                params: Vec::new(),
                measure: None,
            });
        }

        // Lean supports both the legacy `termination_by x y => measure`
        // spelling and the newer `termination_by measure` spelling.
        let has_arrow = self.peek_for_legacy_termination_arrow();
        let mut params = Vec::new();
        if has_arrow {
            while !matches!(self.current_kind(), TokenKind::FatArrow) {
                match self.current_kind().clone() {
                    TokenKind::Ident(param) => {
                        params.push(param);
                        self.advance();
                    }
                    TokenKind::Underscore => {
                        params.push("_".to_string());
                        self.advance();
                    }
                    _ => {
                        return Err(self.termination_hint_error(
                            "expected a parameter name or `_` before `=>` in `termination_by`",
                        ));
                    }
                }
            }
            if params.is_empty() {
                return Err(self.termination_hint_error(
                    "legacy `termination_by ... => ...` requires at least one parameter",
                ));
            }
            self.expect(&TokenKind::FatArrow)?;
        }

        let measure = self.termination_measure_expr()?;
        self.ensure_termination_hint_boundary(
            "unexpected token after `termination_by` measure expression",
        )?;
        let end_span = measure.span();
        Ok(TerminationBy {
            span: Span::new(start_span.start, end_span.end),
            kind: TerminationKind::WellFounded,
            params,
            measure: Some(Box::new(measure)),
        })
    }

    fn parse_decreasing_by_clause(
        &mut self,
        hints: &TerminationHints,
    ) -> Result<DecreasingBy, ParseError> {
        let start_span = self.current_span();
        self.advance();

        // As above, consume the keyword so duplicate-clause recovery cannot
        // redispatch the same token forever.
        if hints.decreasing_by.is_some() {
            return Err(self.termination_hint_error("duplicate `decreasing_by` clause"));
        }

        let tactic = self.termination_tactic_expr()?;
        self.ensure_termination_hint_boundary(
            "unexpected token after `decreasing_by` tactic body",
        )?;
        let end_span = tactic.span();
        Ok(DecreasingBy {
            span: Span::new(start_span.start, end_span.end),
            tactic: Box::new(tactic),
        })
    }

    /// Parse a termination measure expression (after `=>` or directly after `termination_by`).
    ///
    /// Delegates to the real expression parser. The expression parser naturally stops
    /// at termination hint boundaries (`termination_by`, `decreasing_by`) via the
    /// `is_atom_start()` guard in expr_app.rs, and at declaration keywords.
    fn termination_measure_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        if self.at_termination_hint_end(0) {
            return Err(
                self.termination_hint_error("`termination_by` requires a measure expression")
            );
        }
        self.expr()
    }

    /// Parse a `decreasing_by` tactic block.
    ///
    /// Delegates to the real tactic sequence parser. The tactic parser stops at
    /// termination hint boundaries (`termination_by`, `decreasing_by`) via the
    /// `at_tactic_end()` guard in expr_lambda_let.rs, and at declaration keywords.
    /// The result is wrapped in `SurfaceExpr::ByTactic` to match the `DecreasingBy`
    /// field type.
    fn termination_tactic_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let start_span = self.current_span();

        if self.at_termination_hint_end(0) {
            return Err(
                self.termination_hint_error("`decreasing_by` requires a non-empty tactic body")
            );
        }

        match self.tactic_seq() {
            Ok(tactics) if !tactics.is_empty() => {
                let end_span = tactics.last().map_or(start_span, |t| t.span());
                Ok(SurfaceExpr::ByTactic(
                    Span::new(start_span.start, end_span.end),
                    tactics,
                ))
            }
            Ok(_) => {
                Err(self.termination_hint_error("`decreasing_by` requires a non-empty tactic body"))
            }
            Err(err) => Err(err),
        }
    }

    fn termination_hint_error(&self, message: impl Into<String>) -> ParseError {
        ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current().col as usize,
            message: message.into(),
        }
    }

    /// Recovery diagnostics have a strict line/column/byte contract even
    /// though legacy `ParseError` sites inconsistently use absolute bytes in
    /// `col`. Re-anchor nested expression/tactic errors to the parser's current
    /// token before recording this hint-local recovery.
    fn termination_hint_recovery_error(&self, err: ParseError) -> ParseError {
        match err {
            ParseError::UnexpectedToken { message, .. } => ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message,
            },
            other => other,
        }
    }

    fn ensure_termination_hint_boundary(&self, message: &str) -> Result<(), ParseError> {
        if self.at_termination_hint_end(0) {
            Ok(())
        } else {
            Err(self.termination_hint_error(message))
        }
    }

    /// Skip a malformed hint tail without consuming the next hint/declaration.
    fn skip_to_termination_hint_boundary(&mut self) {
        // Declaration and hint keywords are hard boundaries even after an
        // unmatched opener. Carrying delimiter depth across a failed parse can
        // otherwise swallow the rest of the file (`termination_by ( => ...`
        // followed by `def next`). These keywords cannot legally continue a
        // measure/tactic at any nesting depth, so stopping is unambiguous.
        while !self.at_termination_hint_end(0) {
            self.advance();
        }
    }

    /// Check if we're at the end of a termination hint expression
    pub(in crate::grammar) fn at_termination_hint_end(&self, depth: usize) -> bool {
        if depth > 0 {
            return false;
        }
        // Check for next termination hint or declaration start
        if let TokenKind::Ident(name) = self.current_kind() {
            if name == "termination_by" || name == "termination_by?" || name == "decreasing_by" {
                return true;
            }
        }
        self.is_decl_start()
            || matches!(
                self.current_kind(),
                TokenKind::Where | TokenKind::Eof | TokenKind::End
            )
    }

    /// Determine whether `termination_by` uses the legacy parameter syntax.
    ///
    /// The legacy prefix is narrowly `ident-or-underscore+ =>`. Looking for an
    /// arbitrary top-level `=>` is unsound because valid modern measures may
    /// themselves contain one (`fun x => x`, `match x with | ... => ...`).
    /// Used to distinguish (#1132):
    /// - `termination_by x y => measure` (old syntax with params)
    /// - `termination_by measure` (new syntax without =>)
    fn peek_for_legacy_termination_arrow(&self) -> bool {
        let mut offset = 0usize;
        let mut params = 0usize;
        loop {
            match self.peek_kind(offset) {
                Some(TokenKind::Ident(_)) | Some(TokenKind::Underscore) => {
                    params += 1;
                    offset += 1;
                }
                Some(TokenKind::FatArrow) => return params > 0,
                _ => return false,
            }
        }
    }

    /// Parse a definition body using pattern matching syntax.
    ///
    /// Lean 4: `def f | pat1 => body1 | pat2 => body2` is sugar for
    /// `def f := fun _x => match _x with | pat1 => body1 | pat2 => body2`.
    /// Multi-argument: `def f | p1, p2 => body` uses tuple scrutinees.
    ///
    /// Reference: ~/lean4-ref/src/Lean/Elab/MutualDef.lean (elabFunValues)
    pub(in crate::grammar) fn def_match_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        self.def_match_body_bounded(start_span, EquationArmBoundary::Declaration)
    }

    /// [`Self::def_match_body`] with an explicit arm-list boundary mode.
    ///
    /// `Declaration` is the top-level `def`/`theorem`/`where` behavior
    /// (each arm body must end at a declaration-level boundary token).
    /// `LetValue` is the term-level equation-style `let rec` behavior (B101):
    /// the surrounding let-value layout gate terminates the final arm body at
    /// a dedent, so the token after an arm is the let's continuation body
    /// rather than a declaration boundary.
    pub(in crate::grammar) fn def_match_body_bounded(
        &mut self,
        start_span: Span,
        boundary: EquationArmBoundary,
    ) -> Result<SurfaceExpr, ParseError> {
        if !self.check(&TokenKind::Pipe) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "expected definition equation arm beginning with `|`, got {:?}",
                    self.current_kind()
                ),
            });
        }

        let mut arms = Vec::new();
        let mut arity: Option<usize> = None;

        while self.eat(&TokenKind::Pipe) {
            // Parse comma-separated patterns for this arm
            let mut patterns = vec![self.def_match_pattern()?];
            while self.eat(&TokenKind::Comma) {
                patterns.push(self.def_match_pattern()?);
            }

            // Enforce consistent arity across arms
            match arity {
                None => arity = Some(patterns.len()),
                Some(n) if n != patterns.len() => {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current().col as usize,
                        message: format!(
                            "definition equation arity mismatch: expected {n} pattern(s), found {}",
                            patterns.len()
                        ),
                    });
                }
                _ => {}
            }

            self.expect(&TokenKind::FatArrow)?;
            let body = self.def_match_arm_body(boundary)?;
            // Combine multiple patterns into a tuple pattern
            let pattern = if patterns.len() == 1 {
                patterns.pop().expect("non-empty patterns vec")
            } else {
                patterns
                    .into_iter()
                    .rev()
                    .reduce(|acc, pat| SurfacePattern::Ctor("Prod.mk".to_string(), vec![pat, acc]))
                    .expect("patterns.len() > 1")
            };
            arms.push(SurfaceMatchArm {
                span: pattern.span(),
                pattern,
                body,
            });
        }

        debug_assert!(!arms.is_empty(), "leading equation pipe creates an arm");

        // Build anonymous scrutinee variable(s) and the match expression.
        // For arity 1: fun _x => match _x with | arms...
        // For arity N: fun _x => match _x with | (p1, p2) => body | ...
        let scrutinee = SurfaceExpr::Ident(start_span, "_x".to_string());
        let binder = SurfaceBinder::new("_x".to_string(), None, SurfaceBinderInfo::Explicit);
        let match_expr = SurfaceExpr::Match(start_span, None, Box::new(scrutinee), arms);
        Ok(SurfaceExpr::PatternMatchLambda(
            start_span,
            vec![binder],
            Box::new(match_expr),
        ))
    }

    /// Parse a single pattern in a def-match arm.
    /// Uses the full pattern parser with or-pattern and cons support.
    fn def_match_pattern(&mut self) -> Result<SurfacePattern, ParseError> {
        self.pattern_with_or()
    }

    /// Parse the body expression of a def-match arm.
    /// Stops at `|`, EOF, declaration starts, and termination hints.
    fn def_match_arm_body(
        &mut self,
        boundary: EquationArmBoundary,
    ) -> Result<SurfaceExpr, ParseError> {
        // Parse a full operator-precedence expression. The `|` arm delimiter is
        // lexed as `TokenKind::Pipe`, which is NOT an operator in the precedence
        // chain (logical-or is `TokenKind::Or` = `∨`/`||`) and cannot start an
        // atom, so `expr()` halts cleanly at the next `| pat =>` arm — while
        // still parsing binary operators and applications in the body
        // (e.g. `| n => n + n`, which the atom-only parser could not handle).
        // Declaration keywords (`def`/`theorem`/…) and termination hints
        // likewise cannot continue or start an expression, so they bound it too.
        if self.at_def_match_arm_boundary() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "expected definition equation body after `=>`".to_string(),
            });
        }

        let body = self.expr()?;
        // In `LetValue` mode the let-value indent gate has already bounded the
        // arm body: a dedented continuation (the let's own body, e.g. `go n`)
        // legitimately follows the final arm, so any token may appear here.
        // In a `where` block, the next helper's header (a newline-leading
        // ident the where-aware expression parser deliberately stopped at)
        // also legally bounds the final arm body.
        if boundary == EquationArmBoundary::Declaration
            && !(self.at_def_match_arm_boundary() || self.at_next_where_def_start())
        {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "unexpected token in definition equation body: {:?}",
                    self.current_kind()
                ),
            });
        }
        Ok(body)
    }

    fn at_def_match_arm_boundary(&self) -> bool {
        // `@foo` is an explicit application atom, not an attribute/declaration
        // start. `TokenKind::At` is also used by the top-level `@[attr]`
        // syntax, so the generic declaration-boundary predicate cannot
        // disambiguate the two without this one-token lookahead. In particular,
        // an equation body may legitimately begin with `@Bool.rec ...`.
        if matches!(self.current_kind(), TokenKind::At)
            && matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
        {
            return false;
        }
        matches!(
            self.current_kind(),
            TokenKind::Pipe | TokenKind::Where | TokenKind::End | TokenKind::Eof
        ) || self.at_termination_hint_end(0)
    }

    /// Inside a `where` block, the last arm body of an equation-form helper is
    /// legally bounded by the NEXT helper's header (a newline-leading ident the
    /// where-aware expression parser deliberately stopped at). Byte-identical
    /// to the stop condition in `expr_app.rs`, so the boundary set only gains
    /// positions where `expr()` already halted.
    fn at_next_where_def_start(&self) -> bool {
        self.in_where_block
            && matches!(self.current_kind(), TokenKind::Ident(_))
            && self
                .tokens
                .get(self.pos)
                .is_some_and(|t| t.preceded_by_newline)
            && self.peek_is_where_def_start(0)
    }

    pub(in crate::grammar) fn theorem_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        self.expect(&TokenKind::Colon)?;
        let ty = self.expr()?;

        // Proof can be provided with:
        // - := expr
        // - | pattern => expr (pattern matching without :=)
        let proof = if self.eat(&TokenKind::ColonEq) {
            self.expr()?
        } else if self.check(&TokenKind::Pipe) {
            // Pattern matching theorem: theorem foo : T | p1 => e1 | p2 => e2
            self.def_match_body(start_span)?
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected := or |, got {:?}", self.current_kind()),
            });
        };

        // Parse optional termination_by and decreasing_by clauses for recursive theorems
        let termination = self.parse_termination_hints();

        // Parse optional where clause with local definitions
        let where_decls = self.parse_where_local_defs();

        Ok(SurfaceDecl::Theorem {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            proof: Box::new(proof),
            attrs,
            termination,
            modifiers,
            where_decls,
        })
    }

    pub(in crate::grammar) fn axiom_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        self.expect(&TokenKind::Colon)?;
        let ty = self.expr()?;

        Ok(SurfaceDecl::Axiom {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            attrs,
            modifiers,
        })
    }

    /// Parse opaque declaration with explicit modifiers.
    pub(in crate::grammar) fn opaque_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        self.expect(&TokenKind::Colon)?;
        let ty = self.expr()?;

        // Optional value: `:= expr`
        let val = if self.eat(&TokenKind::ColonEq) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        Ok(SurfaceDecl::Opaque {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            val,
            attrs,
            modifiers,
        })
    }

    /// Parse optional `where` clause containing local definitions.
    ///
    /// ```text
    /// def foo : Nat := helper 42
    /// where
    ///   helper (n : Nat) : Nat := n + 1
    /// ```
    ///
    /// Returns an empty Vec if no `where` keyword is found.
    ///
    /// Reference: Lean 4 `src/Lean/Elab/MutualDef.lean` (elabWhereDeclsAsLetRec)
    pub(in crate::grammar) fn parse_where_local_defs(&mut self) -> Vec<WhereLocalDef> {
        if !self.eat(&TokenKind::Where) {
            return Vec::new();
        }

        // Enable in_where_block so the expression parser stops at identifiers
        // that start new where-definitions (ident ... :=).
        let saved_in_where = self.in_where_block;
        self.in_where_block = true;

        let mut defs = Vec::new();

        // Parse local definitions until we hit a declaration boundary,
        // termination hint, or EOF. Each definition starts with an identifier.
        while let TokenKind::Ident(_) = self.current_kind() {
            // Stop if this looks like a termination hint or another declaration
            if self.at_termination_hint_end(0) || self.is_decl_start() {
                break;
            }

            match self.parse_single_where_def() {
                Ok(def) => defs.push(def),
                Err(_) => break,
            }
        }

        self.in_where_block = saved_in_where;
        defs
    }

    /// Parse a single local definition inside a `where` block.
    ///
    /// Syntax: `name binders? (: ret_ty)? := body`
    /// or the equation form `name binders? (: ret_ty)? | pat => body | …`
    /// (a helper defined by pattern matching, e.g. `where go : Nat → Nat
    /// | 0 => 0 | k+1 => go k`) — desugared via [`Self::def_match_body`] exactly
    /// like a top-level `def`'s equation body.
    fn parse_single_where_def(&mut self) -> Result<WhereLocalDef, ParseError> {
        let start_span = self.current_span();

        // Parse the name
        let name = self.decl_name()?;

        // Parse optional binders
        let binders = self.optional_binders()?;

        // Parse optional return type annotation
        let ret_ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        // Body: either `:= expr` or the equation form `| pat => body | …`.
        let body = if self.check(&TokenKind::Pipe) {
            self.def_match_body(start_span)?
        } else {
            self.expect(&TokenKind::ColonEq)?;
            self.expr()?
        };

        let end_span = self.current_span();

        Ok(WhereLocalDef {
            span: Span::new(start_span.start, end_span.end),
            name,
            binders,
            ret_ty,
            body,
        })
    }
}
